{-# LANGUAGE BangPatterns         #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE PatternGuards        #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- |
-- Module      : Data.Array.Accelerate.Trafo.Simplify
-- Copyright   : [2012..2014] Manuel M T Chakravarty, Gabriele Keller, Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--

module Data.Array.Accelerate.Trafo.Simplify (

  Simplify(..),

) where

-- standard library
import Prelude                                          hiding ( exp, iterate )
import Data.List                                        ( nubBy )
import Data.Maybe
import Data.Monoid
import Data.Typeable
import Control.Applicative                              hiding ( Const )

-- friends
import Data.Array.Accelerate.AST                        hiding ( prj )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Analysis.Match
import Data.Array.Accelerate.Trafo.Base
import Data.Array.Accelerate.Trafo.Algebra
import Data.Array.Accelerate.Trafo.Shrink
import Data.Array.Accelerate.Trafo.Substitution
import Data.Array.Accelerate.Analysis.Shape
import Data.Array.Accelerate.Array.Sugar                ( Elt, Shape, Slice, toElt, fromElt, (:.)(..)
                                                        , Tuple(..), IsTuple, fromTuple, TupleRepr, shapeToList )
import Data.Array.Accelerate.Pretty.Print
import qualified Data.Array.Accelerate.Debug            as Stats


class Simplify f where
  simplify :: f -> f

instance Kit acc => Simplify (PreFun acc senv aenv f) where
  simplify = simplifyFun

instance Kit acc => Simplify (PreExp acc senv aenv e) where
  simplify = simplifyExp


-- Scalar optimisations
-- ====================

-- Common subexpression elimination finds computations that are performed at
-- least twice on a given execution path and eliminates the second and later
-- occurrences, replacing them with uses of saved values. This implements a
-- simplified version of that idea, where we look for the expressions of the
-- form:
--
--   let x = e1 in e2
--
-- and replace all occurrences of e1 in e2 with x. This is not full redundancy
-- elimination, but good enough to catch some cases, and in particular those
-- likely to be introduced by scalar composition of terms in the fusion process.
--
-- While it may seem that common subexpression elimination is always worthwhile,
-- as it reduces the number of arithmetic operations performed, this is not
-- necessarily advantageous. The simplest case in which it may not be desirable
-- is if it causes a register to be occupied for a long time in order to hold
-- the shared expression's value, which hence reduces the number of registers
-- available for other uses. Even worse is if the value has to be spilled to
-- memory because there are insufficient registers available. We sidestep this
-- tricky and target-dependent issue by, for now, simply ignoring it.
--
localCSE :: (Kit acc, Elt a, Elt b)
         => Gamma      acc env env senv aenv
         -> PreOpenExp acc env     senv aenv a
         -> PreOpenExp acc (env,a) senv aenv b
         -> Maybe (PreOpenExp acc env senv aenv b)
localCSE env bnd body
  | Just ix <- lookupExp env bnd = Stats.ruleFired "CSE" . Just $ inline body (Var ix)
  | otherwise                    = Nothing


-- Compared to regular Haskell, the scalar expression language of Accelerate is
-- rather limited in order to meet the restrictions of what can be efficiently
-- implemented on specialised hardware, such as GPUs. For example, to avoid
-- excessive SIMD divergence, we do not support any form of recursion or
-- iteration in scalar expressions. This harmonises well with the stratified
-- design of the Accelerate language: collective array operations comprise many
-- scalar computations that are executed in parallel, so for simplicity of
-- scheduling these operations we would like some assurance that each scalar
-- computation takes approximately the same time to execute as all others.
--
-- However, some computations are naturally expressed in terms of iteration. For
-- some problems, we can instead use generative techniques to implement the
-- program by defining a single step of a recurrence relation as an Accelerate
-- collective operation and using standard Haskell to unroll the loop a _fixed_
-- number of times.
--
-- However, this is outrageously slow because the intermediate values are
-- written to memory at the end of every iteration. Luckily the fusion process
-- will eliminate this intermediate memory traffic by combining the 'n'
-- collective operations into a single operation with 'n' instances of the loop
-- body. However, doing this we uncover an embarrassing secret: C compilers do
-- not compile C code, they compile _idiomatic_ C code.
--
-- This process recovers the iteration structure that was lost in the process of
-- fusing the collective operations. This allows a backend to generate explicit
-- loops in its target language.
--
recoverLoops
    :: (Kit acc, Elt b)
    => Gamma      acc env env senv aenv
    -> PreOpenExp acc env     senv aenv a
    -> PreOpenExp acc (env,a) senv aenv b
    -> Maybe (PreOpenExp acc env senv aenv b)
recoverLoops _ _ _
  = Nothing
{--
recoverLoops _ bnd e3
  -- To introduce scaler loops, we look for expressions of the form:
  --
  --   let x =
  --     let y = e1 in e2
  --   in e3
  --
  -- and if e2 and e3 are congruent, replace with:
  --
  --   iterate[2] (\y -> e2) e1
  --
  | Let e1 e2           <- bnd
  , Just REFL           <- matchEnvTop e2 e3
  , Just REFL           <- match e2 e3
  = Stats.ruleFired "loop recovery/intro" . Just
  $ Iterate (constant 2) e2 e1

  -- To merge expressions into a loop body, look for the pattern:
  --
  --   let x = iterate[n] f e1
  --   in e3
  --
  -- and if e3 matches the loop body, replace the let binding with the bare
  -- iteration with the trip count increased by one.
  --
  | Iterate n f e1      <- bnd
  , Just REFL           <- match f e3
  = Stats.ruleFired "loop recovery/merge" . Just
  $ Iterate (constant 1 `plus` n) f e1

  | otherwise
  = Nothing

  where
    plus :: PreOpenExp acc env aenv Int -> PreOpenExp acc env aenv Int -> PreOpenExp acc env aenv Int
    plus x y = PrimApp (PrimAdd numType) $ Tuple $ NilTup `SnocTup` x `SnocTup` y

    constant :: Int -> PreOpenExp acc env aenv Int
    constant i = Const ((),i)

    matchEnvTop :: (Elt s, Elt t)
                => PreOpenExp acc (env,s) aenv f
                -> PreOpenExp acc (env,t) aenv g
                -> Maybe (s :=: t)
    matchEnvTop _ _ = gcast REFL
--}


-- Walk a scalar expression applying simplifications to terms bottom-up.
--
-- TODO: Look for particular patterns of expressions that can be replaced by
--       something equivalent and simpler. In particular, indexing operations
--       introduced by the fusion transformation. This would benefit from a
--       rewrite rule schema.
--
-- TODO: Our implementation of CSE doesn't catch the following, where an
--       expression in the body is equivalent to an existing binding (presumably
--       through simplifications):
--
--       > let x = e in .. e ..
--
simplifyOpenExp
    :: forall acc env senv aenv e. Kit acc
    => Gamma acc env env senv aenv
    -> PreOpenExp acc env senv aenv e
    -> (Bool, PreOpenExp acc env senv aenv e)
simplifyOpenExp env = first getAny . cvtE
  where
    cvtE :: PreOpenExp acc env senv aenv t -> (Any, PreOpenExp acc env senv aenv t)
    cvtE exp = case exp of
      Let bnd body
        | Just reduct <- localCSE     env (snd bnd') (snd body') -> yes . snd $ cvtE reduct
        | Just reduct <- recoverLoops env (snd bnd') (snd body') -> yes . snd $ cvtE reduct
        | otherwise                                              -> Let <$> bnd' <*> body'
        where
          bnd'  = cvtE bnd
          env'  = PushExp env (snd bnd')
          body' = cvtE' (incExp env') body

      Var ix                    -> pure $ Var ix
      Const c                   -> pure $ Const c
      Tuple tup                 -> Tuple <$> cvtT tup
      Prj ix t                  -> prj ix (cvtE t)
      IndexNil                  -> pure IndexNil
      IndexAny                  -> pure IndexAny
      IndexCons sh sz           -> indexCons (cvtE sh) (cvtE sz)
      IndexHead sh              -> indexHead (cvtE sh)
      IndexTail sh              -> indexTail (cvtE sh)
      IndexSlice x ix sh        -> IndexSlice x <$> cvtE ix <*> cvtE sh
      IndexFull x ix sl         -> IndexFull x <$> cvtE ix <*> cvtE sl
      ToIndex sh ix             -> toIndex (cvtE sh) (cvtE ix)
      FromIndex sh ix           -> fromIndex (cvtE sh) (cvtE ix)
      Cond p t e                -> cond (cvtE p) (cvtE t) (cvtE e)
      PrimConst c               -> pure $ PrimConst c
      PrimApp f x               -> evalPrimApp env f <$> cvtE x
      Index a sh                -> Index a <$> cvtE sh
      LinearIndex a i           -> LinearIndex a <$> cvtE i
      Shape a                   -> pure $ Shape a
      ShapeSize sh              -> shapeSize (cvtE sh)
      Intersect s t             -> cvtE s `intersect` cvtE t
      Union s t                 -> cvtE s `union` cvtE t
      IndexS x sh               -> IndexS x <$> cvtE sh
      LinearIndexS x i          -> LinearIndexS x <$> cvtE i
      ShapeS x                  -> pure $ ShapeS x
      Foreign ff f e            -> Foreign ff <$> first Any (simplifyOpenFun EmptyExp f) <*> cvtE e
      While p f x               -> While <$> cvtF env p <*> cvtF env f <*> cvtE x

    cvtT :: Tuple (PreOpenExp acc env senv aenv) t -> (Any, Tuple (PreOpenExp acc env senv aenv) t)
    cvtT NilTup        = pure NilTup
    cvtT (SnocTup t e) = SnocTup <$> cvtT t <*> cvtE e

    cvtE' :: Gamma acc env' env' senv aenv -> PreOpenExp acc env' senv aenv e' -> (Any, PreOpenExp acc env' senv aenv e')
    cvtE' env' = first Any . simplifyOpenExp env'

    cvtF :: Gamma acc env' env' senv aenv -> PreOpenFun acc env' senv aenv f -> (Any, PreOpenFun acc env' senv aenv f)
    cvtF env' = first Any . simplifyOpenFun env'

    -- Return the minimal set of unique shapes to intersect. This is a bit
    -- inefficient, but the number of shapes is expected to be small so should
    -- be fine in practice.
    --
    intersect :: Shape t
              => (Any, PreOpenExp acc env senv aenv t)
              -> (Any, PreOpenExp acc env senv aenv t)
              -> (Any, PreOpenExp acc env senv aenv t)
    intersect (c1, sh1) (c2, sh2)
      | Nothing <- match sh sh' = Stats.ruleFired "intersect" (yes sh')
      | otherwise               = (c1 <> c2, sh')
      where
        sh      = Intersect sh1 sh2
        sh'     = foldl1 Intersect
                $ nubBy (\x y -> isJust (match x y))
                $ leaves sh1 ++ leaves sh2

        leaves :: Shape t => PreOpenExp acc env senv aenv t -> [PreOpenExp acc env senv aenv t]
        leaves (Intersect x y)  = leaves x ++ leaves y
        leaves rest             = [rest]

    -- Return the minimal set of unique shapes to take the union of. This is a bit
    -- inefficient, but the number of shapes is expected to be small so should
    -- be fine in practice.
    --
    union :: Shape t
          => (Any, PreOpenExp acc env senv aenv t)
          -> (Any, PreOpenExp acc env senv aenv t)
          -> (Any, PreOpenExp acc env senv aenv t)
    union (c1, sh1) (c2, sh2)
      | Nothing <- match sh sh' = Stats.ruleFired "union" (yes sh')
      | otherwise               = (c1 <> c2, sh')
      where
        sh      = Union sh1 sh2
        sh'     = foldl1 Union
                $ nubBy (\x y -> isJust (match x y))
                $ leaves sh1 ++ leaves sh2

        leaves :: Shape t => PreOpenExp acc env senv aenv t -> [PreOpenExp acc env senv aenv t]
        leaves (Union x y)  = leaves x ++ leaves y
        leaves rest         = [rest]


    -- Simplify conditional expressions, in particular by eliminating branches
    -- when the predicate is a known constant.
    --
    cond :: forall t. Elt t
         => (Any, PreOpenExp acc env senv aenv Bool)
         -> (Any, PreOpenExp acc env senv aenv t)
         -> (Any, PreOpenExp acc env senv aenv t)
         -> (Any, PreOpenExp acc env senv aenv t)
    cond p@(_,p') t@(_,t') e@(_,e')
      | Const True  <- p'        = Stats.knownBranch "True"      (yes t')
      | Const False <- p'        = Stats.knownBranch "False"     (yes e')
      | Just REFL <- match t' e' = Stats.knownBranch "redundant" (yes e')
      | otherwise                = Cond <$> p <*> t <*> e

    -- If we are projecting elements from a tuple structure or tuple of constant
    -- valued tuple, pick out the appropriate component directly.
    --
    prj :: forall s t. (Elt s, Elt t, IsTuple t)
        => TupleIdx (TupleRepr t) s
        -> (Any, PreOpenExp acc env senv aenv t)
        -> (Any, PreOpenExp acc env senv aenv s)
    prj ix exp@(_,exp')
      | Tuple t <- exp' = Stats.inline "prj/Tuple" . yes $ prjT ix t
      | Const c <- exp' = Stats.inline "prj/Const" . yes $ prjC ix (fromTuple (toElt c :: t))
      | Let a b <- exp' = Stats.ruleFired "prj/Let"      $ cvtE (Let a (Prj ix b))
      | otherwise       = Prj ix <$> exp
      where
        prjT :: TupleIdx tup s -> Tuple (PreOpenExp acc env senv aenv) tup -> PreOpenExp acc env senv aenv s
        prjT ZeroTupIdx       (SnocTup _ e) = e
        prjT (SuccTupIdx idx) (SnocTup t _) = prjT idx t
        prjT _                _             = error "DO MORE OF WHAT MAKES YOU HAPPY"

        prjC :: TupleIdx tup s -> tup -> PreOpenExp acc env senv aenv s
        prjC ZeroTupIdx       (_,   v) = Const (fromElt v)
        prjC (SuccTupIdx idx) (tup, _) = prjC idx tup

    -- Shape manipulations
    --
    indexCons :: (Slice sl, Elt sz)
              => (Any, PreOpenExp acc env senv aenv sl)
              -> (Any, PreOpenExp acc env senv aenv sz)
              -> (Any, PreOpenExp acc env senv aenv (sl :. sz))
    indexCons (_,IndexNil) (_,Const c)
      | Just c'         <- cast c       -- EltRepr Z ~ EltRepr ()
      = Stats.ruleFired "Z:.const" $ yes (Const c')
    indexCons (_,IndexNil) (_,IndexHead sz')
      | 1               <- expDim sz'   -- no type information that this is a 1D shape, hence gcast next
      , Just sh'        <- gcast sz'
      = Stats.ruleFired "Z:.indexHead" $ yes sh'
    indexCons (_,IndexTail sl') (_,IndexHead sz')
      | Just REFL       <- match sl' sz'
      = Stats.ruleFired "indexTail:.indexHead" $ yes sl'
    indexCons sl sz
      = IndexCons <$> sl <*> sz

    indexHead :: forall sl sz. (Slice sl, Elt sz) => (Any, PreOpenExp acc env senv aenv (sl :. sz)) -> (Any, PreOpenExp acc env senv aenv sz)
    indexHead (_, Const c)
      | _ :. sz <- toElt c :: sl :. sz  = Stats.ruleFired "indexHead/const"     $ yes (Const (fromElt sz))
    indexHead (_, IndexCons _ sz)       = Stats.ruleFired "indexHead/indexCons" $ yes sz
    indexHead sh                        = IndexHead <$> sh

    indexTail :: forall sl sz. (Slice sl, Elt sz) => (Any, PreOpenExp acc env senv aenv (sl :. sz)) -> (Any, PreOpenExp acc env senv aenv sl)
    indexTail (_, Const c)
      | sl :. _ <- toElt c :: sl :. sz  = Stats.ruleFired "indexTail/const"     $ yes (Const (fromElt sl))
    indexTail (_, IndexCons sl _)       = Stats.ruleFired "indexTail/indexCons" $ yes sl
    indexTail sh                        = IndexTail <$> sh

    shapeSize :: forall sh. Shape sh => (Any, PreOpenExp acc env senv aenv sh) -> (Any, PreOpenExp acc env senv aenv Int)
    shapeSize (_, Const c) = Stats.ruleFired "shapeSize/const" $ yes (Const (product (shapeToList (toElt c :: sh))))
    shapeSize sh           = ShapeSize <$> sh

    toIndex :: forall sh. Shape sh => (Any, PreOpenExp acc env senv aenv sh) -> (Any, PreOpenExp acc env senv aenv sh) -> (Any, PreOpenExp acc env senv aenv Int)
    toIndex  (_,sh) (_,FromIndex sh' ix)
      | Just REFL <- match sh sh' = Stats.ruleFired "toIndex/fromIndex" $ yes ix
    toIndex sh ix                 = ToIndex <$> sh <*> ix

    fromIndex :: forall sh. Shape sh => (Any, PreOpenExp acc env senv aenv sh) -> (Any, PreOpenExp acc env senv aenv Int) -> (Any, PreOpenExp acc env senv aenv sh)
    fromIndex  (_,sh) (_,ToIndex sh' ix)
      | Just REFL <- match sh sh' = Stats.ruleFired "fromIndex/toIndex" $ yes ix
    fromIndex sh ix               = FromIndex <$> sh <*> ix

    first :: (a -> a') -> (a,b) -> (a',b)
    first f (x,y) = (f x, y)

    yes :: x -> (Any, x)
    yes x = (Any True, x)


-- Simplification for open functions
--
simplifyOpenFun
    :: Kit acc
    => Gamma acc env env senv aenv
    -> PreOpenFun acc env senv aenv f
    -> (Bool, PreOpenFun acc env senv aenv f)
simplifyOpenFun env (Body e) = Body <$> simplifyOpenExp env  e
simplifyOpenFun env (Lam f)  = Lam  <$> simplifyOpenFun env' f
  where
    env' = incExp env `PushExp` Var ZeroIdx


-- Simplify closed expressions and functions. The process is applied repeatedly
-- until no more changes are made.
--
simplifyExp :: Kit acc => PreExp acc senv aenv t -> PreExp acc senv aenv t
simplifyExp = iterate (show . prettyPreExp prettyAcc 0 0 noParens) (simplifyOpenExp EmptyExp)

simplifyFun :: Kit acc => PreFun acc senv aenv f -> PreFun acc senv aenv f
simplifyFun = iterate (show . prettyPreFun prettyAcc 0) (simplifyOpenFun EmptyExp)


-- NOTE: [Simplifier iterations]
--
-- Run the simplification pass _before_ the shrinking step. There are cases
-- where it is better to run shrinking first, and then simplification would
-- complete in a single step, but the converse is also true. However, as
-- shrinking can remove some structure of the let bindings, which might be
-- useful for the transformations (e.g. loop recovery) we want to maintain this
-- information for at least the first pass.
--
-- We always apply the simplification step once. Following this, we iterate
-- shrinking and simplification until the expression no longer changes. Both
-- shrink and simplify return a boolean indicating whether any work was done; we
-- stop as soon as either returns false.
--
-- With internal checks on, we also issue a warning if the iteration limit is
-- reached, but it was still possible to make changes to the expression.
--
{-# SPECIALISE iterate :: (Exp senv aenv t -> String) -> (Exp senv aenv t -> (Bool, Exp senv aenv t)) -> Exp senv aenv t -> Exp senv aenv t #-}
{-# SPECIALISE iterate :: (Fun senv aenv t -> String) -> (Fun senv aenv t -> (Bool, Fun senv aenv t)) -> Fun senv aenv t -> Fun senv aenv t #-}

iterate
    :: forall f a. (Match f, Shrink (f a))
    => (f a -> String)
    -> (f a -> (Bool, f a))
    -> f a
    -> f a
iterate ppr f = fix 0 . setup . simplify'
  where
    -- The maximum number of simplifier iterations. To be conservative and avoid
    -- excessive run times, we set this value very low.
    --
    lIMIT       = 1

    simplify'   = Stats.simplifierDone . f
    setup (_,x) = msg x x

    fix :: Int -> f a -> f a
    fix !i !x0
      | i >= lIMIT      = $internalWarning "iterate" "iteration limit reached" (x0 ==^ f x0) x0
      | not shrunk      = x1
      | not simplified  = x2
      | otherwise       = fix (i+1) x2
      where
        (shrunk,     x1) = trace $ shrink' x0
        (simplified, x2) = trace $ simplify' x1

    -- debugging support
    --
    u ==^ (_,v)         = isJust (match u v)

    trace v@(changed,x)
      | changed         = msg x v
      | otherwise       = v

    msg :: f a -> x -> x
    msg x next          = Stats.trace Stats.dump_simpl_iterations (unlines [ "simplifier done", ppr x ]) next

