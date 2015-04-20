{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PatternGuards       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_HADDOCK prune #-}
-- |
-- Module      : Data.Array.Accelerate.Interpreter
-- Copyright   : [2008..2014] Manuel M T Chakravarty, Gabriele Keller
--               [2008..2009] Sean Lee
--               [2009..2014] Trevor L. McDonell
--               [2014..2014] Frederik M. Madsen
-- License     : BSD3
--
-- Maintainer  : Manuel M T Chakravarty <chak@cse.unsw.edu.au>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- This interpreter is meant to be a reference implementation of the semantics
-- of the embedded array language.  The emphasis is on defining the semantics
-- clearly, not on performance.
--
-- /Surface types versus representation types/
--
-- As a general rule, we perform all computations on representation types and we store all data
-- as values of representation types.  To guarantee the type safety of the interpreter, this
-- currently implies a lot of conversions between surface and representation types.  Optimising
-- the code by eliminating back and forth conversions is fine, but only where it doesn't
-- negatively affects clarity — after all, the main purpose of the interpreter is to serve as an
-- executable specification.
--

module Data.Array.Accelerate.Interpreter (

  -- * Interpret an array expression
  Arrays, run, run1, streamOut,

  -- Internal (hidden)
  evalPrim, evalPrimConst, evalPrj

) where

-- standard libraries
import Control.Monad
import Data.Bits
import Data.Char                                        ( chr, ord )
import Prelude                                          hiding ( sum )
import System.IO.Unsafe                                 ( unsafePerformIO )

-- friends
import Data.Array.Accelerate.AST
import Data.Array.Accelerate.Array.Data
import Data.Array.Accelerate.Array.Representation               ( SliceIndex(..) )
import Data.Array.Accelerate.Array.Sugar
import Data.Array.Accelerate.Debug                              ( queryFlag, chunk_size )
import Data.Array.Accelerate.Error
import Data.Array.Accelerate.Trafo                              hiding ( Delayed )
import Data.Array.Accelerate.Product
import Data.Array.Accelerate.Type
import qualified Data.Array.Accelerate.Smart                    as Sugar
import qualified Data.Array.Accelerate.Trafo                    as AST
import qualified Data.Array.Accelerate.Array.Representation     as R


-- Program execution
-- -----------------

-- | Run a complete embedded array program using the reference interpreter.
--
run :: Arrays a => Sugar.Acc a -> a
run acc
  = let a = convertAccWith config acc
    in  evalOpenAcc a Empty


-- | Prepare and run an embedded array program of one argument
--
run1 :: (Arrays a, Arrays b) => (Sugar.Acc a -> Sugar.Acc b) -> a -> b
run1 afun
  = let f = convertAfunWith config afun
    in  evalOpenAfun f Empty


-- | Stream a lazily read list of input arrays through the given program,
-- collecting results as we go
--
streamOut :: Arrays a => Sugar.Seq [a] -> [a]
streamOut seq = let seq' = convertSeqWith config seq
                in evalDelayedSeq defaultSeqConfig seq'


config :: Phase
config =  Phase
  { recoverAccSharing      = True
  , recoverExpSharing      = True
  , recoverSeqSharing      = True
  , floatOutAccFromExp     = True
  , enableAccFusion        = True
  , convertOffsetOfSegment = False
--  , vectoriseSequences     = True
  }


-- Delayed Arrays
-- --------------

-- Note that in contrast to the representation used in the optimised AST, the
-- delayed array representation used here is _only_ for delayed arrays --- we do
-- not require an optional Manifest|Delayed data type to evaluate the program.
--
data Delayed a where
  Delayed :: (Shape sh, Elt e)
          => sh
          -> (sh -> e)
          -> (Int -> e)
          -> Delayed (Array sh e)

-- Array expression evaluation
-- ---------------------------

type EvalAcc acc = forall aenv a. acc aenv a -> Val aenv -> a

-- Evaluate an open array function
--
evalOpenAfun :: DelayedOpenAfun aenv f -> Val aenv -> f
evalOpenAfun (Alam  f) aenv = \a -> evalOpenAfun f (aenv `Push` a)
evalOpenAfun (Abody b) aenv = evalOpenAcc b aenv


-- The core interpreter for optimised array programs
--
evalOpenAcc
    :: forall aenv a.
       DelayedOpenAcc aenv a
    -> Val aenv
    -> a
evalOpenAcc AST.Delayed{}       _    = $internalError "evalOpenAcc" "expected manifest array"
evalOpenAcc (AST.Manifest pacc) aenv =
  let
      manifest :: DelayedOpenAcc aenv a' -> a'
      manifest acc = evalOpenAcc acc aenv

      delayed :: DelayedOpenAcc aenv (Array sh e) -> Delayed (Array sh e)
      delayed AST.Manifest{}  = $internalError "evalOpenAcc" "expected delayed array"
      delayed AST.Delayed{..} = Delayed (evalE extentD) (evalF indexD) (evalF linearIndexD)

      evalE :: DelayedExp () aenv t -> t
      evalE exp = evalPreExp evalOpenAcc exp aenv (EmptyS, 0)

      evalF :: DelayedFun () aenv f -> f
      evalF fun = evalPreFun evalOpenAcc fun aenv (EmptyS, 0)

      evalOp :: PreOpenArrayOp (DelayedOpenAcc aenv) DelayedOpenAcc () aenv a -> a
      evalOp op = case op of        
        -- Producers
        -- ---------
        Map f acc                   -> mapOp (evalF f) (delayed acc)
        Generate sh f               -> generateOp (evalE sh) (evalF f)
        Transform sh p f acc        -> transformOp (evalE sh) (evalF p) (evalF f) (delayed acc)
        Backpermute sh p acc        -> backpermuteOp (evalE sh) (evalF p) (delayed acc)
        ZipWith f acc1 acc2         -> zipWithOp (evalF f) (delayed acc1) (delayed acc2)
        Replicate slice slix acc    -> replicateOp slice (evalE slix) (manifest acc)
        Slice slice acc slix        -> sliceOp slice (manifest acc) (evalE slix)

        -- Consumers
        -- ---------
        Fold f z acc                -> foldOp (evalF f) (evalE z) (delayed acc)
        Fold1 f acc                 -> fold1Op (evalF f) (delayed acc)
        FoldSeg f z acc seg         -> foldSegOp (evalF f) (evalE z) (delayed acc) (delayed seg)
        Fold1Seg f acc seg          -> fold1SegOp (evalF f) (delayed acc) (delayed seg)
        Scanl f z acc               -> scanlOp (evalF f) (evalE z) (delayed acc)
        Scanl' f z acc              -> scanl'Op (evalF f) (evalE z) (delayed acc)
        Scanl1 f acc                -> scanl1Op (evalF f) (delayed acc)
        Scanr f z acc               -> scanrOp (evalF f) (evalE z) (delayed acc)
        Scanr' f z acc              -> scanr'Op (evalF f) (evalE z) (delayed acc)
        Scanr1 f acc                -> scanr1Op (evalF f) (delayed acc)
        Permute f def p acc         -> permuteOp (evalF f) (manifest def) (evalF p) (delayed acc)
        Stencil sten b acc          -> stencilOp (evalF sten) b (manifest acc)
        Stencil2 sten b1 acc1 b2 acc2-> stencil2Op (evalF sten) b1 (manifest acc1) b2 (manifest acc2)
  in
  case pacc of
    Avar ix                     -> prj ix aenv
    Alet acc1 acc2              -> evalOpenAcc acc2 (aenv `Push` manifest acc1)
    Atuple atup                 -> toAtuple $ evalAtuple atup aenv
    Aprj ix atup                -> evalPrj ix . fromAtuple $ manifest atup
    Apply afun acc              -> evalOpenAfun afun aenv  $ manifest acc
    Aforeign _ afun acc         -> evalOpenAfun afun Empty $ manifest acc
    Acond p acc1 acc2
      | evalE p                 -> manifest acc1
      | otherwise               -> manifest acc2

    Awhile cond body acc        -> go (manifest acc)
      where
        p       = evalOpenAfun cond aenv
        f       = evalOpenAfun body aenv
        go !x
          | p x ! Z     = go (f x)
          | otherwise   = x

    Use arr                     -> toArr arr
    Unit e                      -> unitOp (evalE e)
    Reshape sh acc              -> reshapeOp (evalE sh) (manifest acc)
    ArrayOp op                  -> evalOp op
    Collect s                   -> evalSeq defaultSeqConfig s aenv

-- Array tuple construction and projection
--
evalAtuple :: Atuple (DelayedOpenAcc aenv) t -> Val aenv -> t
evalAtuple NilAtup        _    = ()
evalAtuple (SnocAtup t a) aenv = (evalAtuple t aenv, evalOpenAcc a aenv)


-- Array primitives
-- ----------------

unitOp :: Elt e => e -> Scalar e
unitOp e = newArray Z (const e)

generateOp
    :: (Shape sh, Elt e)
    => sh
    -> (sh -> e)
    -> Array sh e
generateOp = newArray

transformOp
    :: (Shape sh, Shape sh', Elt b)
    => sh'
    -> (sh' -> sh)
    -> (a -> b)
    -> Delayed (Array sh a)
    -> Array sh' b
transformOp sh' p f (Delayed _ xs _)
  = newArray sh' (\ix -> f (xs $ p ix))

reshapeOp
    :: (Shape sh, Shape sh', Elt e)
    => sh
    -> Array sh' e
    -> Array sh  e
reshapeOp newShape arr@(Array _ adata)
  = $boundsCheck "reshape" ("shape mismatch: " ++ show (size newShape) ++ "/=" ++ show (size (shape arr))) (size newShape == size (shape arr))
  $ Array (fromElt newShape) adata

replicateOp
    :: (Shape sh, Shape sl, Elt slix, Elt e)
    => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
    -> slix
    -> Array sl e
    -> Array sh e
replicateOp slice slix arr
  = newArray (toElt sh) (\ix -> arr ! liftToElt pf ix)
  where
    (sh, pf) = extend slice (fromElt slix) (fromElt (shape arr))

extend :: SliceIndex slix sl co dim
       -> slix
       -> sl
       -> (dim, dim -> sl)
extend SliceNil              ()        ()       = ((), const ())
extend (SliceAll sliceIdx)   (slx, ()) (sl, sz)
  = let (dim', f') = extend sliceIdx slx sl
    in  ((dim', sz), \(ix, i) -> (f' ix, i))
extend (SliceFixed sliceIdx) (slx, sz) sl
  = let (dim', f') = extend sliceIdx slx sl
    in  ((dim', sz), \(ix, _) -> f' ix)

sliceOp
    :: (Shape sh, Shape sl, Elt slix, Elt e)
    => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
    -> Array sh e
    -> slix
    -> Array sl e
sliceOp slice arr slix
  = newArray (toElt sh') (\ix -> arr ! liftToElt pf ix)
  where
    (sh', pf) = restrict slice (fromElt slix) (fromElt (shape arr))

restrict :: SliceIndex slix sl co sh
         -> slix
         -> sh
         -> (sl, sl -> sh)
restrict SliceNil              ()        ()       = ((), const ())
restrict (SliceAll sliceIdx)   (slx, ()) (sl, sz)
  = let (sl', f') = restrict sliceIdx slx sl
    in  ((sl', sz), \(ix, i) -> (f' ix, i))
restrict (SliceFixed sliceIdx) (slx, i)  (sl, sz)
  = let (sl', f') = restrict sliceIdx slx sl
    in  $indexCheck "slice" i sz $ (sl', \ix -> (f' ix, i))

mapOp :: (Shape sh, Elt a, Elt b)
      => (a -> b)
      -> Delayed (Array sh a)
      -> Array sh b
mapOp f (Delayed sh xs _)
  = newArray sh (\ix -> f (xs ix))

zipWithOp
    :: (Shape sh, Elt a, Elt b, Elt c)
    => (a -> b -> c)
    -> Delayed (Array sh a)
    -> Delayed (Array sh b)
    -> Array sh c
zipWithOp f (Delayed shx xs _) (Delayed shy ys _)
  = newArray (shx `intersect` shy) (\ix -> f (xs ix) (ys ix))

zipWith'Op
    :: (Shape sh, Elt a)
    => (a -> a -> a)
    -> Delayed (Array sh a)
    -> Delayed (Array sh a)
    -> Array sh a
zipWith'Op f (Delayed shx xs _) (Delayed shy ys _)
  = newArray (shx `union` shy) (\ix -> if ix `outside` shx
                                       then ys ix
                                       else if ix `outside` shy
                                       then xs ix
                                       else f (xs ix) (ys ix))
  where
    a `outside` b = or $ zipWith (>=) (shapeToList a) (shapeToList b)

foldOp
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh :. Int) e)
    -> Array sh e
foldOp f z (Delayed (sh :. n) arr _)
  | size sh == 0
  = newArray (listToShape . map (max 1) . shapeToList $ sh) (const z)

  | otherwise
  = newArray sh (\ix -> iter (Z:.n) (\(Z:.i) -> arr (ix :. i)) f z)

fold1Op
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> Delayed (Array (sh :. Int) e)
    -> Array sh e
fold1Op f (Delayed (sh :. n) arr _)
  = newArray sh (\ix -> iter1 (Z:.n) (\(Z:.i) -> arr (ix :. i)) f)

foldSegOp
    :: forall sh e i. (Shape sh, Elt e, Elt i, IsIntegral i)
    => (e -> e -> e)
    -> e
    -> Delayed (Array (sh :. Int) e)
    -> Delayed (Segments i)
    -> Array (sh :. Int) e
foldSegOp f z (Delayed (sh :. _) arr _) seg@(Delayed (Z :. n) _ _)
  | IntegralDict <- integralDict (integralType :: IntegralType i)
  = newArray (sh :. n)
  $ \(sz :. ix) -> let start = fromIntegral $ offset ! (Z :. ix)
                       end   = fromIntegral $ offset ! (Z :. ix+1)
                   in
                   iter (Z :. end-start) (\(Z:.i) -> arr (sz :. start+i)) f z
  where
    offset      = scanlOp (+) 0 seg

fold1SegOp
    :: forall sh e i. (Shape sh, Elt e, Elt i, IsIntegral i)
    => (e -> e -> e)
    -> Delayed (Array (sh :. Int) e)
    -> Delayed (Segments i)
    -> Array (sh :. Int) e
fold1SegOp f (Delayed (sh :. _) arr _) seg@(Delayed (Z :. n) _ _)
  | IntegralDict <- integralDict (integralType :: IntegralType i)
  = newArray (sh :. n)
  $ \(sz :. ix) -> let start = fromIntegral $ offset ! (Z :. ix)
                       end   = fromIntegral $ offset ! (Z :. ix+1)
                   in
                   iter1 (Z :. end-start) (\(Z:.i) -> arr (sz :. start+i)) f
  where
    offset      = scanlOp (+) 0 seg

scanl1Op
    :: Elt e
    => (e -> e -> e)
    -> Delayed (Vector e)
    -> Vector e
scanl1Op f (Delayed sh@(Z :. n) _ ain)
  = adata `seq` Array (fromElt sh) adata
  where
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData n

      let write (Z:.0) = unsafeWriteArrayData aout 0 (fromElt $ ain 0)
          write (Z:.i) = do
            x <- unsafeReadArrayData aout (i-1)
            y <- return . fromElt $  ain  i
            unsafeWriteArrayData aout i (f' x y)

      iter1 sh write (>>)
      return (aout, undefined)

scanlOp
    :: Elt e
    => (e -> e -> e)
    -> e
    -> Delayed (Vector e)
    -> Vector e
scanlOp f z (Delayed (Z :. n) _ ain)
  = adata `seq` Array (fromElt sh') adata
  where
    sh'         = Z :. n+1
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData (n+1)

      let write (Z:.0) = unsafeWriteArrayData aout 0 (fromElt z)
          write (Z:.i) = do
            x <- unsafeReadArrayData aout (i-1)
            y <- return . fromElt $  ain  (i-1)
            unsafeWriteArrayData aout i (f' x y)

      iter sh' write (>>) (return ())
      return (aout, undefined)

scanl'Op
    :: Elt e
    => (e -> e -> e)
    -> e
    -> Delayed (Vector e)
    -> (Vector e, Scalar e)
scanl'Op f z (scanlOp f z -> arr)
  = let
        arr'    = case arr of Array _ adata -> Array ((), n-1) adata
        sum     = unitOp (arr ! (Z:.n-1))
        n       = size (shape arr)
    in
    (arr', sum)

scanrOp
    :: Elt e
    => (e -> e -> e)
    -> e
    -> Delayed (Vector e)
    -> Vector e
scanrOp f z (Delayed (Z :. n) _ ain)
  = adata `seq` Array (fromElt sh') adata
  where
    sh'         = Z :. n+1
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData (n+1)

      let write (Z:.0) = unsafeWriteArrayData aout n (fromElt z)
          write (Z:.i) = do
            x <- unsafeReadArrayData aout (n-i+1)
            y <- return . fromElt $  ain  (n-i)
            unsafeWriteArrayData aout (n-i) (f' x y)

      iter sh' write (>>) (return ())
      return (aout, undefined)

scanr1Op
    :: Elt e
    => (e -> e -> e)
    -> Delayed (Vector e)
    -> Vector e
scanr1Op f (Delayed sh@(Z :. n) _ ain)
  = adata `seq` Array (fromElt sh) adata
  where
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData n

      let write (Z:.0) = unsafeWriteArrayData aout (n-1) (fromElt $ ain (n-1))
          write (Z:.i) = do
            x <- unsafeReadArrayData aout (n-i)
            y <- return . fromElt $  ain  (n-i-1)
            unsafeWriteArrayData aout (n-i-1) (f' x y)

      iter1 sh write (>>)
      return (aout, undefined)

scanr'Op
    :: forall e. Elt e
    => (e -> e -> e)
    -> e
    -> Delayed (Vector e)
    -> (Vector e, Scalar e)
scanr'Op f z (Delayed (Z :. n) _ ain)
  = (Array ((),n) adata, unitOp (toElt asum))
  where
    f' x y      = sinkFromElt2 f (fromElt x) y
    --
    (adata, asum) = runArrayData $ do
      aout <- newArrayData n

      let trav i !y | i < 0     = return y
          trav i y              = do
            unsafeWriteArrayData aout i y
            trav (i-1) (f' (ain i) y)

      final <- trav (n-1) (fromElt z)
      return (aout, final)

permuteOp
    :: (Shape sh, Shape sh', Elt e)
    => (e -> e -> e)
    -> Array sh' e
    -> (sh -> sh')
    -> Delayed (Array sh  e)
    -> Array sh' e
permuteOp f def@(Array _ adef) p (Delayed sh _ ain)
  = adata `seq` Array (fromElt sh') adata
  where
    sh'         = shape def
    n'          = size sh'
    f'          = sinkFromElt2 f
    --
    (adata, _)  = runArrayData $ do
      aout <- newArrayData n'

      let -- initialise array with default values
          init i
            | i >= n'   = return ()
            | otherwise = do
                x <- unsafeReadArrayData adef i
                unsafeWriteArrayData aout i x
                init (i+1)

          -- project each element onto the destination array and update
          update src
            = let dst   = p src
                  i     = toIndex sh  src
                  j     = toIndex sh' dst
              in
              unless (fromElt dst == R.ignore) $ do
                x <- return . fromElt $  ain  i
                y <- unsafeReadArrayData aout j
                unsafeWriteArrayData aout j (f' x y)

      init 0
      iter sh update (>>) (return ())
      return (aout, undefined)

backpermuteOp
    :: (Shape sh, Shape sh', Elt e)
    => sh'
    -> (sh' -> sh)
    -> Delayed (Array sh e)
    -> Array sh' e
backpermuteOp sh' p (Delayed _ arr _)
  = newArray sh' (\ix -> arr $ p ix)

stencilOp
    :: (Elt a, Elt b, Stencil sh a stencil)
    => (stencil -> b)
    -> Boundary (EltRepr a)
    -> Array sh a
    -> Array sh b
stencilOp stencil boundary arr
  = newArray sh f
  where
    f           = stencil . stencilAccess bounded
    sh          = shape arr
    --
    bounded ix  =
      case bound sh ix boundary of
        Left v    -> toElt v
        Right ix' -> arr ! ix'

stencil2Op
    :: (Elt a, Elt b, Elt c, Stencil sh a stencil1, Stencil sh b stencil2)
    => (stencil1 -> stencil2 -> c)
    -> Boundary (EltRepr a)
    -> Array sh a
    -> Boundary (EltRepr b)
    -> Array sh b
    -> Array sh c
stencil2Op stencil boundary1 arr1 boundary2 arr2
  = newArray (sh1 `intersect` sh2) f
  where
    sh1         = shape arr1
    sh2         = shape arr2
    f ix        = stencil (stencilAccess bounded1 ix)
                          (stencilAccess bounded2 ix)

    bounded1 ix =
      case bound sh1 ix boundary1 of
        Left v    -> toElt v
        Right ix' -> arr1 ! ix'

    bounded2 ix =
      case bound sh2 ix boundary2 of
        Left v    -> toElt v
        Right ix' -> arr2 ! ix'

toSeqOp :: forall slix sl dim co e proxy. (Elt slix, Shape sl, Shape dim, Elt e)
        => SliceIndex (EltRepr slix)
                      (EltRepr sl)
                      co
                      (EltRepr dim)
        -> proxy slix
        -> Array dim e
        -> [Array sl e]
toSeqOp sliceIndex _ arr = map (sliceOp sliceIndex arr :: slix -> Array sl e)
                               (enumSlices sliceIndex (shape arr))

-- Scalar expression evaluation
-- ----------------------------

-- Evaluate a closed scalar expression
--
evalPreExp :: EvalAcc acc -> PreExp acc senv aenv t -> Val aenv -> Val' senv -> t
evalPreExp evalAcc e = evalPreOpenExp evalAcc e EmptyElt

-- Evaluate a closed scalar function
--
evalPreFun :: EvalAcc acc -> PreFun acc senv aenv t -> Val aenv -> Val' senv -> t
evalPreFun evalAcc f = evalPreOpenFun evalAcc f EmptyElt

-- Evaluate an open scalar function
--
evalPreOpenFun :: EvalAcc acc -> PreOpenFun acc env senv aenv t -> ValElt env -> Val aenv -> Val' senv -> t
evalPreOpenFun evalAcc (Body e) env aenv senv = evalPreOpenExp evalAcc e env aenv senv
evalPreOpenFun evalAcc (Lam f)  env aenv senv =
  \x -> evalPreOpenFun evalAcc f (env `PushElt` fromElt x) aenv senv


-- Evaluate an open scalar expression
--
-- NB: The implementation of 'Index' and 'Shape' demonstrate clearly why
--     array expressions must be hoisted out of scalar expressions before code
--     execution. If these operations are in the body of a function that gets
--     mapped over an array, the array argument would be evaluated many times
--     leading to a large amount of wasteful recomputation.
--
evalPreOpenExp
    :: forall acc env senv aenv t.
       EvalAcc acc
    -> PreOpenExp acc env senv aenv t
    -> ValElt env
    -> Val aenv
    -> Val' senv
    -> t
evalPreOpenExp evalAcc pexp env aenv senv =
  let
      evalE :: PreOpenExp acc env senv aenv t' -> t'
      evalE e = evalPreOpenExp evalAcc e env aenv senv

      evalF :: PreOpenFun acc env senv aenv f' -> f'
      evalF f = evalPreOpenFun evalAcc f env aenv senv

      evalA :: acc aenv a -> a
      evalA a = evalAcc a aenv
  in
  case pexp of
    Let exp1 exp2               -> let !v1  = evalE exp1
                                       env' = env `PushElt` fromElt v1
                                   in  evalPreOpenExp evalAcc exp2 env' aenv senv
    Var ix                      -> prjElt ix env
    Const c                     -> toElt c
    PrimConst c                 -> evalPrimConst c
    PrimApp f x                 -> evalPrim f (evalE x)
    Tuple tup                   -> toTuple $ evalTuple evalAcc tup env aenv senv
    Prj ix tup                  -> evalPrj ix . fromTuple $ evalE tup
    IndexNil                    -> Z
    IndexAny                    -> Any
    IndexCons sh sz             -> evalE sh :. evalE sz
    IndexHead sh                -> let _  :. ix = evalE sh in ix
    IndexTail sh                -> let ix :. _  = evalE sh in ix
    IndexSlice slice slix sh    -> toElt $ restrict slice (fromElt (evalE slix))
                                                          (fromElt (evalE sh))
      where
        restrict :: SliceIndex slix sl co sh -> slix -> sh -> sl
        restrict SliceNil              ()        ()         = ()
        restrict (SliceAll sliceIdx)   (slx, ()) (sl, sz)   =
          let sl' = restrict sliceIdx slx sl
          in  (sl', sz)
        restrict (SliceFixed sliceIdx) (slx, _i)  (sl, _sz) =
          restrict sliceIdx slx sl

    IndexFull slice slix sh     -> toElt $ extend slice (fromElt (evalE slix))
                                                        (fromElt (evalE sh))
      where
        extend :: SliceIndex slix sl co sh -> slix -> sl -> sh
        extend SliceNil              ()        ()       = ()
        extend (SliceAll sliceIdx)   (slx, ()) (sl, sz) =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)
        extend (SliceFixed sliceIdx) (slx, sz) sl       =
          let sh' = extend sliceIdx slx sl
          in  (sh', sz)

    ToIndex sh ix               -> toIndex (evalE sh) (evalE ix)
    FromIndex sh ix             -> fromIndex (evalE sh) (evalE ix)
    Cond c t e
      | evalE c                 -> evalE t
      | otherwise               -> evalE e

    While cond body seed        -> go (evalE seed)
      where
        f       = evalF body
        p       = evalF cond
        go !x
          | p x         = go (f x)
          | otherwise   = x

    Index acc ix                -> evalA acc ! evalE ix
    LinearIndex acc i           -> let a  = evalA acc
                                       ix = fromIndex (shape a) (evalE i)
                                   in a ! ix
    Shape acc                   -> shape (evalA acc)
    ShapeSize sh                -> size (evalE sh)
    Intersect sh1 sh2           -> intersect (evalE sh1) (evalE sh2)
    Union sh1 sh2               -> union (evalE sh1) (evalE sh2)
    IndexS x sh                 -> prj' x senv ! (senvSize senv .: evalE sh)
    LinearIndexS x i            -> let c = prj' x senv
                                       ix = senvSize senv .: fromIndex (indexInit (shape c)) (evalE i)
                                   in c ! ix
    ShapeS x                    -> indexInit (shape (prj' x senv))
    Foreign _ f e               -> evalPreOpenFun evalAcc f EmptyElt Empty (EmptyS, 0) $ evalE e


-- Scalar primitives
-- -----------------

evalPrimConst :: PrimConst a -> a
evalPrimConst (PrimMinBound ty) = evalMinBound ty
evalPrimConst (PrimMaxBound ty) = evalMaxBound ty
evalPrimConst (PrimPi       ty) = evalPi ty

evalPrim :: PrimFun p -> p
evalPrim (PrimAdd             ty) = evalAdd ty
evalPrim (PrimSub             ty) = evalSub ty
evalPrim (PrimMul             ty) = evalMul ty
evalPrim (PrimNeg             ty) = evalNeg ty
evalPrim (PrimAbs             ty) = evalAbs ty
evalPrim (PrimSig             ty) = evalSig ty
evalPrim (PrimQuot            ty) = evalQuot ty
evalPrim (PrimRem             ty) = evalRem ty
evalPrim (PrimQuotRem         ty) = evalQuotRem ty
evalPrim (PrimIDiv            ty) = evalIDiv ty
evalPrim (PrimMod             ty) = evalMod ty
evalPrim (PrimDivMod          ty) = evalDivMod ty
evalPrim (PrimBAnd            ty) = evalBAnd ty
evalPrim (PrimBOr             ty) = evalBOr ty
evalPrim (PrimBXor            ty) = evalBXor ty
evalPrim (PrimBNot            ty) = evalBNot ty
evalPrim (PrimBShiftL         ty) = evalBShiftL ty
evalPrim (PrimBShiftR         ty) = evalBShiftR ty
evalPrim (PrimBRotateL        ty) = evalBRotateL ty
evalPrim (PrimBRotateR        ty) = evalBRotateR ty
evalPrim (PrimFDiv            ty) = evalFDiv ty
evalPrim (PrimRecip           ty) = evalRecip ty
evalPrim (PrimSin             ty) = evalSin ty
evalPrim (PrimCos             ty) = evalCos ty
evalPrim (PrimTan             ty) = evalTan ty
evalPrim (PrimAsin            ty) = evalAsin ty
evalPrim (PrimAcos            ty) = evalAcos ty
evalPrim (PrimAtan            ty) = evalAtan ty
evalPrim (PrimAsinh           ty) = evalAsinh ty
evalPrim (PrimAcosh           ty) = evalAcosh ty
evalPrim (PrimAtanh           ty) = evalAtanh ty
evalPrim (PrimExpFloating     ty) = evalExpFloating ty
evalPrim (PrimSqrt            ty) = evalSqrt ty
evalPrim (PrimLog             ty) = evalLog ty
evalPrim (PrimFPow            ty) = evalFPow ty
evalPrim (PrimLogBase         ty) = evalLogBase ty
evalPrim (PrimTruncate     ta tb) = evalTruncate ta tb
evalPrim (PrimRound        ta tb) = evalRound ta tb
evalPrim (PrimFloor        ta tb) = evalFloor ta tb
evalPrim (PrimCeiling      ta tb) = evalCeiling ta tb
evalPrim (PrimAtan2           ty) = evalAtan2 ty
evalPrim (PrimIsNaN           ty) = evalIsNaN ty
evalPrim (PrimLt              ty) = evalLt ty
evalPrim (PrimGt              ty) = evalGt ty
evalPrim (PrimLtEq            ty) = evalLtEq ty
evalPrim (PrimGtEq            ty) = evalGtEq ty
evalPrim (PrimEq              ty) = evalEq ty
evalPrim (PrimNEq             ty) = evalNEq ty
evalPrim (PrimMax             ty) = evalMax ty
evalPrim (PrimMin             ty) = evalMin ty
evalPrim PrimLAnd                 = evalLAnd
evalPrim PrimLOr                  = evalLOr
evalPrim PrimLNot                 = evalLNot
evalPrim PrimOrd                  = evalOrd
evalPrim PrimChr                  = evalChr
evalPrim PrimBoolToInt            = evalBoolToInt
evalPrim (PrimFromIntegral ta tb) = evalFromIntegral ta tb


-- Tuple construction and projection
-- ---------------------------------

evalTuple :: EvalAcc acc -> Tuple (PreOpenExp acc env senv aenv) t -> ValElt env -> Val aenv -> Val' senv -> t
evalTuple _       NilTup            _env _aenv _senv = ()
evalTuple evalAcc (tup `SnocTup` e) env  aenv  senv  =
  (evalTuple evalAcc tup env aenv senv, evalPreOpenExp evalAcc e env aenv senv)

evalPrj :: TupleIdx t e -> t -> e
evalPrj ZeroTupIdx       (!_, v)   = v
evalPrj (SuccTupIdx idx) (tup, !_) = evalPrj idx tup
  -- FIXME: Strictly speaking, we ought to force all components of a tuples;
  --        not only those that we happen to encounter during the recursive
  --        walk.


-- Implementation of scalar primitives
-- -----------------------------------

evalLAnd :: (Bool, Bool) -> Bool
evalLAnd (x, y) = x && y

evalLOr  :: (Bool, Bool) -> Bool
evalLOr (x, y) = x || y

evalLNot :: Bool -> Bool
evalLNot = not

evalOrd :: Char -> Int
evalOrd = ord

evalChr :: Int -> Char
evalChr = chr

evalBoolToInt :: Bool -> Int
evalBoolToInt = fromEnum

evalFromIntegral :: IntegralType a -> NumType b -> a -> b
evalFromIntegral ta (IntegralNumType tb)
  | IntegralDict <- integralDict ta
  , IntegralDict <- integralDict tb
  = fromIntegral

evalFromIntegral ta (FloatingNumType tb)
  | IntegralDict <- integralDict ta
  , FloatingDict <- floatingDict tb
  = fromIntegral


-- Extract methods from reified dictionaries
--

-- Constant methods of Bounded
--

evalMinBound :: BoundedType a -> a
evalMinBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = minBound

evalMinBound (NonNumBoundedType   ty)
  | NonNumDict   <- nonNumDict ty
  = minBound

evalMaxBound :: BoundedType a -> a
evalMaxBound (IntegralBoundedType ty)
  | IntegralDict <- integralDict ty
  = maxBound

evalMaxBound (NonNumBoundedType   ty)
  | NonNumDict   <- nonNumDict ty
  = maxBound

-- Constant method of floating
--

evalPi :: FloatingType a -> a
evalPi ty | FloatingDict <- floatingDict ty = pi

evalSin :: FloatingType a -> (a -> a)
evalSin ty | FloatingDict <- floatingDict ty = sin

evalCos :: FloatingType a -> (a -> a)
evalCos ty | FloatingDict <- floatingDict ty = cos

evalTan :: FloatingType a -> (a -> a)
evalTan ty | FloatingDict <- floatingDict ty = tan

evalAsin :: FloatingType a -> (a -> a)
evalAsin ty | FloatingDict <- floatingDict ty = asin

evalAcos :: FloatingType a -> (a -> a)
evalAcos ty | FloatingDict <- floatingDict ty = acos

evalAtan :: FloatingType a -> (a -> a)
evalAtan ty | FloatingDict <- floatingDict ty = atan

evalAsinh :: FloatingType a -> (a -> a)
evalAsinh ty | FloatingDict <- floatingDict ty = asinh

evalAcosh :: FloatingType a -> (a -> a)
evalAcosh ty | FloatingDict <- floatingDict ty = acosh

evalAtanh :: FloatingType a -> (a -> a)
evalAtanh ty | FloatingDict <- floatingDict ty = atanh

evalExpFloating :: FloatingType a -> (a -> a)
evalExpFloating ty | FloatingDict <- floatingDict ty = exp

evalSqrt :: FloatingType a -> (a -> a)
evalSqrt ty | FloatingDict <- floatingDict ty = sqrt

evalLog :: FloatingType a -> (a -> a)
evalLog ty | FloatingDict <- floatingDict ty = log

evalFPow :: FloatingType a -> ((a, a) -> a)
evalFPow ty | FloatingDict <- floatingDict ty = uncurry (**)

evalLogBase :: FloatingType a -> ((a, a) -> a)
evalLogBase ty | FloatingDict <- floatingDict ty = uncurry logBase

evalTruncate :: FloatingType a -> IntegralType b -> (a -> b)
evalTruncate ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = truncate

evalRound :: FloatingType a -> IntegralType b -> (a -> b)
evalRound ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = round

evalFloor :: FloatingType a -> IntegralType b -> (a -> b)
evalFloor ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = floor

evalCeiling :: FloatingType a -> IntegralType b -> (a -> b)
evalCeiling ta tb
  | FloatingDict <- floatingDict ta
  , IntegralDict <- integralDict tb
  = ceiling

evalAtan2 :: FloatingType a -> ((a, a) -> a)
evalAtan2 ty | FloatingDict <- floatingDict ty = uncurry atan2

evalIsNaN :: FloatingType a -> (a -> Bool)
evalIsNaN ty | FloatingDict <- floatingDict ty = isNaN


-- Methods of Num
--

evalAdd :: NumType a -> ((a, a) -> a)
evalAdd (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (+)
evalAdd (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (+)

evalSub :: NumType a -> ((a, a) -> a)
evalSub (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (-)
evalSub (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (-)

evalMul :: NumType a -> ((a, a) -> a)
evalMul (IntegralNumType ty) | IntegralDict <- integralDict ty = uncurry (*)
evalMul (FloatingNumType ty) | FloatingDict <- floatingDict ty = uncurry (*)

evalNeg :: NumType a -> (a -> a)
evalNeg (IntegralNumType ty) | IntegralDict <- integralDict ty = negate
evalNeg (FloatingNumType ty) | FloatingDict <- floatingDict ty = negate

evalAbs :: NumType a -> (a -> a)
evalAbs (IntegralNumType ty) | IntegralDict <- integralDict ty = abs
evalAbs (FloatingNumType ty) | FloatingDict <- floatingDict ty = abs

evalSig :: NumType a -> (a -> a)
evalSig (IntegralNumType ty) | IntegralDict <- integralDict ty = signum
evalSig (FloatingNumType ty) | FloatingDict <- floatingDict ty = signum

evalQuot :: IntegralType a -> ((a, a) -> a)
evalQuot ty | IntegralDict <- integralDict ty = uncurry quot

evalRem :: IntegralType a -> ((a, a) -> a)
evalRem ty | IntegralDict <- integralDict ty = uncurry rem

evalQuotRem :: IntegralType a -> ((a, a) -> (a, a))
evalQuotRem ty | IntegralDict <- integralDict ty = uncurry quotRem

evalIDiv :: IntegralType a -> ((a, a) -> a)
evalIDiv ty | IntegralDict <- integralDict ty = uncurry div

evalMod :: IntegralType a -> ((a, a) -> a)
evalMod ty | IntegralDict <- integralDict ty = uncurry mod

evalDivMod :: IntegralType a -> ((a, a) -> (a, a))
evalDivMod ty | IntegralDict <- integralDict ty = uncurry divMod

evalBAnd :: IntegralType a -> ((a, a) -> a)
evalBAnd ty | IntegralDict <- integralDict ty = uncurry (.&.)

evalBOr :: IntegralType a -> ((a, a) -> a)
evalBOr ty | IntegralDict <- integralDict ty = uncurry (.|.)

evalBXor :: IntegralType a -> ((a, a) -> a)
evalBXor ty | IntegralDict <- integralDict ty = uncurry xor

evalBNot :: IntegralType a -> (a -> a)
evalBNot ty | IntegralDict <- integralDict ty = complement

evalBShiftL :: IntegralType a -> ((a, Int) -> a)
evalBShiftL ty | IntegralDict <- integralDict ty = uncurry shiftL

evalBShiftR :: IntegralType a -> ((a, Int) -> a)
evalBShiftR ty | IntegralDict <- integralDict ty = uncurry shiftR

evalBRotateL :: IntegralType a -> ((a, Int) -> a)
evalBRotateL ty | IntegralDict <- integralDict ty = uncurry rotateL

evalBRotateR :: IntegralType a -> ((a, Int) -> a)
evalBRotateR ty | IntegralDict <- integralDict ty = uncurry rotateR

evalFDiv :: FloatingType a -> ((a, a) -> a)
evalFDiv ty | FloatingDict <- floatingDict ty = uncurry (/)

evalRecip :: FloatingType a -> (a -> a)
evalRecip ty | FloatingDict <- floatingDict ty = recip



evalLt :: ScalarType a -> ((a, a) -> Bool)
evalLt (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (<)
evalLt (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (<)
evalLt (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (<)

evalGt :: ScalarType a -> ((a, a) -> Bool)
evalGt (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (>)
evalGt (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (>)
evalGt (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (>)

evalLtEq :: ScalarType a -> ((a, a) -> Bool)
evalLtEq (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (<=)
evalLtEq (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (<=)
evalLtEq (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (<=)

evalGtEq :: ScalarType a -> ((a, a) -> Bool)
evalGtEq (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (>=)
evalGtEq (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (>=)
evalGtEq (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (>=)

evalEq :: ScalarType a -> ((a, a) -> Bool)
evalEq (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (==)
evalEq (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (==)
evalEq (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (==)

evalNEq :: ScalarType a -> ((a, a) -> Bool)
evalNEq (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry (/=)
evalNEq (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry (/=)
evalNEq (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry (/=)

evalMax :: ScalarType a -> ((a, a) -> a)
evalMax (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry max
evalMax (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry max
evalMax (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry max

evalMin :: ScalarType a -> ((a, a) -> a)
evalMin (NumScalarType (IntegralNumType ty)) | IntegralDict <- integralDict ty = uncurry min
evalMin (NumScalarType (FloatingNumType ty)) | FloatingDict <- floatingDict ty = uncurry min
evalMin (NonNumScalarType ty)                | NonNumDict   <- nonNumDict ty   = uncurry min



-- Sequence evaluation
-- ---------------

-- Configuration for sequence evaluation.
--
data SeqConfig = SeqConfig
  { chunkSize :: Int -- Allocation limit for a sequence in
                     -- words. Actual runtime allocation should be the
                     -- maximum of this size and the size of the
                     -- largest element in the sequence.
  }

-- Default sequence evaluation configuration for testing purposes.
--
defaultSeqConfig :: SeqConfig
defaultSeqConfig = SeqConfig { chunkSize = case unsafePerformIO (queryFlag chunk_size) of Nothing -> 5; Just n -> n }

-- Chunk of arrays of shape 'sh' and element type 'e'.
type Chunk sh e = Array (sh :. Int) e

indexLast :: Shape sh => (sh :. Int) -> Int
indexLast = last . shapeToList

indexInit :: Shape sh => (sh :. Int) -> sh
indexInit = listToShape . init . shapeToList

infixr 3 .:
(.:) :: Shape sh => Int -> sh -> (sh :. Int)
(.:) n sh = listToShape (shapeToList sh ++ [n])

type Val' senv = (ValS senv, Int)

-- Valuation for an environment of sequence windows.
--
data ValS senv where
  EmptyS :: ValS ()
  PushS  :: ValS senv -> Chunk sh e -> ValS (senv, Array sh e)

-- Projection of a window from a window valuation using a de Bruijn
-- index.
--
prjS :: Idx senv (Array sh e) -> ValS senv -> Chunk sh e
prjS ZeroIdx       (PushS _   v) = v
prjS (SuccIdx idx) (PushS val _) = prjS idx val
prjS _             _             = $internalError "prj" "inconsistent valuation"

senvSize :: Val' senv -> Int
senvSize = snd

-- Projection of a window from a window valuation using a de Bruijn
-- index.
--
prj' :: Idx senv (Array sh e) -> Val' senv -> Chunk sh e
prj' x (senv, _) = prjS x senv

push' :: Val' senv -> Chunk sh e -> Val' (senv, Array sh e)
push' (senv, n) c = (PushS senv c, n)

data Shapes senv where
  EmptyShapes :: Shapes ()
  PushShape   :: Shapes senv -> sh -> Shapes (senv, Array sh e)

-- Projection of a window from a window valuation using a de Bruijn
-- index.
--
prjShape :: Idx senv (Array sh e) -> Shapes senv -> sh
prjShape ZeroIdx       (PushShape _   v) = v
prjShape (SuccIdx idx) (PushShape val _) = prjShape idx val
prjShape _             _             = $internalError "prj" "inconsistent valuation"

-- An executable sequence.
--
data ExecSeq senv arrs where
  ExecP :: (Shape sh, Elt e) => ExecP senv (Array sh e) -> ExecSeq (senv, Array sh e) arrs -> ExecSeq senv  arrs
  ExecC :: Arrays a =>          ExecC senv a ->                                               ExecSeq senv  a
  ExecR :: (Shape sh, Elt e) => Idx   senv (Array sh e) ->                                    ExecSeq senv  [Array sh e]

-- An executable producer.
--
data ExecP senv a where
  ExecStreamIn :: sh
               -> [Array sh a]
               -> ExecP senv (Array sh a)

  ExecMap :: (Val' senv -> Chunk sh e)
          -> ExecP senv (Array sh e)

  -- Stream scan skeleton.
  ExecScan :: (Shape sh, Elt e)
           => (Val' senv -> s -> (Chunk sh e, s))   -- Chunk scanner.
           -> s                                     -- Accumulator (internal state).
           -> ExecP senv (Array sh e)

-- An executable consumer.
--
data ExecC senv a where

  -- Stream reduction skeleton.
  ExecFold :: (Val' senv -> s -> s)   -- Chunk consumer function.
           -> (s -> r)                -- Finalizer function.
           -> s                       -- Accumulator (internal state).
           -> ExecC senv r

  ExecStuple :: IsAtuple a
             => Atuple (ExecC senv) (TupleRepr a)
             -> ExecC senv a

evalDelayedSeq :: SeqConfig
               -> DelayedSeq arrs
               -> arrs
evalDelayedSeq cfg (DelayedSeq aenv s) | aenv' <- evalExtend aenv Empty
                                       = evalSeq cfg s aenv'

evalSeq :: forall aenv arrs.
            SeqConfig
         -> PreOpenSeq DelayedOpenAcc aenv () arrs
         -> Val aenv -> arrs
evalSeq conf s aenv = evalSeq' s
  where
    evalSeq' :: PreOpenSeq DelayedOpenAcc aenv senv arrs -> arrs
    evalSeq' (Producer _ s) = evalSeq' s
    evalSeq' (Consumer _)   =
      let (s0, maxElemSize) = initSeq aenv EmptyShapes s
          pd = maxStepSize (chunkSize conf) maxElemSize
      in loop pd s0
    evalSeq' (Reify _) =
      let (s0, maxElemSize) = initSeq aenv EmptyShapes s
          pd = maxStepSize (chunkSize conf) maxElemSize
      in reify pd s0

    -- Initialize the producers and the accumulators of the consumers
    -- with the given array enviroment.
    initSeq :: forall senv arrs'.
                Val aenv
             -> Shapes senv
             -> PreOpenSeq DelayedOpenAcc aenv senv arrs'
             -> (ExecSeq senv arrs', Int)
    initSeq aenv shs s =
      case s of
        Producer   p s' ->
          let (execP, sh) = initProducer p shs
              (s'',   n1) = initSeq aenv (PushShape shs sh) s'
          in (ExecP execP s'', size sh `max` n1)
        Consumer   c    -> (ExecC (initConsumer c), 0)
        Reify      ix   -> (ExecR ix, 0)

    -- Iterate the given sequence until it terminates.
    -- A sequence only terminates when one of the producers are exhausted.
    loop :: Arrays arrs
         => Int
         -> ExecSeq () arrs
         -> arrs
    loop n s =
      let k = stepSize n s
          (s', arrs0) = step s (EmptyS, k)
      in if k < n then arrs0 else loop n s'

    -- Iterate the given sequence until it terminates.
    -- A sequence only terminates when one of the producers are exhausted.
    reify :: Arrays (Array sh e)
          => Int
          -> ExecSeq () [Array sh e]
          -> [Array sh e]
    reify n s =
      let k = stepSize n s
          (s', arrs0) = step s (EmptyS, k)
      in if k < n then arrs0 else arrs0 ++ reify n s'

    maxStepSize :: Int -> Int -> Int
    maxStepSize maxChunkSize elemSize =
      let (a,b) = maxChunkSize `quotRem` (elemSize `max` 1)
      in a + signum b

    stepSize :: Int -> ExecSeq senv arrs' -> Int
    stepSize n s =
      case s of
        ExecP p s -> min (stepSize n s) $
          case p of
            ExecStreamIn _ xs -> length (take n xs)
            _ -> n
        _ -> n

    -- One iteration of a sequence.
    step :: forall senv arrs'.
            ExecSeq senv arrs'
         -> Val' senv
         -> (ExecSeq senv arrs', arrs')
    step s senv =
      case s of
        ExecP p s' ->
          let (c', p') = produce p senv
              (s'', a) = step s' (senv `push'` c')
          in (ExecP p' s'', a)
        ExecC   c  ->
          let (c', a) = consume c senv
          in  (ExecC c', a)
        ExecR x -> (ExecR x, chunkToList (senvSize senv) (prj' x senv))

    evalClosedExp :: DelayedExp () aenv t -> t
    evalClosedExp exp = evalPreExp evalOpenAcc exp aenv (EmptyS, 0)

    evalF :: DelayedFun senv aenv f -> Val' senv -> Int -> f
    evalF fun (senv, _) i = evalPreFun evalOpenAcc fun aenv (senv, i)

    evalClosedFun :: DelayedFun () aenv f -> f
    evalClosedFun fun = evalPreFun evalOpenAcc fun aenv (EmptyS, 0)

    initProducer :: forall sh e senv.
                    Producer DelayedOpenAcc aenv senv (Array sh e)
                 -> Shapes senv
                 -> (ExecP senv (Array sh e), sh)
    initProducer p shs =
      case p of
        StreamIn shExp arrs ->
          let sh = evalClosedExp shExp
          in (ExecStreamIn sh arrs, sh)
        ToSeq sliceIndex slix (delayed -> Delayed sh ix _) ->
          let sl = R.sliceShape sliceIndex (fromElt sh)
          in (ExecStreamIn (toElt sl) (toSeqOp sliceIndex slix (newArray sh ix)), toElt sl)
        SeqOp op -> (initSeqOp op, seqOpShape op shs)
        ScanSeq f e x -> (ExecScan scanner (evalClosedExp e), Z)
          where
            scanner senv a =
              let (v1, a') = scanl'Op (evalClosedFun f) a (delayArray (prj' x senv))
              in (v1, a' ! Z)

    initSeqOp :: PreOpenArrayOp (Idx senv) DelayedOpenAcc senv aenv (Array sh e) -> ExecP senv (Array sh e)
    initSeqOp op = ExecMap $ \ senv ->
      case op of
--        Unit e                    -> unitSop (evalE e senv) (senvSize senv)
        Map f x                   -> mapSop (evalF f senv) (prj' x senv)
        Generate sh f             -> generateSop (evalClosedExp sh) (evalF f senv) (senvSize senv)
        Transform sh p f x        -> transformSop (evalClosedExp sh) (evalF p senv) (evalF f senv) (prj' x senv)
        Backpermute sh p x        -> backpermuteSop (evalClosedExp sh) (evalF p senv) (prj' x senv)
--        Reshape sh x              -> reshapeSop (evalClosedExp sh) (prj' x senv)

        ZipWith f x1 x2           -> zipWithSop (evalF f senv) (prj' x1 senv) (prj' x2 senv)
        Replicate slice slix x    -> replicateSop slice (evalClosedExp slix) (prj' x senv)
        Slice slice x slix        -> sliceSop slice (evalClosedExp slix) (prj' x senv)

        -- Consumers
        -- ---------
        Fold f z x                -> foldSop (evalClosedFun f) (evalClosedExp z) (prj' x senv)
        Fold1 f x                 -> fold1Sop (evalClosedFun f) (prj' x senv)
        FoldSeg f z x y           -> foldSegSop (evalClosedFun f) (evalClosedExp z) (prj' x senv) (prj' y senv)
        Fold1Seg f x y            -> fold1SegSop (evalClosedFun f) (prj' x senv) (prj' y senv)
        Scanl f z x               -> scanlSop (evalClosedFun f) (evalClosedExp z) (prj' x senv)
        Scanl1 f x                -> scanl1Sop (evalClosedFun f) (prj' x senv)
        Scanr f z x               -> scanrSop (evalClosedFun f) (evalClosedExp z) (prj' x senv)
        Scanr1 f x                -> scanr1Sop (evalClosedFun f) (prj' x senv)
        Permute f x1 p x2         -> permuteSop (evalClosedFun f) (evalF p senv) (prj' x1 senv) (prj' x2 senv)
        Stencil sten b x          -> stencilSop (evalClosedFun sten) b (prj' x senv)
        Stencil2 sten b1 x1 b2 x2 -> stencil2Sop (evalClosedFun sten) b1 b2 (prj' x1 senv) (prj' x2 senv)


    seqOpShape :: PreOpenArrayOp (Idx senv) DelayedOpenAcc senv aenv (Array sh e) -> Shapes senv -> sh
    seqOpShape op shs =
      case op of
--        Unit _                    -> Z
        Map _ x                   -> prjShape x shs
        Generate sh _             -> evalClosedExp sh
        Transform sh _ _ _        -> evalClosedExp sh
        Backpermute sh _ _        -> evalClosedExp sh
--        Reshape sh _              -> evalClosedExp sh

        ZipWith _ x1 x2           -> prjShape x1 shs `intersect` prjShape x2 shs
        Replicate slice slix x    -> toElt $ fst $ extend slice (fromElt (evalClosedExp slix)) (fromElt (prjShape x shs))
        Slice slice x slix        -> toElt $ fst $ restrict slice (fromElt (evalClosedExp slix)) (fromElt (prjShape x shs))

        -- Consumers
        -- ---------
        Fold _ _ x                -> let sh :. _ = prjShape x shs in sh
        Fold1 _ x                 -> let sh :. _ = prjShape x shs in sh
        FoldSeg _ _ x y           -> let sh :. _ = prjShape x shs in let _ :. n = prjShape y shs in sh :. n
        Fold1Seg _ x y            -> let sh :. _ = prjShape x shs in let _ :. n = prjShape y shs in sh :. n
        Scanl _ _ x               -> let Z :. n = prjShape x shs in Z :. n + 1
        Scanl1 _ x                -> prjShape x shs
        Scanr _ _ x               -> let Z :. n = prjShape x shs in Z :. n + 1
        Scanr1 _ x                -> prjShape x shs
        Permute _ x1 _ _          -> prjShape x1 shs
        Stencil _ _ x             -> prjShape x shs
        Stencil2 _ _ x1 _ x2      -> prjShape x1 shs `intersect` prjShape x2 shs

    initConsumer :: forall a senv.
                    Consumer DelayedOpenAcc aenv senv a
                 -> ExecC senv a
    initConsumer c =
      case c of
        FoldSeq f e x ->
          let a0 = unitSop (\ _ -> evalClosedExp e) (chunkSize conf)
              consumer senv v = zipWith'Op (evalClosedFun f) (delayArray v) (delayArray (prj' x senv))
              finalizer = fold1Op (evalClosedFun f)  . delayArray
          in ExecFold consumer finalizer a0
        FoldSeqFlatten f acc x ->
          let f' = evalOpenAfun f aenv
              a0 = evalOpenAcc acc aenv
              consumer senv a = f' a (prj' x senv)
              finalizer = id
          in ExecFold consumer finalizer a0
        Stuple t ->
          let initTup :: Atuple (Consumer DelayedOpenAcc aenv senv) t -> Atuple (ExecC senv) t
              initTup NilAtup        = NilAtup
              initTup (SnocAtup t c) = SnocAtup (initTup t) (initConsumer c)
          in ExecStuple (initTup t)

    delayed :: DelayedOpenAcc aenv (Array sh e) -> Delayed (Array sh e)
    delayed AST.Manifest{}  = $internalError "evalOpenAcc" "expected delayed array"
    delayed AST.Delayed{..} = Delayed (evalPreExp evalOpenAcc extentD aenv (EmptyS, 0))
                                      (evalPreFun evalOpenAcc indexD aenv (EmptyS, 0))
                                      (evalPreFun evalOpenAcc linearIndexD aenv (EmptyS, 0))

produce :: (Shape sh, Elt e)
        => ExecP senv (Array sh e)
        -> Val' senv -> (Chunk sh e, ExecP senv (Array sh e))
produce p senv =
  case p of
    ExecStreamIn sh xs ->
      let k           = senvSize senv
          (xs', xs'') = (take k xs, drop k xs)
          c           = reshapeOp (length xs' .: sh) $ concatVectors (size sh) (map (reshapeOp (Z :. size sh)) xs')
      in (c, ExecStreamIn sh xs'')
    ExecMap f -> (f senv, ExecMap f)
    ExecScan scanner a ->
      let (c', a') = scanner senv a
      in (c', ExecScan scanner a')

consume :: forall senv a. ExecC senv a -> Val' senv -> (ExecC senv a, a)
consume c senv =
  case c of
    ExecFold f g acc ->
      let acc' = f senv acc
      -- Even though we call g here, lazy evaluation should guarantee it is
      -- only ever called once.
      in (ExecFold f g acc', g acc')
    ExecStuple t ->
      let consT :: Atuple (ExecC senv) t -> (Atuple (ExecC senv) t, t)
          consT NilAtup        = (NilAtup, ())
          consT (SnocAtup t c) | (c', acc) <- consume c senv
                               , (t', acc') <- consT t
                               = (SnocAtup t' c', (acc', acc))
          (t', acc) = consT t
      in (ExecStuple t', toAtuple acc)

evalExtend :: Extend DelayedOpenAcc aenv aenv' -> Val aenv -> Val aenv'
evalExtend BaseEnv aenv = aenv
evalExtend (PushEnv ext1 ext2) aenv | aenv' <- evalExtend ext1 aenv
                                    = Push aenv' (evalOpenAcc ext2 aenv')

delayArray :: Array sh e -> Delayed (Array sh e)
delayArray arr@(Array _ adata) = Delayed (shape arr) (arr!) (toElt . unsafeIndexArrayData adata)

chunkToList :: (Shape sh, Elt e) => Int -> Chunk sh e -> [Array sh e]
chunkToList n c = map go [0..n-1]
  where
    go i = newArray (indexInit (shape c)) (\ ix -> c ! (i .: ix))


unitSop :: Elt e => (Int -> e) -> Int -> Chunk Z e
unitSop e n = generateOp (Z :. n) (\ (Z :. i) -> e i)

generateSop
    :: forall sh e. (Shape sh, Elt e)
    => sh
    -> (Int -> sh -> e)
    -> Int
    -> Chunk sh e
generateSop sh f n = generateOp (n .: sh) (\ ix -> f (indexLast ix) (indexInit ix))

transformSop
    :: (Shape sh, Shape sh', Elt b)
    => sh'
    -> (Int -> sh' -> sh)
    -> (Int -> a -> b)
    -> Chunk sh a
    -> Chunk sh' b
transformSop sh' p f arr
  = newArray (indexLast (shape arr) .: sh') (\ix -> f (indexLast ix) (arr ! (indexLast ix .: p (indexLast ix) (indexInit ix))))
    --transformOp (indexLast (shape arr) .: sh') (\ ix -> indexLast ix .: p (indexLast ix) (indexInit ix)) (f _) (delayArray arr)

{-
reshapeSop
    :: (Shape sh, Shape sh', Elt e)
    => sh
    -> Chunk sh' e
    -> Chunk sh  e
reshapeSop sh arr
  = reshapeOp (indexLast (shape arr) .: sh) arr
-}

replicateSop
    :: (Shape sh, Shape sl, Elt slix, Elt e)
    => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
    -> slix
    -> Chunk sl e
    -> Chunk sh e
replicateSop slice slix arr
  = newArray (indexLast (shape arr) .: toElt sh) (\ix -> arr ! (indexLast ix .: liftToElt pf (indexInit ix)))
  where
    (sh, pf) = extend slice (fromElt slix) (fromElt (indexInit (shape arr)))

sliceSop
    :: (Shape sh, Shape sl, Elt slix, Elt e)
    => SliceIndex (EltRepr slix) (EltRepr sl) co (EltRepr sh)
    -> slix
    -> Chunk sh e
    -> Chunk sl e
sliceSop slice slix arr
  = newArray (indexLast (shape arr) .: toElt sh') (\ix -> arr ! (indexLast ix .: liftToElt pf (indexInit ix)))
  where
    (sh', pf) = restrict slice (fromElt slix) (fromElt (indexInit (shape arr)))


mapSop :: (Shape sh, Elt a, Elt b)
      => (Int -> a -> b)
      -> Chunk sh a
      -> Chunk sh b
mapSop f arr
  = newArray (shape arr) (\ix -> f (indexLast ix) (arr ! ix))

zipWithSop
    :: (Shape sh, Elt a, Elt b, Elt c)
    => (Int -> a -> b -> c)
    -> Chunk sh a
    -> Chunk sh b
    -> Chunk sh c
zipWithSop f a1 a2
  = newArray (shape a1 `intersect` shape a2) (\ix -> f (indexLast ix) (a1 ! ix) (a2 ! ix))
  -- = zipWithOp f (delayArray a1) (delayArray a2)

foldSop
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> e
    -> Chunk (sh :. Int) e
    -> Chunk sh e
foldSop f z a
  = foldOp f z (delayArray a)

fold1Sop
    :: (Shape sh, Elt e)
    => (e -> e -> e)
    -> Chunk (sh :. Int) e
    -> Chunk sh e
fold1Sop f a
  = fold1Op f (delayArray a)

concatOp :: (Shape sh, Elt e) => Array (sh :. Int :. Int) e -> Array (sh :. Int) e
concatOp arr
  = reshapeOp sh' arr
  where
    sh = shape arr
    sh0 :. k = indexInit sh
    n = indexLast sh
    sh' = sh0 :. n * k

foldSegSop
    :: forall sh e i. (Shape sh, Elt e, Elt i, IsIntegral i)
    => (e -> e -> e)
    -> e
    -> Chunk (sh :. Int) e
    -> Chunk (Z :. Int) i
    -> Chunk (sh :. Int) e
foldSegSop f z arr seg
  = reshapeOp ((n .: sh) :. k) $ foldSegOp f z (delayArray (concatOp arr)) (delayArray (concatOp seg))
    where
      n  = indexLast (shape arr)
      sh :. _ = indexInit (shape arr)
      _  :. k = indexInit (shape seg)

fold1SegSop
    :: forall sh e i. (Shape sh, Elt e, Elt i, IsIntegral i)
    => (e -> e -> e)
    -> Chunk (sh :. Int) e
    -> Chunk (Z :. Int) i
    -> Chunk (sh :. Int) e
fold1SegSop f arr seg
  = reshapeOp ((n .: sh) :. k) $ fold1SegOp f (delayArray (concatOp arr)) (delayArray (concatOp seg))
    where
      n  = indexLast (shape arr)
      sh :. _ = indexInit (shape arr)
      _  :. k = indexInit (shape seg)

scanl1Sop
    :: Elt e
    => (e -> e -> e)
    -> Chunk (Z :. Int) e
    -> Chunk (Z :. Int) e
scanl1Sop _f _xs
  = $internalError "scanl1Sop" "Not implemented" -- Segmented scan

scanlSop
    :: Elt e
    => (e -> e -> e)
    -> e
    -> Chunk (Z :. Int) e
    -> Chunk (Z :. Int) e
scanlSop _f _z _arr
  = $internalError "scanlSop" "Not implemented"

scanrSop
    :: Elt e
    => (e -> e -> e)
    -> e
    -> Chunk (Z :. Int) e
    -> Chunk (Z :. Int) e
scanrSop _f _z _arr
  = $internalError "scanrSop" "Not implemented"

scanr1Sop
    :: Elt e
    => (e -> e -> e)
    -> Chunk (Z :. Int) e
    -> Chunk (Z :. Int) e
scanr1Sop _f _arr
  = $internalError "scanr1Sop" "Not implemented"


permuteSop
    :: (Shape sh, Shape sh', Elt e)
    => (e -> e -> e)
    -> (Int -> sh -> sh')
    -> Chunk sh' e
    -> Chunk sh  e
    -> Chunk sh' e
permuteSop f p def arr
  = permuteOp f def (\ ix -> indexLast ix .: p (indexLast ix) (indexInit ix)) (delayArray arr)

backpermuteSop
    :: (Shape sh, Shape sh', Elt e)
    => sh'
    -> (Int -> sh' -> sh)
    -> Chunk sh e
    -> Chunk sh' e
backpermuteSop sh' p a
  = backpermuteOp (indexLast (shape a) .: sh') (\ ix -> indexLast ix .: p (indexLast ix) (indexInit ix)) (delayArray a)

stencilSop
    :: (Elt a, Elt b, Stencil sh a stencil)
    => (stencil -> b)
    -> Boundary (EltRepr a)
    -> Chunk sh a
    -> Chunk sh b
stencilSop _stencil _boundary _arr
  = $internalError "stencilSop" "Not implemented"

stencil2Sop
    :: (Elt a, Elt b, Elt c, Stencil sh a stencil1, Stencil sh b stencil2)
    => (stencil1 -> stencil2 -> c)
    -> Boundary (EltRepr a)
    -> Boundary (EltRepr b)
    -> Chunk sh a
    -> Chunk sh b
    -> Chunk sh c
stencil2Sop _stencil _boundary1 _boundary2 _arr1 _arr2
  = $internalError "stencil2Sop" "Not implemented"
