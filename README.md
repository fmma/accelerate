An Embedded Language for Accelerated Array Computations
=======================================================

[![Build Status](https://travis-ci.org/tmcdonell/accelerate.svg?branch=master)](https://travis-ci.org/tmcdonell/accelerate)

`Data.Array.Accelerate` defines an embedded language of array computations for high-performance computing in Haskell. Computations on multi-dimensional, regular arrays are expressed in the form of parameterised collective operations (such as maps, reductions, and permutations). These computations are online-compiled and executed on a range of architectures.

For more details, see our papers:
 * [Accelerating Haskell Array Codes with Multicore GPUs][CKLM+11]
 * [Optimising Purely Functional GPU Programs][MCKL13]
 * [Embedding Foreign Code][CMCK14]

There are also slides from some fairly recent presentations:
 * [Embedded Languages for High-Performance Computing in Haskell][Embedded]
 * [GPGPU Programming in Haskell with Accelerate][YLJ13-slides] ([video][YLJ13-video]) ([workshop][YLJ13-workshop])

Chapter 6 of Simon Marlow's book [Parallel and Concurrent Programming in Haskell][Mar13] contains a tutorial introduction to Accelerate.

[Trevor's PhD thesis][Trevor-thesis] details the design and implementation of frontend optimisations and CUDA backend.


**Table of Contents**

- [An Embedded Language for Accelerated Array Computations](#an-embedded-language-for-accelerated-array-computations)
	- [A simple example](#a-simple-example)
	- [Availability](#availability)
	- [Additional components](#additional-components)
	- [Requirements](#requirements)
	- [Documentation](#documentation)
	- [Examples](#examples)
	- [Mailing list and contacts](#mailing-list-and-contacts)
	- [Citing Accelerate](#citing-accelerate)
	- [What's missing?](#whats-missing)

A simple example
----------------

As a simple example, consider the computation of a dot product of two vectors of single-precision floating-point numbers:

    dotp :: Acc (Vector Float) -> Acc (Vector Float) -> Acc (Scalar Float)
    dotp xs ys = fold (+) 0 (zipWith (*) xs ys)

Except for the type, this code is almost the same as the corresponding Haskell code on lists of floats. The types indicate that the computation may be online-compiled for performance — for example, using `Data.Array.Accelerate.CUDA.run` it may be on-the-fly off-loaded to a GPU.

Availability
------------

Package accelerate is available from

 * Hackage: [accelerate][Hackage] — install with `cabal install accelerate`
 * GitHub: [AccelerateHS/accelerate][GitHub] - get the source with `git clone https://github.com/AccelerateHS/accelerate.git`

Additional components
---------------------

The following supported addons are available as separate packages on Hackage and included as submodules in the GitHub repository:

  * [`accelerate-cuda`][accelerate-cuda] Backend targeting CUDA-enabled NVIDA GPUs — requires the NVIDIA CUDA SDK and hardware with compute capability 1.2 or greater (see the [table on Wikipedia][wiki-cc])
  * [`accelerate-examples`][accelerate-examples] Computational kernels and applications showcasing the use of Accelerate as well as a regression test suite (supporting function and performance testing)
  * [`accelerate-io`][accelerate-io] Fast conversion between Accelerate arrays and other array formats (including Repa arrays)
  * [`accelerate-fft`][accelerate-fft] Fast Fourier transform implementation, with optimised implementation for the CUDA backend
  * [`accelerate-backend-kit`][accelerate-backend-kit] Simplified internal AST to get going on writing backends
  * [`accelerate-buildbot`][accelerate-buildbot] Build bot for automatic performance & regression testing

Install them from Hackage with `cabal install PACKAGENAME`.

The following components are experimental and incomplete incomplete:

  * [`accelerate-llvm`][accelerate-llvm] A framework for constructing backends targeting LLVM IR, with concrete backends for multicore CPUs and NVIDIA GPUs.

The following components are incomplete and not currently maintained. Please contact us if you are interested in working on them!

  * [`accelerate-opencl`][accelerate-opencl] Backend targeting GPUs via the OpenCL standard
  * [`accelerate-repa`][accelerate-repa] Backend targeting multicore CPUs via the [Repa][repa] parallel array library

Requirements
------------

  * Glasgow Haskell Compiler (GHC), 7.8.3 or later
  * For the CUDA backend, CUDA version 5.0 or later
  * Haskell libraries as specified in the [`accelerate.cabal`][accelerate-cabal] and optionally [`accelerate-cuda.cabal`][accelerate-cuda-cabal] files.

Documentation
-------------

  * Haddock documentation is included in the package and linked from the [Hackage page][Hackage].
  * Online documentation is on the [GitHub wiki][Wiki].
  * The idea behind the HOAS (higher-order abstract syntax) to de-Bruijn conversion used in the library is [described separately.][HOAS-conv]

Examples
--------

The GitHub repository contains a submodule [accelerate-examples][accelerate-examples], which provides a range of computational kernels and a few complete applications. To install these from Hackage, issue `cabal install accelerate-examples`. The examples include:

  * An implementation of [canny edge detection][wiki-canny]
  * An interactive [mandelbrot set][wiki-mandelbrot] generator
  * An [N-body simulation][wiki-nbody] of gravitational attraction between solid particles
  * An implementation of the [PageRank][wiki-pagerank] algorithm
  * A simple [ray-tracer][wiki-raytracing]
  * A particle based simulation of stable fluid flows
  * A cellular automata simulation
  * A "password recovery" tool, for dictionary lookup of MD5 hashes

[![Mandelbrot](http://www.cse.unsw.edu.au/~tmcdonell/images/mandelbrot-small.jpg "accelerate-mandelbrot")](http://www.cse.unsw.edu.au/~tmcdonell/images/mandelbrot.jpg)
[![Raytracer](http://www.cse.unsw.edu.au/~tmcdonell/images/ray-small.jpg "accelerate-ray")](http://www.cse.unsw.edu.au/~tmcdonell/images/ray.jpg)

<!--
<video width=400 height=300 controls=false autoplay loop>
  <source="http://www.cse.unsw.edu.au/~tmcdonell/images/ray.mp4" type="video/mp4">
</video>
-->

Accelerate users have also built some substantial applications of their own.
Please feel free to add your own examples!

  * Henning Thielemann, [patch-image](http://hackage.haskell.org/package/patch-image): Combine a collage of overlapping images
  * apunktbau, [bildpunkt](https://github.com/apunktbau/bildpunkt): A ray-marching distance field renderer
  * klarh, [hasdy](https://github.com/klarh/hasdy): Molecular dynamics in Haskell using Accelerate
  * Alexandros Gremm used Accelerate as part of the [2014 CSCS summer school](http://user.cscs.ch/blog/2014/cscs_usi_summer_school_2014_30_june_10_july_2014_in_serpiano_tessin/index.html) ([code](https://github.com/agremm/cscs))


Mailing list and contacts
-------------------------

  * Mailing list: [`accelerate-haskell@googlegroups.com`](mailto:accelerate-haskell@googlegroups.com) (discussions on both use and development are welcome)
  * Sign up for the mailing list at the [Accelerate Google Groups page][Google-Group].
  * Bug reports and issues tracking: [GitHub project page][Issues].

The maintainers of Accelerate are Manuel M T Chakravarty <chak@cse.unsw.edu.au> and Trevor L McDonell <tmcdonell@cse.unsw.edu.au>.


Citing Accelerate
-----------------

If you use Accelerate for academic research, you are encouraged (though not
required) to cite the following papers ([BibTeX](http://www.cse.unsw.edu.au/~tmcdonell/papers/accelerate.bib)):

  * Manuel M. T. Chakravarty, Gabriele Keller, Sean Lee, Trevor L. McDonell, and Vinod Grover.
    [Accelerating Haskell Array Codes with Multicore GPUs][CKLM+11].
    In _DAMP '11: Declarative Aspects of Multicore Programming_, ACM, 2011.

  * Trevor L. McDonell, Manuel M. T. Chakravarty, Gabriele Keller, and Ben Lippmeier.
    [Optimising Purely Functional GPU Programs][MCKL13].
    In _ICFP '13: The 18th ACM SIGPLAN International Conference on Functional Programming_, ACM, 2013.

  * Robert Clifton-Everest, Trevor L. McDonell, Manuel M. T. Chakravarty, and Gabriele Keller.
    [Embedding Foreign Code][CMCK14].
    In _PADL '14: The 16th International Symposium on Practical Aspects of Declarative Languages_, Springer-Verlag, LNCS, 2014.

Accelerate is primarily developed by academics, so citations matter a lot to us.
As an added benefit, you increase Accelerate's exposure and potential user (and
developer!) base, which is a benefit to all users of Accelerate. Thanks in advance!


What's missing?
---------------

Here is a list of features that are currently missing:

 * Preliminary API (parts of the API may still change in subsequent releases)



  [CKLM+11]:                http://www.cse.unsw.edu.au/~chak/papers/CKLM+11.html
  [MCKL13]:                 http://www.cse.unsw.edu.au/~chak/papers/MCKL13.html
  [CMCK14]:                 http://www.cse.unsw.edu.au/~chak/papers/CMCK14.html
  [HIW'09]:                 http://haskell.org/haskellwiki/HaskellImplementorsWorkshop
  [Mar13]:                  http://chimera.labs.oreilly.com/books/1230000000929
  [Embedded]:               https://speakerdeck.com/mchakravarty/embedded-languages-for-high-performance-computing-in-haskell
  [Hackage]:                http://hackage.haskell.org/package/accelerate
  [accelerate-cuda]:        https://github.com/AccelerateHS/accelerate-cuda
  [accelerate-examples]:    https://github.com/AccelerateHS/accelerate-examples
  [accelerate-io]:          https://github.com/AccelerateHS/accelerate-io
  [accelerate-fft]:         https://github.com/AccelerateHS/accelerate-fft
  [accelerate-backend-kit]: https://github.com/AccelerateHS/accelerate-backend-kit
  [accelerate-buildbot]:    https://github.com/AccelerateHS/accelerate-buildbot
  [accelerate-repa]:        https://github.com/blambo/accelerate-repa
  [accelerate-opencl]:      https://github.com/hiPERFIT/accelerate-opencl
  [accelerate-cabal]:       https://github.com/AccelerateHS/accelerate/accelerate.cabal
  [accelerate-cuda-cabal]:  https://github.com/AccelerateHS/accelerate-cuda/accelerate-cuda.cabal
  [accelerate-llvm]:        https://github.com/AccelerateHS/accelerate-llvm
  [GitHub]:                 https://github.com/AccelerateHS/accelerate
  [Wiki]:                   https://github.com/AccelerateHS/accelerate/wiki
  [Issues]:                 https://github.com/AccelerateHS/accelerate/issues
  [Google-Group]:           http://groups.google.com/group/accelerate-haskell
  [HOAS-conv]:              http://www.cse.unsw.edu.au/~chak/haskell/term-conv/
  [repa]:                   http://hackage.haskell.org/package/repa
  [wiki-cc]:                http://en.wikipedia.org/wiki/CUDA#Supported_GPUs
  [YLJ13-video]:            http://youtu.be/ARqE4yT2Z0o
  [YLJ13-slides]:           https://speakerdeck.com/tmcdonell/gpgpu-programming-in-haskell-with-accelerate
  [YLJ13-workshop]:         https://speakerdeck.com/tmcdonell/gpgpu-programming-in-haskell-with-accelerate-workshop
  [wiki-canny]:             http://en.wikipedia.org/wiki/Canny_edge_detector
  [wiki-mandelbrot]:        http://en.wikipedia.org/wiki/Mandelbrot_set
  [wiki-nbody]:             http://en.wikipedia.org/wiki/N-body
  [wiki-raytracing]:        http://en.wikipedia.org/wiki/Ray_tracing
  [wiki-pagerank]:          http://en.wikipedia.org/wiki/Pagerank
  [Trevor-thesis]:          http://www.cse.unsw.edu.au/~tmcdonell/papers/TrevorMcDonell_PhD_submission.pdf


