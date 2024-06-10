## Instructions for a general toolbox for isogeny-based cryptography in genus 2 in Magma

This subdirectory contains `Magma` code for many of the tools for isogeny-based cryptography in genus 2, with specific subfolders associated to specific sections of the paper.

### Contents

The eight subfolders of this directory each serve a specific purpose, with many later folders often relying on earlier folders.

- The folder `costello-code` contains the basis Kummer arithmetic, such as doubling and differential addition, and many of the maps described by Costello in 2018/850. The code in this folder is a direct copy of his associated repository, with some minor additions to the underlying Kummer arithmetic where necessary.
- The folder `gluing` contains code that glues together a curve `E` and its Galois conjugate, to show that this is isomorphic over `Fp2` to the Weil restriction of `E`.
- The folder `proofs` contains symbolic proofs of several results in the paper, namely 1) that the value `e` in the Möbius transform defined in Costello's concrete maps to construct a (2,2)-isogeny can always be chosen to be a rational value, and 2) that the improved partial maps K --> J given in section 2 are correct.
- The folder `section 2` contains code to practically instantiate many of the maps described in section 2 of the paper and furthermore gives the addition matrices `W_ij` associated to a point `L_ij` of order 2 on both squared Kummer surfaces and elliptic Kummer surfaces. Lastly, it contains code to compute several invariants used throughout the work.
- The folder `section 3` contains code to practically compute pairings of degree 2 on Jacobians, general Kummer surfaces and squared Kummer surfaces. This folder contains three ways to compute such a pairing, namely using Gaudry's theta functions, using Robert's biextensions, and using our own improved map K --> J.
- The folder `section 4` contains code for the essential algorithms 
`CheckOrigin`, `PointDifference`, `Normalisation` and `PointCompression`. It furthermore contains the biquadratics on the general Kummer surface and the intermediate Kummer surface, as required for `PointDifference`. Lastly, it contains a rough description of the `elegant sampling` method described in the paper.
- The folder `section 5` contains code to compute (2,2)-isogenies on Kummer surfaces, derived from the alpha maps as described in section 5 of the paper.
- The folder `section 6` contains code that runs compressed and uncompressed SQIsign verification in Magma. The Python subdirectory generally contains better and more optimized code, whereas this folder mostly contains a toy example.