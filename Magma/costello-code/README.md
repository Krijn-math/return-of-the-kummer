### Content

In this folder are 4 Magma files, originally associated to the paper
*[Computing Supersingular Isogenies on Kummer Surfaces, ASIACRYPT 2018](https://eprint.iacr.org/2018/850)* by Craig Costello. Mostly, only minor changes have been made to make bug-fixing easier.
- The file `Params.m` contains various lower-level functions called by the other 3 files. We have added code to make initialisation of the hyperelliptic urves, Jacobians and Kummer surfaces used in all other files a bit easier.
- The file `Maps.m` corresponds to Section 3 of the paper. It contains the back-and-forth maps between the (Weil restriction) of a supersingular Montgomery curve over GF(p^2) and the corresponding abelian surface over Fp.
- The file 'Jacobian.m' corresponds to Section 4 of the paper. It computes Richelot isogenies on supersingular abelian surfaces. 
- The file 'Kummer.m' corresponds to Section 5 of the paper. It computes chains of (2,2) isogenies on fast Kummer surfaces, in line with cryptography applications, e.g., SIDH. Additionally, we have implemented `ThreePointLadder` in this folder, by devising an analogue of the elliptic curve instantiation, and have implemented some functions related to the twist of a Kummer surface, as described in section 2 of our paper.

### Execution

Assuming the files are in the current directory, and Magma is running, they can be executed via (e.g.) 

			load "Kummer.m";

The files will run on any SIDH-friendly prime of the form p=2^eA*3^eB-1 (use p>>100 so there's enough supersingular curves minimally defined over GF(p^2)), but making them cryptographically large will slow things down because they call Magma's internal Sqrt function (over GF(p^2)) when computing the starting/public parameters. For such sizes, these public parameters would be fixed and, starting from the initial Kummer, no square roots are needed again. See Section 6 of Costello's paper for more details.

The original code is licensed under the MIT license, Copyright (c) Microsoft, all rights reserved.

