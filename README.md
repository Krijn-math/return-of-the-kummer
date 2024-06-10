# Return of the Kummer

This repository contains the code accompanying the paper 
*[	Return of the Kummer: a toolbox for genus 2 cryptography](https://eprint.iacr.org/2024/XXX)* by Maria Corte-Real Santos and Krijn Reijnders.

All code in this repository was written in `Magma`, `Python` and [`SageMath`](https://www.sagemath.org/), and is made publicly available under the MIT license. The dependencies are:
- Python 3.11.1 (with matplotlib)
- SageMath version 10.1
- Magma version V.25-4

### Contents

This repository contains two main directories:
- `Magma`: this contains many of the crucial techniques and tools for isogeny-based cryptography in genus 2 as described in the paper. The folder is subdivided into the sections of the paper. Symbolic proofs for several results of the paper are given in the subfolder `proofs`. All the code in this directory is written in `Magma`, and is explained in more detail in the `README.md` file for this subdirectory.
- `Python`: this contains the code used for benchmarking verification, thus includes the required Kummer arithmetic to achieve both compressed and uncompressed SQIsign verification on Kummer surfaces. The code in this directory is written in `Python`, with a small part in `SageMath`, and is explained in more detail in the `README.md` file for this subdirectory.

### Acknowledgements
The Magma code in the `Magma` subdirectory is based on the work *[Computing supersingular isogenies on Kummer surfaces](https://ia.cr/2018/850)* by Craig Costello, and in particular uses code from the [associated repository](https://www.microsoft.com/en-us/download/details.aspx?id=57309).
The code is furthermore partly based on the work *[Fast genus 2 arithmetic based on Theta functions](https://ia.cr/2005/314)* by Pierrick Gaudry, and its [associated code](http://www.lix.polytechnique.fr/Labo/Pierrick.Gaudry/publis/kummer.mag).


#### Notes
 Throughout, by `python` we mean `python3` if your terminal requires this (e.g., some MacOS versions may require this.)

## Licenses

Code in this repository that does not indicate otherwise is published under the MIT license,
as is the third-party code that this code is based on.
