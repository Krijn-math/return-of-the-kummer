## Supplementary material for SQIsign verification using Kummers

This is an implementation of SQIsign verification using Kummer surfaces.
Many of these algorithms are new and can benefit from improvements here and there.
Nevertheless, the code is sound enough to give a crude estimate of performance of Kummer surfaces.

To compare against the number of Fp-operations in ApresSQI, we have used the same metric to compare.
Note that practical C implementations will most likely differ with regards to relative performance.

To (re)run benchmarking, run

```bash
python kummer_verification.py
```
(tested with python 3.12.2)

Note: the current implementation does not use Kummer normalization, as the current algorithm is too unoptimal.
On the other hand, the current challenge isogeny is too long. Manual timing results suggests 15000 Fp-operations
can be saved by using a challenge isogeny of degree 128, instead of 245.