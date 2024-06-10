##########################################################
# File containing functions to decompress points 
#           (based on Section 4.5 of the paper)
##########################################################

from globals import *

# Setting up the prime
if __name__ == "__main__":
    p = 417942208511
    set_prime(p)

from point_diff import *
from point_sampling import *
from kummer_arithmetic import *
from kummer_isogeny import *


def point_decompression(K, ros, scals, bit, precomp):
    """
    Computes point R = [a]P + [b]Q on a Kummer surface, given scalars a,b and deterministically 
            sampling points P, Q (as described in Section 4.5 of the paper). 
            This is performed by the verifier. 
            

    INPUTS: - K, the Kummer surface
            - ros, the Rosenhain invariants corresponding to K
            - scals, the scalars used for point decompression 
            - bit, indicates whether we run 3ptLadder with the point difference or point sum
            - precomp, precomputation used to sample the basis
    
    OUTPUTS: R such that R = [a]P + [b]Q where scals = [a,b] and P,Q are deterministically sampled
    """

    # eventually we want to change so a = 1 always
    a = scals[0]
    b = scals[1]

    P, Q, _ = sample_basis(K, ros, precomp)

    aP = kummer_scalar(P, K, a)
    diffs = point_difference_both(aP, Q, K)
    return three_point_ladder(aP, Q, diffs[bit], b, K)


def point_decompression_single(K, ros, b, bit, switch, precomp):

    P, Q, _ = sample_basis(K, ros, precomp)

    if switch:
        T = P
        P = Q
        Q = T

    diffs = point_difference_both(P, Q, K)
    return three_point_ladder(P, Q, diffs[bit], b, K)


def point_decompression_single_with_Q(K, ros, b, bit, switch, precomp):
    """
    Computes point R = P + [b]Q on a Kummer surface, given scalarnb and deterministically 
            sampling points P, Q (as described in Section 4.5 of the paper). 
            This is performed by the verifier. 
            

    INPUTS: - K, the Kummer surface
            - ros, the Rosenhain invariants corresponding to K
            - b, the scalar used for point decompression 
            - bit, indicates whether we run 3ptLadder with the point difference or point sum
            - switch, indicates whether we switch the roles of P and Q (so that R = [b]P + Q instead)
            - precomp, precomputation used to sample the basis
    
    OUTPUTS: R such that R = P + [b]Q where P,Q are deterministically sampled
    """
    P, Q, _ = sample_basis(K, ros, precomp)
    R = deepcopy(Q)

    if switch:
        T = P
        P = Q
        Q = T

    diffs = point_difference_both(P, Q, K)
    return three_point_ladder(P, Q, diffs[bit], b, K), R
