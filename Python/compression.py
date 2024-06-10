###############################################################################################
# File containing functions to compress points (based on Section 4.5 of the paper)
# This is done by the signer, and we rely on SageMath here 
# (as we are focusing on fast verif)
###############################################################################################


from globals import *

# Setting up the prime
if __name__ == "__main__":
    p = 417942208511
    set_prime(p)

from point_diff import *
from point_sampling import *
from kummer_arithmetic import *
from kummer_isogeny import *
from decompression import *

# We need SageMath for Jacobian arithmetic in disc log (only needed on the signer side)
from sage.all import *


def disclog(P, Q, R, ell, ord):
    """
    Main subroutine of disclog_wrapper, which will compute scalars a,b 
    such that R = [a]P + [b]Q, given points R, P, Q on the Jacobian
    """
    if ord == 1:
        for a in range(ell + 1):
            for b in range(ell + 1):
                if R == a * P + b * Q:
                    return a, b
        print("Error")
        assert False

    e = ord >> 1
    e1 = fp_sub(ord, e)
    fac1 = fp_expon(ell, e1)
    P1 = fac1 * P
    Q1 = fac1 * Q
    R1 = fac1 * R

    a1, b1 = disclog(P1, Q1, R1, ell, e)

    fac2 = fp_expon(ell, e)
    P2 = fac2 * P
    Q2 = fac2 * Q
    R2 = R - a1 * P - b1 * Q
    a2, b2 = disclog(P2, Q2, R2, ell, e1)

    return fp_add(
        a1, fp_mul(
            a2, fp_expon(
                ell, e))), fp_add(
        b1, fp_mul(
            b2, fp_expon(
                ell, e)))


def disclog_wrapper(P, Q, R, ell, ord):
    """
    Computes values a,b in Z/(ell^ord)Z such that the point R = [a]P + [b]Q

    INPUTS: - P and Q, points on the Jacobian generating the (ell^ord)-torsion
            - R, point on the Jacobian 
            - ell and ord, integers such that P, Q are points of order ell^ord

    OUTPUTS: - scalars a,b such that R = [a]P+[b]Q
    """

    a, b = disclog(P, Q, R, ell, ord)
    ell_ord = fp_expon(ell, ord)

    a = (a % ell_ord)
    b = (b % ell_ord)
    assert R == a * P + b * Q

    return a, b


def kummer_disclog(P, Q, R, K, ros, extra_info):
    """
    Computes values a,b such that the point R = [a]P + [b]Q

    INPUTS: - P and Q, points on the Kummer surface generating the (ell^ord)-torsion
            - R, point on the Kummer surface 
            - K, the Kummer surface
            - ros, the Rosenhain invariants corresponding to L
            - extra_info, used to compute the divisors on the Jacobian corresponding to points P, Q

    OUTPUTS: - scalars a,b such that R = [a]P+[b]Q

    NOTE: This function currently uses SageMath for Jacobian arithmetic and Finte Fields.
            Only the signer performs this subroutine, though.
    """
    # Requires SageMath here
    FF = FiniteField(p)
    PP = PolynomialRing(FF, 'x')
    x = PP.gen()
    C = HyperellipticCurve(
        x * (x - 1) * (x - ros[0]) * (x - ros[1]) * (x - ros[2]))
    J = Jacobian(C)

    # extra_info contains u1,u0,v1,v0 of P and Q so
    # that we dont have to recompute it using
    # kummer_to_jac_point
    DP = extra_info[0]
    DQ = extra_info[1]

    DP = J([x**2 + DP[0] * x + DP[1], DP[2] * x + DP[3]])
    DP = cofac * DP


    DQ = J([x**2 + DQ[0] * x + DQ[1], DQ[2] * x + DQ[3]])
    DQ = cofac * DQ
    
    # this will fail when the ros is wrong, usually mu --> 1/mu, nu --> 1/nu
    DR = kummer_to_jac_point(R, K, ros)
    DR = J([x**2 + DR[0] * x + DR[1], DR[2] * x + DR[3]])

    return disclog(DP, DQ, DR, 2, f2 - 1)


def point_compression(R, K, ros):
    """
    Given a point R, find scalars a,b that will describe the point (i.e., 
        for a deterministic choice of P,Q we have [a]P + [b]Q = R

    INPUTS: - R, a point on the Kummer surface
            - K, the Kummer surface
            - ros, the Rosenhain invariants associated to K
    
    OUTPUTS: - a,b scalars such that [a]P + [b]Q = R (for a deterministic choice of P,Q)
             - a bit, signals whether R = 3ptLadder on [a]P, Q and [a]P + Q or [a]P - Q

    """

    # Deterministically sample basis on K
    X1, X2 = precompute_sample_basis()

    # if extra = True, extra info contains the u1,u0,v1,v0 of P and Q, which
    # we input into kummer_disclog
    P, Q, extra_info = sample_basis(K, ros, [X1, X2], extra=True)

    # Find a,b such that [a]P + [b]Q = R
    a, b = kummer_disclog(P, Q, R, K, ros, extra_info)
    # we change to a = 1 below

    aP = kummer_scalar(P, K, a)

    # Compute [a]P \pm Q
    # We only want to compute one of these
    D0, D1 = point_difference_both(aP, Q, K)

    R0 = three_point_ladder(aP, Q, D0, b, K)
    if R0 == R:
        return a, b, 0
    else:
        assert R == three_point_ladder(aP, Q, D1, b, K)
        return a, b, 1


def point_compression_single(R, K, ros):
    """
    Given a point R, find scalar b that will describe the point (i.e., 
        for a deterministic choice of P,Q we have P + [b]Q = R

    INPUTS: - R, a point on the Kummer surface
            - K, the Kummer surface
            - ros, the Rosenhain invariants associated to K
    
    OUTPUTS: - b scalars such that P + [b]Q = R (for a deterministic choice of P,Q)
             - a bit, indicates whether R = 3ptLadder on P, Q and P + Q or P - Q
             - switch, indicates whether we switch the roles of P and Q (so that R = [b]P + Q instead)

    NOTE: Uses SageMath for xgcd function. This is only performed on the signer side though.
    """

    # Deterministically sample basis on K
    X1, X2 = precompute_sample_basis()

    # if extra = True, extra info contains the u1,u0,v1,v0 of P and Q, which
    # we input into kummer_disclog
    P, Q, extra_info = sample_basis(K, ros, [X1, X2], extra=True)

    # Find a,b such that [a]P + [b]Q = R
    a, b = kummer_disclog(P, Q, R, K, ros, extra_info)

    assert (a % 2 == 1 or b % 2 == 1)

    if (a % 2 == 1):
        # invert a mod 2^f and set b as b*a^-1
        d1, d2, d3 = xgcd(a, 2**(f2 - 1))
        assert d1 == 1
        d2 = d2 % (2**(f2 - 1))
        assert ((a * d2) % (2**(f2 - 1)) == 1)

        b = (b * d2) % (2**(f2 - 1))
        a = 1
        switch = 0

    elif (b % 2 == 1):
        d1, d2, d3 = xgcd(b, 2**(f2 - 1))
        assert d1 == 1
        d2 = d2 % (2**(f2 - 1))
        assert ((b * d2) % (2**(f2 - 1)) == 1)

        a = (a * d2) % (2**(f2 - 1))

        # also switch roles of P and Q
        # need to communicate this somehow, extra bit
        b = a
        a = 1
        T = P
        P = Q
        Q = T
        switch = 1
    else:
        assert False

    # as we had R = aP + bQ, so dR = a*d*P + b*d*Q
    # now dR = 1*P + b*Q

    # Compute P \pm Q
    # We only want to compute one of these
    D0, D1 = point_difference_both(P, Q, K)

    Rd = kummer_scalar(R, K, d2)

    R0 = three_point_ladder(P, Q, D0, b, K)

    if R0 == Rd:
        return b, 0, switch
    else:
        R1 = three_point_ladder(P, Q, D1, b, K)
        assert Rd == R1
        return b, 1, switch


if __name__ == "__main__":
    # TESTING
    
    # Setup

    R = [221127383281, 119318199626, 256922487017, 1]
    K = [
        [99046282131, 80137275825, 43785859117],
        [149964968508, 348114515828, 1, 1],
        [348114515828, 149964968508, 344289703673, 344289703673],
        [346513123615, 16653617905, 64454801943, 64454801943]
    ]
    ros = [158121108515, 64189784019, 25626095119]

    assert on_kummer(R, K)
    assert kummer_scalar(R, K, pow(2, f2 - 1)) == K[1]

    print("Setup is done for compression.")
    print("")
    # RUN COMPRESSION
    print("Doing compression (with SageMath)....")
    a, b, bit = point_compression(R, K, ros)
    print("Done!")
    print("")

    # CHECK RECONSTRUCTION WILL WORK
    print("Doing decompression (with Python)....")
    Rp = point_decompression(K, ros, [a, b], bit)
    assert R == Rp
    print("Done and correct!")
    print("")

    # RUN COMPRESSION SINGLE
    print("Doing compression with a == 1 (with SageMath)....")
    b, bit, switch = point_compression_single(R, K, ros)
    print("Done!")
    print("")

    # CHECK RECONSTRUCTION WILL WORK
    print("Doing decompression with a == 1 (with Python)....")
    Rp = point_decompression_single(K, ros, b, bit, switch)

    # we no longer get R == Rp, but should get <R> == <Rp>
    # thus, they generate the same isogeny
    K1, eval = naive_kummer_isogeny(R, K, [], f2 - 1)
    K2, eval = naive_kummer_isogeny(Rp, K, [], f2 - 1)

    assert K1 == K2

    print("Done and correct!")
