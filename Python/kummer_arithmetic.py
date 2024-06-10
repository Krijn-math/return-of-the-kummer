# ###############################################################
#         Useful functions for fast Kummer arithmetic
# ###############################################################

from globals import *
from fp import *
from hyperell_curve import *
from math import prod 

def hadamard(P):
    """
    The 4-way hadamard transform

        INPUTS: - A tuple of four projective field elements [x,y,z,t]
        OUTPUTS: - The hadamard transform [x+y+z+t,x+y-z-t,x-y+z-t,x-y-z+t]
    """

    T1 = fp_add(P[0], P[1])
    T2 = fp_add(P[2], P[3])
    T3 = fp_sub(P[0], P[1])
    T4 = fp_sub(P[2], P[3])

    return [fp_add(T1, T2), fp_sub(T1, T2), fp_add(T3, T4), fp_sub(T3, T4)]


def squaring(P):
    """
    The 4-way squaring

        INPUTS: - A tuple of four projective field elements [x,y,z,t]
        OUTPUTS: - The coordinate-wise squarings [x^2,y^2,z^2,t^2]
    """
    return [fp_sqr(x) for x in P]


def four_way_mult(V, W):
    """
        The 4-way coordinate-wise multiplication of 2 tuples

        INPUTS: - Two tuples of four projective field elements
        OUTPUTS: - One 4-tuple of their coordinate-wise products
    """

    return [
        fp_mul(
            V[0], W[0]), fp_mul(
            V[1], W[1]), fp_mul(
                V[2], W[2]), fp_mul(
                    V[3], W[3])]


def invert4_constants(P):
    """
    The 4-way inversion in projective 3-space

        INPUTS: - One tuple of 4-elements in P^3
        OUTPUTS: - A tuple of elements projectively equivalent to their inverses
    """

    pi1 = fp_mul(P[2], P[3])
    pi2 = fp_mul(pi1, P[0])
    pi1 = fp_mul(pi1, P[1])
    pi3 = fp_mul(P[0], P[1])
    pi4 = fp_mul(pi3, P[2])
    pi3 = fp_mul(pi3, P[3])

    return [pi1, pi2, pi3, pi4]


def coord_prod(P):
    """
    Computes the product of the coordinates of a point P

    INPUTS: - One tuple P of 4-elements in P^3
    OUTPUTS: - The product P[0]*P[1]*P[2]*P[3] of the coordinates of P
    """

    P01 = fp_mul(P[0], P[1])
    P23 = fp_mul(P[2], P[3])
    prod = fp_mul(P01, P23)
    return prod


def coord_add(P):
    """
    Computes the addition of the coordinates of a point P

    INPUTS: - One tuple P of 4-elements in P^3
    OUTPUTS: - outputs P[0]+P[1]+P[2]+P[3]
    """

    P01 = fp_add(P[0], P[1])
    P23 = fp_add(P[2], P[3])
    add = fp_add(P01, P23)
    return add


def kummer_constants_from_squared_thetas(P):
    """
Computes the Kummer surface constants used in the DBL and DBLADD functions

    INPUTS: - the 4 squared theta constants [mu1,mu2,mu3,mu4]
    OUTPUTS: - the first tuple is projectively equivalent to [1/mu1: 1/mu2: 1/mu3: 1/mu4]
                     - the second tuple is projectively equivalent to [1/mu1h: 1/mu2h: 1/mu3h: 1/mu4h],
                     where the mujh are the j-th component of the hadamard transform of [mu1,mu2,mu3,mu4]
"""

    return invert4_constants(P), invert4_constants(hadamard(P))


def squared_kummer_from_squared_thetas(thetas):
    """
    Computes all of the Kummer surface constants

        INPUTS: - the 4 squared theta constants [mu1,mu2,mu3,mu4]
        OUTPUTS: - K1: [K_F,K_G,K_H], which define a Kummer surface (see Section 5)
                         - K2: [mu1,mu2,mu3,mu4], the unchanged input, but part of the full description of a Kummer
                         - K3, K4: the two 4-tuples of projective constants needed in the DBL and DBLADD routines
    """

    mu1 = thetas[0]
    mu2 = thetas[1]
    mu3 = thetas[2]
    mu4 = thetas[3]

    M1 = fp_add(fp_add(mu1, mu2), fp_add(mu3, mu4))
    M2 = fp_sub(fp_add(mu1, mu2), fp_add(mu3, mu4))
    M3 = fp_sub(fp_add(mu1, mu3), fp_add(mu2, mu4))
    M4 = fp_sub(fp_add(mu1, mu4), fp_add(mu2, mu3))
    M12 = fp_mul(M1, M2)
    M34 = fp_mul(M3, M4)
    KF = fp_mul(M12, M34)

    m12 = fp_mul(mu1, mu2)
    m13 = fp_mul(mu1, mu3)
    m14 = fp_mul(mu1, mu4)
    m23 = fp_mul(mu2, mu3)
    m24 = fp_mul(mu2, mu4)
    m34 = fp_mul(mu3, mu4)
    m1423 = fp_inv(fp_sub(m14, m23))
    m1324 = fp_inv(fp_sub(m13, m24))
    m1234 = fp_inv(fp_sub(m12, m34))
    KF = fp_mul(fp_mul(fp_mul(KF, m1423), m1324), m1234)

    KG = fp_mul(
        fp_sub(
            fp_add(
                fp_sqr(mu1), fp_sqr(mu4)), fp_add(
                fp_sqr(mu2), fp_sqr(mu3))), fp_inv(
                    fp_sub(
                        m14, m23)))

    KH = fp_mul(
        fp_sub(
            fp_add(
                fp_sqr(mu1), fp_sqr(mu2)), fp_add(
                fp_sqr(mu3), fp_sqr(mu4))), fp_inv(
                    fp_sub(
                        m12, m34)))
    KF = fp_mul(fp_mul(fp_mul(4, fp_sqr(KF)), m12), m34)

    K1 = [KF, KG, KH]
    K2 = thetas
    K3, K4 = kummer_constants_from_squared_thetas(thetas)

    return [K1, K2, K3, K4]

# ############################################################################################################################################################
# Computations as described in Section 5 of Costello 2018/850.
# Note that various checks of correctness and point normalisations (that would not be used in an actual implementation) are performed throughout.
# ############################################################################################################################################################


def normalise(P):
    """
    Normalizes Kummer points in P^3, mainly for equality and correctness checking. Sets the 4th coordinate as 1, unless there is a zero coordinate, in which case it's a 2-torsion point, where we set the 1st coordinate as 1.

        INPUT: - P: Point in P^3, represented as a 4-tuple
        OUTPUT: - Normalised point equivalent to P
    """

    if prod(P) != 0:
        Pinv = fp_inv(P[3])
        return [fp_mul(P[0], Pinv), fp_mul(P[1], Pinv), fp_mul(P[2], Pinv), 1]
    else:
        # assuming P[0] != 0
        Pinv = fp_inv(P[0])
        return [1, fp_mul(P[1], Pinv), fp_mul(P[2], Pinv), fp_mul(P[3], Pinv)]


def on_kummer(P, K):
    """
    Checks if a given point is on a given Squared Kummer surface.

        INPUTS: - P: Point in P^3, represented as a 4-tuple
                        - K: Kummer surface
        OUTPUT: - boolean: true if P lies on K, false otherwise
    """

    P1234 = coord_prod(P)
    P1sq = fp_sqr(P[0])
    P2sq = fp_sqr(P[1])
    P3sq = fp_sqr(P[2])
    P4sq = fp_sqr(P[3])
    P12a = fp_add(P[0], P[1])
    P34a = fp_add(P[2], P[3])
    P1234a = fp_mul(P12a, P34a)
    P12m = fp_mul(P[0], P[1])
    P34m = fp_mul(P[2], P[3])
    P1234m = fp_add(P12m, P34m)

    return fp_mul(
        K[0][0], P1234) == fp_sqr(
        fp_sub(
            fp_add(
                P1sq, fp_add(
                    P2sq, fp_add(
                        P3sq, P4sq))),
            fp_add(
                fp_mul(
                    K[0][1], P1234a), fp_mul(
                        K[0][2], P1234m))
            )
        )


def DBL(P, K):
    """
    (Pseudo-)doubling of a Kummer point

        INPUTS: - P: Point in P^3, represented as a 4-tuple, lying on...
                        - K: Kummer surface
        OUTPUT: - [2]P
    """
    P = hadamard(P)
    P = squaring(P)
    P = four_way_mult(P, K[3])
    P = hadamard(P)
    P = squaring(P)
    P = four_way_mult(P, K[2])

    return P

    ## For debugging
    # if on_kummer(P, K):
    #     return normalise(P)
    # else:
    #     print("Warning: DBL failed!!!")
    #     return "Somethings wrong in DBL..."


def eDBLs(P, K, e):
    """
    Repeated (Pseudo-)doublings of a Kummer point

        INPUTS: - P: Point in P^3, represented as a 4-tuple, lying on...
                        - K: Kummer surface
                        - e: an integer
        OUTPUT: - [2^e]P
    """

    for _ in range(e):
        P = DBL(P, K)

    return P

    ## For debugging
    # if on_kummer(P, K):
    #     return normalise(P)
    # else:
    #     print("Warning: eDBLs failed!!!")
    #     assert False
    #     return "Somethings wrong in eDBLs..."


def DBLADD(P, Q, R, K):
    """
    (Pseudo-)addition of Kummer points

        INPUTS: - P, Q, invert4_constants(R): Points in P^3, all represented as a 4-tuple, where R=(Q+-P) lying on...
                        - K: Kummer surface
        OUTPUT: - (Q-+P)
    """

    P = hadamard(P)
    U = hadamard(Q)

    Q = four_way_mult(P, K[3])
    P = four_way_mult(P, Q)
    Q = four_way_mult(Q, U)

    P = hadamard(P)
    Q = hadamard(Q)

    P = squaring(P)
    Q = squaring(Q)

    P = four_way_mult(P, K[2])
    Q = four_way_mult(Q, R)

    return P, Q

    ## For debugging
    # if on_kummer(P, K) and on_kummer(Q, K):
    #     return P, Q
    # else:
    #     print("Warning: DBLADD failed!!!")
    #     assert False
    #     return "Somethings wrong in DBLADD..."


def kummer_scalar(P, K, m):
    """
    Scalar multiplication of Kummer points

        INPUTS: - P: Point in P^3, represented as a 4-tuple, lying on...
                        - K: Kummer surface
                        - m: a positive integer scalar
        OUTPUT: - [m]P
    """

    def binary(n): return n > 0 and [n & 1] + binary(n >> 1) or []
    bits = binary(m)

    Pm = P
    pp = DBL(P, K)
    R = invert4_constants(P)

    for i in range(len(bits) - 2, -1, -1):
        if bits[i] == 0:
            Pm, pp = DBLADD(Pm, pp, R, K)
        else:
            pp, Pm = DBLADD(pp, Pm, R, K)


    return Pm

    ## For debugging
    # if on_kummer(Pm, K):
    #     return normalise(Pm)
    # else:
    #     print("Warning: kummer_scalar failed!!!")
    #     assert False
    #     return "Somethings wrong in Kummer Scalar..."


def three_point_ladder(P, Q, R, m, K):
    """
    Computes 3-point ladder (from SIKE)

        INPUTS: - P, Q, R = P-Q: Points in P^3, represented as 4-tuples, lying on...
                        - K: Kummer surface
                        - m: a positive integer scalar
        OUTPUT: -  P + [m]Q
    """
    def binary(n): return n > 0 and [n & 1] + binary(n >> 1) or []
    bits = binary(m)

    P0 = Q
    P1 = P
    P2 = R

    for i in bits:
        if i == 1:
            P0, P1 = DBLADD(P0, P1, invert4_constants(P2), K)
        else:
            P0, P2 = DBLADD(P0, P2, invert4_constants(P1), K)

    if P1 == [0, 0, 0, 0]:
        print("TODO: fix DBLADD")
        assert False

    return P1

    ## For debugging
    # if on_kummer(P1, K):
    #     return normalise(P1)
    # else:
    #     assert False
    #     return print("Somethings Wrong...")


# #################################
# CheckOrigin functions
# #################################

def get_u_helper(P, K, ros):
    """
    This function outputs constants needed to get u0, u1, 
    and v0^2 with no inversions with get_v02()

    INPUTS: - P, a point of the Kummer surface
            - K, the Kummer surface
            - ros, Rosenhain invariants corresponding to the Kummer surface

    OUTPUTS: - u0n and u0d, the numerator and denominator of u0 
             - u1n and u1d, the numerator and denominator of u1
             - ln and ld, the numberator and denominator of a value we will need
                            to compute v0^2
            - X0, a value we will need to compute v0^2 

    """
    w4 = ros[0]
    w5 = ros[1]
    w6 = ros[2]

    # point correction
    temp_K2 = [fp_inv(k) for k in K[1]]
    X = four_way_mult(P, temp_K2)

    w46 = fp_mul(w4, w6)
    w45 = fp_mul(w4, w5)
    w56 = fp_mul(w5, w6)

    sw5 = fp_sub(1, w5)
    w4sw6 = fp_sub(w4, w6)
    sw6 = fp_sub(1, w6)
    w4sw5 = fp_sub(w4, w5)

    u0n_1 = fp_mul(sw5, fp_mul(w46, X[0]))
    u0n_2 = fp_mul(w4sw6, fp_mul(w5, X[1]))
    u0n_3 = fp_mul(sw6, fp_mul(w45, X[2]))
    u0n_4 = fp_mul(w4sw5, fp_mul(w6, X[3]))
    u0n = fp_sub(fp_add(u0n_1, u0n_2), fp_add(u0n_3, u0n_4))

    u0d_1 = fp_mul(w4sw6, X[0])
    u0d_2 = fp_mul(sw5, X[1])
    u0d_3 = fp_mul(w4sw5, X[2])
    u0d_4 = fp_mul(sw6, X[3])
    u0d = fp_sub(fp_add(u0d_1, u0d_2), fp_add(u0d_3, u0d_4))

    u1n_1 = fp_sub(w4, w56)
    u1n_2 = fp_sub(fp_add(X[2], X[3]), fp_add(X[0], X[1]))
    u1n = fp_mul(u1n_1, u1n_2)

    u1d = u0d

    sw4 = fp_sub(1, w4)
    w6sw5 = fp_sub(w6, w5)
    w4sw56 = fp_sub(w4, w56)

    ln = fp_mul(fp_mul(fp_mul(sw4, w6sw5), w4sw56), u0n)
    ld = fp_sqr(u0d)

    return u0n, u0d, u1n, u1d, ln, ld, X[0]


def get_v02(P, K, ros):
    """
    Outputs u0, u1, v0^2 for a Kummer surface K 
        (as described in Section 2.7 of the paper)

    INPUTS: - P, a point on the Kummer surface
            - K, the Kummer surface
            - ros, the Rosenhain invariants relating to the Kummer surface
    
    OUTPUTS: u0, u1, v0^2 as arrays [numerator, denominator] (to avoid inversions)
    """
    u0n, u0d, u1n, u1d, ln, ld, X0 = get_u_helper(P, K, ros)

    w4 = ros[0]
    w5 = ros[1]
    w6 = ros[2]

    # numerator = u0n*(w5*u0d - u0n)*((w4 + w6)*u1d + u1n) - u1d*ln*X0;
    # (using the fact that u0d^2 = ld)
    # denominator = u1d*u0d^2 = ld*u1d

    v1 = fp_sub(fp_mul(w5, u0d), u0n)
    v2 = fp_add(fp_mul(fp_add(w4, w6), u1d), u1n)
    v3 = fp_mul(fp_mul(u1d, ln), X0)

    v02n = fp_sub(fp_mul(u0n, fp_mul(v1, v2)), v3)
    v02d = fp_mul(ld, u1d)

    return [u0n, u0d], [u1n, u1d], [v02n, v02d]


def check_origin(P, K, ros):
    """
    Check Origin function as described in Algorithm 1 of the paper 

    INPUTS: - P, a point on the Kummer surface
           - K, the Kummer surface
           - ros, the Rosenhain invariants relating to that Kummer surface
    
    OUTPUTS: True if the pre-image of P liked on the Jacobian J_ros, and False if 
             it lies on the twist. 
    """
    _, _, v02 = get_v02(P, K, ros)

    return fp_issquare(seq_to_element(v02))

# #################################
# Random Kummer Point
# #################################


def random_kummer_point_fromros(K, ros):
    """
    Computes a pseudo-random point on a given Kummer surface,
    always with the second point given by (w4, 0)

        INPUTS: - K: Kummer surface and ros: associated Rosenhain
        OUTPUT: - a random point P on K
    """

    x1, y1 = random_curve_point(ros)
    x2 = ros[0]
    y2 = 0

    u1 = -fp_add(x1, x2)
    u0 = fp_mul(x1, x2)

    # assert fp_add(fp_add(fp_sqr(x1),fp_mul(u1, x1)), u0) == 0
    # assert fp_add(fp_add(fp_sqr(x2),fp_mul(u1, x2)), u0) == 0

    top = fp_sub(fp_mul(y1, x2), fp_mul(y2, x1))
    bot = fp_sub(x2, x1)
    v0 = fp_mul(top, fp_inv(bot))

    v02 = fp_sqr(v0)

    # v1 = fp_mul(fp_sub(y1,y2), fp_inv(fp_sub(x1,x2)))
    # assert fp_add(fp_mul(v1, x1), v0) == y1
    # assert fp_add(fp_mul(v1, x2), v0) == y2

    return curve_to_squaredkummer(K, ros, u0, u1, v02)

def random_kummer_point(K, ros):
    """
    Computes a pseudo-random point on a given Kummer surface,
    always with the second point given by (w4, 0)

        INPUTS: - K: Kummer surface and ros: associated Rosenhain
        OUTPUT: - a random point P on K
    """

    x1, y1 = random_curve_point(ros)
    x2, y2 = random_curve_point(ros)

    u1 = -fp_add(x1, x2)
    u0 = fp_mul(x1, x2)

    # assert fp_add(fp_add(fp_sqr(x1),fp_mul(u1, x1)), u0) == 0
    # assert fp_add(fp_add(fp_sqr(x2),fp_mul(u1, x2)), u0) == 0

    top = fp_sub(fp_mul(y1, x2), fp_mul(y2, x1))
    bot = fp_sub(x2, x1)
    v0 = fp_mul(top, fp_inv(bot))

    v02 = fp_sqr(v0)

    # v1 = fp_mul(fp_sub(y1,y2), fp_inv(fp_sub(x1,x2)))
    # assert fp_add(fp_mul(v1, x1), v0) == y1
    # assert fp_add(fp_mul(v1, x2), v0) == y2

    return curve_to_squaredkummer(K, ros, u0, u1, v02)


def kummer_to_jac_point(P, K, ros):
    """
    Computes the preimage of a point on the Kummer surface 
            (as described in Section 2.7)

    INPUTS: - P, a point on the Kummer surface
            - K, the Kummer surface
            - ros, the Rosenhain invariants corresponding to K
    
    OUTPUTS: a point D_P on the Jacobian J_ros that maps to P on the Kummer surface
                    
    """
    #assert on_kummer(P, K)

    u0, u1, v02 = get_v02(P, K, ros)

    # TODO: Remove inversions?
    u0 = seq_to_element(u0)
    u1 = seq_to_element(u1)
    v02 = seq_to_element(v02)

    #assert fp_issquare(v02)
    print(u0, u1, v02)

    # Two roots of x^2 + u1*x + u0
    x1, x2 = fp_polyroot([u0, u1, 1], all=True)

    
    x1 = seq_to_element(x1)
    x2 = seq_to_element(x2)

    y1 = get_y(x1, ros)
    y2 = get_y(x2, ros)

    # assert _on_curve(x1, y1, ros)
    # assert _on_curve(x2, y2, ros)

    # Finding the correct choice of y's that give the correct v0^2
    for z1 in [y1, -y1]:
        for z2 in [y2, -y2]:
            top = fp_sub(fp_mul(z1, x2), fp_mul(z2, x1))
            bot = fp_sub(x2, x1)
            v0 = fp_mul(top, fp_inv(bot))
            if fp_sqr(
                    v0) == v02:  # this sporadically fails
                y1 = z1
                y2 = z2
                v1 = fp_mul(fp_sub(y1, y2), fp_inv(fp_sub(x1, x2)))
                return u1, u0, v1, v0
            
    assert False

# ###############################################################
#         Equality of Kummer surfaces
# ###############################################################


def twist_kummer(K):
    """
    Computes the elliptic twist of a Kummer surface 
            (as described in Section 2.9)

    INPUTS: K, the Kummer surface
    OUTPUTS: The twist of the Kummer surface
    """
    mus = K[1]
    twistmus = [-mus[0], -mus[1], mus[2], mus[3]]
    return squared_kummer_from_squared_thetas(twistmus)


def equal_kummer(K1, K2):
    """
    Checks if K1 and K2 are defined by the same mus are normalisation, or 
    by the twisted mus.

    INPUTS: - K1, a Kummer surface 
            - K2, a Kummer surface

    OUTPUTS: True if the mus of K1 and K2 are the same, False if they are 
            twists of one anther
    """
    
    
    mu_K1 = normalise(K1[1])
    mu_K2 = normalise(K2[1])

    twist_mu_K1 = normalise(twist_kummer(K1)[1])

    if mu_K1 == mu_K2:
        return True
    elif twist_mu_K1 == mu_K2:
        return True
    else:
        return False


