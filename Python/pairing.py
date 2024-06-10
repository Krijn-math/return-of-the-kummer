#######################################################
#######################################################
# This file contains the functions needed to compute 
#    pairings (of degree 2) on Kummer surfaces.

# We implement the 2nd and 3rd methods as given in 
#    Section 3 of the paper 
#######################################################
#######################################################


from globals import *

# Setting prime for testing
if __name__ == "__main__":
    p = 417942208511
    set_prime(p)

from kummer_arithmetic import *
from translation_matrices import *
from point_diff import point_difference

###############################
# Extra functions
###############################

def wp_to_sqkummer(inds, ros):
    """
    Given indices <i,j> corresponding to Weierstrass points 
    Pi = (w_i, 0) and Pj = (wj, 0) on the curve, 
    outputs the divisor D_P = (P1) + (P2) on the Jacobian 
    in Mumford representation.

    WARNING: for our purposes, we only map indices 1 < i < j.
    The mapping of points with w_1 = infty are slightly more complicated.

    NOTE: the w_i are as described in the paper, and so w_i corresponds to wp[i-1].
    """
    i = inds[0]
    j = inds[1]
    wp = [0, 0, 1, ros[0], ros[1], ros[2]]

    if i != 0:
        u1 = -fp_add(wp[i], wp[j])
        u0 = fp_mul(wp[i], wp[j])
        return curve_to_squaredkummer(K, ros, u0, u1, 0)

    print("Figure out mapping of infty points")
    assert False

#########################################################################################
# Robert Mondronomy approach
# URL: https://www.normalesup.org/~robert/pro/publications/articles/biextensions.pdf
#########################################################################################


def pairing_robert_precomp(inds, P, K):
    """
        Performs the precomputation required to compute the 
        2-tate pairing using Robert's approach, Algorithm 5.2.
        See also Appendix 3 in the paper.

        Given
        - indices inds = <i,j>
        - a point P
        - on a kummer surface K

        Returns 
        - the normalizing index
        - the addition matrix M_ij corresponding to the indices,
        - and the lambda value.

        WARNING: for now only for 1 < i < j, note that Tate
        pairings with i = 1 can be computed using bilineairity.
    """

    if inds[0] > 0:
        L = wp_to_sqkummer(inds, ros)

    # normalising index
    for i in range(4):
        if P[i] != 0 and L[i] != 0:
            ni = i

    # we still use inversion for now, but this can be simplified,
    # as we only care about the quadratic residue
    inv_ni = fp_inv(L[ni])
    L = [fp_mul(L[i], inv_ni) for i in range(4)]

    M = get_mat(inds)
    ML = matrix_mult(M, L)

    lambda1 = fp_div(ML[ni], K[2][ni])
    assert [K[2][i] * lambda1 for i in range(4)] == ML

    return ni, M, lambda1


def pairing_robert(inds, P, K):
    """
        Performs the 2-tate pairing using Robert's approach, Algorithm 5.2.
        See also Appendix 3 in the paper.

        Given
        - indices inds = <i,j>
        - a point P
        - on a kummer surface K

        Returns 
        - the reduced 2-tate pairing t_ij(P) = t_2(L_ij, P)

        WARNING: for now only for 1 < i < j, note that Tate
        pairings with i = 1 can be computed using bilineairity.
    """

    ni, M, lambda1 = pairing_robert_precomp(inds, P, K)

    # we still use inversion for now, but this can be simplified,
    # as we only care about the quadratic residue
    inv_P_ni = fp_inv(P[ni])
    L = [fp_mul(P[i], inv_P_ni) for i in range(4)]
    D = point_difference(P, L, K)

    inv_D_ni = fp_inv(D[ni])
    D = [fp_mul(D[i], inv_D_ni) for i in range(4)]

    MD = matrix_mult(M, D)
    lambda2 = fp_mul(MD[ni], inv_P_ni)
    assert MD == [P[i] * lambda2 for i in range(4)]

    return fp_div(lambda2, lambda1)

###############################
# Recovering u0, u1 method
###############################

def identify(P, ros, K):
    """
        For now, a rather coarse method to identify P in K[2] as L_ij
    """

    assert normalise(DBL(P, K)) == normalise(K[1])

    for i in range(0, 5):
        for j in range(i + 1, 6):
            Ptmp = wp_to_sqkummer([i, j], ros)
            if P == Ptmp or P == normalise(Ptmp) or normalise(P) == normalise(Ptmp):
                return i, j
    for j in range(1, 6):
        u1 = 1
        wp = [0, 0, 1, ros[0], ros[1], ros[2]]
        u0 = -wp[j]
        curve_to_squaredkummer(K, ros, u0, u1, 0)
    print("There is some error in 'identify'.")
    return [0, 0, 0, 0]


def pairing(P, K, ros, ind):
    """
        Performs the 2-tate pairing using the efficient maps to
        recover u0 and u1, given a point P on a kummer K
        See also section 3.3 in the paper.

        Given
        - indices ind = <i,j>
        - a point P
        - on a kummer surface K^Sqr
        - and the rosenhain invariants ros = (lambda, mu, nu)

        Returns 
        - the reduced 2-tate pairing t_ij(P) = t_2(L_ij, P)
    """

    # For now, we assume coprimality (e.g., P is not of order 2)
    # this can be fixed using standard pairing techniques, e.g. add random S to P
    i = ind[0]
    j = ind[1]

    assert i < j

    u0, u1, T = get_v02(P, K, ros)

    u0n = u0[0]
    u0d = u0[1]
    u1n = u1[0]
    u1d = u1[1]

    u0 = fp_mul(u0n, fp_inv(u0d))
    u1 = fp_mul(u1n, fp_inv(u1d))

    # Weierstrass points
    wp = [0, 0, 1, ros[0], ros[1], ros[2]]

    wi = wp[i]
    wj = wp[j]

    # The case where inf is in L_ij is a slightly different formula
    if i == 0:
        wj_sq = fp_sqr(wj)
        wju1 = fp_mul(wj, u1)
        return fp_add(fp_add(wj_sq, wju1), u0)

    wij = fp_mul(wi, wj)
    wij_sqr = fp_sqr(wij)
    wi_sqr_wj = fp_mul(wij, wi)
    wi_wj_sqr = fp_mul(wij, wj)
    wi_sqr = fp_sqr(wi)
    wj_sqr = fp_sqr(wj)

    u0n_sqr = fp_sqr(u0n)
    u0d_sqr = fp_sqr(u0d)
    u1n_sqr = fp_sqr(u1n)
    u1d_sqr = fp_sqr(u1d)

    u0du1d = fp_mul(u0d, u1d)
    u0du1d_sqr = fp_sqr(u0du1d)
    u0d_sqr_u1d = fp_mul(u0du1d, u0d)
    u0d_u1d_sqr = fp_mul(u0du1d, u1d)

    u0nu1n = fp_mul(u0n, u1n)

    u0d_sqr_u1d_u1n = fp_mul(u0d_sqr_u1d, u1n)
    u0d_u1d_sqr_u0n = fp_mul(u0d_u1d_sqr, u0n)

    u0ndu1nd = fp_mul(u0du1d, u0nu1n)
    u0du1n_sqr = fp_mul(u0d_sqr, u1n_sqr)
    u0nu1d_sqr = fp_mul(u1d_sqr, u0n_sqr)

    resn = fp_add(
        fp_mul(
            u0du1d_sqr, wij_sqr), fp_mul(
            u0d_sqr_u1d_u1n, wi_sqr_wj))
    resn = fp_add(resn, fp_mul(u0d_u1d_sqr_u0n, wi_sqr))
    resn = fp_add(resn, fp_mul(u0d_sqr_u1d_u1n, wi_wj_sqr))
    resn = fp_add(resn, fp_mul(u0du1n_sqr, wij))
    resn = fp_add(resn, fp_mul(u0ndu1nd, wi))
    resn = fp_add(resn, fp_mul(u0d_u1d_sqr_u0n, wj_sqr))
    resn = fp_add(resn, fp_mul(u0ndu1nd, wj))
    resn = fp_add(resn, u0nu1d_sqr)

    if resn != 0:
        # This is the nice case, coprimality between L_ij and P
        resd = u0du1d_sqr
        return fp_mul(resn, fp_inv(resd))

    # Otherwise we have non-coprimality between L_ij and P
    # Note: we can chose the points carefully so that this doesn't occur in our case
    # There are two cases:
    #     1) P is of order 2, just add a random point on the Kummer and use W_P
    if DBL(P, K) == K[1]:
        T = random_kummer_point_fromros(K, ros)

        # get the index for the point P of order 2
        i2, j2 = identify(P, ros, K)

        M = get_mat([i2, j2])

        #then compute pairing values res1 = t_ij(T+P) and res2 = t_ij(T) so that t_ij(P) = res1/res2
        res1 = pairing(matrix_mult(M, T), K, ind)
        res2 = pairing(T, K, ros, ind)

        return fp_mul(res1, fp_inv(res2))

    # 2) P is not of order 2, just add a correct order two point S and use W_S
    else:
        i2 = randint(1, 4)
        j2 = randint(i2 + 1, 5)
        print(ind)
        while [i2, j2] == ind:
            i2 = randint(1, 4)
            j2 = randint(i2 + 1, 5)

        M = get_mat(K, ros, [i2, j2])
        print(M)
        print(matrix_mult(M, P))
        res1 = pairing(matrix_mult(M, P), K, ros, ind)

        # get the point L_i2j2 for the index i2, j2
        # for now, this does not seem to work for i2 = infty
        # this can easily be evaded using bilinearity
        Li2j2 = wp_to_sqkummer([i2, j2], ros)

        # print([i2,j2], DBL(Li2j2,K))
        assert DBL(Li2j2, K) == K[1]

        res2 = pairing(Li2j2, K, ros, ind)

        return fp_mul(res1, fp_inv(res2))

def profile(P, K, ros):
    """
        returns the values of the 2-Tate pairing for a Kummer point P
        for all elements of K[2], hence, the full profile.
        By multiplicity/bilinearity of the Tate pairing, it is enough
        to compute this for a generating subset of K[2]

        WARNING: this is costly for now, as it recomputes u0, u1 per 
        call to pairing, whereas we can simply compute it once and then
        compute the pairing values given that u0 and u1.
    """
    return [fp_legendre(pairing(P, K, ros, [i,j])) for i in range(6) for j in range(i + 1, 6)]


if __name__ == "__main__":

    # Testing get_v02

    ros = [79530844451, 73494698586, 202324325786]
    u0 = 261490242801
    u1 = 99714663135
    v02 = 224770923405

    K = [[359839655292, 260280618262, 57025794571],
         [253391591110, 6889027152, 1, 1],
         [6889027152, 253391591110, 183392295428, 183392295428],
         [403297045753, 147106535345, 237788911426, 237788911426]]

    P = [123737847053, 414730086170, 403322349118, 5992365730]

    u0p, u1p, v02p = get_v02(P, K, ros)

    assert fp_mul(u0p[0], fp_inv(u0p[1])) == u0
    assert fp_mul(u1p[0], fp_inv(u1p[1])) == u1
    assert fp_mul(v02p[0], fp_inv(v02p[1])) == v02

    # Test pairing
    trivial_profile = [1 for i in range(6) for _ in range(i + 1, 6)]
    bad1 = [-1, -1, -1, -1, 1, 1, 1, 1, -1, 1, 1, -1, 1, -1, -1]
    bad2 = [-1, 1, 1, -1, 1, -1, -1, 1, -1, 1, -1, 1, -1, 1, -1]
    bad3 = [1, -1, -1, 1, 1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1]

    P = [112932564266, 191368028511, 720568528, 121761157326]
    K = [
        [92032593726, 84262897272, 10238939227],
        [182108198173, 320096907610, 1, 1],
        [320096907610, 182108198173, 224633657922, 224633657922],
        [239033547884, 294988780344, 31537877117, 31537877117]]
    ros = [333283103033, 66147609746, 162494883452]

    p12 = 27832563933
    p34 = 75695504842
    p56 = 29944859306

    assert pairing(P, K, ros, [0, 1]) == p12
    assert pairing(P, K, ros, [2, 3]) == p34
    assert pairing(P, K, ros, [4, 5]) == p56

    bad_profiles = [ trivial_profile ]

    for i in range(100):
        P = random_kummer_point(K, ros)

        if P == [0,0,0,0]:
            assert False

        P_prof = profile(P, K, ros)
        if P_prof == trivial_profile:
            continue

        P = kummer_scalar(P, K, cofac)

        if eDBLs(P, K, f2 - 2) == K[1]:
            #we've got a bad profile here
            if P_prof not in bad_profiles:
                bad_profiles.append(P_prof)

    assert len(bad_profiles) == 4
    assert bad1 in bad_profiles
    assert bad2 in bad_profiles
    assert bad3 in bad_profiles

    for i in range(100):
        P = random_kummer_point(K, ros)
        assert profile(DBL(P, K), K, ros) == trivial_profile

        P2 = kummer_scalar(P, K, cofac)

        P_prof = profile(P, K, ros)

        if P_prof == trivial_profile:
            assert eDBLs(P2, K, f2 - 2) == K[1]
            continue
        elif P_prof in bad_profiles:
            continue

        #should be a point with order divisble by 2^f2-1
        P3 = eDBLs(P2, K, f2 - 2)
        assert P3 != K[1]
        assert DBL(P3, K) == K[1]


    print("Testing done.")
    # TODO: test non coprime case
