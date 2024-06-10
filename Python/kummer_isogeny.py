# #############################################################################
#     Functions for computing elliptic (2,2)-isogenies between Kummer surfaces
#     Some of this code is due to Costello in software attached to the paper
#           'Computing supersingular isogenies on Kummer surfaces'
#     URL: https://www.microsoft.com/en-us/download/details.aspx?id=57309
# #############################################################################


from globals import *
from fp import *
from kummer_arithmetic import *
from copy import deepcopy

# #########################################################
# Functions to compute the (2,2)-isogeny
# #########################################################


def _get_scals(P2,HP2,HP4):
    """
    Get scalars needed to compute the (2,2)-isogenies

    INPUT:  - Point P2 of order 2 describing the ellpitic (2,2)-isogeny
            - Hadamard of P2, 
            - Hadamard of point P4 of order 4 such that P2 = [2]P4
    OUTPUT: Scaling map pis = [pi1, pi2, pi3, pi4] used in the isogeny computation
    """

    if P2[2] != 0:
        pi1 = fp_mul(HP2[1], HP4[2])
        pi2 = fp_mul(HP4[2], HP2[0])
        pi3 = fp_mul(HP2[1], HP4[0])
        pi4 = pi3
    else:
        pi1 = fp_mul(HP2[1], HP4[3])
        pi2 = fp_mul(HP4[3], HP2[0])
        pi3 = fp_mul(HP2[1], HP4[0])
        pi4 = pi3

    return [pi1, pi2, pi3, pi4]

def isogenous_squared_thetas_from_torsion_kernel(P2, P4):
    """
    Given a special point of order 2 and a point of order 4 lying above it, this function computes the squared theta constants of the image Kummer surface corresponding to the kernel specified by the torsion points (see the paper), as well as constants used to compute the image of any point under the associated isogeny.

        INPUTS: - P2: a Kummer point of order 2 in one of the two (2,2)-subgroups of interest
                        - P4: a Kummer point of order 4 such that P2=[2]P4 on K
        OUTPUT: - mus: a 4-tuple of the squared theta coordinates of the image Kummer
                        - pis: some constants used in the isogeny evaluation (next) function, i.e., in the special scaling C. See the paper.
    """

    HP2 = hadamard(P2)
    HP4 = hadamard(P4)

    pis = _get_scals(P2,HP2,HP4)
    mus = four_way_mult(HP2, pis)
    mus = hadamard(mus)
    mus = squaring(mus)

    return mus, pis


def isogeny_kummer_point(Q, pis):
    """
    Evaluating the (2,2) isogeny from the above function on a general point on the domain Kummer.

        INPUTS: - Q: any non-kernel point on a given Kummer K
        OUTPUT: - varphi(Q): the image of varphi on Qs
    """

    Q = hadamard(Q)
    Q = four_way_mult(Q, pis)
    Q = hadamard(Q)
    Q = squaring(Q)

    return Q


def naive_kummer_isogeny(P, K, eval, e):
    """
    Computes an (2^e, 2^e)-isogeny with domain K described by a point P of order 2^e, and optinally evaluating points at this isogeny. 
    In this function we do not use any strategies

    INPUT: - P, points of order 2^e describing the isogeny
           - K, domain Kummer surface
           - eval, the points that we want to evaluate
           - e, the length of the chain of (2,2)-isogenies

    OUTPUT: - K, the image Kummer surface
            - eval, the evaluated points

    """
    for l in range(e, 1, -1):

        P4 = eDBLs(P, K, l - 2)
        P2 = DBL(P4, K)

        mus, pis = isogenous_squared_thetas_from_torsion_kernel(P2, P4)
        P = isogeny_kummer_point(P, pis)
        K = squared_kummer_from_squared_thetas(mus)
        assert on_kummer(P, K)

        for i in range(len(eval)):
            eval[i] = isogeny_kummer_point(eval[i], pis)
            assert on_kummer(eval[i], K)

    return K, eval

# ###########################################################################
# Functions to recover the Rosenhain invariants of the image Kummer surface
# ###########################################################################

def kummer_to_rosenhain(K,  bit, twotors = []):
    """
    Computes the Rosenhain invariants corresponding to a Kummer surface.
    When two torsion information is known and a bit of information is given (to determine 
    which subgroup we are working with, i.e., to distinguish between tau or 1/tau), no square roots 
    are needed. Otherwise, we require a squareroot to compute the Rosenhains.

    INPUTS: - K, the Kummer surface
            - (optionally) twotors, give a 2-torsion point to compute the Rosenhain invariants
            - (optionally) bit, gives a bit of information to distinguish which subgroup we are working with (i.e., tau or 1/tau)
    OUTPUTS: Rosenhain invariants of K 
    
    """
    # for now written here, should be move somewhere else
    
    if twotors:
        P2 = twotors[0]
        if not bit:
            tau = fp_div(P2[2], P2[0]) 
        else:
            tau = fp_div(P2[0], P2[2]) 

        mus = K[1]
        lam = fp_div(mus[0], mus[1])
        taumu2 = fp_mul(tau,mus[1])
        mu = fp_div(fp_sub(taumu2, mus[3]), fp_sub(fp_mul(taumu2,lam),mus[3]))
        nu = fp_mul(lam,mu)

        return [lam, mu, nu]
    
    else:
        # If we don't have twotors information we have to compute squareroots 
        assert K[1][2] == 1
        assert K[1][3] == 1
        ABCD = hadamard(K[1])

        assert fp_sub(ABCD[0], 4) == ABCD[1]
        assert ABCD[2] == ABCD[3]

        tmp = fp_div(fp_sqr(ABCD[2]), fp_mul(ABCD[0], ABCD[1]))
        tmp = fp_squareroot(tmp)

        lam = fp_div(K[1][0], K[1][1])
        mu = fp_div(fp_add(tmp, 1), fp_sub(1, tmp))
       
        if bit:
            mu2 = fp_inv(mu)    
            nu = fp_mul(lam, mu)
            nu2 = fp_mul(lam, mu2)
            return [lam, mu2, nu2]
        else: 
            return [lam, mu, nu]



def optimal_kummer_isogeny(P, K, eval, e, strategy):
    """
    Computes an (2^e, 2^e)-isogeny with domain K described by a point P of order 2^e, and optinally evaluating points at this isogeny. 
    In this function we use optimal strategies

    INPUT: - P, point describing the isogeny
           - K, domain Kummer surface
           - eval, the points that we want to evaluate
           - e, the length of the chain of (2,2)-isogenies
           - strategy, the optimal strategy that we take to compute the chain of isogenies

    OUTPUT: - K, the image Kummer surface
            - eval, the evaluated points

    """

    MAX = e-1
    pts = [0] * 50
    pts_index = [0] * 50
    npts = 0
    ii = 0

    # go through tree according to strategy
    index = 0
    for row in range(1, MAX):
        while index < (MAX - row):
            pts[npts] = deepcopy(P)
            pts_index[npts] = index
            npts += 1
            m = strategy[ii]
            ii += 1

            P = eDBLs(P, K, m)
            index += m

        P4 = deepcopy(P)
        P2 = DBL(P4, K)

        mus, pis = isogenous_squared_thetas_from_torsion_kernel(P2, P4)
        
        K2 = mus
        K3, K4 = kummer_constants_from_squared_thetas(mus)

        K = [[], K2, K3, K4]        #we dont need K[0] and its just extra computations
        
        for i in range(npts):
            pts[i] = isogeny_kummer_point(pts[i], pis)
        for i in range(len(eval)):
            eval[i] = isogeny_kummer_point(eval[i], pis)

        P = deepcopy(pts[npts - 1])
        index = pts_index[npts - 1]
        npts -= 1

    P4 = deepcopy(P)
    P2 = DBL(P4, K)

    mus, pis = isogenous_squared_thetas_from_torsion_kernel(P2, P4)
    K = squared_kummer_from_squared_thetas(mus)

    for i in range(len(eval)):
        eval[i] = isogeny_kummer_point(eval[i], pis)

    eval.append(isogeny_kummer_point(P4, pis))      # We need this to recover Rosenhains on the codomain

    return K, eval

