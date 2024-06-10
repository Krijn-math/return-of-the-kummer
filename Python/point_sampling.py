#############################################################################################
# File containing functions to sample points deterministically 
#  as described in Section 4.4 of the accompanying paper
#############################################################################################


from globals import *

# Setting prime for testing
if __name__ == "__main__":
    p = 22728720641309136015759539049556903787604752849407962277276342173428260798463
    set_prime(p)

from pairing import *

def first_basis_point(K, ros, Xs, extra):
    """
    Find a point with profile <1, -1, -1, -1> or <1, -1, 1, -1>
    as described in Section 4.4 of the paper. 

    INPUTS: - K, the Kummer surface
            - ros, the Rosenhain invariants corresponding to K
            - Xs, precomputed list of x's such that the profile will be <1, -1, ...> (as described in Section 4.4)
            - extra, if True we also output the u1,u0,v1,v0 of output point
   
    OUTPUTS: - P, point P on Kummer surface with correct profile 
             - u1,u0,v1,v0 giving the divisor on the Jacobian corresponding to P if extra = True
    """

    for x in Xs:
        x1 = fp_sub(x, 1)
        x2 = fp_sub(x, ros[0])
        x3 = fp_sub(x, ros[1])
        x4 = fp_sub(x, ros[2])
        rhs = fp_mul(fp_mul(fp_mul(fp_mul(x, x1), x2), x3), x4)
        square = fp_issquare(rhs)
        if square:
            # right_profile = [fp_issquare(x3), fp_issquare(x4)] in [[False, False], [True, False]]
            # so can simply compute
            if fp_issquare(x4):
                continue
            break


    w4 = ros[0]
    u0 = fp_mul(x, w4)
    u1 = fp_add(-x, -w4)
    v0 = fp_mul(w4, fp_inv(fp_sub(x, w4)))
    v02 = fp_mul(fp_sqr(v0), rhs)

    P = curve_to_squaredkummer(K, ros, u0, u1, v02)
    P = kummer_scalar(P, K, cofac)

    ## For testing
    # assert normalise(eDBLs(P, K, f2 - 1)) == normalise(K[1])

    if extra:
        y = fp_squareroot(rhs)
        v0 = fp_mul(v0, -y)
        v1 = fp_mul(y, fp_inv(fp_sub(x, w4)))
        return P, [u1, u0, v1, v0]
    else:
        return P, []


def second_basis_point(K, ros, Xs, extra):
    """
    Find a point with profile <1, 1, -1, 1>
    as described in Section 4.4 of the paper. 

    INPUTS: - K, the Kummer surface
            - ros, the Rosenhain invariants corresponding to K
            - Xs, precomputed list of x's such that the profile will be <1, 1, ...> (as described in Section 4.4)
            - extra, if True we also output the u1,u0,v1,v0 of output point

    OUTPUTS: - P, point P on Kummer surface with correct profile 
                - u1,u0,v1,v0 giving the divisor on the Jacobian corresponding to P if extra = True
    """

    for x in Xs:
        x1 = fp_sub(x, 1)
        x2 = fp_sub(x, ros[0])
        x3 = fp_sub(x, ros[1])
        x4 = fp_sub(x, ros[2])
        rhs = fp_mul(fp_mul(fp_mul(fp_mul(x, x1), x2), x3), x4)
        square = fp_issquare(rhs)
        if square:
            r1 = fp_issquare(x3)
            if r1:
                continue
            r2 = fp_issquare(x4)
            right_profile = (
                [r1, r2] == [False, True])
            if right_profile:
                break

    w4 = ros[0]
    u0 = fp_mul(x, w4)
    u1 = fp_add(-x, -w4)
    v0 = fp_mul(w4, fp_inv(fp_sub(x, w4)))
    v02 = fp_mul(fp_sqr(v0), rhs)

    P = curve_to_squaredkummer(K, ros, u0, u1, v02)
    P = kummer_scalar(P, K, cofac)

    ## For testing
    # assert kummer_scalar(P, K, fp_expon(2, f2 - 1)) == normalise(K[1])

    if extra:
        y = fp_squareroot(rhs)
        v0 = fp_mul(v0, -y)
        v1 = fp_mul(y, fp_inv(fp_sub(x, w4)))
        return P, [u1, u0, v1, v0]
    else:
        return P, []


def precompute_sample_basis():
    """
    Does the precomputation needed for sampling basis points 

    Outputs two lists:
        - X1, list containing x's such that x is a square and x-1 is not a square
        - X2, list containing x's such that x and x-1 are squares
    """
    X1 = [
        x for x in range(
            1, 101) if (
            fp_issquare(x) and not fp_issquare(
                fp_sub(
                    x, 1)))]
    X2 = [
        x for x in range(
            1, 101) if (
            fp_issquare(x) and fp_issquare(
                fp_sub(
                    x, 1)))]
    return X1, X2


def sample_basis(K, ros, precomp, extra=False):
    """
        This function deterministically samples basis points 
        (as described in Section 4.4 of the accompanying paper)

        INPUTS: - K, the Kummer surface
                - ros, the Rosenhain invariants corresponding to K
                - precomp, inputs the precomputated lists from precompute_sample_basis()
                - (optional) extra, if True then we output the u0,u1,v0,v1 of output points
        OUTPUTS: - P and Q, basis points
                 - (optinal) extra information u0,u1,v0,v1 for each point which gives the 
                                corresp. divisor on the Jacobian
    """

    P, P_extra = first_basis_point(K, ros, precomp[0], extra)
    Q, Q_extra = second_basis_point(K, ros, precomp[1], extra)

    if extra:
        return P, Q, [P_extra, Q_extra]
    else:
        return P, Q, []


if __name__ == "__main__":
   
    # TESTING

    K = [[ 7041655638023515919331565511106590238281554242154854679521336330094732662417, 12816125466215355429819005255456343062448394168615155549975510168462395782418, 10379747910487700547310200853440207469037982619799287441782080322471200226029 ],
         [ 11545483542424421150640952177693754494636102173944694171474021422782547534639, 1270641923790934279178053077762588567812291994670461378501488745679848247779, 1, 1 ],
         [ 1270641923790934279178053077762588567812291994670461378501488745679848247779, 11545483542424421150640952177693754494636102173944694171474021422782547534639, 20568787689459598749563077350268922835940131260152556215550770082488270660843, 20568787689459598749563077350268922835940131260152556215550770082488270660843 ],
         [ 4027456327498610444657346627530900377675854917522213208697994402301628038238, 6976603889711167591803526936736981506185742070312376779104104038356168950458, 9068718871929702988449091100490710487815646546178784459981354135267520514621, 9068718871929702988449091100490710487815646546178784459981354135267520514621 ]
    ]

    ros = [ 12665351602429089147996171423360066756586131526082101555621533352108778703142, 18673377501228578563036560204009423478228752017737790685190703320447812977203, 1474395203343827452734710927004116429148167713720745685583479602896185255562 ]

    X1, X2 = precompute_sample_basis()
    P, Q, [] = sample_basis(K, ros, [X1, X2])

    assert(on_kummer(P, K))
    assert(on_kummer(Q, K))

    P2 = eDBLs(P, K, f2-2)
    Q2 = eDBLs(Q, K, f2-2)
    assert(P2 != K[1])
    assert(Q2 != K[1])
    assert(P2 != Q2)

    assert DBL(P2, K) == K[1]
    assert DBL(Q2, K) == K[1]

    print("Testing done")