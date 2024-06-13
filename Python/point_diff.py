#############################################################################################
# File containing functions to find the difference of two points
# Here we heavily rely on Proposition 4 of 
#     "qDSA: Small and Secure Digital Signatures with Curve-based Diffie–Hellman Key Pairs"
#      by Joost Renes and Benjamin Smith
#############################################################################################

from globals import *

# For testing
if __name__ == "__main__":
    p = 431
    set_prime(p)

from biquadratics import *

def point_difference(P, Q, K):
    """
    Given points P, Q on squared Kummer surface K,
    computes the difference P-Q or sum P+Q on K using Proposition 4 in qDSA
    
    INPUTS: - P and Q, points on the squared Kummer surface K
            - K, the squared Kummer surface

    OUTPUTS: - P pm Q, the point difference or sum
    
    COST: Excluding the cost of Hadamard, the biquadratics and the root-finding,
    we find a total cost of 30 M + 1S  + 11a, given a cost of 11M + 3a for the gcd
    """

    ## For debugging
    # assert on_kummer(P, K)
    # assert on_kummer(Q, K)

    # We go via the intermediate Kummer surface
    # where we have nice(-ish) biquadratics

    Kint = intermediate_kummer_from_squared_kummer(K)

    # Moving P and Q to the intermediate Kummer surface
    Pint = hadamard(P)
    Qint = hadamard(Q)

    # Find the coordinates of the point difference Dint = Pint - Qint
    # Let Dint = [X0 : X1 : X2 : X3]
    BB = biquadratic_matrix(Kint, Pint, Qint)

    # We store quadratic polynomials as coefficients [c0, c1, c2]
    # for polynomial f(X) = c0 + c1*X + c2*X^2

    # Set X0 = 1
    f01 = [BB[1][1], fp_add(-BB[0][1], -BB[0][1]), BB[0][0]]
    # Find a root of the first polynomial and set X1 to be this root
    r = fp_polyroot(f01)  # Outputs [n,d] where X1 = n*d^(-1)
    h11 = r[1]
    r1 = r[0]  # This is d*X1

    r1_sq = fp_sqr(r1)
    h11_sq = fp_sqr(h11)
    r1h11 = fp_mul(r1, h11)

    ## For testing
    # assert (
    #     fp_add(
    #         fp_add(
    #             fp_mul(
    #                 f01[0], h11_sq), fp_mul(
    #                 f01[1], r1h11)), fp_mul(
    #                     f01[2], r1_sq)) == 0)

    # Evaluate the other polynomials with respect to X0 = 1, X1 = r1
    # Find the other coordinates by finding common roots by taking gcds

    f02 = [BB[2][2], fp_add(-BB[0][2], -BB[0][2]), BB[0][0]]
    f12 = [fp_mul(BB[2][2], r1_sq), fp_mul(
        r1h11, fp_add(-BB[1][2], -BB[1][2])), fp_mul(h11_sq, BB[1][1])]
    h2 = gcd_quadratics(f02, f12)  # of form h21*x + h20
    h20 = h2[0]
    h21 = h2[1]
    r2 = -h20  # This is h21*X2

    f03 = [BB[3][3], fp_add(-BB[0][3], -BB[0][3]), BB[0][0]]
    f13 = [fp_mul(BB[3][3], r1_sq), fp_mul(
        r1h11, fp_add(-BB[1][3], -BB[1][3])), fp_mul(h11_sq, BB[1][1])]
    h3 = gcd_quadratics(f03, f13)  # of form h31*x + h30
    h30 = h3[0]
    h31 = h3[1]
    r3 = -h30  # This is h31*X3

    # Point difference of intermediate Kummer surface
    h23 = fp_mul(h21, h31)
    h13 = fp_mul(h11, h31)
    h12 = fp_mul(h11, h21)
    Dint = [
        fp_mul(
            h11, h23), fp_mul(
            h23, r1), fp_mul(
                h13, r2), fp_mul(
                    h12, r3)]  # = [1, r1/h11, r2/h21, r3/h31]

    # Move this point to the squared Kummer surface
    D = hadamard(Dint)

    ## For testing
    # assert on_kummer(D, K)

    return D


def point_difference_both(P, Q, K):
    """
    Given points P, Q on squared Kummer surface K,
    computes the difference P-Q and sum P+Q on K using Proposition 4 in qDSA
    
    INPUTS: - P and Q, points on the squared Kummer surface K
            - K, the squared Kummer surface

    OUTPUTS: - P - Q, the point difference
             - P + Q, the point sum
    
    """
     
    # We go via the intermediate Kummer surface
    # where we have nice(-ish) biquadratics

    Kint = intermediate_kummer_from_squared_kummer(K)

    # Moving P and Q to the intermediate Kummer surface
    Pint = hadamard(P)
    Qint = hadamard(Q)

    #############################
    ######    GET ROOTS     #####
    #############################

    # Find the coordinates of the point difference Dint = Pint - Qint
    # Let Dint = [X0 : X1 : X2 : X3]
    BB = biquadratic_matrix(Kint, Pint, Qint)

    # We store quadratic polynomials as coefficients [c0, c1, c2]
    # for polynomial f(X) = c0 + c1*X + x2*X^2

    # Set X0 = 1
    f01 = [BB[1][1], fp_add(-BB[0][1], -BB[0][1]), BB[0][0]]
    # Find a root of the first polynomial and set X1 to be this root
    rts = fp_polyroot(f01, all=True)  # Outputs [n,d] where X1 = n*d^(-1)

    diffs = []

    for r in rts:
        h11 = r[1]
        r1 = r[0]  # This is d*X1

        r1_sq = fp_sqr(r1)
        h11_sq = fp_sqr(h11)
        r1h11 = fp_mul(r1, h11)
        ## For testing:
        # assert (
        #     fp_add(
        #         fp_add(
        #             fp_mul(
        #                 f01[0], h11_sq), fp_mul(
        #                 f01[1], r1h11)), fp_mul(
        #             f01[2], r1_sq)) == 0)

        # Evaluate the other polynomials with respect to X0 = 1, X1 = r1
        # Find the other coordinates by finding common roots by taking gcds

        f02 = [BB[2][2], fp_add(-BB[0][2], -BB[0][2]), BB[0][0]]
        f12 = [fp_mul(BB[2][2], r1_sq), fp_mul(
            r1h11, fp_add(-BB[1][2], -BB[1][2])), fp_mul(h11_sq, BB[1][1])]
        h2 = gcd_quadratics(f02, f12)  # of form h21*x + h20
        h20 = h2[0]
        h21 = h2[1]
    
        r2 = -h20  # This is h21*X2

        f03 = [BB[3][3], fp_add(-BB[0][3], -BB[0][3]), BB[0][0]]
        f13 = [fp_mul(BB[3][3], r1_sq), fp_mul(
            r1h11, fp_add(-BB[1][3], -BB[1][3])), fp_mul(h11_sq, BB[1][1])]
        h3 = gcd_quadratics(f03, f13)  # of form h31*x + h30
        h30 = h3[0]
        h31 = h3[1]
        r3 = -h30  # This is h31*X3

        # Point difference of intermediate Kummer surface
        h23 = fp_mul(h21, h31)
        h13 = fp_mul(h11, h31)
        h12 = fp_mul(h11, h21)
        Dint = [
            fp_mul(
                h11, h23), fp_mul(
                h23, r1), fp_mul(
                h13, r2), fp_mul(
                    h12, r3)]  # = [1, r1/h11, r2/h21, r3/h31]

        # Move this point to the squared Kummer surface
        D = hadamard(Dint)
        
        ## For testing
        # assert on_kummer(D, K)

        diffs.append(D)

    D = diffs[0]
    S = diffs[1]

    return D, S


if __name__ == "__main__":

    # Testing Point Difference
    K = [[405, 105, 417],
         [111, 425, 1, 1],
         [425, 111, 196, 196],
         [166, 185, 336, 336]]

    P = [203, 72, 362, 320]
    Q = [206, 313, 336, 172]
    S = [163, 391, 286, 6]
    D = [50, 255, 143, 305]

    X1, X2 = point_difference_both(P, Q, K)
    assert ([normalise(X1), normalise(X2)] == [normalise(D), normalise(S)]) or (
        [normalise(X2), normalise(X1)] == [normalise(D), normalise(S)])

    # Testing Point Difference with three_point_ladder in kummer_arithmetic.py

    P = [416, 153, 267, 313]
    Q = [308, 267, 28, 293]
    m = 9
    K = [
        [392, 418, 376],
        [134, 284, 1, 1],
        [284, 134, 128, 128],
        [404, 325, 248, 248]
    ]

    D = point_difference(P, Q, K)

    Rp = three_point_ladder(P, Q, D, m, K)

    R = [293, 233, 5, 1]
    R2 = [156, 31, 157, 1]
    assert ((normalise(Rp) == normalise(R))
            or (normalise(Rp) == normalise(R2)))

    print("Testing complete.")
