from kummer_arithmetic import *

###################################################################################################
# File containing functions to compute the biquadratic forms on the "intermediate" Kummer surface
# Here we use the formulae in
#     "qDSA: Small and Secure Digital Signatures with Curve-based Diffie–Hellman Key Pairs"
#      by Joost Renes and Benjamin Smith
###################################################################################################


def intermediate_kummer_from_squared_kummer(K):
    """
    Given a squared Kummer surface K, returns the constants needed to do computations on the intermediate Kummer
    
    INPUT: K, the Kummer surface 
    OUTPUT: - mus = [mu1,mu2,mu3,mu4],
            - mudual = Hadamard(mus)
    """

    mu = K[1]
    inv2 = fp_inv(2)
    mudual = [fp_mul(inv2, m) for m in hadamard(mu)]
    # mudual = hadamard(mu)

    C1 = fp_sub(fp_mul(mudual[0], mudual[1]), fp_mul(mudual[2], mudual[3]))
    C1_inv = fp_inv(C1)
    C2 = fp_sub(fp_mul(mudual[0], mudual[2]), fp_mul(mudual[1], mudual[3]))
    C2_inv = fp_inv(C2)
    C3 = fp_sub(fp_mul(mudual[0], mudual[3]), fp_mul(mudual[1], mudual[2]))
    C3_inv = fp_inv(C3)

    M = coord_prod(mu)
    Mdual = coord_prod(mudual)
    C = fp_mul(fp_mul(M, Mdual), 8)
    C = fp_mul(C, C1_inv)
    C = fp_mul(C, C2_inv)
    C = fp_mul(C, C3_inv)

    return [mu, mudual, [C]]


def bii_value(Kint, i, P, Q):
    """
    Given an intermediate Kummer surface, 
        returns the (i,i)-th biquadratic evaluated at P and Q
    
    INPUT: - Kint, the intermediate Kummer surface
           - i, we will compute the (i,i)-th biquadratic value
           - P and Q, point on the intermediate Kummer surface
    OUTPUT: B_{i,i}, the (i,i)-th value of the biquadratics evaluted at P, Q
    
    """

    mu = Kint[0]
    mudual = Kint[1]

    mu01 = fp_mul(mu[0], mu[1])
    mu23 = fp_mul(mu[2], mu[3])
    eps1 = fp_mul(mu[1], mu23)
    eps2 = fp_mul(mu[0], mu23)
    eps3 = fp_mul(mu01, mu[3])
    eps4 = fp_mul(mu01, mu[2])
    eps = [eps1, eps2, eps3, eps4]

    kappa = hadamard(eps)

    epsdual = invert4_constants(mudual)
    Pe = four_way_mult(squaring(P), epsdual)
    Qe = four_way_mult(squaring(Q), epsdual)

    F1 = coord_add(four_way_mult(Pe, Qe))
    F2 = coord_add(four_way_mult(Pe, [Qe[1], Qe[0], Qe[3], Qe[2]]))
    F3 = coord_add(four_way_mult(Pe, [Qe[2], Qe[3], Qe[0], Qe[1]]))
    F4 = coord_add(four_way_mult(Pe, [Qe[3], Qe[2], Qe[1], Qe[0]]))

    if i == 0:
        k0 = fp_mul(kappa[0], F1)
        k1 = fp_mul(kappa[1], F2)
        k2 = fp_mul(kappa[2], F3)
        k3 = fp_mul(kappa[3], F4)
        k01 = fp_add(k0, k1)
        k23 = fp_add(k2, k3)
        k = fp_add(k01, k23)
        return fp_mul(mudual[0], k)
    elif i == 1:
        k0 = fp_mul(kappa[1], F1)
        k1 = fp_mul(kappa[0], F2)
        k2 = fp_mul(kappa[3], F3)
        k3 = fp_mul(kappa[2], F4)
        k01 = fp_add(k0, k1)
        k23 = fp_add(k2, k3)
        k = fp_add(k01, k23)
        return fp_mul(mudual[1], k)
    elif i == 2:
        k0 = fp_mul(kappa[2], F1)
        k1 = fp_mul(kappa[3], F2)
        k2 = fp_mul(kappa[0], F3)
        k3 = fp_mul(kappa[1], F4)
        k01 = fp_add(k0, k1)
        k23 = fp_add(k2, k3)
        k = fp_add(k01, k23)
        return fp_mul(mudual[2], k)
    elif i == 3:
        k0 = fp_mul(kappa[3], F1)
        k1 = fp_mul(kappa[2], F2)
        k2 = fp_mul(kappa[1], F3)
        k3 = fp_mul(kappa[0], F4)
        k01 = fp_add(k0, k1)
        k23 = fp_add(k2, k3)
        k = fp_add(k01, k23)
        return fp_mul(mudual[3], k)
    else:
        print(f"Input index incorrect")
        assert False


def bij_value(Kint, i, j, P, Q):
    """
    Given an intermediate Kummer surface, 
        returns the (i,j)-th biquadratic evaluated at points P,Q 
    
    INPUT: - Kint, the intermediate Kummer surface
           - i and j, indices where we will compute the (i,j)-th biquadratic value
           - P and Q, point on the intermediate Kummer surface
    OUTPUT: B_{i,j}, the (i,j)-th value of the biquadratics evaluted at P, Q
    
    """

    mudual = Kint[1]

    k, l = {0, 1, 2, 3} - {i, j}

    C1 = fp_mul(mudual[i], mudual[j])
    C2 = fp_sub(fp_mul(mudual[i], mudual[k]), fp_mul(mudual[j], mudual[l]))
    C3 = fp_sub(fp_mul(mudual[i], mudual[l]), fp_mul(mudual[j], mudual[k]))
    Cij = fp_mul(fp_mul(C1, C2), C3)

    Pij = fp_mul(P[i], P[j])
    Pkl = fp_mul(P[k], P[l])
    Qij = fp_mul(Q[i], Q[j])
    Qkl = fp_mul(Q[k], Q[l])

    C4 = fp_sub(fp_mul(mudual[i], mudual[j]), fp_mul(mudual[k], mudual[l]))
    Pijkl = fp_sub(Pij, Pkl)
    Qijkl = fp_sub(Qij, Qkl)

    Bij_pre = fp_mul(fp_mul(fp_mul(Pijkl, Qijkl), mudual[l]), mudual[k])
    Bij_pre = fp_add(Bij_pre, fp_mul(fp_mul(C4, Pkl), Qkl))

    return fp_mul(fp_mul(Kint[2][0], Cij), Bij_pre)


def biquadratic_matrix(Kint, P, Q):
    """
    Given an intermediate Kummer surface, 
        returns the biquadratics evaluated at points P,Q 
    
    INPUT: - Kint, the intermediate Kummer surface
           - P and Q, point on the intermediate Kummer surface
    OUTPUT: The matrix of biquadratics B_{i,j} for 1 <= i,j <= 4
    
    """
    B1 = 4 * [0]
    B2 = 4 * [0]
    B3 = 4 * [0]
    B4 = 4 * [0]
    BB = [B1, B2, B3, B4]

    for i in range(4):
        BB[i][i] = bii_value(Kint, i, P, Q)

    for i in range(3):
        for j in range(i + 1, 4):
            BB[i][j] = bij_value(Kint, i, j, P, Q)
            BB[j][i] = BB[i][j]

    return BB
