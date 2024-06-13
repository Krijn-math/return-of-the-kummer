from globals import *

if __name__ == "__main__":
    p = 417942208511
    set_prime(p)

from kummer_arithmetic import *


def get_mat(K, ros, ind):
    """
        computes the matrices that represent addition by L_ij in K[2]
        given by the addition matrices W_ij from the appendix
    """
    if ind == [0, 1]:
        return [[0, 1, 0, 0],
                [1, 0, 0, 0],
                [0, 0, 0, 1],
                [0, 0, 1, 0]]

    if ind == [2, 3]:
        return [[0, 0, 0, 1],
                [0, 0, 1, 0],
                [0, 1, 0, 0],
                [1, 0, 0, 0]]

    if ind == [4, 5]:
        return [[0, 0, 1, 0],
                [0, 0, 0, 1],
                [1, 0, 0, 0],
                [0, 1, 0, 0]]

    mu0 = K[1][0]
    mu1 = K[1][1]
    G = K[0][1]
    tau = fp_polyroot([1, -G, 1])
    taun = tau[0]
    taud = tau[1]

    u1 = -fp_add(1, ros[1])
    u0 = fp_mul(1, ros[1])
    P = curve_to_squaredkummer(K, ros, u0, u1, 0)

    if (taun**2) * P[2] != (mu0 * taun - taud) / (mu1 * taun - taud):
        taun, taud = taud, taun

    # improvement: remove the inversions and remove superflouous computations
    tau = fp_mul(taun, fp_inv(taud))
    tau_inv = fp_inv(tau)
    tau_sqr = fp_sqr(tau)
    tau_inv_sqr = fp_sqr(tau_inv)
    gamma_tau = fp_mul(fp_sub(tau, mu0), fp_inv(fp_sub(mu1, tau)))
    gamma_tauinv = fp_mul(fp_sub(tau_inv, mu0), fp_inv(fp_sub(mu1, tau_inv)))

    if ind == [0, 2]:
        gamma_tau_tau = fp_mul(tau, gamma_tau)
        return [[1, -gamma_tau, gamma_tau_tau, -tau],
                [gamma_tau, -1, tau, -gamma_tau_tau],
                [gamma_tau_tau, -tau, 1, -gamma_tau],
                [tau, -gamma_tau_tau, gamma_tau, -1]]

    if ind == [0, 3]:
        gamma_tau_tauinv = fp_mul(tau_inv, gamma_tau)
        return [[1, -gamma_tau, gamma_tau_tauinv, -tau_inv],
                [gamma_tau, -1, tau_inv, -gamma_tau_tauinv],
                [gamma_tau_tauinv, -tau_inv, 1, -gamma_tau],
                [tau_inv, -gamma_tau_tauinv, gamma_tau, -1]]

    if ind == [0, 4]:
        gamma_tauinv_tauinv = fp_mul(tau_inv, gamma_tauinv)
        return [[1, -gamma_tauinv, -tau_inv, gamma_tauinv_tauinv],
                [gamma_tauinv, -1, -gamma_tauinv_tauinv, tau_inv],
                [tau_inv, -gamma_tauinv_tauinv, -1, gamma_tauinv],
                [gamma_tauinv_tauinv, -tau_inv, -gamma_tauinv, 1]]

    if ind == [0, 5]:
        gamma_tauinv_tau = fp_mul(tau, gamma_tauinv)
        return [[1, -gamma_tauinv, -tau, gamma_tauinv_tau],
                [gamma_tauinv, -1, -gamma_tauinv_tau, tau],
                [tau, -gamma_tauinv_tau, -1, gamma_tauinv],
                [gamma_tauinv_tau, -tau, -gamma_tauinv, 1]]

    if ind == [1, 2]:
        gamma_tauinv_tau = fp_mul(tau, gamma_tauinv)
        return [[1, -gamma_tauinv, gamma_tauinv_tau, -tau],
                [gamma_tauinv, -1, tau, -gamma_tauinv_tau],
                [gamma_tauinv_tau, -tau, 1, -gamma_tauinv],
                [tau, -gamma_tauinv_tau, gamma_tauinv, -1]]

    if ind == [1, 3]:
        gamma_tauinv_tauinv = fp_mul(tau_inv, gamma_tauinv)
        return [[1, -gamma_tauinv, gamma_tauinv_tauinv, -tau_inv],
                [gamma_tauinv, -1, tau_inv, -gamma_tauinv_tauinv],
                [gamma_tauinv_tauinv, -tau_inv, 1, -gamma_tauinv],
                [tau_inv, -gamma_tauinv_tauinv, gamma_tauinv, -1]]

    if ind == [1, 4]:
        gamma_tau_tauinv = fp_mul(tau_inv, gamma_tau)
        return [[1, -gamma_tau, -tau_inv, gamma_tau_tauinv],
                [gamma_tau, -1, -gamma_tau_tauinv, tau_inv],
                [tau_inv, -gamma_tau_tauinv, -1, gamma_tau],
                [gamma_tau_tauinv, -tau_inv, -gamma_tau, 1]]

    if ind == [1, 5]:
        gamma_tau_tau = fp_mul(tau, gamma_tau)
        return [[1, -gamma_tau, -tau, gamma_tau_tau],
                [gamma_tau, -1, -gamma_tau_tau, tau],
                [tau, -gamma_tau_tau, -1, gamma_tau],
                [gamma_tau_tau, -tau, -gamma_tau, 1]]

    if ind == [2, 4]:
        return [[1, 1, -tau, -tau_inv],
                [1, 1, -tau_inv, -tau],
                [tau, tau_inv, -1, -1],
                [tau_inv, tau, -1, -1]]

    if ind == [2, 5]:
        tau_sqr = fp_sqr(tau)
        tau_inv_sqr = fp_sqr(tau_inv)
        return [[1, tau_inv_sqr, -tau_inv, -tau_inv],
                [tau_inv_sqr, 1, -tau_inv, -tau_inv],
                [tau_inv, tau_inv, -1, -tau_inv_sqr],
                [tau_inv, tau_inv, -tau_inv_sqr, -1]]

    if ind == [3, 4]:
        return [[1, tau_sqr, -tau, -tau],
                [tau_sqr, 1, -tau, -tau],
                [tau, tau, -1, -tau_sqr],
                [tau, tau, -tau_sqr, -1]]

    if ind == [3, 5]:
        return [[1, 1, -tau_inv, -tau],
                [1, 1, -tau, -tau_inv],
                [tau_inv, tau, -1, -1],
                [tau, tau_inv, -1, -1]]

    print(f"Some problem with indices {ind} in get_mat")
    return None


def matrix_mult(M, P):
    # Computes M*P
    """
        given an addition matrix W_ij from the function above, applies it to a Kummer point P in K
        and thus, returns a representation of P + L_ij
    """
    assert P != [0,0,0,0]

    MP = [0, 0, 0, 0]
    for j in range(3):
        tmp = 0
        for i in range(3):
            tmp = fp_add(tmp, fp_mul(M[j][i], P[i]))
        MP[j] = tmp

    return MP