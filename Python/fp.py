# ##############################################################
# This file contains functions needed to perform Fp arithmetic
# ##############################################################


from globals import *


def fp_add(a, b):
    """
    Function to add two Fp elements a,b

    Input: integers a,b (mod p)
    Output: a+b (mod p)
    """
    counter[2] += 1
    return (a + b) % p


def fp_sub(a, b):
    """
    Function to subtract two Fp elements a,b

    Input: integers a,b (mod p)
    Output: a-b (mod p)
    """
    counter[2] += 1
    return (a - b) % p


def fp_mul(a, b):
    """
    Function to multiply two Fp elements a,b

    Input: integers a,b (mod p)
    Output: a*b (mod p)
    """

    if (a == b):
        counter[1] += 1
        return (a**2) % p

    counter[0] += 1
    return (a * b) % p


def fp_sqr(a):
    """
    Function to square an Fp element a

    Input: integers a (mod p)
    Output: a^2 (mod p)
    """
    counter[1] += 1
    return (a**2) % p


def fp_inv(a):
    """
    Function to find the inverse of an Fp element a

    Input: integers a (mod p)
    Output: a^(-1) (mod p) such that a*a^(-1) = 1 (mod p)
    """
    counter[4] += 1
    return pow(a, p - 2, p)

def fp_div(a, b):
    """
    Function to divide a by b for Fp elements a,b

    Input: integers a, b (mod p)
    Output: a*b^(-1) (mod p) such that b*b^(-1) = 1 (mod p)
    """
    
    return fp_mul(a, fp_inv(b))

def fp_neg(a):
    """
    Function to find the negative of an Fp element a

    Input: integers a (mod p)
    Output: -a (mod p)
    """

    return (-a) % p


def fp_squareroot(a):
    """
    Function to find the squareroot of an Fp element a

    Input: integers a (mod p)
    Output: square root b such that b^2 = a (mod p)
    """
    counter[5] += 1
    return pow(a, (p + 1) // 4, p)


def fp_expon(a, n):
    """
    Function to compute the exponenetiation of an Fp element a by an integer

    Input: integer a (mod p) and integer n
    Output: a^n (mod p)
    """

    nbits = [int(x) for x in bin(n)[2:]]
    x = a

    for i in range(1, len(nbits)):
        x = fp_sqr(x)
        if nbits[i] == 1:
            x = fp_mul(x, a)
    return x


def fp_issquare(a):
    """
    Function to check if an element a \\in Fp is a square

    Input: integers a (mod p)
    Output: Boolean
"""
    counter[3] += 1
    return pow(a, (p + 1) // 2, p) == a

def fp_legendre(a):
    """
    Function to check if an element a \\in Fp is a square
    Similar to fp_issquare, but returns -1,1 instead of bool

    Input: integers a (mod p)
    Output: 1, -1
"""
    res = fp_expon(a, (p - 1) // 2)
    if res == 1:
        return 1
    if res == (p-1):
        return -1

def fp_issquare_sqrt(a):
    """
    Function to check if an element a \\in Fp is a square,
            and if so output the squareroot


    Input: integers a (mod p)
    Output: Bool and (if true) square root b
                                    such that b^2 = a (mod p), otherwise 0
"""
    counter[5] += 1
    s = pow(a, (p + 1) // 4, p)
    if fp_sqr(s) == a:
        return True, s
    else:
        return False, 0


def fp_polyroot(f, all=False):
    """
    Given the coeffficients of a polynomial f(X) \\in Fp[X],
            outputs a root of this polynomial

    Input: coefficients [c0,c1,c2] of polynomial c0 + c1*X + c2*X^2
    Output: [n, d] where n*d^{-1} is a root of this polynomial

            COST: 1 Fp squareroot, 1M, 1S, 5a
"""
    c0 = f[0]
    c1 = f[1]
    c2 = f[2]

    c02 = fp_mul(c0, c2)
    c02 = fp_add(c02, c02)
    c02 = fp_add(c02, c02)

    s = fp_sub(fp_sqr(c1), c02)
    s = fp_squareroot(s)
    d = fp_add(c2, c2)
    # d = fp_inv(fp_add(c2, c2))
    n = fp_add((-c1), s)

    if all:
        n1 = fp_add((-c1), (-s))
        return [n, d], [n1, d]
    else:
        return [n, d]


def gcd_quadratics_old(f, g):
    """
    Given the coeffficients of quadratic polynomials f(X), g(X) \\in Fp[X],
            outputs the coefficients of the gcd of this polynomial

    Input: coefficients [c0,c1,c2] of polynomial f(X) = c0 + c1*X + c2*X^2
                       and coefficients [d0,d1,d2] of polynomial g(X) = d0 + d1*X + d2*X^2
    Output: the coefficients of the gcd of these polynomials

            Code adapted from inversion-free GCD in https://github.com/Microsoft/SuperSolver,
            Algorithm 1 in https://eprint.iacr.org/2021/1488.pdf
            (in particular, our implementation only works if f, g are quadratic polynomials)
"""

    if f == g:
        return f

    r, s = f, g
    lcr, lcs = r[2], s[2]

    r = [fp_mul(lcs, x) for x in r]
    s = [fp_mul(lcr, x) for x in s]

    while len(r) > 1 and r != s:
        diff = len(r) - len(s)
        for i in range(len(s)):
            r[i + diff] = fp_sub(r[i + diff], s[i])
        while r[len(r) - 1] == 0:
            r.pop(len(r) - 1)
        lcr = r[len(r) - 1]
        lcs = s[len(s) - 1]
        r = [fp_mul(lcs, x) for x in r]
        s = [fp_mul(lcr, x) for x in s]
        if len(r) < len(s):
            r, s = s, r
    if len(r) == 1:
        return [1]
    else:
        return [fp_mul(r[0], fp_inv(r[1])), 1]


def gcd_quadratics_monic(f, g):
    """
    Given the coeffficients of monic quadratic polynomials f(X), g(X) \\in k[X],
            outputs the coefficients of the gcd of this polynomial

    Input: coefficients [f0,f1,1] of polynomial f(X) = f0 + f1*X + X^2
                       and coefficients [g0,g1,1] of polynomial g(X) = g0 + g1*X + X^2
    Output: the coefficients of the gcd of these polynomials
                            (either 1, f or ax + b for some a,b \\in k)

            Code adapted from inversion-free GCD in https://github.com/Microsoft/SuperSolver,
            Algorithm 1 in https://eprint.iacr.org/2021/1488.pdf
            (in particular, our implementation only works if f, g are quadratic polynomials)

            It costs 4M, 6a
"""

    # Check monic
    assert f[2] == 1
    assert g[2] == 1

    if f == g:
        return f

    f0 = f[0]
    f1 = f[1]

    g0 = g[0]
    g1 = g[1]

    r0 = fp_mul(fp_sub(f1, g1), g0)
    r1 = fp_mul(fp_sub(f1, g1), g1)
    r1 = fp_sub(r1, fp_sub(f0, g0))
    s0 = fp_sub(f0, g0)
    s1 = fp_sub(f1, g1)

    r = fp_mul(r0, s1)
    s = fp_mul(s0, r1)

    if s == r:
        return [r0, r1]
    # [fp_mul(r0, fp_inv(r1)), 1]
    else:
        return [1]


def gcd_quadratics(f, g):
    """
    Given the coeffficients of monic quadratic polynomials f(X), g(X) \\in k[X],
            outputs the coefficients of the gcd of this polynomial

    Input: coefficients [f0,f1,f2] of polynomial f(X) = f0 + f1*X + f2*X^2
                       and coefficients [g0,g1,g2] of polynomial g(X) = g0 + g1*X + g2*X^2
    Output: the coefficients of the gcd of these polynomials
                            (either 1, f or ax + b for some a,b \\in k)

            Code adapted from inversion-free GCD in https://github.com/Microsoft/SuperSolver,
            Algorithm 1 in https://eprint.iacr.org/2021/1488.pdf
            (in particular, our implementation only works if f, g are quadratic polynomials)

            It costs 11M, 3a
"""

    if f == g:
        return f

    f0 = f[0]
    f1 = f[1]
    f2 = f[2]

    g0 = g[0]
    g1 = g[1]
    g2 = g[2]

    g2f1 = fp_mul(g2, f1)
    f2g1 = fp_mul(f2, g1)
    f2g2 = fp_mul(f2, g2)
    g2f0 = fp_mul(g2, f0)
    f2g0 = fp_mul(f2, g0)

    g2f0sf2g0 = fp_sub(g2f0, f2g0)
    g2f1sf2g1 = fp_sub(g2f1, f2g1)

    s0 = fp_mul(f2g2, g2f0sf2g0)
    s1 = fp_mul(f2g2, g2f1sf2g1)

    r0 = fp_mul(f2g0, g2f1sf2g1)
    r1 = fp_mul(f2g1, g2f1sf2g1)
    r1 = fp_sub(r1, s0)

    r = fp_mul(r0, s1)
    s = fp_mul(s0, r1)

    if s == r:
        return [r0, r1]
        # return [fp_mul(r0, fp_inv(r1)), 1]
    else:
        return [1]


def seq_to_element(L):
    """
    Given a sequence L = [n, d], outputs the element
            in Fp corresponding to n*d^{-1}


    Input: sequence L of length 2
    Output: L[0] * L[1]^{-1} in Fp
"""
    return fp_mul(L[0], fp_inv(L[1]))


if __name__ == "__main__":

    # Testing the function gcd_quadratics:
    p = 101
    set_prime(p)
    f = [8, 5, 81]
    g = [40, 24, 12]
    h = gcd_quadratics_old(f, g)
    # hnew = gcd_quadratics_monic(f,g)
    hnew = gcd_quadratics(f, g)
    assert h == hnew

    f = [11, 15, 1]
    g = [96, 34, 1]
    h = gcd_quadratics_old(f, g)
    # hnew = gcd_quadratics_monic(f, g)
    hnew = gcd_quadratics(f, g)
    assert h == [fp_mul(hnew[0], fp_inv(hnew[1])), 1]
