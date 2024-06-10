# #######################################################################
#   Useful functions involving hyperelliptic curves and their Jacobians
# #######################################################################

from globals import *
from fp import *

def get_y(x, ros):
    """
    Finds the y coordinate of a point assuming we are given a valid x-coordinate
    
    INPUTS: - x, a valid x-coordinate lying on the Rosenhain curve
            - ros, the Rosenhain invariants of a curve

    OUTPUT: y, the corresponding y coordinate (here we make a choice of squareroot)
    """
    # we assume that x is on the curve so that y2 is square

    x2 = fp_sub(x, 1)
    x3 = fp_sub(x, ros[0])
    x4 = fp_sub(x, ros[1])
    x5 = fp_sub(x, ros[2])

    y2 = fp_mul(x, x2)
    y2 = fp_mul(y2, x3)
    y2 = fp_mul(y2, x4)
    y2 = fp_mul(y2, x5)

    ## For debugging
    # assert fp_issquare(y2)

    return fp_squareroot(y2)

def curve_to_squaredkummer(K, ros, u0, u1, v02):
    """
    
    
    """
    w4 = ros[0]
    w5 = ros[1]
    w6 = ros[2]

    mu0 = K[1][0]
    mu1 = K[1][1]
    # mu2 = K[1][2] # = 1 in our case
    # mu3 = K[1][3] # = 1 in our case

    w46 = fp_mul(w4, w6)
    w45 = fp_mul(w4, w5)

    X0 = fp_mul(u0, fp_sub(w5, u0))
    X0 = fp_mul(X0, fp_add(fp_add(w4, w6), u1))
    X0 = fp_sub(X0, v02)
    X0 = fp_mul(X0, mu0)

    X1 = fp_mul(u0, fp_sub(w46, u0))
    X1 = fp_mul(X1, fp_add(fp_add(1, w5), u1))
    X1 = fp_sub(X1, v02)
    X1 = fp_mul(X1, mu1)

    X2 = fp_mul(u0, fp_sub(w6, u0))
    X2 = fp_mul(X2, fp_add(fp_add(w4, w5), u1))
    X2 = fp_sub(X2, v02)

    X3 = fp_mul(u0, fp_sub(w45, u0))
    X3 = fp_mul(X3, fp_add(fp_add(1, w6), u1))
    X3 = fp_sub(X3, v02)

    P = [X0, X1, X2, X3]

    ## For debugging
    #assert on_kummer(P, K)

    return P


def random_curve_point(ros):
    """
    Computes a random point on a Rosenhein curves defined by ros

        INPUTS: - ros: Rosenhein invariants of the curve
        OUTPUT: - a random point P = (x,y) on curve C
                defined by ros
    """

    square = False

    while not square:
        x = randint(0, p - 1)
        x2 = fp_sub(x, 1)
        x3 = fp_sub(x, ros[0])
        x4 = fp_sub(x, ros[1])
        x5 = fp_sub(x, ros[2])

        y2 = fp_mul(x, x2)
        y2 = fp_mul(y2, x3)
        y2 = fp_mul(y2, x4)
        y2 = fp_mul(y2, x5)

        square, y = fp_issquare_sqrt(y2)

    return x, y


def curve_to_jac_point(x1, y1, x2, y2):
    """
    Computes Mumford representation of divisor corresponding
        to points (x1, y1), (x2,y2) on Curve

        INPUTS: - points (x1, y1), (x2,y2) on Curve
        OUTPUT: - u0, u1, v0, v1 which give
            Mumford representation (x^2 + u1*x + u0, v1*x + v0)
            of corresponding divisor
    """

    u1 = -fp_add(x1, x2)
    u0 = fp_mul(x1, x2)

    top = fp_sub(fp_mul(y1, x2), fp_mul(y2, x1))
    bot = fp_sub(x2, x1)
    v0 = fp_mul(top, fp_inv(bot))
    v1 = fp_mul(fp_sub(y1, y2), fp_inv(fp_sub(x1, x2)))

    return u1, u0, v1, v0