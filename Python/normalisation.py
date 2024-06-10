############################################################################
# This file contains functions for normalisation of Kummer surfaces
############################################################################

from globals import *
import itertools

# Setting the prime for testing
if __name__ == "__main__":
    p = 417942208511
    set_prime(p)

from kummer_arithmetic import *

def to_degree_six(ros):
    """
    Map a Rosenhain curve via x --> 1/(x+1)
    to move Weierstrass point at infinity

    INPUT: - ros, the Rosenhaim invariants defining the curve
    OUPUT: - new_roots, new roots of degree 6 curve
    """

    new_roots = [
        0, #infty
        1, #0
        fp_inv(2), #1
        fp_inv(fp_add(ros[0], 1)), #lambda
        fp_inv(fp_add(ros[1], 1)), #mu
        fp_inv(fp_add(ros[2], 1)) #lambda*mu
    ]

    return new_roots

# ###################
# Helper functions
# ###################

def _temp_eval(a, b, c, d, val):
    """
    Evaluate a Möbius map at a input value

    INPUT: - (a,b,c,d), constants defining the Möbius map
           - val, value to evaluate the map at
    OUPUT: y, the map evaluated at val
    """

    top = fp_add(fp_mul(a, val), b)
    bot = fp_add(fp_mul(c, val), d)
    y = fp_div(top, bot)

    return y

# ###############################
# Maps to Rosenhain invariants
# ###############################

def rosenhain_from_six_roots(roots):
    """
    Computes the new Rosenhains after permuting the roots

    INPUT: roots, a list of the roots of the curve C (giving the Weierstrass points)
    OUTUPT: ros, the Rosenhain invariants of the curve C when put in Rosenhain form
    """

    assert(len(roots) == 6)

    linf = roots[0]
    l0 = roots[1]
    l1 = roots[2]

    a = fp_sub(l1,linf)
    b = fp_mul(l0,fp_sub(linf,l1))
    c = fp_sub(l1,l0)
    d = fp_mul(linf,fp_sub(l0,l1))

    #we then need the evaluation of (ax + b)/(cx + d)
    #for lam, lmu, lnu

    return [ _temp_eval(a, b, c, d, roots[i]) for i in [3,4,5] ]

def get_elliptic_rosenhains(roots):

    """
    Gets the Rosehain invariants that correspond to elliptic Kummer surfaces

    INPUT: roots, a list of the roots of the curve C (giving the Weierstrass points)
                    Here, C is contructed from and elliptic curve via Scholten's construction.
    OUTPUT: elliptic_rosenhains, the possible Rosenhain invariants of the curve C when put in Rosenhain form
                            
    WARNING: this is highly suboptimal, can easily be improved
    """
    
    elliptic_rosenhains = []
    
    for perm_roots in list(itertools.permutations(roots)):
        ros = rosenhain_from_six_roots(perm_roots)
        if fp_mul(ros[0], ros[1]) == ros[2] or fp_mul(ros[1], ros[2]) == ros[0] or fp_mul(ros[0], ros[2]) == ros[1]:
            elliptic_rosenhains.append(ros)
    
    return elliptic_rosenhains

def normalise_rosenhain(ros):
    """
    Performs Kummer surface normalisation as described in Section 4.3

    INPUT: - ros, Rosenhain invariants corresponding to the Kummer surface
    OUTPUT: normalised Rosenhain invaraints that will give a normalised Kummer surface
    
    """
    new_roots = to_degree_six(ros)
    scholtens = get_elliptic_rosenhains(new_roots)
    scholtens.sort()
    return scholtens[0]

if __name__ == "__main__":
    
    # Testing 

    testset = [
        [ 217610473851, 138087012420, 42413722345 ],
        [ 46720581338, 345675709269, 91426010800 ],
        [ 34444146955, 221729241802, 385660306297 ],
        [ 114007141469, 124779713017, 35804802686 ],
        [ 123135305869, 25400171069, 24315095789 ]
    ]

    python_results = [
        normalise_rosenhain(test) for test in testset
    ]

    magma_results = [
        [ 58594144, 48779918860, 306403563246 ],
        [ 15775240406, 85895158793, 258997075956 ],
        [ 34444146955, 101336964274, 322400069680 ],
        [ 35804802686, 114007141469, 124779713017 ],
        [ 20549989461, 140204151858, 339455135710 ]
    ]

    assert(python_results == magma_results)
    print("Testing done.")
