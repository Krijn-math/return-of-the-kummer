
# ##############################################################
# This file contains functions needed to set up global variables
# ##############################################################

from math import ceil, log2

def valuation(n, ell):
    res = 0
    while not n % ell:
        res += 1
        n //= ell
    return res


def set_prime(newp):
    print(f"Setting new global prime to be p = {newp}.")
    global p, f2, e, cofac, counter, logp
    p = newp 
    logp = ceil(log2(p))
    f2 = valuation(p + 1, 2) 
    e = 976
    cofac = (p + 1) // pow(2, f2)
    counter = [0,0,0,0,0,0] #M, S, a, legendre, inversions, sqrts

def reset_counter():
    global counter
    counter = [0,0,0,0,0,0] #M, S, a, legendre, inversions, sqrts


def get_cost(array):
    # We can modify these cost metric if necessary to get more accurate costs
    model = [1, 0.8, 0.00, logp, logp, logp]
    return sum([op*cost for op, cost in zip(array, model)])
