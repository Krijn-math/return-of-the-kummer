# takes an uncompressed signature and returns the compressed signature
# first for fake signatures, later should fit to the sage output of apressqi

#this script runs in sage because we need to compress the points using disclog
#on the jacobian

from globals import *

if __name__ == "__main__":
    # p = 417942208511
    p = 2**246*3*67 - 1
    set_prime(p)
    strat = [94, 56, 38, 22, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 16, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 22, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 38, 22, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 16, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1]


from kummer_isogeny import *
from kummer_arithmetic import *
from fp import *
from example_signature import pk, sigma, sigma2
from compression import point_compression_single
from normalisation import normalise_rosenhain
from hashing import hash_to_point

def kummer_to_rosenhain(kummer):
    #implements the formulas from Costello 2018/850

    assert kummer[1][2] == 1
    assert kummer[1][3] == 1

    ABCD = hadamard(kummer[1])

    assert fp_sub(ABCD[0], 4) == ABCD[1]
    assert ABCD[2] == ABCD[3]

    top = fp_add(fp_mul(ABCD[0], ABCD[1]), fp_mul(ABCD[2], ABCD[3]))
    bot = fp_sub(fp_mul(ABCD[0], ABCD[1]), fp_mul(ABCD[2], ABCD[3]))

    lam = fp_div(kummer[1][0], kummer[1][1])
    mu = fp_div(top, bot)
    nu = fp_mul(lam, mu)

    return [lam, mu, nu]


def rosenhain_to_kummer(ros):
    #implements the formulas from Costello 2018/850

    lam = ros[0]
    mu = ros[1]
    nu = ros[2]
    assert fp_mul(lam, mu) == nu

    tmp1 = fp_mul(fp_sub(mu, 1), fp_sub(1, mu))
    tmp2 = fp_mul(fp_sub(nu, 1), fp_sub(lam, mu))
    tmp = fp_div(tmp1, tmp2)

    mu2 = fp_squareroot(tmp)
    mu3 = 1
    mu4 = 1
    mu1 = fp_mul(mu2, lam)

    K = squared_kummer_from_squared_thetas([mu1, mu2, mu3, mu4])
    return K

def normalise_kummer(kummer):
    ros = kummer_to_rosenhain(K)
    ros = normalise_rosenhain(ros)
    return rosenhain_to_kummer(ros)

def uncompressed_to_compressed_response(pk, response_isogeny):
    # assumes a response isogeny given by n blocks of kernel points K_i

    K = pk
    Nblocks = len(response_isogeny)

    compressed_resp = []

    #first compress the response isogeny
    for n in range(Nblocks):
        print(f"Doing compression for block {n+1}")
        P = response_isogeny[n]
        assert on_kummer(P, K)

        ros = kummer_to_rosenhain(K)    #improved by now getting ros from isogenies
        b, diff_bit, switch = point_compression_single(P, K, ros)
        compressed_resp.append([b, diff_bit, switch])

        K, eval = optimal_kummer_isogeny(P, K, [], f2 - 1, strat)

    return compressed_resp

compressed_response = uncompressed_to_compressed_response(pk, sigma[1])

if __name__ == "__main__":

    if p == 417942208511:
        ros = [79530844451, 73494698586, 202324325786]

        K = [[359839655292, 260280618262, 57025794571],
            [253391591110, 6889027152, 1, 1],
            [6889027152, 253391591110, 183392295428, 183392295428],
            [403297045753, 147106535345, 237788911426, 237788911426]]
        
        assert ros == kummer_to_rosenhain(K)

        K = [
            [99046282131, 80137275825, 43785859117],
            [149964968508, 348114515828, 1, 1],
            [348114515828, 149964968508, 344289703673, 344289703673],
            [346513123615, 16653617905, 64454801943, 64454801943]
        ]
        ros = [158121108515, 64189784019, 25626095119]

        assert ros == kummer_to_rosenhain(K)


