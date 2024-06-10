############################################################################
# This file contains functions to run verification on the Kummer surface 
#    and runs benchmarks on both uncompressed and compressed variants 
############################################################################


from globals import *

# Setting the prime and strategies used
if __name__ == "__main__":
    p = 2**246*3*67 - 1
    set_prime(p)
    strat = [94, 56, 38, 22, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 16, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 22, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 38, 22, 13, 8, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 16, 9, 5, 3, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 1, 7, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1]
    lam_strat = [48, 32, 20, 12, 7, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 12, 8, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 20, 12, 7, 4, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5, 3, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1]


from kummer_isogeny import *
from kummer_arithmetic import *
from fp import *
from point_sampling import precompute_sample_basis
from decompression import point_decompression_single, point_decompression_single_with_Q
from hashing import hash_to_point


# DOING PRECOMPUTATION FOR SAMPLE BASIS
if __name__ == "__main__":
    X1, X2 = precompute_sample_basis()
    precomp = [X1, X2]


############################################################################
####################### SIGNATURE VERIFICATION #############################
############################################################################


def kummer_point_equal(P, Q):
    """
    Checks if two Kummer points are equal 

    INPUTS: - P and Q, points on the same Kummer surface
    OUTPUTS: True if P = Q (projectively), and False otherwise
    """
    return normalise(P) == normalise(Q)

def verification_uncompressed(pk, sigma, message):
    """
    Takes a public key, an uncompressed signature, 
    and message, and verfies the signature.

    INPUTS: - pk, a Kummer surface
            - sigma, an uncompressed siganture consisting of:
                    1) the E_2 kummer surface that is the goal of the signature
                    2) a number of points, where P_i is on K_i and P_{i+1} is on K_i/<P_i>
                            with pk = K_0
            - message
    
    OUTPUT: True if the signature verifies, and False otherwise
    """

    K = pk
    Nblocks = len(sigma[1])

    for n in range(Nblocks):
        # print(f"Doing isogeny for block {n+1}, current cost {get_cost(counter)}")
        ker = sigma[1][n]

        ## For debugging
        # assert on_kummer(ker, K)

        K, eval = optimal_kummer_isogeny(ker, K, [], f2 - 1, strat)

    # print(f"\nresp done, current cost {get_cost(counter)}")

    ker = sigma[2]

    ## For debugging
    # assert normalise(eDBLs(ker, K, f2 - 2)) == normalise(K[1]), eDBLs(ker, K, f2 - 2)

    K, eval = optimal_kummer_isogeny(ker, K, [], 128, lam_strat)
    # print(f"chall done, current cost {get_cost(counter)}")

    K[1] = normalise(K[1])   
    ros = kummer_to_rosenhain(K, twotors = [eval[0]], bit = 1)

    hash = hash_to_point(message, K, ros, precomp)
    # print(f"hash done, current cost {get_cost(counter)}\n")

    # TODO: Just want to see the costs, but not properly done
    goal = kummer_scalar(hash, K, sigma[3])

    if kummer_point_equal(goal, hash):
        # print(f"The signature (uncompressed) verified.")
        return True
    else:
        # print(f"The signature (uncompressed) did not verify.")
        return False


def verification_compressed(pk, sigma, message):
    """
    Takes a public key, a compressed signature, 
    and message, and verfies the signature.

    INPUTS: - pk, a Kummer surface
            - sigma, a compressed siganture consisting of:
                    1) an array of blocks that are the compressed response isogeny
                    2) a block to describe the challenge
                    3) the message as an integer between 1 and 2**f2-1
            - message
    
    OUTPUT: True if the signature verifies, and False otherwise
    """
    # compressed signature consists of 
    # first, an array of blocks that are the compressed response isogeny
    # then, a block to describe the challenge
    # then, the message as an interger between 1 and 2**f2-1

    K = pk
    Nblocks = len(sigma[0])
    switch_tau = sigma[3]
    
    for n in range(Nblocks):
        # print(f"Doing isogeny for block {n+1}, current cost {get_cost(counter)}")

        b, bit, switch = sigma[0][n]
        
        bot = fp_inv(K[1][2])
        K[1] = [fp_mul(K[1][0],bot), fp_mul(K[1][1],bot), 1,1]

        if n == 0:
            ros = kummer_to_rosenhain(K, switch_tau[0])
        else:
            ros = kummer_to_rosenhain(K, switch_tau[n], twotors = eval)

        ker = point_decompression_single(K, ros, b, bit, switch, precomp)

        K, eval = optimal_kummer_isogeny(ker, K, [], f2 - 1, strat)

        
    # print(f"\nresp done, current cost {get_cost(counter)}")

    b, bit, switch = sigma[1]
    
    bot = fp_inv(K[1][2])
    K[1] = [fp_mul(K[1][0],bot), fp_mul(K[1][1],bot), 1,1]  
    ros = kummer_to_rosenhain(K, switch_tau[4], twotors = eval)

    ker, Q = point_decompression_single_with_Q(K, ros, b, bit, switch, precomp)

    # We have avoided normalisation, on the Kummers now this is extremely expensive (left for future work)

    # for now the verification was crafted in such a way with f2 - 1 instead of size lambda isogeny
    # by manual checks, going to size lambda saves roughly 15,000 multiplications
    K, eval = optimal_kummer_isogeny(ker, K, [Q], f2 - 1, strat)
    # print(f"chall done, current cost {get_cost(counter)}")

    bot = fp_inv(K[1][2])
    K[1] = [fp_mul(K[1][0],bot), fp_mul(K[1][1],bot), 1,1]
    ros = kummer_to_rosenhain(K, switch_tau[5], twotors = [eval[1]])


    hash = hash_to_point(message, K, ros, precomp)
    # print(f"hash done, current cost {get_cost(counter)}\n")

    goal = kummer_scalar(eval[0], K, sigma[2])

    if kummer_point_equal(DBL(hash, K), goal):
        # print(f"The signature (compressed) verified.")
        return True
    else:
        # print(f"The signature (compressed) did not verify.")
        return False


if __name__ == "__main__":

    # Running some benchmarks

    from example_signature import pk, sigma, message

    # Let's do uncompressed verification first
    set = deepcopy(counter)
    verification_uncompressed(pk, sigma, message)
    cost = [counter[i] - set[i] for i in range(len(counter))]
    print(f"Cost of uncompressed SQIsign on Kummer is {get_cost(cost)}")
    

    from fake_signature import compressed_sigma, message

    # Let's do the compressed verification now
    set = deepcopy(counter)
    verification_compressed(pk, compressed_sigma, message)
    cost = [counter[i] - set[i] for i in range(len(counter))]
    print(f"Cost of   compressed SQIsign on Kummer is {get_cost(cost)}")
    print("Note: this excludes normalization, and includes a too long challenge.")


