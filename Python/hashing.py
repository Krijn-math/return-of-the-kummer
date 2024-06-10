#############################################################################################
# File containing functions needed to do hashing for "challenge"
#############################################################################################

from globals import *

# Setting up the prime for testing
if __name__ == "__main__":
    p = 417942208511
    set_prime(p)

from random import randint
from pairing import *
from kummer_arithmetic import on_kummer, three_point_ladder
from kummer_isogeny import naive_kummer_isogeny
from point_sampling import sample_basis
from point_diff import point_difference

def hash_to_point(message, K, ros, precomp):
    """
    Assuming a message is an integer between 0 and 2^f, where f > 128
    hashes to a random 2^f point.

    INPUTS: - message
            - K, the Kummer surface
            - ros, the Rosenhain invariants associated to K
            - precomp, precomputation needed to sample basis 
    """

    P, Q, _ = sample_basis(K, ros, precomp)
    D = point_difference(P, Q, K)

    return three_point_ladder(P, Q, D, message, K)


if __name__ == "__main__":
    # TESTING

    message = randint(0, 2**(f2 - 1))

    K = [
        [99046282131, 80137275825, 43785859117],
        [149964968508, 348114515828, 1, 1],
        [348114515828, 149964968508, 344289703673, 344289703673],
        [346513123615, 16653617905, 64454801943, 64454801943]
    ]
    ros = [158121108515, 64189784019, 25626095119]

    R = hash_to_point(message, K, ros)
    assert on_kummer(R, K)

    K2 = naive_kummer_isogeny(R, K, [], f2 - 1)

    print("Testing complete.")