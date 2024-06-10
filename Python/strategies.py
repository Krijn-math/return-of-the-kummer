# implements the algorithm from the SIKE spec


def compute_kummer_strategy(n):

    assert (n >= 2)

    # Uses data from Costello's paper
    # for m = 1*s model
    # p = 6272   #cost for a doubling
    # q = 3480   #cost for Kummer-isogeny evaluation

    # for m = 0.8*s model
    p = 5714  # cost for a doubling
    q = 3200  # cost for Kummer-isogeny evaluation

    S = {1: []}
    C = {1: 0}
    for i in range(2, n + 1):
        b, cost = min(((b, C[i - b] + C[b] + b * p + (i - b) * q)
                      for b in range(1, i)), key=lambda t: t[1])
        S[i] = [b] + S[i - b] + S[b]
        C[i] = cost
    return S[n], C[n]


if __name__ == "__main__":
    # Sn, Cn = compute_kummer_strategy(244)
    Sn, Cn = compute_kummer_strategy(31)
    Sn, Cn = compute_kummer_strategy(243)
    Sn, Cn = compute_kummer_strategy(128)
    print(Sn)
    print(Cn)
