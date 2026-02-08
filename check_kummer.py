import math

def get_primes(n):
    primes = []
    sieve = [True] * (n + 1)
    for p in range(2, n + 1):
        if sieve[p]:
            primes.append(p)
            for i in range(p * p, n + 1, p):
                sieve[i] = False
    return primes

primes_list = get_primes(1000)

def has_carry(n, k, p):
    # Check if k + (n-k) has a carry in base p
    # Equivalent to checking if there's some i such that (k // p^i) % p + ((n-k) // p^i) % p >= p
    # Or simply: digit sum of n is less than digit sum of k + digit sum of n-k
    temp_n = n
    temp_k = k
    temp_m = n - k
    while temp_n > 0:
        if (temp_k % p) + (temp_m % p) >= p:
            return True
        temp_n //= p
        temp_k //= p
        temp_m //= p
    return False

def g_nk_is_greater_than_limit(n, k, limit):
    # Check if all primes p <= limit do NOT divide nCr(n, k)
    # nCr(n, k) is divisible by p if there is a carry in n = k + (n-k) base p
    for p in primes_list:
        if p > limit:
            break
        if has_carry(n, k, p):
            return False # g(n, k) <= p <= limit
    return True

def check_range(k_min, k_max):
    print(f"{'n':>3} {'k':>3} {'max(n/k, k)':>15} {'Exception?':>10}")
    for k in range(k_min, k_max + 1):
        # Check Case 2: 2k <= n < k^2
        for n in range(2*k, k*k):
            limit = k
            if g_nk_is_greater_than_limit(n, k, limit):
                print(f"{n:>3} {k:>3} {limit:>15.2f} {'YES':>10}")
        # Check Case 1: n >= k^2
        # We need an upper bound for n. Let's try n up to 2*k^2 or something.
        # Actually, let's try n up to 10000 for small k.
        for n in range(k*k, min(10000, 100*k*k)):
            limit = n/k
            if g_nk_is_greater_than_limit(n, k, limit):
                print(f"{n:>3} {k:>3} {limit:>15.2f} {'YES (Case 1)':>10}")

check_range(2, 1000)
