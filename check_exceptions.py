import math

def get_primes(n):
    primes = []
    is_prime = [True] * (n + 1)
    for p in range(2, n + 1):
        if is_prime[p]:
            primes.append(p)
            for i in range(p * p, n + 1, p):
                is_prime[i] = False
    return primes

def prime_factors(n):
    factors = set()
    d = 2
    temp = n
    while d * d <= temp:
        if temp % d == 0:
            factors.add(d)
            while temp % d == 0:
                temp //= d
        d += 1
    if temp > 1:
        factors.add(temp)
    return factors

def check(k_start, k_end):
    for k in range(k_start, k_end + 1):
        has_exception = False
        lower = 2 * k
        upper = k * k
        primes_le_k = get_primes(k)
        
        for n in range(lower, upper):
            # Calculate binom(n, k)
            binom = math.comb(n, k)
            
            # Check if there exists p <= k such that p | binom
            found_p = False
            for p in primes_le_k:
                if binom % p == 0:
                    found_p = True
                    break
            
            if not found_p:
                print(f"Exception: n={n}, k={k}")
                has_exception = True
        
        if not has_exception:
            # print(f"No exceptions for k={k}")
            pass

check(2, 50)
