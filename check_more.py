import math

def least_prime_factor(n):
    if n < 2: return None
    if n % 2 == 0: return 2
    for i in range(3, int(math.sqrt(n)) + 1, 2):
        if n % i == 0:
            return i
    return n

def check_range(k_min, k_max):
    print(f"{'n':>3} {'k':>3} {'g(n,k)':>7} {'max(n/k, k)':>15} {'Exception?':>10}")
    for k in range(k_min, k_max + 1):
        # We only care about n >= 2k
        # For Case 1: n >= k^2. g(n,k) <= k except (62,6)
        # For Case 2: 2k <= n < k^2. g(n,k) <= k except others.
        for n in range(2*k, k*k + 1): # Check Case 2 and the boundary of Case 1
            c = math.comb(n, k)
            g = least_prime_factor(c)
            limit = max(n/k, k)
            if g > limit:
                print(f"{n:>3} {k:>3} {g:>7} {limit:>15.2f} {'YES':>10}")

check_range(2, 200)
