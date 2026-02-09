import math

def has_prime_factor_le_k(n, k):
    # Check if there exists p <= k such that p | C(n, k)
    # This is equivalent to checking if there is a carry in n = (n-k) + k in base p
    for p in range(2, k + 1):
        # Primality test for p
        is_prime = True
        for i in range(2, int(math.sqrt(p)) + 1):
            if p % i == 0:
                is_prime = False
                break
        if not is_prime:
            continue
            
        # Check for carry in base p
        temp_n = n
        temp_k = k
        while temp_k > 0:
            if temp_n % p < temp_k % p:
                return True # Carry found, so p | C(n, k)
            temp_n //= p
            temp_k //= p
    return False

def check_range(k_start, k_end):
    exceptions = []
    for k in range(k_start, k_end + 1):
        if k % 10 == 0:
            print(f"Checking k={k}...")
        for n in range(2*k, k*k + 1):
            limit = max(n/k, k)
            # We want to find g(n, k) > limit
            # If limit is k, then g(n, k) > k means no prime p <= k divides C(n, k)
            # If limit is n/k, we need to check more.
            # But in Case 2 (2k <= n < k^2), limit is k.
            
            if not has_prime_factor_le_k(n, k):
                # No prime <= k divides C(n, k). So g(n, k) > k.
                # Since n < k^2, limit is k. So this is an exception.
                exceptions.append((n, k))
                print(f"Exception: n={n}, k={k}")
    return exceptions

check_range(2, 200)
