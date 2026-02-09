
import math

def get_smooth_part(n, limit):
    smooth = 1
    temp = n
    # Check small primes
    d = 2
    while d <= limit:
        while temp % d == 0:
            smooth *= d
            temp //= d
        d += 1
    return smooth

def check_hypothesis(k):
    # We want to know if every sequence of k integers has a term with smooth part >= k.
    # We can check this for a range of starting values.
    # But we can't check all integers.
    # However, the pattern of smooth parts is periodic? No.
    # But let's check for small range to see if it holds.
    # If it holds for, say, n up to 10000, it's likely true.
    
    print(f"Checking k={k}")
    
    # We only care about primes <= k.
    # Construct a window of length k.
    for n in range(1, 100000):
        # Window [n, n+k-1]
        max_smooth = 0
        for i in range(k):
            val = n + i
            sp = get_smooth_part(val, k) # k-smooth part
            if sp > max_smooth:
                max_smooth = sp
        
        if max_smooth < k:
            print(f"Counterexample for k={k} at n={n}: {[get_smooth_part(n+i, k) for i in range(k)]}")
            return False
            
    print(f"Hypothesis likely true for k={k}")
    return True

def factor_sieve(limit):
    primes = []
    is_prime = [True] * (limit + 1)
    for p in range(2, limit + 1):
        if is_prime[p]:
            primes.append(p)
            for i in range(p * p, limit + 1, p):
                is_prime[i] = False
    return primes

def check_smooth_product(k):
    # Check if for every sequence of k integers, the product of their k-smooth parts > k!
    # If this is true, then no solution exists for any n >= k^2.
    # Note: smooth part depends on limit n/k.
    # But for n >= k^2, limit >= k.
    # So a_m >= k-smooth part.
    # So if product of k-smooth parts > k!, we are done.
    
    fact_k = 1
    for i in range(1, k+1): fact_k *= i
    
    print(f"Checking product of smooth parts for k={k} against {fact_k}")
    
    min_prod = float('inf')
    
    # Check window [n, n+k-1]
    # We only need to check up to where the pattern repeats or stabilizes?
    # Actually, smooth parts pattern is periodic with period = LCM(1..k).
    # For k=11, LCM(1..11) = 27720.
    # We just check one period.
    
    lcm = 1
    for i in range(1, k+1):
        lcm = (lcm * i) // math.gcd(lcm, i)
        
    print(f"  Period (LCM): {lcm}")
    
    for n in range(1, lcm + k + 1):
        prod = 1
        for i in range(k):
            val = n + i
            sp = get_smooth_part(val, k)
            prod *= sp
        
        if prod <= fact_k:
            # We found a sequence with small smooth product.
            # This is a potential counterexample location.
            # But remember, we require prod = k! exactly for a solution.
            # If prod <= k!, it might be equal.
            if prod == fact_k:
                 print(f"  Match k! at n={n}: {[get_smooth_part(n+i, k) for i in range(k)]}")
            else:
                 pass # Less than k! is fine, we just need to know if we can exceed it.
                 # Wait, if min_prod > k!, then IMPOSSIBLE.
        
        if prod < min_prod:
            min_prod = prod
            
    if min_prod > fact_k:
        print(f"  Success: Min product {min_prod} > {fact_k}. No solution possible.")
        return True
    else:
        print(f"  Failure: Min product {min_prod} <= {fact_k}.")
        return False

def check_k11_full():
    k = 11
    limit = 39916800 + 11 # 11! + 11
    print(f"Checking full range for k=11 up to {limit}...")
    
    # We can iterate and check condition
    # g(n, k) <= n/k
    # Find exceptions
    
    # Fast check:
    # For each n, we need a prime p <= n/k that divides binom(n, k).
    # Most n have p=2 or p=3.
    
    chunk_size = 1000000
    for start in range(k*k, limit + 1, chunk_size):
        end = min(start + chunk_size, limit + 1)
        # print(f"  Scanning {start} to {end}...")
        
        for n in range(start, end):
            nk = n // 11
            
            # Check for prime factor <= nk
            # 1. Check 2
            # 2 | binom <=> carry
            if nk >= 2:
                # k=11 = 1011_2
                # n-k + k
                # Quick check: (n-k) & k == 0 implies NO carries -> odd.
                # If (n-k) & k != 0, then even -> 2 divides.
                if ((n - 11) & 11) != 0:
                    continue # Divisible by 2
            
            # 2. Check 3
            if nk >= 3:
                # k=11 = 102_3
                # 3 divides if carry
                # (n-11) + 11
                # manual check
                temp_n_k = n - 11
                if (temp_n_k % 3) + 2 >= 3: continue
                if ((temp_n_k // 3) % 3) + 0 >= 3: continue # 0 digit
                if ((temp_n_k // 9) % 3) + 1 >= 3: continue
                
            # 3. Check 5
            if nk >= 5:
                # k=11 = 21_5
                temp_n_k = n - 11
                if (temp_n_k % 5) + 1 >= 5: continue
                if ((temp_n_k // 5) % 5) + 2 >= 5: continue
                
            # If we reach here, check other primes
            found = False
            p = 7
            while p <= nk:
                # Check carry
                temp_k = 11
                temp_nk = n - 11
                while temp_k > 0 or temp_nk > 0:
                    if (temp_k % p) + (temp_nk % p) >= p:
                        found = True
                        break
                    temp_k //= p
                    temp_nk //= p
                if found: break
                
                # Next prime
                p += 2
                while not is_prime(p) and p <= nk: p += 2
                
            if not found:
                print(f"EXCEPTION k=11: n={n}")
                
    print("Finished k=11")


def is_prime(num):
    if num < 2: return False
    for i in range(2, int(math.sqrt(num)) + 1):
        if num % i == 0: return False
    return True

check_k11_full()
