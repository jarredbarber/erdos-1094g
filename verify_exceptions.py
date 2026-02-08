import math

def least_prime_factor(n):
    if n < 2: return None
    if n % 2 == 0: return 2
    for i in range(3, int(math.sqrt(n)) + 1, 2):
        if n % i == 0:
            return i
    return n

def nCr(n, k):
    return math.comb(n, k)

exceptions = [
    (7, 3), (13, 4), (14, 4), (23, 5), (62, 6), (44, 8),
    (46, 10), (47, 10), (74, 10), (94, 10), (95, 10), (47, 11)
]

print(f"{'n':>3} {'k':>3} {'nCr':>15} {'g(n,k)':>7} {'max(n/k, k)':>15} {'Is exception?':>15}")
for n, k in exceptions:
    c = nCr(n, k)
    g = least_prime_factor(c)
    limit = max(n/k, k)
    is_exc = g > limit
    print(f"{n:>3} {k:>3} {c:>15} {g:>7} {limit:>15.2f} {str(is_exc):>15}")

# Also check a few non-exceptions near the boundaries
test_cases = [(6, 3), (8, 3), (12, 4), (15, 4), (61, 6), (63, 6)]
print("\nChecking non-exceptions:")
for n, k in test_cases:
    c = nCr(n, k)
    g = least_prime_factor(c)
    limit = max(n/k, k)
    is_exc = g > limit
    print(f"{n:>3} {k:>3} {c:>15} {g:>7} {limit:>15.2f} {str(is_exc):>15}")
