import math

def lpf(n):
    if n < 2: return None
    if n % 2 == 0: return 2
    for i in range(3, int(math.sqrt(n)) + 1, 2):
        if n % i == 0: return i
    return n

n, k = 241, 16
c = math.comb(n, k)
g = lpf(c)
limit = max(n/k, k)
print(f"n={n}, k={k}, c={c}, g={g}, limit={limit}, exc={g > limit}")

n, k = 284, 28
c = math.comb(n, k)
g = lpf(c)
limit = max(n/k, k)
print(f"n={n}, k={k}, c={c}, g={g}, limit={limit}, exc={g > limit}")
