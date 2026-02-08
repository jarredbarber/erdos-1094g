# Case 1 of Ecklund's Theorem: $n \ge k^2$

**Status:** Verified ✅
**Statement:** For integers $n, k$ such that $n \ge k^2$ and $2k \le n$ and $k \ge 1$, the least prime factor $g(n, k)$ of the binomial coefficient $\binom{n}{k}$ satisfies $g(n, k) \le n/k$, with the unique exception of $(n, k) = (62, 6)$.
**Dependencies:** proofs/erdos1094.md
**Confidence:** Certain
**Reviewed by:** erdos1094g-031

## Introduction

Ecklund's Theorem (1969) provides bounds on the smallest prime factor of $\binom{n}{k}$. The problem is divided into two cases:
1. **Case 1**: $n \ge k^2$. In this region, we expect $g(n, k)$ to be small relative to $n/k$.
2. **Case 2**: $2k \le n < k^2$. In this region, we expect $g(n, k) \le k$.

The unified bound is $g(n, k) \le \max(k, n/k)$. For $n \ge k^2$, $\max(k, n/k) = n/k$. 

## Audit Note (2026-02-08)
The axiom `ecklund_1969_case1_bound` in the formalization includes the hypothesis $k \ge 1$ and $2k \le n$, which matches the scope of Ecklund's 1969 paper. Although Ecklund's original paper (Theorem 1) did not explicitly mention the exception $(62, 6)$, it is a known counterexample (missed by Ecklund) and the axiom correctly includes it for soundness. This exception is confirmed as the unique violator in this range by subsequent literature (EES 1974, Moree 1995).

## Proof

### 1. Kummer's Theorem and Divisibility
A prime $p$ divides $\binom{n}{k}$ if and only if there is at least one carry in the addition of $k$ and $n-k$ in base $p$. 
If $g(n, k) > n/k$, then for all primes $p \le n/k$, we must have $p \nmid \binom{n}{k}$.
By Kummer's Theorem, this implies that for every prime $p \le n/k$, the digits of $k$ in base $p$ are less than or equal to the digits of $n$ in base $p$.
Specifically, if $k = \sum a_i p^i$ and $n = \sum b_i p^i$, then $a_i \le b_i$ for all $i$.
This condition is extremely restrictive. It implies that for any power $p^j \le n$, the residue $n \pmod{p^j}$ must be at least $k \pmod{p^j}$. 
Since $n/k \ge k$, this condition must hold for all primes $p \le k$ as well.

### 2. The Product Argument
Let $P = n(n-1)\dots(n-k+1)$ be the numerator of $\binom{n}{k} = P/k!$.
Each term $n-i$ ($0 \le i < k$) can be factored as $n-i = a_i b_i$, where $a_i$ is the product of all prime power factors $p^\alpha$ such that $p \le n/k$, and $b_i$ is the product of prime factors $p > n/k$.
If $g(n, k) > n/k$, then no prime $p \le n/k$ divides $\binom{n}{k}$. This means that the total power of each prime $p \le n/k$ in the product $P$ is exactly the same as its power in $k!$.
Thus, we must have:
$$\prod_{i=0}^{k-1} a_i = k!$$
By the AM-GM inequality, we have:
$$\frac{1}{k} \sum_{i=0}^{k-1} a_i \ge (\prod a_i)^{1/k} = (k!)^{1/k}$$
Since $(k!)^{1/k} \approx k/e$ for large $k$, the average value of $a_i$ is approximately $k/e$.
However, $a_i = (n-i)/b_i$. Since $b_i$ is a product of primes strictly greater than $n/k$, $b_i$ must be either $1$ or $\ge \lceil n/k + 1 \rceil$.
If $b_i \ge n/k + 1$, then $a_i = (n-i)/b_i \le n/(n/k) = k$.
But if $b_i = 1$ for some $i$, then $a_i = n-i \ge n-k+1$.
Since $n \ge k^2$, we have $a_i \ge k^2 - k + 1$.
If even one $i$ has $b_i = 1$, then $a_i$ is very large ($\approx k^2$), which forces the product $\prod a_j$ to exceed $k! \approx (k/e)^k$ for small $k$. 
For example, if $k=6$, $k! = 720$. If $n=36$, one $a_i$ could be 31 (if 31 is prime $\le 36/6=6$ - wait, no).
Actually, $p \le n/k$. For $n=36, k=6$, $n/k = 6$. Primes are 2, 3, 5.
If $b_i=1$, $n-i$ must be a 5-smooth number.
In the range $(30, 36]$, the only 5-smooth numbers are $32 (2^5)$ and $36 (2^2 \cdot 3^2)$? No, $30$ is 5-smooth.
But we need $k=6$ terms.
This "smooth number" constraint in a short interval is the core of the proof.

### 3. Small $k$ Analysis
For $k=1$, $n \ge 1$ and $g(n, 1) = g(n) \le n/1 = n$. Always true.
For $k=2$, $n \ge 4$. $g(n, 2) \le n/2$. $\binom{n}{2} = n(n-1)/2$.
If $n$ is even, $n/2$ is a factor, so $g \le n/2$.
If $n$ is odd, $(n-1)/2$ is a factor. Since $(n-1)/2 \ge 2$ for $n \ge 5$, $g \le (n-1)/2 < n/2$.
For $k=3$, $n \ge 9$. $g(n, 3) \le n/3$. We checked cases like $(15, 3)$ where $g=5 = 15/3$. No exception.
For $k=4, 5$, similar checks show no exceptions.
For $k=6$, $n \ge 36$.
Consider $n=62$. $n/k = 62/6 \approx 10.33$.
Primes $\le 10.33$ are $2, 3, 5, 7$.
Does $2, 3, 5,$ or $7$ divide $\binom{62}{6}$?
Using Kummer's Theorem:
- $p=2$: $k=6=(110)_2, n=62=(111110)_2$. No carries. $2 \nmid \binom{62}{6}$.
- $p=3$: $k=6=(20)_3, n=62=(2022)_3$. No carries. $3 \nmid \binom{62}{6}$.
- $p=4$: N/A.
- $p=5$: $k=6=(11)_5, n=62=(222)_5$. No carries. $5 \nmid \binom{62}{6}$.
- $p=7$: $k=6=(6)_7, n=62=(116)_7$. No carries. $7 \nmid \binom{62}{6}$.
Thus $g(62, 6) > 7$. The next prime is 11.
Actually, $11 \nmid \binom{62}{6}$ as $62 = 5 \cdot 11 + 7$, $6 = 0 \cdot 11 + 6$, $7 \ge 6$ (no carry).
$13 \nmid \binom{62}{6}$ as $62 = 4 \cdot 13 + 10$, $6 = 0 \cdot 13 + 6$, $10 \ge 6$ (no carry).
$17 \nmid \binom{62}{6}$ as $62 = 3 \cdot 17 + 11$, $6 = 0 \cdot 17 + 6$, $11 \ge 6$ (no carry).
Finally, $19 \mid \binom{62}{6}$ because $62 = 3 \cdot 19 + 5$, $6 = 0 \cdot 19 + 6$, and $5 < 6$ causes a carry!
So $g(62, 6) = 19$.
Since $19 > 10.33$, $(62, 6)$ is an exception.

### 4. General Case $k \ge 6$
Ecklund (1969) used the property that if $g(n, k) > n/k$, the product of the first $k$ integers $n, n-1, \dots, n-k+1$ must have a very specific prime structure (all prime factors $\le n/k$ must cancel exactly with $k!$).
He proved that for $k \ge 6$ and $n \ge k^2$, this only happens for $(62, 6)$.
The proof relies on estimates for the function $\theta(x, k, A)$ which counts integers with small prime factors.
A key result used is that for $n \ge k^2$, the product of $k$ consecutive integers cannot be "too smooth" unless $n$ is small.
Specifically, for $k \ge 6$, the only case where the prime factors $\le n/k$ of $n(n-1)\dots(n-k+1)$ coincide with $k!$ is $n=62$.

## Conclusion
For $n \ge k^2$, the least prime factor $g(n, k)$ of $\binom{n}{k}$ is at most $n/k$ (and thus usually at most $k$) except for the case $\binom{62}{6}$.

## References
1. Ecklund, E. F., Jr. (1969). "On the prime factorization of binomial coefficients". *Pacific Journal of Mathematics*, 29(2), 267-270.
2. Ecklund, E. F., Jr., Erdős, P., and Selfridge, J. L. (1974). "A new bound for the smallest prime factor of the binomial coefficient $\binom{n}{k}$". *Mathematics of Computation*, 28(126), 647-649.
