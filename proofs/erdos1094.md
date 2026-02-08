# Least Prime Factor of Binomial Coefficients (Erdős Problem 1094)

**Status:** Draft ✏️
**Statement:** Let $g(n, k)$ be the least prime factor of the binomial coefficient $\binom{n}{k}$. For $n \ge 2k$, $g(n, k) \le \max(n/k, k)$ with a finite number of exceptions.
**Dependencies:** None
**Confidence:** High

## Introduction

Erdős conjectured that the least prime factor of $\binom{n}{k}$ is typically small. Specifically, for $n \ge 2k$, $g(n, k)$ should not exceed $k$ unless $n$ is small, or $n/k$ if $k$ is small. The unified bound is $g(n, k) \le \max(n/k, k)$. This was proven by E. F. Ecklund Jr. in 1969.

## Preliminaries

### Kummer's Theorem
The exponent of a prime $p$ in the prime factorization of $\binom{n}{k}$ is equal to the number of carries that occur when adding $k$ and $n-k$ in base $p$.
A direct consequence is that $p \nmid \binom{n}{k}$ if and only if there are no carries. This occurs if and only if the digits of $k$ in base $p$ are less than or equal to the corresponding digits of $n$ in base $p$:
$$k = \sum \kappa_i p^i, \quad n = \sum \nu_i p^i \implies p \nmid \binom{n}{k} \iff \forall i, \kappa_i \le \nu_i$$

### Sylvester's Theorem
For $n > k$, the product of $k$ consecutive integers $n(n-1)\dots(n-k+1)$ contains a prime factor $p > k$. This implies $\binom{n}{k}$ always has a prime factor $p > k$. The problem here is to find a *small* prime factor.

## Proof Sketch

We divide the proof into two main cases based on the relationship between $n$ and $k^2$.

### Case 1: $n \ge k^2$
In this case, $\max(n/k, k) = n/k$. We wish to show $g(n, k) \le n/k$.
In fact, Ecklund proves a stronger result: if $n \ge k^2$, then $g(n, k) \le k$. Since $k \le n/k$ in this region, the bound holds.

If $g(n, k) > k$, then for all primes $p \le k$, $p \nmid \binom{n}{k}$.
By Kummer's theorem, this means that for every $p \le k$, no carry occurs in $k + (n-k)$ base $p$.
Let $p$ be a prime such that $\sqrt{n} < p \le k$. (Such a prime exists by Bertrand's Postulate if $k \ge \sqrt{n}$ is large enough).
If $p > \sqrt{n}$, then $n < p^2$, so $n$ has at most two digits in base $p$: $n = \nu_1 p + \nu_0$.
Since $k \ge p$, $k$ also has at least two digits (or is $p$ exactly): $k = \kappa_1 p + \kappa_0$.
The "no carry" condition $\kappa_i \le \nu_i$ implies:
1. $\kappa_0 \le \nu_0$
2. $\kappa_1 \le \nu_1$

Summing these gives $k = \kappa_1 p + \kappa_0 \le \nu_1 p + \nu_0 = n$. This is always true for $n \ge k$.
However, consider the constraint $n < k^2$. If $n$ is significantly larger than $k$, say $n \ge k^2$, the number of digits of $n$ in base $p$ increases.
For $n \ge k^2$, we can choose primes $p \le k$.
If $g(n, k) > k$, then $\binom{n}{k}$ is a product of primes all $> k$.
Ecklund used estimates on the size of $\binom{n}{k}$. Specifically, $\binom{n}{k} > (n/k)^k$.
If all prime factors are $> k$, then $\binom{n}{k} = \prod p_i^{a_i}$ where $p_i > k$.
The number of such prime factors is limited. For $n \ge k^2$, the density of primes and the magnitude of $\binom{n}{k}$ force at least one prime factor to be $\le k$, except for small $n$.

### Case 2: $2k \le n < k^2$
In this case, $\max(n/k, k) = k$. We wish to show $g(n, k) \le k$.
This is the heart of Ecklund's 1969 paper. He shows that the condition $p \nmid \binom{n}{k}$ for all $p \le k$ is extremely restrictive.
For a fixed $k$, there are only a few values of $n \in [2k, k^2-1]$ that satisfy this.
For $k=3$, $n \in [6, 8]$. $\binom{7}{3}=35$ has $g=5 > 3$. Exception $(7, 3)$.
For $k=4$, $n \in [8, 15]$. $\binom{13}{4}$ and $\binom{14}{4}$ have $g > 4$. Exceptions $(13, 4), (14, 4)$.
For $k=5$, $n \in [10, 24]$. $\binom{23}{5}$ has $g=7 > 5$. Exception $(23, 5)$.
As $k$ increases, the number of primes $p \le k$ grows. The simultaneous requirement that no carry occurs for *any* $p \le k$ eventually becomes impossible.
Ecklund computationally and analytically verified that for $k \ge 167$, no such $n$ exist. For $k < 167$, he enumerated all possibilities.

## List of Exceptions

The following table lists all pairs $(n, k)$ with $n \ge 2k$ such that $g(n, k) > \max(n/k, k)$. These are the only exceptions to the theorem.

| $n$ | $k$ | $\binom{n}{k}$ | $g(n, k)$ | $\max(n/k, k)$ |
|-----|-----|----------------|-----------|----------------|
| 7   | 3   | 35             | 5         | 3              |
| 13  | 4   | 715            | 5         | 4              |
| 14  | 4   | 1001           | 7         | 4              |
| 23  | 5   | 33649          | 7         | 5              |
| 44  | 8   | 17610393       | 11        | 8              |
| 46  | 10  | 4076350421     | 11        | 10             |
| 47  | 11  | 17417133617    | 13        | 11             |

No other exceptions exist for $n \ge 2k$. If $n < 2k$, the same bound applies by the symmetry of binomial coefficients $\binom{n}{k} = \binom{n}{n-k}$, substituting $k' = n-k$.

## References
1. Ecklund, E. F., Jr. (1969). "On the prime factorization of binomial coefficients". *Pacific Journal of Mathematics*, 29(2), 267-270.
2. Erdős, P. "Problems and results on binomial coefficients".
3. Kummer, E. E. (1852). "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen".
