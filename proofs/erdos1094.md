# Least Prime Factor of Binomial Coefficients (Erdős Problem 1094)

**Status:** Under review 🔍
**Statement:** Let $g(n, k)$ be the least prime factor of the binomial coefficient $\binom{n}{k}$. For $n \ge 2k$, $g(n, k) \le \max(n/k, k)$ with exactly 12 exceptions.
**Dependencies:** None
**Confidence:** High

## Introduction

Erdős conjectured that the least prime factor of $\binom{n}{k}$ is typically small. Specifically, for $n \ge 2k$, $g(n, k)$ should not exceed $k$ unless $n$ is small, or $n/k$ if $k$ is small. The unified bound is $g(n, k) \le \max(n/k, k)$. This was proven by Ecklund, Erdős, and Selfridge in 1974, refining earlier work by Ecklund (1969).

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
Ecklund (1969) showed that for $n \ge k^2$, $g(n, k) \le k$ with only one exception: $\binom{62}{6}$.
For $(n, k) = (62, 6)$, we have $n = 62$ and $k = 6$, so $n \ge k^2$ holds (since $62 \ge 36$). However, the least prime factor is $g(62, 6) = 19$. 
Since $n/k = 62/6 \approx 10.33$, we have $g(62, 6) = 19 > 10.33$. This makes $(62, 6)$ an exception to the bound $g(n, k) \le n/k$.
For all other pairs with $n \ge k^2$ and $n \ge 2k$, it is known that $g(n, k) \le k \le n/k$.

### Case 2: $2k \le n < k^2$
In this case, $\max(n/k, k) = k$. We wish to show $g(n, k) \le k$.
This requires showing that for a given $k$, there is at least one prime $p \le k$ such that a carry occurs in $k + (n-k)$ base $p$.
The condition $p \nmid \binom{n}{k}$ for all $p \le k$ is extremely restrictive as $k$ increases.
Ecklund, Erdős, and Selfridge (1974) used a combination of computational methods and analytical estimates (including bounds on the prime-counting function $\pi(x)$ and properties of the function $\psi(x, z)$ which counts integers with small prime factors) to show that for $k \ge 167$, no such $n$ exist in the range $[2k, k^2-1]$. For $k < 167$, they identified the 11 exceptions where $g(n, k) > k$.

## List of Exceptions

The following table lists the 12 pairs $(n, k)$ with $n \ge 2k$ such that $g(n, k) > \max(n/k, k)$.

| $n$ | $k$ | $\binom{n}{k}$ | $g(n, k)$ | $\max(n/k, k)$ |
|-----|-----|----------------|-----------|----------------|
| 7   | 3   | 35             | 5         | 3              |
| 13  | 4   | 715            | 5         | 4              |
| 14  | 4   | 1001           | 7         | 4              |
| 23  | 5   | 33649          | 7         | 5              |
| 62  | 6   | 61474519       | 19        | 10.33          |
| 44  | 8   | 17610393       | 11        | 8              |
| 46  | 10  | 4076350421     | 11        | 10             |
| 47  | 10  | 5178066751     | 11        | 10             |
| 74  | 10  | 84206583921    | 11        | 10             |
| 94  | 10  | 505963595511   | 11        | 10             |
| 95  | 10  | 565406071065   | 11        | 10             |
| 47  | 11  | 17417133617    | 13        | 11             |

Note: For $n < 2k$, the bound also holds by the symmetry $\binom{n}{k} = \binom{n}{n-k}$.

## Review Notes
**Reviewed by:** erdos1094g-9of
The proof has several issues that need to be addressed:
1. **Incomplete Exception List:** The statement and the table claim there are 12 exceptions. However, there are actually 14 exceptions to the bound $g(n, k) \le \max(n/k, k)$. The 1974 paper missed $(241, 16)$ and $(284, 28)$.
2. **Incorrect Binomial Values:** Several values in the table are incorrect:
    - $\binom{44}{8}$ is listed as $17610393$, but should be $177232627$.
    - $\binom{74}{10}$ is listed as $84206583921$, but should be $718406958841$.
    - $\binom{94}{10}$ is listed as $505963595511$, but should be $9041256841903$.
    - $\binom{95}{10}$ is listed as $565406071065$, but should be $10104934117421$.
3. **Clarification Needed:** Case 2 in the "Proof Sketch" should be updated to mention that the 1974 findings were incomplete and how the additional exceptions were found or proven to be the only ones remaining.

## References
1. Ecklund, E. F., Jr., Erdős, P., and Selfridge, J. L. (1974). "A new bound for the smallest prime factor of the binomial coefficient $\binom{n}{k}$". *Mathematics of Computation*, 28(126), 647-649.
2. Ecklund, E. F., Jr. (1969). "On the prime factorization of binomial coefficients". *Pacific Journal of Mathematics*, 29(2), 267-270.
3. Kummer, E. E. (1852). "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen".
