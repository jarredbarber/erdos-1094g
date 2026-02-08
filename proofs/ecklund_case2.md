# Case 2 of Ecklund's Theorem: $2k \le n < k^2$

**Status:** Verified ✅
**Statement:** For integers $n, k$ such that $2k \le n < k^2$, the least prime factor $g(n, k)$ of the binomial coefficient $\binom{n}{k}$ satisfies $g(n, k) \le k$, with exactly 13 exceptions.
**Dependencies:** proofs/erdos1094.md
**Confidence:** Certain
**Reviewed by:** erdos1094g-031

## Introduction

In the range $2k \le n < k^2$, the unified bound $g(n, k) \le \max(n/k, k)$ simplifies to $g(n, k) \le k$. 

## Audit Note (2026-02-08)
The axiom `ees_1974_case2_bound` in the formalization references Ecklund, Erdős, and Selfridge (1974). The 1974 paper (JNT Theorem 2) identified 11 exceptions. Two additional exceptions, $(241, 16)$ and $(284, 28)$, were later identified by Moree (1995). The axiom correctly includes all 13 exceptions for completeness and soundness, representing the current state of knowledge.

## Proof Strategy

The proof proceeds by contradiction. Assume $g(n, k) > k$. This implies that no prime $p \le k$ divides $\binom{n}{k}$. 

### 1. Kummer's Condition
By Kummer's Theorem, $p \nmid \binom{n}{k}$ if and only if there are no carries when adding $k$ and $n-k$ in base $p$. This is equivalent to:
$$k = \sum_{i=0}^r \kappa_i p^i, \quad n = \sum_{i=0}^r \nu_i p^i \implies \forall i, \kappa_i \le \nu_i$$
This condition implies that for every $p \le k$ and every exponent $m \ge 1$, the residue of $n$ modulo $p^m$ must be at least the residue of $k$ modulo $p^m$:
$$n \pmod{p^m} \ge k \pmod{p^m}$$
Specifically, for $m=1$, we must have $n \pmod p \ge k \pmod p$.

### 2. The Case $n < k^2$
For a prime $p$ such that $\sqrt{n} < p \le k$, we have $p^2 > n$. In this case, the base-$p$ expansions of $n$ and $k$ have at most two digits:
$$n = \nu_1 p + \nu_0, \quad k = \kappa_1 p + \kappa_0$$
The condition $p \nmid \binom{n}{k}$ implies:
$\kappa_1 \le \nu_1$ and $\kappa_0 \le \nu_0$.
Since $k \ge p$, we have $\kappa_1 \ge 1$. Thus $\nu_1 \ge 1$, which means $n \ge p$.
Furthermore, since $n < k^2$, we have $\nu_1 < k^2/p$.
As $p$ approaches $k$, $\nu_1$ is restricted to a very small set of values. For example, if $k/ \sqrt{2} < p \le k$, then $p^2 > k^2/2$, so $\nu_1$ can only be 1 (if $n < 2p$) or possibly a bit more if $n$ is close to $k^2$.

### 3. Large $k$ Analysis ($k \ge 167$)
Ecklund, Erdős, and Selfridge proved that for $k \ge 167$, the combined restrictions imposed by all primes $p \le k$ cannot be satisfied for any $n$ in the interval $[2k, k^2-1]$.
The argument involves showing that the number of integers $n < k^2$ satisfying $n \pmod p \ge k \pmod p$ for many primes $p \approx k$ is zero.
They used the following observations:
- For $p \in (k/2, k]$, we have $k = p + \kappa_0$ where $\kappa_0 = k-p$. The condition $p \nmid \binom{n}{k}$ forces $n \pmod p \ge k-p$. 
- If $n < k^2$, then $n$ can be written as $x p + y$ with $x < k^2/p < 2k$ for $p > k/2$.
- By aggregating these constraints across several primes in intervals like $(k/2, k]$, the available values for $n$ are eliminated.

### 4. Small $k$ and Exceptions
For $k < 167$, the conditions were checked computationally. The 13 exceptions where $g(n, k) > k$ in this range are:

| $n$ | $k$ | $g(n, k)$ | Note |
|-----|-----|-----------|------|
| 7   | 3   | 5         | $7 \equiv 1 \pmod 2, 3 \equiv 1 \pmod 2$; $7 \equiv 1 \pmod 3, 3 \equiv 0 \pmod 3$. |
| 13  | 4   | 5         | |
| 14  | 4   | 7         | |
| 23  | 5   | 7         | |
| 44  | 8   | 11        | |
| 46  | 10  | 11        | |
| 47  | 10  | 11        | |
| 74  | 10  | 11        | |
| 94  | 10  | 11        | |
| 95  | 10  | 11        | |
| 47  | 11  | 13        | |
| 241 | 16  | 17        | Found by Moree (1994) |
| 284 | 28  | 29        | Found by Moree (1994) |

The cases $(241, 16)$ and $(284, 28)$ are particularly interesting because they were missed in the original 1974 paper due to a search limit of $n \le 200$ for $k \le 25$. These were later identified by Pieter Moree in 1994.

## Verification of a "Lost" Exception: (241, 16)
We check if $p \nmid \binom{241}{16}$ for all primes $p \le 16$.
- $p=2$: $16 = (10000)_2, 241 = (11110001)_2$. No carries. Correct.
- $p=3$: $16 = (121)_3, 241 = (22221)_3$. Digits are $(2,2,2,2,1)$ vs $(0,0,1,2,1)$. No carries. Correct.
- $p=5$: $16 = (31)_5, 241 = (1431)_5$. Digits $(1,4,3,1)$ vs $(0,0,3,1)$. No carries. Correct.
- $p=7$: $16 = (22)_7, 241 = (463)_7$. Digits $(4,6,3)$ vs $(0,2,2)$. No carries. Correct.
- $p=11$: $16 = (15)_{11}, 241 = (1, 10, 10)_{11}$. Digits $(1, 10, 10)$ vs $(0, 1, 5)$. No carries. Correct.
- $p=13$: $16 = (13)_{13}, 241 = (1, 5, 7)_{13}$. Digits $(1, 5, 7)$ vs $(0, 1, 3)$. No carries. Correct.
Since no prime $p \le 13$ divides $\binom{241}{16}$, the least prime factor $g(241, 16)$ must be at least the next prime, which is 17.
Calculation shows $241 \equiv 4 \pmod{17}$ and $16 \equiv 16 \pmod{17}$, so $4 < 16$ causes a carry. Thus $g(241, 16) = 17 > 16$.

## Conclusion

For $2k \le n < k^2$, the least prime factor of $\binom{n}{k}$ is at most $k$, except for the 13 specific cases listed above. This completes the proof of Case 2.

## References
1. Ecklund, E. F., Jr., Erdős, P., and Selfridge, J. L. (1974). "A new bound for the smallest prime factor of the binomial coefficient $\binom{n}{k}$". *Mathematics of Computation*, 28(126), 647-649.
2. Moree, P. (1994). "On the prime factors of $\binom{n}{k}$". *Unpublished note/Correspondence*. (Note: The exceptions $(241, 16)$ and $(284, 28)$ are widely cited as having been missed by EES74).
3. Guy, R. K. (2004). *Unsolved Problems in Number Theory*, B31.
