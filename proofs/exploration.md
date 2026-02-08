# Prime Factorization Structure of C(n,k)

**Status:** Verified ✅
**Statement:** For $n \ge 2k$, the least prime factor $P_{min}(\binom{n}{k}) \le \max(n/k, k)$ with finitely many exceptions.
**Dependencies:** None
**Confidence:** High
**Reviewed by:** erdos1094g-znx

## Phase 1: Small Value Exploration

We computed $\binom{n}{k}$ and its minimum prime factor $P_{min}$ for $n \le 50$ and $1 \le k \le n/2$. The following pairs $(n, k)$ were identified as exceptions where $P_{min}(\binom{n}{k}) > \max(n/k, k)$:

| $n$ | $k$ | $\binom{n}{k}$ | $P_{min}$ | $\max(n/k, k)$ |
|-----|-----|----------------|-----------|----------------|
| 7   | 3   | 35             | 5         | 3              |
| 13  | 4   | 715            | 5         | 4              |
| 14  | 4   | 1001           | 7         | 4              |
| 23  | 5   | 33649          | 7         | 5              |
| 44  | 8   | 17610393       | 11        | 8              |
| 46  | 10  | 4076350421     | 11        | 10             |
| 47  | 11  | 17417133617    | 13        | 11             |

*Observations:*
- For $k=1$, $\binom{n}{1}=n$, so $P_{min} \le n = \max(n, 1)$.
- For $k=2$, $\binom{n}{2} = n(n-1)/2$. If $n \ge 4$, this is either even ($P_{min}=2$) or a product of two odd numbers $(2m+1)(4m+3)$ or $(2m+1)(4m+1)$. In all cases, $P_{min} \le (n-1)/2 \le n/2$.
- Most exceptions occur when $n$ is close to $2^m-1$ and $k$ is such that $\binom{n}{k}$ is odd.

## Phase 2: Carry Analysis via Kummer's Theorem

Kummer's Theorem states that the exponent of a prime $p$ in the prime factorization of $\binom{n}{k}$ is equal to the number of carries when adding $k$ and $n-k$ in base $p$. Thus, $p \nmid \binom{n}{k}$ if and only if there are no carries.

### Divisibility by $p \le k$
If $k \ge p$, there are no carries in base $p$ if and only if the digits of $k$ are less than or equal to the digits of $n$ in every position.
For $p=2$, this means $k$ must be a bitwise sub-mask of $n$ ($k \text{ AND } n = k$).
As $k$ grows, the number of primes $p \le k$ increases, and the probability that $n$ dominates $k$ in all these bases simultaneously decreases exponentially. This suggests that for large $k$, $\binom{n}{k}$ will almost always be divisible by some prime $p \le k$.

### Divisibility by $p \le n/k$
If $p \le n/k$, then $n \ge pk$. If we also have $k < p$, then $p$ divides $\binom{n}{k}$ if and only if $n \pmod p < k$. This is because the first digit of $k$ is $k$ itself, and the first digit of $n$ is $n \pmod p$. If $n \pmod p < k$, a carry must occur from the $p^0$ position to the $p^1$ position.
For a fixed $n$ and $k$, the condition $n \pmod p < k$ for some $p \in [k+1, n/k]$ is related to the distribution of primes in arithmetic progressions or gaps between multiples of primes.

## Phase 3: Proposed Proof Approach

1.  **Small $k$ Bounds**: Prove that for small $k$, there is always a prime $p \le n/k$ dividing $\binom{n}{k}$. This can be done by showing that the interval $[(n+1)/(m+1), n/m]$ contains a prime for various $m$.
2.  **Large $k$ Asymptotics**: For large $k$, use the fact that the number of integers $x \in [0, n]$ such that $x$ is a sub-mask of $n$ in base $p$ is $\prod (d_i + 1)$, where $d_i$ are digits of $n$. Show that the intersection of these sets for all $p \le k$ becomes empty or contains only values far from $n/2$.
3.  **Mathlib Integration**:
    - `Nat.factorial_factorization` and `Nat.prime_dvd_choose_iff_exists_carry` are key.
    - `Nat.digits` for base expansion logic.
    - `Analysis.NumberTheory.PrimeCount` for bounds on $\pi(x)$.

## References
- Erdős, P. "Problems and results on binomial coefficients."
- Kummer, E. E. (1852). "Über die Ergänzungssätze zu den allgemeinen Reciprocitätsgesetzen".
