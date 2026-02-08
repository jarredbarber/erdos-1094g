# Erdős Problem 1094: Least Prime Factor of Binomial Coefficients

This repository contains a formal verification of Erdős Problem 1094 in Lean 4.

## Problem Statement

The problem concerns the least prime factor of the binomial coefficient $\binom{n}{k}$, denoted $g(n, k)$.
Erdős conjectured (and it was subsequently proved) that for all $n \ge 2k$, the least prime factor satisfies:

$$ g(n, k) \le \max(n/k, k) $$

with only finitely many exceptions.

**Formal Statement:**
```lean
theorem erdos_1094 :
    {(n, k) : ℕ × ℕ | 0 < k ∧ 2 * k ≤ n ∧ (n.choose k).minFac > max (n / k) k}.Finite
```

## Proof Architecture (In Progress)

The proof establishes the result by enumerating the finite set of exceptions and handling the remaining cases via theorems derived from established number theory results.

1.  **Exception Enumeration**: We define the set of 14 known exceptions.
2.  **Case Split**: The problem is split into two regions:
    *   **Case 1**: $n \ge k^2$
    *   **Case 2**: $2k \le n < k^2$
3.  **Bounds**: We are formalizing three key results to bound $g(n, k)$ in each region.

## Key Theorems

The proof relies on the following theorems (formalization in progress):

1.  **Ecklund's Theorem (1969)**: Handles Case 1 ($n \ge k^2$).
    *   *Statement*: $g(n, k) \le n/k$ for $n \ge k^2$, with the single exception $(62, 6)$.

2.  **EES Theorem (1974)**: Handles Case 2 ($2k \le n < k^2$).
    *   *Statement*: $g(n, k) \le k$ for $2k \le n < k^2$, excluding specific exceptions.
    *   *Approach*: Computational verification for small $k$ (completed), structural proof for large $k$ (in progress).

3.  **Sylvester's Theorem (1892)**:
    *   *Statement*: For $n \ge 2k$, $\binom{n}{k}$ has a prime factor $p > k$.

## The 14 Exceptions

The theorem holds for all pairs $(n, k)$ with $n \ge 2k$ except for the following 14 exceptions:

*   (7, 3)
*   (13, 4), (14, 4)
*   (23, 5)
*   (62, 6)
*   (44, 8)
*   (46, 10), (47, 10), (74, 10), (94, 10), (95, 10)
*   (47, 11)
*   (241, 16)
*   (284, 28)

## Build and Verification

To build the project:

```bash
lake build
```

## AI Attribution

This repository was produced autonomously by **Gemini 3 Pro** acting as an agentic coder, coordinated via the **tm** (Task Manager) system.

## Comparison

A parallel attempt by **Claude** (in the `erdos-1094` repository) took a "from-first-principles" approach. This project aims to formalize the necessary number-theoretic results directly in Lean.
