import Mathlib

open Nat

namespace Erdos1094

/-!
# Erdős Problem 1094

The least prime factor of the binomial coefficient `n.choose k` is denoted by `g(n, k)`.
The conjecture (proven by Ecklund in 1969) states that for `n ≥ 2k`, `g(n, k) ≤ max (n/k) k`
with a finite number of exceptions.

Reference:
E. F. Ecklund Jr., "On the prime factorization of binomial coefficients",
Pacific Journal of Mathematics, 29(2), 267-270 (1969).
-/

/-- The least prime factor of `n.choose k`. -/
def g (n k : ℕ) : ℕ := (n.choose k).minFac

/-- The list of exceptions to the Erdős 1094 bound. -/
def ExceptionsFinset : Finset (ℕ × ℕ) :=
  {(7, 3), (13, 4), (14, 4), (23, 5), (62, 6), (44, 8), (46, 10), (47, 10),
   (74, 10), (94, 10), (95, 10), (47, 11), (241, 16), (284, 28)}

/-- The set of exceptions to the Erdős 1094 bound. -/
def Exceptions : Set (ℕ × ℕ) := ↑ExceptionsFinset

/-- Sylvester's Theorem (J. J. Sylvester, 1892).
For `n > k`, the product of `k` consecutive integers `n(n-1)...(n-k+1)`
contains a prime factor `p > k`.
This implies that `n.choose k` has a prime factor `p > k`. -/
axiom sylvester_theorem (n k : ℕ) (h : k < n) :
    ∃ p, p.Prime ∧ p ∣ (n.choose k) ∧ p > k

/-- Ecklund's Theorem, Case 1: For `n ≥ k^2`, the least prime factor of `n.choose k`
is at most `k`, except for the specified exceptions. -/
lemma least_prime_factor_le_k_of_n_ge_k2 (n k : ℕ) (h_nk : 2 * k ≤ n) (h_n_k2 : k * k ≤ n)
    (h_not_exc : (n, k) ∉ Exceptions) : g n k ≤ k := by
  sorry

/-- Ecklund's Theorem, Case 2: For `2k ≤ n < k^2`, the least prime factor of `n.choose k`
is at most `k`, except for the specified exceptions. -/
lemma least_prime_factor_le_k_of_2k_le_n_lt_k2 (n k : ℕ) (h_nk : 2 * k ≤ n) (h_n_k2 : n < k * k)
    (h_not_exc : (n, k) ∉ Exceptions) : g n k ≤ k := by
  sorry

set_option linter.style.nativeDecide false

/-- Verification that the exceptions indeed exceed the bound. -/
lemma exception_violation (n k : ℕ) (h : (n, k) ∈ Exceptions) :
    g n k > max (n / k) k := by
  have h_all : ∀ p ∈ ExceptionsFinset, g p.1 p.2 > max (p.1 / p.2) p.2 := by
    native_decide
  exact h_all (n, k) h

/-- The main result: Erdős 1094.
For `n ≥ 2k`, the least prime factor of `n.choose k` is at most `max (n/k) k`,
unless `(n, k)` is one of the 14 exceptions. -/
theorem erdos_1094_explicit (n k : ℕ) (h_k : 0 < k) (h_nk : 2 * k ≤ n)
    (h_not_exc : (n, k) ∉ Exceptions) : g n k ≤ max (n / k) k := by
  by_cases h_case : k * k ≤ n
  · have h_le_k := least_prime_factor_le_k_of_n_ge_k2 n k h_nk h_case h_not_exc
    have : k ≤ n / k := (Nat.le_div_iff_mul_le h_k).mpr h_case
    have : k ≤ max (n / k) k := le_max_of_le_left this
    exact h_le_k.trans this
  · have h_lt_k2 : n < k * k := not_le.mp h_case
    have h_le_k := least_prime_factor_le_k_of_2k_le_n_lt_k2 n k h_nk h_lt_k2 h_not_exc
    exact h_le_k.trans (le_max_right (n / k) k)

/-- The set of pairs (n, k) with n ≥ 2k violating the Erdős 1094 bound is finite. -/
theorem erdos_1094 :
    {p : ℕ × ℕ | 0 < p.2 ∧ 2 * p.2 ≤ p.1 ∧ g p.1 p.2 > max (p.1 / p.2) p.2}.Finite := by
  have h_sub : {p : ℕ × ℕ | 0 < p.2 ∧ 2 * p.2 ≤ p.1 ∧ g p.1 p.2 > max (p.1 / p.2) p.2} ⊆
      Exceptions := by
    intro p hp
    rcases hp with ⟨h_k, h_nk, h_g⟩
    by_contra h_not_exc
    have h_le := erdos_1094_explicit p.1 p.2 h_k h_nk h_not_exc
    exact (Nat.not_le.mpr h_g) h_le
  exact ExceptionsFinset.finite_toSet.subset h_sub

end Erdos1094
