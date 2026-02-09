import Mathlib
import Erdos.Sylvester
import Erdos.Ecklund
import Erdos.EES1974

open Nat

namespace Erdos1094

/-!
# Erdős Problem 1094

The least prime factor of the binomial coefficient `n.choose k` is denoted by `g(n, k)`.
The conjecture (Erdős-Lacampagne-Selfridge, 1988) states that for `n ≥ 2k`,
`g(n, k) ≤ max (n/k) k` with only finitely many exceptions.

This is listed as an open problem at https://www.erdosproblems.com/1094

The proof strategy decomposes into cases using results of Ecklund (1969),
Erdős-Ecklund-Selfridge (1974), and the Sylvester-Schur theorem (1892).
-/

/-- The least prime factor of `n.choose k`. -/
def g (n k : ℕ) : ℕ := (n.choose k).minFac

/-- The list of exceptions to the Erdős 1094 bound. -/
def ExceptionsFinset : Finset (ℕ × ℕ) :=
  {(7, 3), (13, 4), (14, 4), (23, 5), (62, 6), (44, 8), (46, 10), (47, 10),
   (74, 10), (94, 10), (95, 10), (47, 11), (241, 16), (284, 28)}

/-- The set of exceptions to the Erdős 1094 bound. -/
def Exceptions : Set (ℕ × ℕ) := ↑ExceptionsFinset

/- Sylvester's Theorem (J. J. Sylvester, 1892).
For `n ≥ 2k`, the product of `k` consecutive integers `n(n-1)...(n-k+1)`
contains a prime factor `p > k`.
This implies that `n.choose k` has a prime factor `p > k`.
This theorem is now proved in `Erdos.Sylvester`. -/
-- axiom sylvester_theorem (n k : ℕ) (h : 2 * k ≤ n) :
--    ∃ p, p.Prime ∧ p ∣ (n.choose k) ∧ p > k

/-- Ecklund's Theorem, Case 1: For `n ≥ k^2`, the least prime factor of `n.choose k`
is at most `n / k`, except for the specified exceptions.
Note: Ecklund (1969) originally stated `g(n, k) ≤ n/k` for `n ≥ k^2` with no exceptions in this range,
but `(62, 6)` is a known counterexample (where `g = 19 > 62/6`). -/
theorem ecklund_1969_case1_bound (n k : ℕ) (h_k : 0 < k) (h_nk : 2 * k ≤ n) (h_n_k2 : k * k ≤ n)
    (h_not_exc : (n, k) ≠ (62, 6)) : g n k ≤ n / k := by
  apply Erdos1094.ecklund_case1_proof n k h_k h_nk h_n_k2 h_not_exc

/-- Ecklund's Theorem, Case 1: For `n ≥ k^2`, the least prime factor of `n.choose k`
is at most `n / k`, except for the specified exceptions. -/
lemma least_prime_factor_le_nk_of_n_ge_k2 (n k : ℕ) (h_k : 0 < k) (h_nk : 2 * k ≤ n) (h_n_k2 : k * k ≤ n)
    (h_not_exc : (n, k) ∉ Exceptions) : g n k ≤ n / k := by
  apply ecklund_1969_case1_bound n k h_k h_nk h_n_k2
  intro h_eq
  apply h_not_exc
  rw [Exceptions, Finset.mem_coe]
  refine Finset.mem_of_subset ?_ (Finset.mem_singleton.mpr h_eq)
  -- Show {(62, 6)} ⊆ ExceptionsFinset
  simp [ExceptionsFinset]

/-- Ecklund, Erdős, Selfridge (1974), Theorem 2, supplemented by Moree (1995).
    For $2k \le n < k^2$, $g(n, k) \le k$ unless $(n, k)$ is one of the 13 exceptions. -/
theorem ees_1974_case2_bound (n k : ℕ) (h_nk : 2 * k ≤ n) (h_n_k2 : n < k * k)
    (h_not_exc : (n, k) ∉ ExceptionsCase2) : g n k ≤ k :=
  ees_1974_case2_bound_internal n k h_nk h_n_k2 h_not_exc

/-- Ecklund's Theorem, Case 2: For `2k ≤ n < k^2`, the least prime factor of `n.choose k`
is at most `k`, except for the specified exceptions. -/
lemma least_prime_factor_le_k_of_2k_le_n_lt_k2 (n k : ℕ) (h_nk : 2 * k ≤ n) (h_n_k2 : n < k * k)
    (h_not_exc : (n, k) ∉ Exceptions) : g n k ≤ k := by
  apply ees_1974_case2_bound n k h_nk h_n_k2
  intro h_in
  apply h_not_exc
  rw [Exceptions, Finset.mem_coe]
  refine Finset.mem_of_subset ?_ h_in
  decide



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
  · have h_le_nk := least_prime_factor_le_nk_of_n_ge_k2 n k h_k h_nk h_case h_not_exc
    exact h_le_nk.trans (le_max_left (n / k) k)
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
