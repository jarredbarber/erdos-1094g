import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factorization.Basic

namespace Erdos1094

open Nat

/-- Sylvester-Schur Theorem (J. J. Sylvester, 1892; I. Schur, 1929).
    For n ≥ 2k, the binomial coefficient n.choose k has a prime factor p > k.
    This generalizes Bertrand's Postulate (which is the case n = 2k).
    Not yet in Mathlib as of 2026. -/
axiom sylvester_schur_theorem (n k : ℕ) (h : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k

/-- Sylvester's Theorem (J. J. Sylvester, 1892).
For `n ≥ 2k`, the product of `k` consecutive integers `n(n-1)...(n-k+1)`
contains a prime factor `p > k`.
This implies that `n.choose k` has a prime factor `p > k`.
Note: The theorem requires `k > 0` for the prime factor to exist (as `n.choose 0 = 1`). -/
theorem sylvester_theorem (n k : ℕ) (h : 2 * k ≤ n) (hk : 0 < k) :
    ∃ p, p.Prime ∧ p ∣ (n.choose k) ∧ p > k := by
  by_cases h_eq : n = 2 * k
  · -- Case 1: n = 2k (Bertrand's Postulate)
    subst h_eq
    have h_bert : ∃ p, p.Prime ∧ k < p ∧ p ≤ 2 * k :=
      Nat.exists_prime_lt_and_le_two_mul k (Nat.ne_of_gt hk)
    rcases h_bert with ⟨p, hp, hkp, hp2k⟩
    use p
    refine ⟨hp, ?_, hkp⟩
    -- p divides (2k)! because p ≤ 2k.
    have hp_dvd_2k_fact : p ∣ (2 * k)! := hp.dvd_factorial.mpr hp2k
    -- p does not divide k! because p > k.
    have hp_not_dvd_k_fact : ¬ p ∣ k.factorial := mt hp.dvd_factorial.mp (not_le_of_gt hkp)
    -- (2k).choose k * (k! * k!) = (2k)!
    have h_choose_eq : (2 * k).choose k * k.factorial * k.factorial = (2 * k)! := by
      rw [two_mul]
      convert choose_mul_factorial_mul_factorial (Nat.le_add_left k k)
      simp
    rw [← h_choose_eq] at hp_dvd_2k_fact
    -- p | ((choose * k!) * k!) implies p | (choose * k!) or p | k!
    rw [hp.dvd_mul] at hp_dvd_2k_fact
    cases hp_dvd_2k_fact with
    | inl h =>
      -- p | (choose * k!) implies p | choose or p | k!
      rw [hp.dvd_mul] at h
      cases h with
      | inl h_final => exact h_final
      | inr h_bad => contradiction
    | inr h_bad => contradiction
  · -- Case 2: n > 2k
    have h_gt : 2 * k < n := lt_of_le_of_ne h (Ne.symm h_eq)
    have h_nk : k < n := calc
      k = 1 * k := (one_mul k).symm
      _ < 2 * k := mul_lt_mul_of_pos_right one_lt_two hk
      _ < n := h_gt
    exact sylvester_schur_theorem n k (le_of_lt h_gt)

end Erdos1094
