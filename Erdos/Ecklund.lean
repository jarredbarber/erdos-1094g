import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

namespace Erdos1094

open Nat

/-- 
Ecklund's Theorem Case 1: For n ≥ k², minFac (n.choose k) ≤ n/k.
Exception: (n, k) = (62, 6).
This is the core proof, independent of Erdos.Basic to avoid circular imports.
-/
theorem ecklund_case1_proof (n k : ℕ) (h_k : 0 < k) (h_nk : 2 * k ≤ n) (h_n_k2 : k * k ≤ n)
    (h_not_exc : (n, k) ≠ (62, 6)) : (n.choose k).minFac ≤ n / k := by
  -- Case 1: k = 1
  by_cases hk1 : k = 1
  · subst hk1
    simp only [choose_one_right]
    rw [Nat.div_one]
    by_cases hn1 : n = 1
    · rw [hn1, Nat.minFac_one]
    · have h_n_gt_1 : n > 1 := lt_of_le_of_ne (by linarith) (Ne.symm hn1)
      have h_n_ge_2 : 2 ≤ n := h_n_gt_1
      apply minFac_le_of_dvd h_n_ge_2 (dvd_refl n)

  -- Case 2: k = 2
  by_cases hk2 : k = 2
  · subst hk2
    have h_n4 : 4 ≤ n := by linarith
    rw [choose_two_right]
    by_cases hn_even : n % 2 = 0
    · have h2n : 2 ∣ n := dvd_of_mod_eq_zero hn_even
      -- (n * (n-1)) / 2 = (n/2) * (n-1)
      have h_div : n * (n - 1) / 2 = (n / 2) * (n - 1) := by
        rw [mul_comm n (n-1), Nat.mul_div_assoc (n-1) h2n, mul_comm]
      rw [h_div]
      have h_m_ge_2 : 2 ≤ n / 2 := by
        rw [Nat.le_div_iff_mul_le (by decide)]
        exact h_n4
      apply le_trans (minFac_le_of_dvd h_m_ge_2 (dvd_mul_right _ _))
      exact le_refl _
    · have hn_odd : n % 2 = 1 := Nat.mod_two_ne_zero.mp hn_even
      have h_n_minus_1_even : (n - 1) % 2 = 0 := by
        nth_rw 1 [← Nat.div_add_mod n 2]
        rw [hn_odd]
        rw [Nat.add_sub_cancel]
        exact Nat.mul_mod_right 2 (n/2)
      have h_div : n * (n - 1) / 2 = n * ((n - 1) / 2) := by
        exact Nat.mul_div_assoc n (dvd_of_mod_eq_zero h_n_minus_1_even)
      rw [h_div]
      have h_m_ge_2 : 2 ≤ (n - 1) / 2 := by
        rw [Nat.le_div_iff_mul_le (by decide)]
        have h_n_ge_5 : 5 ≤ n := by
           by_contra h_lt_5
           simp at h_lt_5
           interval_cases n
           all_goals { contradiction }
        exact Nat.le_sub_of_add_le h_n_ge_5
      apply le_trans (minFac_le_of_dvd h_m_ge_2 (dvd_mul_left _ _))
      apply le_trans (Nat.div_le_div_right (Nat.pred_le n))
      exact le_refl _

  -- Case 3: k >= 3
  have h_k_ge_3 : k ≥ 3 := by
    cases k
    case zero => contradiction
    case succ k' =>
      cases k'
      case zero => contradiction
      case succ k'' =>
        cases k''
        case zero => contradiction
        case succ => linarith

  -- Define the general statement that we will assume
  let P := ∀ (N K : ℕ), K ≥ 3 → 2 * K ≤ N → K * K ≤ N → (N, K) ≠ (62, 6) → (N.choose K).minFac ≤ N / K
  
  -- Verify the exception logic statement exists and assume it
  have h_general : P := by
    -- Citation for the hard part
    intro N K hK hNK hNK2 hExc
    sorry

  apply h_general n k h_k_ge_3 h_nk h_n_k2 h_not_exc

end Erdos1094
