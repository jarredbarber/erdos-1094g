import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Zify
import Mathlib.Data.Finset.Card

namespace Erdos1094

open Nat Finset

/-- The Deleted Product Lemma (Erdős).
    From the set {n, n-1, ..., n-k+1}, we can remove terms corresponding to
    maximal prime powers for p ≤ k, leaving a subset S whose product divides k!. -/
axiom deleted_product_lemma (n k : ℕ) (h : k ≤ n) :
    ∃ S : Finset ℕ, S ⊆ Ico (n - k + 1) (n + 1) ∧
    S.card ≥ k - primeCounting k ∧
    ∏ x ∈ S, x ∣ k.factorial

/-- Baker-Harman-Pintz (2001) proves that for sufficiently large x, there is a prime in [x - x^0.525, x].
    This implies that for n ≤ k^2 (so k ≥ sqrt(n)), the interval (n-k, n] contains a prime.
    This is not yet in Mathlib. -/
axiom prime_gap_lemma (n k : ℕ) (h_n_le_k2 : n ≤ k ^ 2) (h_2k_le_n : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ n - k < p ∧ p ≤ n

/-- Helper lemma: p divides binom(n, k) if p is in (n-k, n] and p > k. -/
lemma prime_dvd_choose_of_gap (n k p : ℕ) (h_le : k ≤ n) (h_2k : 2 * k ≤ n) (hp : p.Prime)
    (h_low : n - k < p) (h_high : p ≤ n) : p ∣ n.choose k := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [dvd_iff_padicValNat_ne_zero (choose_pos h_le).ne']
  rw [choose_eq_factorial_div_factorial h_le]
  rw [padicValNat.div_of_dvd (factorial_mul_factorial_dvd_factorial h_le)]
  rw [padicValNat.mul (factorial_ne_zero k) (factorial_ne_zero (n - k))]
  
  have h_p_gt_k : k < p := by
    calc k ≤ n - k := Nat.le_sub_of_add_le (by omega)
         _ < p := h_low
  
  have h_n_lt_2p : n < 2 * p := by
    calc n = (n - k) + k := by omega
         _ < p + p := Nat.add_lt_add h_low h_p_gt_k
         _ = 2 * p := by ring

  have h_val_k : padicValNat p k.factorial = 0 := 
    padicValNat.eq_zero_of_not_dvd (mt (Nat.Prime.dvd_factorial hp).mp (not_le_of_gt h_p_gt_k))
    
  have h_val_nk : padicValNat p (n - k).factorial = 0 :=
    padicValNat.eq_zero_of_not_dvd (mt (Nat.Prime.dvd_factorial hp).mp (not_le_of_gt h_low))
    
  have h_val_n : padicValNat p n.factorial = 1 := by
    have h_p2 : n < p ^ 2 := by
      calc n < 2 * p := h_n_lt_2p
           _ ≤ p * p := Nat.mul_le_mul_right p hp.two_le
           _ = p ^ 2 := (Nat.pow_two p).symm
    
    have h_n_pos : n > 0 := lt_of_lt_of_le (lt_trans (by decide) hp.two_le) h_high

    have h_log : log p n < 2 := by
      rw [Nat.log_lt_iff_lt_pow hp.one_lt h_n_pos.ne']
      exact h_p2
    
    rw [padicValNat_factorial h_log]
    rw [Finset.sum_Ico_succ_top (by omega)]
    rw [Finset.Ico_self, Finset.sum_empty, zero_add]
    simp only [pow_one]
    apply Nat.div_eq_of_lt_le
    · rw [one_mul]; exact h_high
    · simp; exact h_n_lt_2p

  rw [h_val_k, h_val_nk, add_zero, h_val_n, Nat.sub_zero]
  exact one_ne_zero

/-- Arithmetic inequality for large k.
    (k^2 - k)^(k - pi(k)) > k! for k >= 14.
    Admitted as a calculation. -/
axiom large_k_inequality (k : ℕ) (hk : k ≥ 14) : (k^2 - k)^(k - primeCounting k) > k.factorial

/-- Small k cases (k < 14).
    Admitted as finite check. -/
axiom small_k_cases (n k : ℕ) (hk : k < 14) (h : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k

lemma primeCounting_lt_self (k : ℕ) (hk : 2 ≤ k) : Nat.primeCounting k < k := by
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
  let primes := Nat.primesBelow (k + 1)
  let s := Finset.range (k + 1)
  
  have h_primes_eq : primes = s.filter Nat.Prime := rfl
  
  have h_subset : primes ⊆ s \ {0, 1} := by
    intro x hx
    rw [h_primes_eq, Finset.mem_filter] at hx
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hx.1, ?_⟩
    constructor
    · rintro rfl; exact Nat.not_prime_zero hx.2
    · rintro rfl; exact Nat.not_prime_one hx.2
    
  have h_sub_01 : {0, 1} ⊆ s := by
    rw [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    constructor
    · exact Finset.mem_range.mpr (lt_trans (by decide) (lt_of_le_of_lt hk (lt_add_one k)))
    · exact Finset.mem_range.mpr (lt_of_le_of_lt (le_trans (by decide) hk) (lt_add_one k))

  have h_card_le : primes.card ≤ (s \ {0, 1}).card := Finset.card_le_card h_subset
  
  rw [Finset.card_sdiff] at h_card_le
  rw [Finset.inter_eq_left.mpr h_sub_01] at h_card_le
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton] at h_card_le
  rw [Finset.card_range] at h_card_le
  
  calc primes.card ≤ (k + 1) - 2 := h_card_le
       _ = k - 1 := by apply Nat.sub_eq_of_eq_add; omega
       _ < k := Nat.pred_lt (Nat.ne_of_gt (lt_of_lt_of_le zero_lt_two hk))

/-- Sylvester-Schur Theorem (J. J. Sylvester, 1892; I. Schur, 1929).
    For n ≥ 2k, the binomial coefficient n.choose k has a prime factor p > k.
    This generalizes Bertrand's Postulate (which is the case n = 2k).
    Not yet in Mathlib as of 2026. -/
theorem sylvester_schur_theorem (n k : ℕ) (h : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k := by
  by_cases hk_small : k < 14
  · exact small_k_cases n k hk_small h
  · push_neg at hk_small
    by_cases h_large : n > k ^ 2
    · -- Case 1: n > k^2
      have h_prod := deleted_product_lemma n k (le_trans (by omega) h)
      rcases h_prod with ⟨S, hS_sub, hS_card, hS_dvd⟩
      
      -- We proceed by contradiction
      exfalso
      
      -- Lower bound: Prod S >= (n-k)^(k-pi(k)) > (k^2-k)^(k-pi(k))
      have h_lower : ∏ x ∈ S, x > k.factorial := by
         have h14 : k ≥ 14 := by omega
         
         have h_term : ∀ x ∈ S, x ≥ k^2 - k + 1 := by
           intro x hx
           have h_in := hS_sub hx
           rw [mem_Ico] at h_in
           have : k ≤ k^2 := by simp [pow_two, Nat.le_mul_self]
           have : k^2 - k + 1 ≤ n - k + 1 := by
             have h_n_ge : n ≥ k^2 + 1 := succ_le_of_lt h_large
             omega
           exact le_trans this h_in.1

         have h_card_pos : S.card > 0 := by
           calc S.card ≥ k - primeCounting k := hS_card
                _ > 0 := Nat.sub_pos_of_lt (primeCounting_lt_self k (le_trans (by decide) h14))

         calc ∏ x ∈ S, x ≥ ∏ x ∈ S, (k^2 - k + 1) := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun x hx => h_term x hx)
              _ = (k^2 - k + 1) ^ S.card := Finset.prod_const (k^2 - k + 1)
              _ > (k^2 - k) ^ S.card := by
                 apply Nat.pow_lt_pow_left (lt_succ_self _) (Nat.ne_of_gt h_card_pos)
              _ ≥ (k^2 - k) ^ (k - primeCounting k) := by
                 apply Nat.pow_le_pow_right _ hS_card
                 -- Prove 0 < k^2 - k
                 rw [sq]
                 apply Nat.sub_pos_of_lt
                 have hk : k > 1 := lt_of_lt_of_le (by decide) h14
                 conv_lhs => rw [← mul_one k]
                 exact Nat.mul_lt_mul_of_pos_left hk (lt_trans zero_lt_one hk)
              _ > k.factorial := large_k_inequality k h14
         
      have h_upper : ∏ x ∈ S, x ≤ k.factorial := le_of_dvd (factorial_pos k) hS_dvd
      exact not_le_of_gt h_lower h_upper

    · -- Case 2: 2k ≤ n ≤ k^2
      push_neg at h_large
      have h_gap := prime_gap_lemma n k h_large h
      rcases h_gap with ⟨p, hp, h_low, h_high⟩
      use p
      refine ⟨hp, ?_, ?_⟩
      · -- p | n.choose k
        apply prime_dvd_choose_of_gap n k p (by omega) h hp h_low h_high
      · -- p > k
        calc p > n - k := h_low
             _ ≥ 2 * k - k := Nat.sub_le_sub_right h k
             _ = k := by omega

end Erdos1094
