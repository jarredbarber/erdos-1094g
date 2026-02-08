import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Range
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Erdos1094

set_option linter.style.nativeDecide false

open Nat

/-- The exceptions for Case 2 ($2k \le n < k^2$) identified by EES 1974. -/
def ExceptionsCase2 : Finset (ℕ × ℕ) :=
  {(7, 3), (13, 4), (14, 4), (23, 5), (44, 8), (46, 10), (47, 10),
   (74, 10), (94, 10), (95, 10), (47, 11), (241, 16), (284, 28)}

/-- Helper to check if g(n, k) ≤ k. -/
def check_bound (n k : ℕ) : Bool :=
  (n.choose k).minFac ≤ k

/-- Helper to check if (n, k) is in the exception list. -/
def is_exception (n k : ℕ) : Bool :=
  (n, k) ∈ ExceptionsCase2

/-- The property we want to verify for finite ranges. -/
def case2_property (k : ℕ) : Bool :=
  let lower := 2 * k
  let upper := k * k
  List.range (upper - lower) |>.all fun i =>
    let n := lower + i
    check_bound n k || is_exception n k

/-- Verification for k ≤ 28. -/
theorem verify_small_k (k : ℕ) (hk : k ≤ 28) (hk2 : 2 * k < k * k) : case2_property k = true := by
  interval_cases k
  all_goals { native_decide }


/-- List of primes up to k. -/
def list_primes_le (k : ℕ) : List ℕ :=
  List.range (k + 1) |>.filter Nat.Prime

theorem mem_list_primes_le (k p : ℕ) : p ∈ list_primes_le k ↔ p.Prime ∧ p ≤ k := by
  simp [list_primes_le, List.mem_filter, List.mem_range, Nat.lt_succ_iff]
  apply and_comm

/-- Kummer check: returns true if there exists a prime p ≤ k such that p divides n.choose k. -/
def check_kummer_bound (n k : ℕ) : Bool :=
  (list_primes_le k).any fun p =>
    let sum_k := (Nat.digits p k).sum
    let sum_nk := (Nat.digits p (n - k)).sum
    let sum_n := (Nat.digits p n).sum
    decide (sum_n < sum_k + sum_nk)

theorem check_kummer_bound_imp_le (n k : ℕ) (h_nk : k ≤ n) (h_ck : check_kummer_bound n k = true) :
    (n.choose k).minFac ≤ k := by
  rw [check_kummer_bound, List.any_eq_true] at h_ck
  rcases h_ck with ⟨p, hp_mem, h_lt_bool⟩
  rw [mem_list_primes_le] at hp_mem
  rcases hp_mem with ⟨hp_prime, hp_le_k⟩
  have : Fact p.Prime := ⟨hp_prime⟩
  have h_lt : (Nat.digits p n).sum < (Nat.digits p k).sum + (Nat.digits p (n - k)).sum :=
    of_decide_eq_true h_lt_bool
  have h_kummer := sub_one_mul_padicValNat_choose_eq_sub_sum_digits (p := p) h_nk
  have h_diff : (Nat.digits p k).sum + (Nat.digits p (n - k)).sum - (Nat.digits p n).sum > 0 :=
    Nat.sub_pos_of_lt h_lt
  have h_pos : padicValNat p (n.choose k) > 0 := by
    rw [← h_kummer] at h_diff
    exact pos_of_mul_pos_right h_diff (Nat.zero_le _)
  have h_choose_pos : n.choose k ≠ 0 := Nat.choose_pos h_nk |>.ne'
  have h_dvd : p ∣ n.choose k := by
    rw [← Nat.pow_one p]
    refine (padicValNat_dvd_iff 1 (n.choose k)).mpr (Or.inr ?_)
    exact Nat.succ_le_of_lt h_pos
  exact Nat.le_trans (Nat.minFac_le_of_dvd hp_prime.two_le h_dvd) hp_le_k

/-- Check a range of n for a given k. -/
def verify_range_k (k : ℕ) : Bool :=
  List.range (k * k - 2 * k) |>.all fun i =>
    check_kummer_bound (2 * k + i) k

theorem verify_range_k_imp (k : ℕ) (h_verify : verify_range_k k = true) :
    ∀ n, 2 * k ≤ n → n < k * k → (n.choose k).minFac ≤ k := by
  intro n h_nk h_n_k2
  let idx := n - 2 * k
  have h_idx : idx < k * k - 2 * k := Nat.sub_lt_sub_right h_nk h_n_k2
  have h_mem : idx ∈ List.range (k * k - 2 * k) := List.mem_range.mpr h_idx
  rw [verify_range_k, List.all_eq_true] at h_verify
  specialize h_verify idx h_mem
  have h_n_eq : 2 * k + idx = n := Nat.add_sub_of_le h_nk
  rw [h_n_eq] at h_verify
  apply check_kummer_bound_imp_le n k _ h_verify
  linarith

/-- Combined verification for the range 29 ≤ k ≤ 166. -/
def verify_all_k_29_166 : Bool :=
  (List.range (166 - 29 + 1)).all fun i =>
    let k := 29 + i
    verify_range_k k

theorem verify_all_k_29_166_true : verify_all_k_29_166 = true := by
  native_decide

theorem verify_mid_k (k : ℕ) (h_low : 29 ≤ k) (h_high : k ≤ 166) : verify_range_k k = true := by
  have h := verify_all_k_29_166_true
  rw [verify_all_k_29_166, List.all_eq_true] at h
  let i := k - 29
  have h_range_len : 166 - 29 + 1 = 138 := by rfl
  have h_idx : i < 138 := by
    rw [← h_range_len]
    apply Nat.lt_succ_of_le
    apply Nat.sub_le_sub_right h_high
  have h_mem : i ∈ List.range (166 - 29 + 1) := by
    rw [h_range_len]
    exact List.mem_range.mpr h_idx
  specialize h i h_mem
  have h_k : 29 + i = k := Nat.add_sub_of_le h_low
  rw [h_k] at h
  exact h

/-- Result from EES 1974 for large k. -/
axiom ees_large_k (n k : ℕ) (hk : 167 ≤ k) (hnk : 2 * k ≤ n) (hnk2 : n < k * k) :
  (n.choose k).minFac ≤ k

/-- The structural result for k ≥ 29. -/
theorem verify_large_k (n k : ℕ) (h_k : 29 ≤ k) (h_nk : 2 * k ≤ n) (h_n_k2 : n < k * k) :
    (n.choose k).minFac ≤ k := by
  if hk : k ≤ 166 then
    have h_mid := verify_mid_k k h_k hk
    exact verify_range_k_imp k h_mid n h_nk h_n_k2
  else
    have hk_large : 167 ≤ k := by linarith
    exact ees_large_k n k hk_large h_nk h_n_k2

theorem ees_1974_case2_bound_internal (n k : ℕ) (h_nk : 2 * k ≤ n) (h_n_k2 : n < k * k)
    (h_not_exc : (n, k) ∉ ExceptionsCase2) : (n.choose k).minFac ≤ k := by
  by_cases hk : k ≤ 28
  · have h_lt : 2 * k < k * k := by
       apply lt_of_le_of_lt h_nk h_n_k2
    have h_prop := verify_small_k k hk h_lt
    unfold case2_property at h_prop
    rw [List.all_eq_true] at h_prop
    let idx := n - 2 * k
    have h_idx : idx < k * k - 2 * k := by
      apply Nat.sub_lt_sub_right h_nk h_n_k2
    have h_mem : idx ∈ List.range (k * k - 2 * k) := List.mem_range.mpr h_idx
    specialize h_prop idx h_mem
    simp only [Bool.or_eq_true] at h_prop
    have h_n_def : 2 * k + idx = n := Nat.add_sub_of_le h_nk
    rw [h_n_def] at h_prop
    cases h_prop with
    | inl h_bound =>
      unfold check_bound at h_bound
      exact decide_eq_true_iff.mp h_bound
    | inr h_exc_bool =>
      unfold is_exception at h_exc_bool
      have h_in : (n, k) ∈ ExceptionsCase2 := decide_eq_true_iff.mp h_exc_bool
      contradiction
  · have h_k_ge_29 : 29 ≤ k := by linarith
    exact verify_large_k n k h_k_ge_29 h_nk h_n_k2

end Erdos1094
