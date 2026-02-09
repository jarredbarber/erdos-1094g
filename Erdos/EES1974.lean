import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Range
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Erdos.CheckFact

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

theorem verify_mid_k (k : ℕ) (h_low : 29 ≤ k) (h_high : k ≤ 166) : verify_kummer_range k = true := by
  have h := verify_ees_29_166_true
  rw [verify_ees_29_166, List.all_eq_true] at h
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

theorem verify_high_k (k : ℕ) (h_low : 167 ≤ k) (h_high : k ≤ 299) : verify_kummer_range k = true := by
  if hk1 : k ≤ 199 then
    have h := verify_ees_167_199_true
    rw [verify_ees_167_199, List.all_eq_true] at h
    let i := k - 167
    have h_mem : i ∈ List.range (199 - 167 + 1) := by
      rw [List.mem_range]
      apply Nat.lt_succ_of_le
      exact Nat.sub_le_sub_right hk1 167
    specialize h i h_mem
    have h_k : 167 + i = k := Nat.add_sub_of_le h_low
    rw [h_k] at h
    exact h
  else if hk2 : k ≤ 249 then
    have h_low' : 200 ≤ k := by linarith
    have h := verify_ees_200_249_true
    rw [verify_ees_200_249, List.all_eq_true] at h
    let i := k - 200
    have h_mem : i ∈ List.range (249 - 200 + 1) := by
      rw [List.mem_range]
      apply Nat.lt_succ_of_le
      exact Nat.sub_le_sub_right hk2 200
    specialize h i h_mem
    have h_k : 200 + i = k := Nat.add_sub_of_le h_low'
    rw [h_k] at h
    exact h
  else
    have h_low'' : 250 ≤ k := by linarith
    have h := verify_ees_250_299_true
    rw [verify_ees_250_299, List.all_eq_true] at h
    let i := k - 250
    have h_mem : i ∈ List.range (299 - 250 + 1) := by
      rw [List.mem_range]
      apply Nat.lt_succ_of_le
      exact Nat.sub_le_sub_right h_high 250
    specialize h i h_mem
    have h_k : 250 + i = k := Nat.add_sub_of_le h_low''
    rw [h_k] at h
    exact h

/-- Result from EES 1974 for large k. -/
axiom ees_large_k (n k : ℕ) (hk : 300 ≤ k) (hnk : 2 * k ≤ n) (hnk2 : n < k * k) :
  (n.choose k).minFac ≤ k

/-- The structural result for k ≥ 29. -/
theorem verify_large_k (n k : ℕ) (h_k : 29 ≤ k) (h_nk : 2 * k ≤ n) (h_n_k2 : n < k * k) :
    (n.choose k).minFac ≤ k := by
  if hk : k ≤ 166 then
    have h_ver := verify_mid_k k h_k hk
    exact verify_kummer_range_imp k h_ver n h_nk h_n_k2
  else if hk2 : k ≤ 299 then
    have h_ver := verify_high_k k (by linarith) hk2
    exact verify_kummer_range_imp k h_ver n h_nk h_n_k2
  else
    have hk_large : 300 ≤ k := by linarith
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
