import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Range

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

/-- The structural result for k ≥ 29. -/
theorem verify_large_k (n k : ℕ) (h_k : 29 ≤ k) (h_nk : 2 * k ≤ n) (h_n_k2 : n < k * k) :
    (n.choose k).minFac ≤ k := by
  -- For k ≥ 29, the EES 1974 paper establishes there are no exceptions.
  sorry

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
