import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace Erdos1094

open Nat

-- Efficient recursive check for a range of n
def check_range_impl (k n_curr count : ℕ) : Bool :=
  match count with
  | 0 => true
  | s + 1 => 
    let n := n_curr
    if (n.choose k).minFac <= n / k then
      check_range_impl k (n + 1) s
    else
      false

lemma check_range_impl_correct (k n_curr count : ℕ) (h : check_range_impl k n_curr count = true) :
    ∀ i, n_curr ≤ i → i < n_curr + count → (i.choose k).minFac ≤ i / k := by
  induction count generalizing n_curr with
  | zero => 
    intro i h1 h2
    simp only [Nat.add_zero] at h2
    exfalso; linarith
  | succ s ih =>
    intro i h1 h2
    rw [check_range_impl] at h
    by_cases h_cond : (n_curr.choose k).minFac ≤ n_curr / k
    · rw [if_pos h_cond] at h
      cases Nat.eq_or_lt_of_le h1 with
      | inl h_eq =>
        subst h_eq
        exact h_cond
      | inr h_lt =>
        apply ih (n_curr + 1) h i h_lt
        linarith
    · rw [if_neg h_cond] at h
      contradiction

def verify_range (k : ℕ) : Bool :=
  let limit := k.factorial + k
  let start := k * k
  if start > limit then true
  else check_range_impl k start (limit - start + 1)

lemma verify_range_correct (k : ℕ) (h : verify_range k = true) :
    ∀ n, k * k ≤ n → n ≤ k.factorial + k → (n.choose k).minFac ≤ n / k := by
  unfold verify_range at h
  by_cases h_start_gt : k * k > k.factorial + k
  · rw [if_pos h_start_gt] at h
    intro n h1 h2
    exfalso; linarith
  · rw [if_neg h_start_gt] at h
    intro n h1 h2
    have h_le : k * k ≤ k.factorial + k := le_of_not_gt h_start_gt
    apply check_range_impl_correct k (k * k) (k.factorial + k - k * k + 1) h n h1
    rw [← Nat.add_assoc, Nat.add_sub_cancel' h_le]
    linarith

lemma check_k4 (n : ℕ) (h_range : 16 ≤ n ∧ n ≤ 28) : 
  (n.choose 4).minFac ≤ n / 4 := by
  rcases h_range with ⟨h_ge, h_le⟩
  interval_cases n <;> native_decide

lemma check_k5 (n : ℕ) (h_range : 25 ≤ n ∧ n ≤ 125) : 
  (n.choose 5).minFac ≤ n / 5 := by
  rcases h_range with ⟨h_ge, h_le⟩
  interval_cases n <;> native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma check_k6 (n : ℕ) (h_range : 36 ≤ n ∧ n ≤ 726) (h_not_exc : (n, 6) ≠ (62, 6)) : 
  (n.choose 6).minFac ≤ n / 6 := by
  rcases h_range with ⟨h_ge, h_le⟩
  interval_cases n <;> first | contradiction | native_decide

set_option maxHeartbeats 0 in
set_option maxRecDepth 10000 in
lemma check_k7 (n : ℕ) (h_range : 49 ≤ n ∧ n ≤ 5047) : 
  (n.choose 7).minFac ≤ n / 7 := by
  rcases h_range with ⟨h_ge, h_le⟩
  interval_cases n <;> native_decide

theorem check_k8_small : verify_range 8 = true := by native_decide

theorem check_k9_small : verify_range 9 = true := by native_decide

theorem check_k10_small : verify_range 10 = true := by native_decide

theorem check_k11_small : verify_range 11 = true := by native_decide

end Erdos1094
