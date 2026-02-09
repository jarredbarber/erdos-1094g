import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

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
    unfold check_range_impl at h
    split at h
    next h_cond =>
      cases Nat.eq_or_lt_of_le h1 with
      | inl h_eq =>
        subst h_eq
        exact of_decide_eq_true h_cond
      | inr h_lt =>
        apply ih (n_curr + 1) h i h_lt
        linarith
    next => contradiction

def verify_range (k : ℕ) : Bool :=
  let limit := k.factorial + k
  let start := k * k
  if start > limit then true
  else check_range_impl k start (limit - start + 1)

lemma verify_range_correct (k : ℕ) (h : verify_range k = true) :
    ∀ n, k * k ≤ n → n ≤ k.factorial + k → (n.choose k).minFac ≤ n / k := by
  unfold verify_range at h
  split at h
  next h_start_gt =>
    intro n h1 h2
    exfalso; linarith
  next h_start_le =>
    intro n h1 h2
    apply check_range_impl_correct k (k * k) (k.factorial + k - k * k + 1) h n h1
    linarith

theorem check_k8_small : verify_range 8 = true := by native_decide
theorem check_k9_small : verify_range 9 = true := by native_decide
theorem check_k10_small : verify_range 10 = true := by native_decide

end Erdos1094
