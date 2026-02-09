import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.List.Range
import Mathlib.NumberTheory.Padics.PadicVal.Basic

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

/-- Check a range of n for a given k (EES Case 2). -/
def verify_kummer_range (k : ℕ) : Bool :=
  List.range (k * k - 2 * k) |>.all fun i =>
    check_kummer_bound (2 * k + i) k

theorem verify_kummer_range_imp (k : ℕ) (h_verify : verify_kummer_range k = true) :
    ∀ n, 2 * k ≤ n → n < k * k → (n.choose k).minFac ≤ k := by
  intro n h_nk h_n_k2
  let idx := n - 2 * k
  have h_idx : idx < k * k - 2 * k := Nat.sub_lt_sub_right h_nk h_n_k2
  have h_mem : idx ∈ List.range (k * k - 2 * k) := List.mem_range.mpr h_idx
  rw [verify_kummer_range, List.all_eq_true] at h_verify
  specialize h_verify idx h_mem
  have h_n_eq : 2 * k + idx = n := Nat.add_sub_of_le h_nk
  rw [h_n_eq] at h_verify
  apply check_kummer_bound_imp_le n k _ h_verify
  linarith

/-- Combined verification for k ∈ [29, 166]. -/
def verify_ees_29_166 : Bool :=
  (List.range (166 - 29 + 1)).all fun i =>
    let k := 29 + i
    verify_kummer_range k

theorem verify_ees_29_166_true : verify_ees_29_166 = true := by
  native_decide

/-- Combined verification for k ∈ [167, 199]. -/
def verify_ees_167_199 : Bool :=
  (List.range (199 - 167 + 1)).all fun i =>
    let k := 167 + i
    verify_kummer_range k

theorem verify_ees_167_199_true : verify_ees_167_199 = true := by
  native_decide

/-- Combined verification for k ∈ [200, 249]. -/
def verify_ees_200_249 : Bool :=
  (List.range (249 - 200 + 1)).all fun i =>
    let k := 200 + i
    verify_kummer_range k

theorem verify_ees_200_249_true : verify_ees_200_249 = true := by
  native_decide

/-- Combined verification for k ∈ [250, 299]. -/
def verify_ees_250_299 : Bool :=
  (List.range (299 - 250 + 1)).all fun i =>
    let k := 250 + i
    verify_kummer_range k

theorem verify_ees_250_299_true : verify_ees_250_299 = true := by
  native_decide

end Erdos1094
