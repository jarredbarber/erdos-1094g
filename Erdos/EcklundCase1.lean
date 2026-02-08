import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace Erdos1094

open Nat

noncomputable def smoothPart (n B : ℕ) : ℕ :=
  n.factorization.prod (fun p k => if p ≤ B then p ^ k else 1)

noncomputable def roughPart (n B : ℕ) : ℕ :=
  n.factorization.prod (fun p k => if B < p then p ^ k else 1)

lemma smooth_mul_rough (n B : ℕ) (hn : n ≠ 0) : smoothPart n B * roughPart n B = n := by
  sorry

lemma roughPart_gt_B (n B : ℕ) (h : roughPart n B > 1) : roughPart n B > B := by
  have exists_prime : ∃ p, p.Prime ∧ p ∣ roughPart n B := 
    Nat.exists_prime_and_dvd (_root_.ne_of_gt h)
  rcases exists_prime with ⟨p, hp, hp_dvd⟩
  have p_gt_B : B < p := by
    sorry
  exact lt_of_lt_of_le p_gt_B (le_of_dvd (by linarith) hp_dvd)

lemma smoothPart_pos (n B : ℕ) (hn : n ≠ 0) : smoothPart n B > 0 := by
  sorry

lemma prod_smooth_eq_factorial (n k : ℕ) (h_nk : n ≥ k) (h_g : (n.choose k).minFac > n / k) :
    ((List.range k).map (fun i => smoothPart (n - i) (n / k))).prod = k.factorial := by
  sorry

lemma range_contains_multiple_of_k (n k : ℕ) (hk : k > 0) : 
    ∃ i ∈ List.range k, k ∣ (n - i) := by
  sorry

lemma smoothPart_ge_k (n B k : ℕ) (h_dvd : k ∣ n) (h_kB : k ≤ B) (hn : n ≠ 0) :
    smoothPart n B ≥ k := by
  sorry

lemma smoothPart_lt_k (n k i : ℕ) (h_nk : n ≥ k * k) (h_k : k > 0) 
    (h_i : i < k) (h_rough : roughPart (n - i) (n / k) > 1) :
    smoothPart (n - i) (n / k) < k := by
  let q := n / k
  have h_q_ge_k : q ≥ k := Nat.le_div_iff_mul_le (h_k) |>.mpr h_nk
  have h_q_pos : q > 0 := lt_of_lt_of_le h_k h_q_ge_k
  
  have h_ni_pos : n - i > 0 := by
    apply Nat.sub_pos_of_lt (lt_of_lt_of_le h_i (le_trans (Nat.le_mul_self k) h_nk))

  have h_rough_gt : roughPart (n - i) q > q := roughPart_gt_B (n - i) q h_rough
  have h_rough_ge : roughPart (n - i) q ≥ q + 1 := Nat.succ_le_of_lt h_rough_gt
  
  -- Use h_ni_pos for n - i != 0
  have h_ni_ne_0 : n - i ≠ 0 := _root_.ne_of_gt h_ni_pos
  -- Use h_rough_gt for roughPart != 0
  have h_rough_ne_0 : roughPart (n - i) q ≠ 0 := _root_.ne_of_gt (lt_trans (by linarith) h_rough_gt)
  
  rw [← Nat.mul_div_cancel_left (smoothPart (n - i) q) (Nat.pos_of_ne_zero h_rough_ne_0)]
  rw [mul_comm, smooth_mul_rough (n - i) q h_ni_ne_0]
  
  rw [Nat.div_lt_iff_lt_mul (lt_trans (pos_of_gt h_k) (lt_of_le_of_lt h_q_ge_k h_rough_gt))]
  
  calc n - i ≤ n := Nat.sub_le n i
       _ = q * k + n % k := by
         nth_rw 1 [← Nat.div_add_mod n k]
         ring
       _ < q * k + k := Nat.add_lt_add_left (Nat.mod_lt n h_k) (q * k)
       _ = k * (q + 1) := by rw [mul_add, mul_one, mul_comm]
       _ ≤ k * roughPart (n - i) q := Nat.mul_le_mul_left k h_rough_ge

end Erdos1094
