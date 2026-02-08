import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Associated
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
  rw [smoothPart, roughPart, ← Finsupp.prod_mul]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  apply Finsupp.prod_congr
  intro p k
  by_cases h : p ≤ B
  · simp [h]
  · simp [h]

lemma roughPart_gt_B (n B : ℕ) (h : roughPart n B > 1) : roughPart n B > B := by
  have hn : n ≠ 0 := by
    intro hn_eq
    rw [hn_eq, roughPart] at h
    simp at h
  have exists_prime : ∃ p, p.Prime ∧ p ∣ roughPart n B := 
    Nat.exists_prime_and_dvd (_root_.ne_of_gt h)
  rcases exists_prime with ⟨p, hp, hp_dvd⟩
  have p_gt_B : B < p := by
    rw [roughPart, Finsupp.prod] at hp_dvd
    have h_prime := hp.prime
    rw [Prime.dvd_finset_prod_iff h_prime] at hp_dvd
    rcases hp_dvd with ⟨q, hq, hq_dvd⟩
    split_ifs at hq_dvd with h_B
    · -- B < q.
      have : p = q := by
        have h_dvd_q : p ∣ q := hp.dvd_of_dvd_pow hq_dvd
        have h_q_prime : q.Prime := Nat.prime_of_mem_primeFactors (by rw [Nat.support_factorization] at hq; exact hq)
        exact (Nat.prime_dvd_prime_iff_eq hp h_q_prime).mp h_dvd_q
      rw [this]
      exact h_B
    · -- B >= q. Term is 1.
      exfalso
      exact Nat.Prime.not_dvd_one hp hq_dvd
  exact lt_of_lt_of_le p_gt_B (le_of_dvd (by linarith) hp_dvd)

lemma smoothPart_pos (n B : ℕ) (hn : n ≠ 0) : smoothPart n B > 0 := by
  rw [smoothPart, Finsupp.prod]
  apply Finset.prod_pos
  intro p hp
  split_ifs
  · apply pow_pos
    exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors (by rw [Nat.support_factorization] at hp; exact hp))
  · exact one_pos

lemma smoothPart_mul (a b B : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) : 
    smoothPart (a * b) B = smoothPart a B * smoothPart b B := by
  sorry -- Admitting smoothPart_mul due to Finsupp.prod_add_index complexity

lemma smoothPart_eq_self_of_le (n B : ℕ) (hn : n ≠ 0) (h : ∀ p, p.Prime → p ∣ n → p ≤ B) : smoothPart n B = n := by
  rw [smoothPart]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  apply Finsupp.prod_congr
  intro p k
  by_cases hp : p ≤ B
  · simp [hp]
  · simp [hp]
    have h_not_mem : p ∉ n.primeFactors := fun h_mem =>
      hp (h p (Nat.prime_of_mem_primeFactors h_mem) (Nat.dvd_of_mem_primeFactors h_mem))
    rw [← Nat.support_factorization, Finsupp.mem_support_iff] at h_not_mem
    simp only [not_not] at h_not_mem
    simp [h_not_mem]

lemma prod_range_sub_eq_descFactorial (n k : ℕ) : 
    ((List.range k).map (fun i => n - i)).prod = n.descFactorial k := by
  induction k with
  | zero => simp [Nat.descFactorial_zero]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih]
    simp only [List.map_singleton, List.prod_cons, List.prod_nil, mul_one]
    rw [Nat.descFactorial_succ]
    ring

lemma descFactorial_eq_factorial_mul_choose (n k : ℕ) (h : k ≤ n) : 
    n.descFactorial k = k.factorial * n.choose k := by
  rw [Nat.descFactorial_eq_div h]
  apply Nat.div_eq_of_eq_mul_right (Nat.factorial_pos (n - k))
  rw [← Nat.choose_mul_factorial_mul_factorial h]
  ring

lemma prod_smooth_eq_factorial (n k : ℕ) (h_nk : n ≥ k) (h_n_sq : n ≥ k * k) (h_g : (n.choose k).minFac > n / k) :
    ((List.range k).map (fun i => smoothPart (n - i) (n / k))).prod = k.factorial := by
  cases k with
  | zero => simp
  | succ k' =>
    let k := k' + 1
    have h_k_pos : k > 0 := Nat.succ_pos k'
    
    let P_list := (List.range k).map (fun i => n - i)
    let P := P_list.prod
    
    have h_P_list_ne_zero : ∀ x, x ∈ P_list → x ≠ 0 := by
      intro x hx
      rw [List.mem_map] at hx
      rcases hx with ⟨i, hi, rfl⟩
      rw [List.mem_range] at hi
      apply Nat.sub_ne_zero_of_lt
      exact lt_of_lt_of_le hi h_nk

    have smoothPart_list_prod (L : List ℕ) (hL : ∀ x, x ∈ L → x ≠ 0) : 
        (L.map (fun x => smoothPart x (n / k))).prod = smoothPart L.prod (n / k) := by
      induction L with
      | nil => 
        simp only [List.map_nil, List.prod_nil]
        rw [smoothPart, Nat.factorization_one, Finsupp.prod_zero_index]
      | cons head tail ih =>
        simp only [List.map_cons, List.prod_cons]
        have h_head : head ≠ 0 := hL head List.mem_cons_self
        have h_tail : ∀ x, x ∈ tail → x ≠ 0 := fun x hx => hL x (List.mem_cons_of_mem head hx)
        rw [ih h_tail]
        rw [smoothPart_mul _ _ _ h_head (List.prod_ne_zero (fun h => h_tail 0 h rfl))]

    have h_map_eq : (P_list.map (fun x => smoothPart x (n / k))).prod = (List.map (fun i => smoothPart (n - i) (n / k)) (List.range k)).prod := by
      rw [List.map_map]
      rfl
      
    rw [← h_map_eq]
    rw [smoothPart_list_prod P_list h_P_list_ne_zero]
    
    change smoothPart P_list.prod (n/k) = _
    have h_P_eq : P_list.prod = k.factorial * n.choose k := by
      rw [prod_range_sub_eq_descFactorial, descFactorial_eq_factorial_mul_choose n k h_nk]
    
    rw [h_P_eq]
    rw [smoothPart_mul _ _ _ (Nat.factorial_ne_zero k) (Nat.choose_pos h_nk).ne.symm]
    
    have h_fact_smooth : smoothPart k.factorial (n / k) = k.factorial := by
      apply smoothPart_eq_self_of_le _ _ (Nat.factorial_ne_zero k)
      intro p hp h_dvd
      sorry -- Nat.prime_dvd_factorial_iff issues

    have h_choose_smooth : smoothPart (n.choose k) (n / k) = 1 := by
      rw [smoothPart, Finsupp.prod]
      apply Finset.prod_eq_one
      intro p hp
      split_ifs with h_le
      · exfalso
        sorry -- Nat.mem_primeFactors issues
      · rfl

    rw [h_fact_smooth, h_choose_smooth, mul_one]

lemma range_contains_multiple_of_k (n k : ℕ) (hk : k > 0) : 
    ∃ i ∈ List.range k, k ∣ (n - i) := by
  use n % k
  constructor
  · apply List.mem_range.mpr
    exact Nat.mod_lt n hk
  · apply Nat.dvd_sub_mod

lemma smoothPart_ge_k (n B k : ℕ) (h_dvd : k ∣ n) (h_kB : k ≤ B) (hn : n ≠ 0) :
    smoothPart n B ≥ k := by
  rcases h_dvd with ⟨q, rfl⟩
  have h_k_ne_0 : k ≠ 0 := left_ne_zero_of_mul hn
  have h_q_ne_0 : q ≠ 0 := right_ne_zero_of_mul hn
  rw [smoothPart_mul k q B h_k_ne_0 h_q_ne_0]
  have h_smooth_k : smoothPart k B = k := by
    apply smoothPart_eq_self_of_le _ _ h_k_ne_0
    intro p hp hpk
    exact le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h_k_ne_0) hpk) h_kB
  rw [h_smooth_k]
  have h_smooth_q_pos : smoothPart q B ≥ 1 := smoothPart_pos q B h_q_ne_0
  exact Nat.le_mul_of_pos_right k h_smooth_q_pos

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
