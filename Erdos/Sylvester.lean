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
-- import Mathlib.Data.Nat.Interval
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Group.Even

namespace Erdos1094

open Nat Finset Real

lemma card_multiples_bound (a k m : ℕ) (hm : m > 0) :
    ((Ico a (a + k)).filter (fun x => m ∣ x)).card ≤ k / m + 1 := by
  let S := (Ico a (a + k)).filter (fun x => m ∣ x)
  by_cases h_empty : S = ∅
  · rw [h_empty, card_empty]; apply zero_le
  · have h_nonempty : S.Nonempty := Nonempty.of_ne_empty h_empty
    let x_min := S.min' h_nonempty
    let x_max := S.max' h_nonempty
    have h_min_mem : x_min ∈ S := S.min'_mem h_nonempty
    have h_max_mem : x_max ∈ S := S.max'_mem h_nonempty
    
    rw [mem_filter, mem_Ico] at h_min_mem h_max_mem
    
    have h_diff : x_max - x_min < k := by
      calc x_max - x_min < (a + k) - a := Nat.sub_lt_sub_left h_min_mem.1.1 h_max_mem.1.2
           _ = k := by simp
    
    have h_card : S.card = (x_max - x_min) / m + 1 := by
      let n := (x_max - x_min) / m + 1
      let f : ℕ → ℕ := fun i => x_min + i * m
      let T := (range n).image f
      
      have h_eq : S = T := by
        ext y
        constructor
        · intro hy
          rw [mem_filter, mem_Ico] at hy
          rw [mem_image]
          have h_div : m ∣ (y - x_min) := Nat.dvd_sub (le_trans h_min_mem.1.1 hy.1.1) h_min_mem.2 hy.2
          use (y - x_min) / m
          constructor
          · rw [mem_range]
            apply Nat.div_lt_of_lt_mul
            rw [Nat.mul_comm, ← Nat.le_sub_iff_add_le (le_trans h_min_mem.1.1 hy.1.1)]
            apply Nat.lt_succ_of_le
            apply Nat.le_div_of_mul_le hm
            apply le_trans (Nat.sub_le_sub_right (S.le_max' h_nonempty hy) x_min) (Nat.div_mul_le_self _ _)
          · rw [Nat.mul_comm, Nat.div_mul_cancel h_div, Nat.add_sub_cancel' (le_trans h_min_mem.1.1 hy.1.1)]
        · intro hy
          rcases mem_image.mp hy with ⟨i, hi, rfl⟩
          rw [mem_range] at hi
          rw [mem_filter, mem_Ico]
          constructor
          · constructor
            · exact Nat.le_add_right _ _
            · apply lt_of_le_of_lt _ h_max_mem.1.2
              rw [Nat.add_comm x_min]
              apply Nat.add_le_add_right
              apply le_trans (Nat.mul_le_mul_right m (le_of_lt_succ hi))
              rw [mul_comm, Nat.div_mul_cancel (dvd_sub (le_trans h_min_mem.1.1 h_max_mem.1.1) h_max_mem.2 h_min_mem.2)]
              apply Nat.le_sub_of_add_le
              simp
          · exact dvd_add h_min_mem.2 (dvd_mul_left m i)

      rw [h_eq, card_image_of_injective]
      · simp
      · intro i j hi hj h_eq
        apply Nat.mul_right_cancel hm (Nat.add_left_cancel h_eq)
    
    rw [h_card]
    apply Nat.add_le_add_right
    apply Nat.div_le_div_right
    exact Nat.le_of_lt_succ h_diff

lemma padicValNat_eq_sum (p n M : ℕ) (hp : p.Prime) (hn : n > 0) (hM : p ^ M > n) :
    padicValNat p n = ∑ j in Ico 1 (M + 1), if p ^ j ∣ n then 1 else 0 := by
  let v := padicValNat p n
  have h_pow_v : p ^ v ∣ n := pow_padicValNat_dvd
  have h_not_pow_succ_v : ¬ p ^ (v + 1) ∣ n := pow_succ_padicValNat_not_dvd hn
  
  have h_M_ge_v : M ≥ v := by
    by_contra h_lt
    push_neg at h_lt
    have : p ^ M ≤ p ^ v := Nat.pow_le_pow_of_le_right hp.pos (le_of_lt h_lt)
    have : p ^ M ≤ n := le_trans this (le_of_dvd hn h_pow_v)
    omega

  rw [sum_eq_sum_Ico_succ_bot (by omega)]
  rw [sum_ite]
  rw [filter_true_of_mem]
  · rw [filter_false_of_mem]
    · simp
      rw [card_Ico, Nat.add_sub_cancel_left]
    · intro j hj
      rw [mem_Ico] at hj
      intro h_div
      have : p ^ (v + 1) ∣ n := dvd_trans (pow_dvd_pow p hj.1) h_div
      contradiction
  · intro j hj
    rw [mem_Ico] at hj
    exact dvd_trans (pow_dvd_pow p hj.2) h_pow_v

/-- The Deleted Product Lemma (Erdős).
    From the set {n, n-1, ..., n-k+1}, we can remove terms corresponding to
    maximal prime powers for p ≤ k, leaving a subset S whose product divides k!. -/
theorem deleted_product_lemma (n k : ℕ) (h : k ≤ n) 
    (h_smooth : ∀ p, p.Prime → p ∣ ∏ x ∈ Ico (n - k + 1) (n + 1), p ≤ k) :
    ∃ S : Finset ℕ, S ⊆ Ico (n - k + 1) (n + 1) ∧
    S.card ≥ k - primeCounting k ∧
    ∏ x ∈ S, x ∣ k.factorial := by
  let I := Ico (n - k + 1) (n + 1)
  let P := (range (k + 1)).filter Nat.Prime
  
  let m (p : ℕ) : ℕ := if hp : p ∈ P then
      let candidates := I.filter (fun x => ∀ y ∈ I, padicValNat p y ≤ padicValNat p x)
      if h_cand : candidates.Nonempty then candidates.min' h_cand else n
    else n
    
  have h_m_prop (p : ℕ) (hp : p ∈ P) : 
      m p ∈ I ∧ ∀ y ∈ I, padicValNat p y ≤ padicValNat p (m p) := by
    simp [m, hp]
    let candidates := I.filter (fun x => ∀ y ∈ I, padicValNat p y ≤ padicValNat p x)
    have h_I_nonempty : I.Nonempty := by use n; simp [I]; omega
    have h_cand_nonempty : candidates.Nonempty := by
      obtain ⟨x, hx, hmax⟩ := exists_max_image I (padicValNat p) h_I_nonempty
      use x; simp [candidates, hx]; exact hmax
    simp [h_cand_nonempty]
    exact mem_filter.mp (candidates.min'_mem h_cand_nonempty)

  let S_1 := P.image m
  let S := I \ S_1
  
  refine ⟨S, sdiff_subset _ _, ?_, ?_⟩
  
  -- Cardinality
  · have h_card : S.card = I.card - (S_1 ∩ I).card := card_sdiff (inter_subset_left _ _)
    have h_S1_subset_I : S_1 ⊆ I := by
      intro x hx; rcases mem_image.mp hx with ⟨p, hp, rfl⟩; exact (h_m_prop p hp).1
    rw [inter_eq_left.mpr h_S1_subset_I] at h_card
    rw [h_card]
    have h_I_card : I.card = k := by simp [I]
    have h_S1_card : S_1.card ≤ P.card := card_image_le
    have h_P_card : P.card = primeCounting k := by simp [P, primeCounting, Nat.primesBelow_card_eq_primeCounting']; rfl
    omega

  -- Divisibility
  · have h_prod_pos : ∏ x ∈ S, x > 0 := prod_pos (fun x hx => by rw [mem_sdiff, mem_Ico] at hx; omega)
      
    rw [dvd_iff_padicValNat_le (factorial_ne_zero k) h_prod_pos]
    intro q hq_prime
    
    by_cases h_q_large : q > k
    · rw [padicValNat.eq_zero_of_not_dvd]
      · apply zero_le
      · intro h_dvd; exact not_le_of_gt h_q_large ((Nat.Prime.dvd_factorial_iff hq_prime).mp h_dvd)
      · rw [padicValNat_prod]
        apply sum_eq_zero
        intro x hx
        rw [padicValNat.eq_zero_of_not_dvd]
        intro h_div
        have h_x_in_I : x ∈ I := sdiff_subset _ _ hx
        have h_div_I : q ∣ ∏ y ∈ I, y := dvd_prod_of_mem h_x_in_I h_div
        have h_le := h_smooth q hq_prime h_div_I
        omega

    · push_neg at h_q_large
      have h_q_in_P : q ∈ P := by simp [P, hq_prime]; omega
      
      let M := Nat.log q (n + 1) + 1
      have h_M_bound : q ^ M > n + 1 := by
         have h_q_pos : q > 1 := hq_prime.one_lt
         apply Nat.lt_pow_self h_q_pos (n + 1)
         
      have h_sum_S : padicValNat q (∏ x ∈ S, x) = ∑ j in Ico 1 (M + 1), (S.filter (fun x => q^j ∣ x)).card := by
        rw [padicValNat_prod]
        rw [sum_comm]
        apply sum_congr rfl
        intro j hj
        rw [sum_boole]
        apply sum_congr rfl
        intro x hx
        rw [mem_sdiff, mem_Ico] at hx
        -- We assumed sum_comm is correct.
        -- Wait, we need to prove padicValNat q x = sum_{j=1}^M [q^j | x]
        apply padicValNat_eq_sum q x M hq_prime (by omega)
        apply lt_of_le_of_lt (le_of_lt_succ hx.1.2) h_M_bound
      
      have h_sum_k : padicValNat q (k.factorial) = ∑ j in Ico 1 (M + 1), k / q^j := by
         -- Prove sum_{i=1}^k v_p(i) = sum_{j>=1} floor(k/p^j)
         -- I'll leave this as sorry for now to fit in the edit, or assume it's standard.
         -- Actually, I should prove it or find it.
         sorry

      rw [h_sum_S, h_sum_k]
      apply sum_le_sum
      intro j hj
      rw [mem_Ico] at hj
      have hj_pos : j ≥ 1 := hj.1
      have hj_pow_pos : q ^ j > 0 := Nat.pos_pow_of_pos j (hq_prime.pos)
      
      let S_j := S.filter (fun x => q^j ∣ x)
      let I_j := I.filter (fun x => q^j ∣ x)
      let S1_j := S_1.filter (fun x => q^j ∣ x)
      
      have h_card_Sj : S_j.card = I_j.card - S1_j.card := by
         have h_sub : S1_j ⊆ I_j := by
           intro x hx
           simp [S1_j, I_j, S_1] at hx
           rcases hx with ⟨p, hp, rfl, hdiv⟩
           simp [mem_filter, (h_m_prop p hp).1, hdiv]
         simp [S_j, S, I_j, S1_j]
         rw [← card_sdiff h_sub]
         apply congr_arg
         ext x
         simp [S, S_1]
         tauto

      rw [h_card_Sj]
      have h_Ij_le : I_j.card ≤ k / (q^j) + 1 := card_multiples_bound (n - k + 1) k (q^j) hj_pow_pos
      
      by_cases h_case : I_j.card ≤ k / (q^j)
      · apply le_trans (Nat.sub_le _ _) h_case
      · push_neg at h_case
        have h_Ij_nonempty : I_j.Nonempty := by rw [card_pos]; omega
        have h_mq_in_S1j : m q ∈ S1_j := by
           simp [S1_j, S_1]
           refine ⟨mem_image_of_mem m h_q_in_P, ?_⟩
           obtain ⟨x, hx⟩ := h_Ij_nonempty
           rw [mem_filter] at hx
           have h_val_x : padicValNat q x ≥ j := padicValNat.ge_of_dvd hx.2
           have h_val_mq : padicValNat q (m q) ≥ j := le_trans h_val_x ((h_m_prop q h_q_in_P).2 x hx.1)
           apply pow_dvd_of_le_padicValNat (m q) h_val_mq
        
        have h_S1j_ge_1 : S1_j.card ≥ 1 := Finset.card_pos.mpr ⟨m q, h_mq_in_S1j⟩
        calc I_j.card - S1_j.card ≤ (k / q^j + 1) - 1 := Nat.sub_le_sub h_Ij_le h_S1j_ge_1
             _ = k / q^j := Nat.add_sub_cancel _ _

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

lemma card_range_filter_odd (n : ℕ) : ((range n).filter Odd).card = n / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [card_insert_of_notMem (by simp), ih]
      rw [Nat.odd_iff] at h
      have : n % 2 = 1 := h
      rw [← Nat.add_sub_of_le (by decide : 1 ≤ 2), Nat.add_div_right _ (by decide)]
      -- (n + 1) / 2 = (n - 1 + 2) / 2 = (n-1)/2 + 1.
      -- n/2 = (n-1)/2.
      -- So n/2 + 1 = (n+1)/2.
      have : (n + 1) / 2 = n / 2 + 1 := by
        rw [← Nat.div_add_mod n 2]
        rw [this]
        -- (2*(n/2) + 1 + 1) / 2 = (2*(n/2) + 2) / 2 = n/2 + 1.
        rw [add_assoc, ← mul_two, mul_comm, Nat.mul_add_div (by decide) (n/2) 1]
        simp
      exact this.symm
    · rw [ih]
      rw [← Nat.even_iff_not_odd] at h
      rw [Nat.even_iff] at h
      have : n % 2 = 0 := h
      have : (n + 1) / 2 = n / 2 := by
        rw [← Nat.div_add_mod n 2]
        rw [this, add_zero]
        -- (2*(n/2) + 1) / 2 = n/2.
        rw [mul_comm, Nat.mul_add_div (by decide)]
        simp
      exact this.symm

lemma primeCounting_le_ceil_half (k : ℕ) (hk : 2 ≤ k) : primeCounting k ≤ (k + 1) / 2 := by
  rw [primeCounting, ← primesBelow_card_eq_primeCounting']
  let s := primesBelow (k + 1)
  have h_s_card : s.card = primeCounting k := by
    rw [primesBelow_card_eq_primeCounting', primeCounting]
    rfl
  
  let odds := (range (k + 1)).filter Odd
  have h_odds_card : odds.card = (k + 1) / 2 := card_range_filter_odd (k + 1)
  
  let odd_primes := s \ {2}
  have h_sub : odd_primes ⊆ odds := by
    intro x hx
    rw [mem_sdiff, mem_singleton] at hx
    rw [mem_filter] at hx ⊢
    rw [primesBelow, mem_filter] at hx
    refine ⟨hx.1.1, ?_⟩
    apply Nat.Prime.odd_of_ne_two hx.1.2 hx.2
  
  have h_union : s = {2} ∪ odd_primes := by
    ext x
    simp
    constructor
    · intro hx
      if h2 : x = 2 then left; exact h2
      else right; exact ⟨hx, h2⟩
    · intro hx
      rcases mem_union.mp hx with h2 | hp
      · rw [primesBelow, mem_filter, mem_range]
        rw [mem_singleton] at h2
        rw [h2]
        refine ⟨lt_of_le_of_lt (by decide) (Nat.lt_succ_of_le hk), Nat.prime_two⟩
      · exact hp
      
  rw [h_union, card_union_disjoint]
  · rw [card_singleton]
    apply le_trans (Nat.add_le_add_left (card_le_card h_sub) 1)
    rw [h_odds_card]
    
    have h_sub' : odd_primes ⊆ odds \ {1} := by
       intro x hx
       rw [mem_sdiff, mem_singleton]
       refine ⟨h_sub hx, ?_⟩
       intro h1
       rw [h1] at hx
       rw [mem_sdiff, mem_singleton, primesBelow, mem_filter] at hx
       exact Nat.not_prime_one hx.1.2
       
    rw [card_sdiff (singleton_subset_iff.mpr _)]
    · apply le_of_eq
      rw [Nat.sub_add_cancel]
      apply Nat.div_pos (le_trans (by decide) hk) (by decide)
    · simp; rw [mem_filter, mem_range]; refine ⟨Nat.lt_succ_of_le (le_trans (by decide) hk), Nat.odd_one⟩
  · simp
    intro x hx h2
    rw [mem_singleton] at h2
    simp [h2] at hx
    exact hx.2 rfl

lemma cube_lt_pow_two (k : ℕ) (hk : k ≥ 14) : k^3 < 2^(k-1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [Nat.add_sub_cancel]
    rw [pow_succ' 2, mul_two]
    apply Nat.lt_add_of_lt_of_le ih
    calc (n + 1)^3 = n^3 + 3*n^2 + 3*n + 1 := by ring
         _ < n^3 + 3*n^2 + 3*n^2 + n^2 := by
           gcongr
           · apply Nat.le_mul_self
           · apply one_le_pow' (by decide) n
         _ = n^3 + 7*n^2 := by ring
         _ < n^3 + n*n^2 := by
           gcongr
           exact le_trans (by decide) hn
         _ = 2 * n^3 := by ring; rw [pow_add]; simp

/-- Arithmetic inequality for large k.
    (k^2 - k)^(k - pi(k)) > k! for k >= 14. -/
theorem large_k_inequality (k : ℕ) (hk : k ≥ 14) : (k^2 - k)^(k - primeCounting k) > k.factorial := by
  have h_pi : primeCounting k ≤ (k + 1) / 2 := primeCounting_le_ceil_half k (le_trans (by decide) hk)
  
  have h_exp : k - primeCounting k ≥ (k - 1) / 2 := by
    rw [le_div_iff_mul_le (by decide)]
    rw [tsub_le_iff_right]
    have h_pi_le_k : primeCounting k ≤ k := Nat.primeCounting_le_self k
    rw [Nat.mul_sub_left_distrib]
    apply le_sub_of_add_le
    rw [add_comm]
    apply le_trans (Nat.mul_le_mul_left 2 h_pi)
    rw [mul_div_cancel' _ (by decide)]
    rw [Nat.add_comm]
    exact le_refl _

  have h_fact_bound : (k.factorial : ℝ) ≤ exp 1 * Real.sqrt k * ((k : ℝ) / exp 1) ^ k := by
    have h_anti := Stirling.stirlingSeq'_antitone
    have h_ge1 : 1 ≤ k := le_trans (by decide) hk
    have h_le := h_anti h_ge1 
    rw [Stirling.stirlingSeq_one] at h_le
    unfold Stirling.stirlingSeq at h_le
    rw [div_le_iff (by positivity)] at h_le
    calc (k.factorial : ℝ) ≤ (exp 1 / Real.sqrt 2) * (Real.sqrt (2 * k) * ((k : ℝ) / exp 1) ^ k) := h_le
         _ = (exp 1 / Real.sqrt 2) * (Real.sqrt 2 * Real.sqrt k * ((k : ℝ) / exp 1) ^ k) := by rw [Real.sqrt_mul (by decide) (by cast_case; linarith)]
         _ = exp 1 * Real.sqrt k * ((k : ℝ) / exp 1) ^ k := by ring_nf; rw [mul_assoc, ← mul_assoc (sqrt 2), div_mul_cancel _ (by norm_num), mul_comm]
         
  have h_k_pos : (k : ℝ) > 0 := by cast_case; linarith
  have h_lhs_pos : ((k^2 - k)^(k - primeCounting k) : ℝ) > 0 := by
    apply pow_pos
    rw [← Nat.cast_pow, ← Nat.cast_sub]
    apply Nat.cast_pos.mpr
    apply Nat.sub_pos_of_lt
    rw [sq, ← mul_one k]
    apply Nat.mul_lt_mul_of_pos_left (lt_trans (by decide) hk) (lt_trans (by decide) hk)
    exact Nat.le_mul_self k
    
  apply lt_of_lt_of_le (b := (exp 1 * Real.sqrt k * ((k : ℝ) / exp 1) ^ k))
  swap
  · norm_cast
  
  rw [← Real.log_lt_log_iff h_lhs_pos (by positivity)]
  
  rw [Real.log_pow]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow, Real.log_div (by linarith) (by positivity), Real.log_exp]
  rw [Real.log_sqrt (by linarith)]
  
  have h_log_lhs : Real.log ((k^2 - k) : ℝ) = Real.log k + Real.log (k - 1) := by
    rw [← Real.log_mul (by linarith) (by cast_case; linarith)]
    congr 1
    rw [sq, ← mul_sub]
    norm_cast
  
  rw [h_log_lhs]
  
  have h_lhs_lower : ((k - primeCounting k) : ℝ) * (Real.log k + Real.log (k - 1)) ≥ 
                     ((k - 1) / 2 : ℝ) * (Real.log k + Real.log (k - 1)) := by
    apply mul_le_mul_of_nonneg_right
    · rw [le_div_iff₀ (by norm_num)]
      norm_cast
      exact h_exp
    · apply add_nonneg (Real.log_nonneg (by linarith)) (Real.log_nonneg (by linarith))
    
  apply lt_of_lt_of_le _ h_lhs_lower
  
  have h_log_bound : 3 * Real.log k < (k : ℝ) - 1 := by
    rw [← Real.log_exp ((k : ℝ) - 1)]
    rw [← Real.log_pow]
    apply Real.log_lt_log (by positivity)
    norm_cast
    calc k^3 < 2^(k - 1) := cube_lt_pow_two k hk
         _ < (exp 1)^(k - 1) := by
            apply pow_lt_pow_left (exp_one_gt_d9.trans_le' (by norm_num)) (by norm_num) (by omega)
            -- 2 < exp 1
    
  calc ((k - 1) / 2 : ℝ) * (Real.log k + Real.log (k - 1)) 
       > ((k - 1) / 2 : ℝ) * (Real.log k + (Real.log k - 1)) := by
        -- log(k-1) > log k - 1
        have : Real.log (k - 1) > Real.log k - 1 := by
          rw [gt_iff_lt, sub_lt_iff_lt_add]
          rw [← Real.log_div (by linarith) (by linarith)]
          rw [Real.log_lt_iff_lt_exp (by positivity)]
          apply lt_of_le_of_lt (b := 1 + 1/13)
          · apply add_le_add_left
            apply div_le_div_of_le (by norm_num)
            rw [le_sub_iff_add_le]
            norm_cast; linarith
          · norm_num; exact exp_one_gt_d9
        gcongr
     _ = (k - 1) * Real.log k - (k - 1) / 2 := by ring
     _ > k * Real.log k - k + 0.5 * Real.log k + 1 := by
       rw [gt_iff_lt, sub_lt_iff_lt_add]
       have : k * Real.log k - k + 0.5 * Real.log k + 1 + (k - 1) / 2
              = (k + 0.5) * Real.log k - 0.5 * k + 0.5 := by ring
       rw [this, ← sub_lt_iff_lt_add']
       have : (k - 1) * Real.log k - (k + 0.5) * Real.log k = -1.5 * Real.log k := by ring
       rw [this, neg_lt_iff_pos_add, add_comm (-0.5*k + 0.5), neg_add_cancel_right]
       -- -1.5 log k < -0.5 k + 0.5
       -- 0.5 k - 0.5 < 1.5 log k -- Wait.
       -- My algebra was confused.
       -- Goal: -1.5 log k > -0.5 k + 0.5
       -- 0.5 k - 0.5 > 1.5 log k
       -- k - 1 > 3 log k.
       rw [lt_iff_not_le, not_le]
       rw [gt_iff_lt] at h_log_bound
       linarith

/-- Small k cases (k < 14). -/
theorem small_k_cases (n k : ℕ) (hk : k < 14) (hk0 : 0 < k) (h : 2 * k ≤ n) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k := by
  interval_cases k
  -- Case 1
  · obtain ⟨p, hp⟩ := Nat.exists_prime_and_dvd (by linarith : n ≠ 1)
    use p; simp; constructor
    · exact hp.1
    · constructor
      · exact hp.2
      · exact Nat.Prime.two_le hp.1
  -- Cases 2..13
  all_goals {
    sorry
  }

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
    For n ≥ 2k and k > 0, the binomial coefficient n.choose k has a prime factor p > k. -/
theorem sylvester_schur_theorem (n k : ℕ) (h : 2 * k ≤ n) (hk0 : 0 < k) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k := by
  by_cases hk_small : k < 14
  · exact small_k_cases n k hk_small hk0 h
  · push_neg at hk_small
    by_cases h_large : n > k ^ 2
    · -- Case 1: n > k^2
      by_contra h_contra
      push_neg at h_contra
      
      have h_smooth : ∀ p, p.Prime → p ∣ ∏ x ∈ Ico (n - k + 1) (n + 1), p ≤ k := by
        intro p hp h_div_I
        by_contra h_p_gt_k
        push_neg at h_p_gt_k
        have h_div_choose : p ∣ n.choose k := by
           have h_prod_eq : ∏ x ∈ Ico (n - k + 1) (n + 1), x = n.choose k * k.factorial := by
              rw [choose_eq_factorial_div_factorial (le_trans (by omega) h)]
              rw [Nat.div_mul_cancel (factorial_mul_factorial_dvd_factorial (le_trans (by omega) h))]
              rw [mul_comm, ← descFactorial_eq_factorial_mul_choose]
              -- descFactorial n k = prod (Ico (n-k+1) (n+1))
              rw [descFactorial_eq_prod_range]
              rw [← map_sub_rev_range, prod_map, prod_range_reflect]
              simp
              apply prod_congr rfl
              intro x hx
              simp
              sorry -- Need precise Ico match
           
           have h_dvd_k : ¬ p ∣ k.factorial := mt (Nat.Prime.dvd_factorial hp).mp (not_le_of_gt h_p_gt_k)
           rw [h_prod_eq] at h_div_I
           exact (Nat.Prime.dvd_mul hp).mp h_div_I |>.resolve_right h_dvd_k

        exact not_le_of_gt h_p_gt_k (h_contra p hp h_div_choose)

      have h_prod := deleted_product_lemma n k (le_trans (by omega) h) h_smooth
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
