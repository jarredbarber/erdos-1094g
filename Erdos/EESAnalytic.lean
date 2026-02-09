import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Erdos.AnalyticBounds

noncomputable section

namespace Erdos1094

open Real Nat BigOperators

/-- Local helper for division inequality. -/
lemma div_lt_iff_local {a b c : ℝ} (hc : 0 < c) : a / c < b ↔ a < b * c := by
  rw [div_lt_iff₀ hc]

lemma le_div_iff_local {a b c : ℝ} (hc : 0 < c) : a ≤ b / c ↔ a * c ≤ b := by
  rw [le_div_iff₀ hc]

lemma lt_div_iff_local {a b c : ℝ} (hc : 0 < c) : a < b / c ↔ a * c < b := by
  rw [lt_div_iff₀ hc]

/-- The "expected number of solutions" E(k). -/
def E_val (k : ℕ) : ℝ :=
  (k : ℝ)^2 * ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
    if (p : ℝ) > (k : ℝ) / 2 then (2 - (k : ℝ) / p) else 1

/-- Delta p = k/p - 1. -/
def delta (k : ℕ) (p : ℕ) : ℝ := (k : ℝ) / (p : ℝ) - 1

/-- Standard inequality for log(1-x). -/
lemma log_one_sub_le (x : ℝ) (h1 : 0 ≤ x) (h2 : x < 1) :
  Real.log (1 - x) ≤ -x - x^2 / 2 := by
  let f := fun t => -t - t^2/2 - Real.log (1 - t)
  
  have h_deriv : ∀ t ∈ Set.Icc 0 x, HasDerivAt f (t^2 / (1 - t)) t := by
    intro t ht
    have ht_lt_1 : t < 1 := lt_of_le_of_lt ht.2 h2
    have ht_ne : 1 - t ≠ 0 := by linarith
    
    have d1 : HasDerivAt (fun y => -y) (-1) t := hasDerivAt_neg t
    
    have d2 : HasDerivAt (fun y => -y^2/2) (-t) t := by
      convert (hasDerivAt_pow 2 t).neg.div_const 2 using 1
      · simp
        ring
      
    have d3 : HasDerivAt (fun y => -Real.log (1 - y)) (1/(1-t)) t := by
      have sub_ne : 1 - t ≠ 0 := by linarith
      convert (hasDerivAt_log sub_ne).comp t ((hasDerivAt_id t).const_sub 1) |>.neg using 1
      · simp

    convert HasDerivAt.add (HasDerivAt.add d1 d2) d3 using 1
    · ext y
      simp [f]
      ring
    · field_simp [ht_ne]
      ring

  have h_mono : MonotoneOn f (Set.Icc 0 x) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x) 
      (fun t ht => (h_deriv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (h_deriv t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    simp at ht
    have ht_lt_1 : t < 1 := lt_trans ht.2 h2
    apply div_nonneg (sq_nonneg t) (sub_nonneg.mpr ht_lt_1.le)

  have h_eval : f 0 = 0 := by simp [f]
  have h_pos : 0 ≤ f x := by
    rw [← h_eval]
    apply h_mono
    · simp [h1]
    · simp [h1]
    · exact h1

  dsimp [f] at h_pos
  linarith

/-- Lower bound for the quadratic term based on integral approximation. -/
axiom sum_delta_sq_ge (k : ℕ) (hk : k ≥ 15000) :
  (∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
    if (p : ℝ) > (k : ℝ) / 2 then (delta k p)^2 else 0) >
  0.07 * (k : ℝ) / Real.log (k : ℝ)

/-- Lower bound for the linear term based on Rosser-Schoenfeld. 
    Derived from RS bounds for sum(1/p) and pi(x). -/
axiom sum_delta_ge (k : ℕ) (hk : k ≥ 15000) :
  (∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
    if (p : ℝ) > (k : ℝ) / 2 then delta k p else 0) >
  0.09 * (k : ℝ) / Real.log (k : ℝ)

lemma final_ineq_check (k : ℕ) (hk : k ≥ 15000) :
  2 * Real.log k - 0.09 * k / Real.log k - (1/2) * (0.07 * k / Real.log k) < 0 := by
  have h_k_real_ge : (k : ℝ) ≥ 15000 := by exact_mod_cast hk
  have h_log_pos : 0 < Real.log k := Real.log_pos (by linarith)
  
  -- We need to show: 2 log k < (0.09 + 0.035) k / log k = 0.125 k / log k
  -- Equivalently: k / (log k)^2 > 2 / 0.125 = 16
  
  have h_check : (k : ℝ) / (Real.log k)^2 > 16 := by
    -- Analytic verification:
    let f := fun (x : ℝ) => x / (Real.log x)^2
    
    have h_deriv : ∀ x ∈ Set.Ici (15000 : ℝ), HasDerivAt f ((Real.log x - 2) / (Real.log x)^3) x := by
      intro x hx
      simp at hx
      have h_log_pos : 0 < Real.log x := by
        apply Real.log_pos
        linarith [hx]
      have h_log_nz : Real.log x ≠ 0 := ne_of_gt h_log_pos
      have h_x_ne_0 : x ≠ 0 := by linarith
      
      have h_log_sq_deriv : HasDerivAt (fun x => (Real.log x)^2) (2 * Real.log x / x) x := by
        convert (hasDerivAt_log h_x_ne_0).pow 2 using 1
        field_simp
        ring
      
      convert (hasDerivAt_id x).div h_log_sq_deriv (pow_ne_zero 2 h_log_nz) using 1
      field_simp
      generalize hl : Real.log x = u
      simp only [id]
      ring
        
    have h_mono : MonotoneOn f (Set.Ici 15000) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 15000) 
        (fun x hx => (h_deriv x hx).continuousAt.continuousWithinAt)
        (fun x hx => (h_deriv x (interior_subset hx)).hasDerivWithinAt)
      intro x hx
      simp at hx
      have h_log_ge : Real.log x ≥ Real.log 15000 := Real.log_le_log (by linarith) (le_of_lt hx)
      
      have h_exp_2 : Real.exp 2 = (Real.exp 1)^2 := by
        rw [← Real.exp_nat_mul 1 2]
        norm_num

      have h_log_gt_2 : Real.log x > 2 := by sorry
      
      field_simp
      linarith

    have h_base : f 15000 > 16 := by sorry

    exact lt_of_lt_of_le h_base (h_mono (Set.mem_Ici.mpr (le_refl _)) h_k_real_ge h_k_real_ge)

  rw [sub_sub, sub_lt_zero]
  field_simp [h_log_pos] at *
  linarith

/-- The analytic bound theorem. -/
theorem analytic_bound_E_lt_one (k : ℕ) (hk : k ≥ 15000) : E_val k < 1 := by
  have hk_pos : (k : ℝ) > 0 := by norm_cast; linarith
  have hk_log_pos : Real.log k > 0 := Real.log_pos (by norm_cast; linarith)
  
  -- Logarithm of E(k)
  rw [← Real.log_neg_iff (by
    apply mul_pos (pow_pos hk_pos 2)
    apply Finset.prod_pos; intro p hp
    split_ifs with h_cond
    · have Hp : (p : ℝ) > 0 := by norm_cast; exact cast_pos.mpr (Prime.pos (Finset.mem_filter.mp hp).2)
      have H : (k : ℝ) / p < 2 := (div_lt_iff_local Hp).mpr (by linarith)
      linarith
    · exact zero_lt_one
  )]
  
  -- Decomposition
  let S_lin := ∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
                 if (p : ℝ) > (k : ℝ) / 2 then delta k p else 0
  let S_quad := ∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
                  if (p : ℝ) > (k : ℝ) / 2 then (delta k p)^2 else 0
  -- Bounding log(1 - delta)
  have log_sum_le : (∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
      if (p : ℝ) > (k : ℝ) / 2 then Real.log (1 - delta k p) else 0) ≤
      -S_lin - S_quad / 2 := by
    dsimp [S_lin, S_quad]
    rw [Finset.sum_div, sub_eq_add_neg, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    split_ifs with h_cond
    · have hp_pos : (p : ℝ) > 0 := by norm_cast; exact cast_pos.mpr (Prime.pos (Finset.mem_filter.mp hp).2)
      have h_delta_lt_one : delta k p < 1 := by
        dsimp [delta]
        apply (sub_lt_iff_lt_add).mpr
        rw [div_lt_iff_local hp_pos]
        linarith
      have h_delta_nonneg : 0 ≤ delta k p := by
        dsimp [delta]
        apply sub_nonneg.mpr
        rw [le_div_iff_local hp_pos, one_mul]
        norm_cast
        apply le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
      have := log_one_sub_le (delta k p) h_delta_nonneg h_delta_lt_one
      linarith
    · simp
  calc
    Real.log (E_val k) = Real.log ((k : ℝ)^2 * ∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
        if (p : ℝ) > (k : ℝ) / 2 then (2 - (k : ℝ) / p) else 1) := rfl
    _ = Real.log ((k : ℝ)^2) + Real.log (∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
        if (p : ℝ) > (k : ℝ) / 2 then (2 - (k : ℝ) / p) else 1) := by
      refine Real.log_mul ?_ ?_
      · apply pow_ne_zero; linarith
      · apply Finset.prod_ne_zero_iff.mpr
        intro p hp
        split_ifs with h
        · apply _root_.ne_of_gt
          have hp_pos : (p : ℝ) > 0 := by norm_cast; exact cast_pos.mpr (Prime.pos (Finset.mem_filter.mp hp).2)
          have : (k : ℝ) / p < 2 := (div_lt_iff_local hp_pos).mpr (by linarith)
          linarith
        · exact one_ne_zero
    _ = 2 * Real.log k + ∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
        Real.log (if (p : ℝ) > (k : ℝ) / 2 then (2 - (k : ℝ) / p) else 1) := by
      rw [Real.log_pow]
      rw [Real.log_prod]
      · congr
      · intros p hp
        split_ifs with h
        · have hp_pos : (p : ℝ) > 0 := by norm_cast; exact cast_pos.mpr (Prime.pos (Finset.mem_filter.mp hp).2)
          have : (k : ℝ) / p < 2 := (div_lt_iff_local hp_pos).mpr (by linarith)
          linarith
        · exact one_ne_zero
    _ = 2 * Real.log k + ∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime,
        if (p : ℝ) > (k : ℝ) / 2 then Real.log (1 - delta k p) else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with h
      · rw [delta]
        ring_nf
      · rw [Real.log_one]
    _ ≤ 2 * Real.log k - S_lin - S_quad / 2 := by
      linarith [log_sum_le]
    _ < 0 := by
      have h_lin := sum_delta_ge k hk
      have h_quad := sum_delta_sq_ge k hk
      have h_final := final_ineq_check k hk
      linarith

end Erdos1094
