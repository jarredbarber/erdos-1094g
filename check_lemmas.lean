import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

open Real

example : Real.exp 12 = (Real.exp 1) ^ 12 := by
  rw [← Real.exp_nat_mul]
  norm_num

example (f : ℝ → ℝ) (s : Set ℝ) (h : Convex ℝ s) 
  (h_deriv : ∀ x ∈ s, HasDerivAt f (x^2) x) : MonotoneOn f s := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg h (fun x hx => (h_deriv x hx).continuousAt.continuousWithinAt)
  intro x hx
  apply (h_deriv x (interior_subset hx)).hasDerivWithinAt
  intro x hx
  apply sq_nonneg
