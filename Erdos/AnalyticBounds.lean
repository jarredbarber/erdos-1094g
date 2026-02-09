import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Floor.Defs

noncomputable section

namespace Erdos1094

open Real Nat BigOperators

/-- The Meissel-Mertens constant. -/
def MeisselMertens : ℝ := 0.261497212847643

/-- Sum of reciprocals of primes up to x. -/
def sum_prime_recip (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (Nat.floor x + 1)).filter Nat.Prime, (1 / (p : ℝ))

/-- Rosser-Schoenfeld bound (3.20) for the sum of reciprocals of primes. -/
axiom sum_primes_inv_le (x : ℝ) (hx : x ≥ 286) :
  sum_prime_recip x ≤ Real.log (Real.log x) + MeisselMertens + 1 / (2 * (Real.log x)^2)

axiom sum_primes_inv_ge (x : ℝ) (hx : x ≥ 286) :
  sum_prime_recip x ≥ Real.log (Real.log x) + MeisselMertens - 1 / (2 * (Real.log x)^2)

/-- Bounds for pi(x) used in the proof for k >= 300. -/
axiom pi_upper_bound_tight (n : ℕ) (hn : n ≥ 300) :
  (Nat.primeCounting n : ℝ) < (n : ℝ) / (Real.log n - 1.1)

axiom pi_lower_bound_tight (n : ℕ) (hn : n ≥ 150) :
  (Nat.primeCounting n : ℝ) > (n : ℝ) / (Real.log n - 1)

end Erdos1094
