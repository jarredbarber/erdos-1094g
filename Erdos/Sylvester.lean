import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic

namespace Erdos1094

open Nat

/-- **Sylvester-Schur Theorem** (J. J. Sylvester, 1892; I. Schur, 1929).
    For n ≥ 2k and k > 0, the binomial coefficient C(n,k) has a prime factor > k.

    This is a well-established textbook result, not yet in Mathlib.
    Statement verified against literature by human:
    - J. J. Sylvester, "On arithmetical series," Messenger of Math. 21 (1892), 1–19.
    - I. Schur, "Einige Sätze über Primzahlen," S.-B. Preuss. Akad. Wiss. (1929), 125–136.

    The previous partial formalization (deleted product lemma, prime gap argument,
    computational small-k cases) is preserved in git history for reference. -/
axiom sylvester_schur (n k : ℕ) (h : 2 * k ≤ n) (hk0 : 0 < k) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k

/-- Convenience wrapper matching the old theorem name. -/
theorem sylvester_schur_theorem (n k : ℕ) (h : 2 * k ≤ n) (hk0 : 0 < k) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k :=
  sylvester_schur n k h hk0

end Erdos1094
