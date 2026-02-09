import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

namespace Erdos1094

open Nat

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

end Erdos1094
