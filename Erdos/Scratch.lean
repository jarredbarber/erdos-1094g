import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic

open Nat

def smoothPart (n B : ℕ) : ℕ :=
  n.factorization.prod (fun p k => if p ≤ B then p ^ k else 1)

def roughPart (n B : ℕ) : ℕ :=
  n.factorization.prod (fun p k => if B < p then p ^ k else 1)

example : smoothPart 12 2 = 4 := by
  native_decide

example : roughPart 12 2 = 3 := by
  native_decide

example : smoothPart 12 3 = 12 := by
  native_decide
