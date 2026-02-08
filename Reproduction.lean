import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic

open Nat Finset

def S (n k : ℕ) : Finset ℕ := (Ico (n - k + 1) (n + 1))

lemma S_card (n k : ℕ) (h : k ≤ n) : (S n k).card = k := by
  simp [S]
  omega


