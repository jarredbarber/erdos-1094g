import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic

open Nat

variable (p n : ℕ) (hp : p.Prime)

#check hp.dvd_factorial
