import Mathlib

open Nat

def kummer_check (n k p : ℕ) : Bool :=
  let digits_n := Nat.digits p n
  let digits_k := Nat.digits p k
  let zipped := List.zip digits_k digits_n
  !List.all zipped (fun (x : ℕ × ℕ) => decide (x.1 ≤ x.2))

def has_prime_factor_le_k_bool (n k : ℕ) : Bool :=
  (List.range (k + 1)).any (fun p => decide (Nat.Prime p) && kummer_check n k p)

def ExceptionsFinset : List (ℕ × ℕ) :=
  [(7, 3), (13, 4), (14, 4), (23, 5), (62, 6), (44, 8), (46, 10), (47, 10),
   (74, 10), (94, 10), (95, 10), (47, 11), (241, 16), (284, 28)]

def check_range (k_start k_end : ℕ) : IO Unit := do
  let mut count := 0
  for k in [k_start:k_end] do
    let n_min := 2 * k
    let n_max := k * k
    for n in [n_min:n_max] do
      if (n, k) ∈ ExceptionsFinset then
        continue
      if !has_prime_factor_le_k_bool n k then
        IO.println s!"Failed for n={n}, k={k}"
      count := count + 1
  IO.println s!"Checked {count} pairs."

def main : IO Unit := do
  IO.println "Starting check..."
  let start ← IO.monoMsNow
  check_range 3 50
  let mid ← IO.monoMsNow
  IO.println s!"Check up to 50 took {mid - start} ms"
  check_range 50 100
  let end_ ← IO.monoMsNow
  IO.println s!"Check 50 to 100 took {end_ - mid} ms"
