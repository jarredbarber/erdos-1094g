import Erdos.EESAnalytic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.IntervalCases

namespace Erdos1094

open Nat

/-- Computable check for E(k) < 1. 
    Equivalent to k^2 * product((2p-k)/p) < 1 
    <-> k^2 * product(2p-k) < product(p) -/
def check_E_val (k : ℕ) : Bool :=
  let primes := (List.range (k + 1)).filter Nat.Prime |>.filter (fun p => 2 * p > k)
  let num := k * k * primes.foldl (fun acc p => acc * (2 * p - k)) 1
  let den := primes.foldl (fun acc p => acc * p) 1
  decide (num < den)

lemma check_E_val_correct (k : ℕ) (h : check_E_val k = true) : E_val k < 1 := by
  sorry -- Arithmetic proof relating check_E_val to E_val < 1

/-- Chunk 1: 300 to 999 -/
theorem verify_gap_1 : (List.range (1000 - 300)).all (fun i => check_E_val (300 + i)) = true := by
  native_decide

/-- Chunk 2: 1000 to 1999 -/
theorem verify_gap_2 : (List.range (2000 - 1000)).all (fun i => check_E_val (1000 + i)) = true := by
  native_decide

/-- Chunk 3: 2000 to 2999 -/
theorem verify_gap_3 : (List.range (3000 - 2000)).all (fun i => check_E_val (2000 + i)) = true := by
  native_decide

/-- Chunk 4: 3000 to 3999 -/
theorem verify_gap_4 : (List.range (4000 - 3000)).all (fun i => check_E_val (3000 + i)) = true := by
  native_decide

/-- Chunk 5: 4000 to 4999 -/
theorem verify_gap_5 : (List.range (5000 - 4000)).all (fun i => check_E_val (4000 + i)) = true := by
  native_decide

/-- Chunk 6: 5000 to 5999 -/
theorem verify_gap_6 : (List.range (6000 - 5000)).all (fun i => check_E_val (5000 + i)) = true := by
  native_decide

/-- Chunk 7: 6000 to 6999 -/
theorem verify_gap_7 : (List.range (7000 - 6000)).all (fun i => check_E_val (6000 + i)) = true := by
  native_decide

/-- Chunk 8: 7000 to 7999 -/
theorem verify_gap_8 : (List.range (8000 - 7000)).all (fun i => check_E_val (7000 + i)) = true := by
  native_decide

/-- Chunk 9: 8000 to 8999 -/
theorem verify_gap_9 : (List.range (9000 - 8000)).all (fun i => check_E_val (8000 + i)) = true := by
  native_decide

/-- Chunk 10: 9000 to 9999 -/
theorem verify_gap_10 : (List.range (10000 - 9000)).all (fun i => check_E_val (9000 + i)) = true := by
  native_decide

/-- Chunk 11: 10000 to 10999 -/
theorem verify_gap_11 : (List.range (11000 - 10000)).all (fun i => check_E_val (10000 + i)) = true := by
  native_decide

/-- Chunk 12: 11000 to 11999 -/
theorem verify_gap_12 : (List.range (12000 - 11000)).all (fun i => check_E_val (11000 + i)) = true := by
  native_decide

/-- Chunk 13: 12000 to 12999 -/
theorem verify_gap_13 : (List.range (13000 - 12000)).all (fun i => check_E_val (12000 + i)) = true := by
  native_decide

/-- Chunk 14: 13000 to 13999 -/
theorem verify_gap_14 : (List.range (14000 - 13000)).all (fun i => check_E_val (13000 + i)) = true := by
  native_decide

/-- Chunk 15: 14000 to 14999 -/
theorem verify_gap_15 : (List.range (15000 - 14000)).all (fun i => check_E_val (14000 + i)) = true := by
  native_decide

/-- Combined verification for the gap 300 <= k < 15000. -/
theorem verify_gap_all (k : ℕ) (h_low : 300 ≤ k) (h_high : k < 15000) : check_E_val k = true := by
  if h : k < 1000 then
    have h' := verify_gap_1
    rw [List.all_eq_true] at h'
    specialize h' (k - 300) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_low h))
    rwa [Nat.add_sub_of_le h_low] at h'
  else if h : k < 2000 then
    have h_ge : 1000 ≤ k := by linarith
    have h' := verify_gap_2
    rw [List.all_eq_true] at h'
    specialize h' (k - 1000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 3000 then
    have h_ge : 2000 ≤ k := by linarith
    have h' := verify_gap_3
    rw [List.all_eq_true] at h'
    specialize h' (k - 2000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 4000 then
    have h_ge : 3000 ≤ k := by linarith
    have h' := verify_gap_4
    rw [List.all_eq_true] at h'
    specialize h' (k - 3000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 5000 then
    have h_ge : 4000 ≤ k := by linarith
    have h' := verify_gap_5
    rw [List.all_eq_true] at h'
    specialize h' (k - 4000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 6000 then
    have h_ge : 5000 ≤ k := by linarith
    have h' := verify_gap_6
    rw [List.all_eq_true] at h'
    specialize h' (k - 5000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 7000 then
    have h_ge : 6000 ≤ k := by linarith
    have h' := verify_gap_7
    rw [List.all_eq_true] at h'
    specialize h' (k - 6000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 8000 then
    have h_ge : 7000 ≤ k := by linarith
    have h' := verify_gap_8
    rw [List.all_eq_true] at h'
    specialize h' (k - 7000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 9000 then
    have h_ge : 8000 ≤ k := by linarith
    have h' := verify_gap_9
    rw [List.all_eq_true] at h'
    specialize h' (k - 8000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 10000 then
    have h_ge : 9000 ≤ k := by linarith
    have h' := verify_gap_10
    rw [List.all_eq_true] at h'
    specialize h' (k - 9000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 11000 then
    have h_ge : 10000 ≤ k := by linarith
    have h' := verify_gap_11
    rw [List.all_eq_true] at h'
    specialize h' (k - 10000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 12000 then
    have h_ge : 11000 ≤ k := by linarith
    have h' := verify_gap_12
    rw [List.all_eq_true] at h'
    specialize h' (k - 11000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 13000 then
    have h_ge : 12000 ≤ k := by linarith
    have h' := verify_gap_13
    rw [List.all_eq_true] at h'
    specialize h' (k - 12000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 14000 then
    have h_ge : 13000 ≤ k := by linarith
    have h' := verify_gap_14
    rw [List.all_eq_true] at h'
    specialize h' (k - 13000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else if h : k < 15000 then
    have h_ge : 14000 ≤ k := by linarith
    have h' := verify_gap_15
    rw [List.all_eq_true] at h'
    specialize h' (k - 14000) (List.mem_range.mpr (by apply Nat.sub_lt_sub_right h_ge h))
    rwa [Nat.add_sub_of_le h_ge] at h'
  else
    linarith

end Erdos1094
