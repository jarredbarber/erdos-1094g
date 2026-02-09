# Poke Messages

## Human intervention (2026-02-09)

### Sylvester.lean rewritten — broken code reverted, clean axiom added

Sylvester.lean was broken for **6 consecutive commits** (3afe39e through c1289fd). Agents were committing non-compiling code. Reverted to last working state (eea980d), then replaced the entire partial proof with a single clean axiom:

```lean
axiom sylvester_schur (n k : ℕ) (h : 2 * k ≤ n) (hk0 : 0 < k) :
    ∃ p, p.Prime ∧ p ∣ n.choose k ∧ p > k
```

This axiom is **verified against published literature by a human** (Sylvester 1892, Schur 1929). It is a textbook-level result. The old partial proof is preserved in git history.

### Current state after cleanup

**0 sorrys. 3 axioms. Build passes clean.**

**Axioms:**
1. `sylvester_schur` (Sylvester.lean) — ✅ human-verified against literature. DO NOT TOUCH.
2. `ees_large_k` (EES1974.lean:125) — explore task `erdos1094g-faw` created to write refined NL proof
3. `ecklund_case1_ge_8` (Ecklund.lean:20) — explore task `erdos1094g-oze` created to write refined NL proof

### Priority guidance

1. **Do NOT touch Sylvester.lean.** The axiom is final.
2. **Run the two explore tasks** (`oze` and `faw`) to produce refined NL proofs.
3. After explore tasks complete, create formalize tasks to eliminate the axioms based on the refined NL proofs.
4. **Compile on every commit.** Run `lake build Erdos.Basic` before committing. The 6-commit broken streak is unacceptable.

### Closure criteria

**If all 3 axioms are resolved (0 sorrys, 0 non-human-verified axioms, clean build), close the project.** Specifically:
- `sylvester_schur` is already human-verified — it stays as an axiom (acceptable).
- If `ees_large_k` and `ecklund_case1_ge_8` are eliminated (replaced with proofs, 0 sorrys), the project is DONE.
- Send a notification via `tm notify` when this happens.
