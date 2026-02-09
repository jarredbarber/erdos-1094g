# Poke Messages

## Human intervention (2026-02-09, update 2)

Task erdos1094g-kqp temporarily moved to defer state - overseer may reopen if deemed appropriate

### Axiom audit via web search — TWO AXIOMS ARE WRONG

Human verified all axioms against published literature using web search. **Two prime counting axioms are overstated:**

#### ❌ `pi_upper_bound_tight` (AnalyticBounds.lean:28)
- **Axiom claims:** π(n) < n/(log n - 1.1) for n ≥ 300
- **Literature says:** Valid for x ≥ 60,184 (Wikipedia, citing Dusart)
- **The threshold is 200× too low.**

#### ❌ `pi_lower_bound_tight` (AnalyticBounds.lean:31)
- **Axiom claims:** π(n) > n/(log n - 1) for n ≥ 150
- **Literature says:** Valid for x ≥ 5,393 (Wikipedia, citing Rosser)
- **The threshold is 36× too low.**

These must be fixed. Either raise the thresholds to match the literature, or extend the computational range in EES1974.lean to cover the gap. Any proof depending on these axioms with k < 300 (for upper) or k < 5393 (for lower) is unsound.

### Other axiom assessments

| Axiom | Status |
|-------|--------|
| `sylvester_schur` | ✅ Human-verified, textbook result |
| `ecklund_case1_ge_12` | 🟡 Computationally verifiable, not a citation |
| `log_one_sub_le` | ✅ Standard Taylor bound, likely in Mathlib |
| `sum_primes_inv_le/ge` | 🟡 Rosser-Schoenfeld 1962, form needs checking against Theorem 20 |
| `sum_delta_sq_ge` | 🟡 Bespoke bound on agent-defined quantity, not from literature |
| `sum_delta_ge` | 🟡 Same — needs independent verification |
| `ees_heuristic_implication` | 🟡 Name literally says "heuristic" — suspicious |

### Build is broken

EESAnalytic.lean:65 has "No goals to be solved" error. Fix before adding more code.

### Priority guidance

1. **Fix the two wrong axioms FIRST.** Raise thresholds to match literature: `pi_upper_bound_tight` needs n ≥ 60184, `pi_lower_bound_tight` needs n ≥ 5393. Then extend computational verification in EES1974.lean/CheckFact.lean to cover k=167..299 (which may already be done — check).
2. **Fix the build.** EESAnalytic.lean must compile.
3. **Do NOT add more axioms.** The project went from 3 axioms to 10. This is the wrong direction. Every new axiom needs human verification against published sources.
4. **`log_one_sub_le` may not need to be an axiom.** Check Mathlib for `Real.log_one_sub_le` or equivalent.
5. **The `sum_delta` axioms and `ees_heuristic_implication` need NL proofs** reviewed by a verify agent before being trusted.

### Closure criteria (unchanged)

If all axioms are either (a) human-verified against literature, or (b) eliminated with proofs, and build passes with 0 sorrys — the project is DONE. Send notification via `tm notify`.

### Context

- Brave Search API key is now available as `BRAVE_API_KEY` env var. Use it for citation verification.
- The `brave-search` skill is at `/home/jarred/.pi/agent/skills/brave-search/`
- Do NOT grep dotfiles for API keys. Use the env var directly.
