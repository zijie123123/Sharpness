<!-- sharpness-agent-begin -->
# Project instructions for Codex: Lean sharpness formalization

You are formalizing the proof of sharpness for nearest-neighbor Bernoulli bond percolation on `Z^d` in Lean 4 + mathlib.

## Mathematical contract

The final theorem must formalize the same two conclusions as the note:

1. if `p < pCrit`, finite box exit probabilities decay exponentially;
2. if `pCrit < p < 1`, `theta p >= (p - pCrit) / (p * (1 - pCrit))`.

Do not change the meaning of the theorem to a weaker or different result.  Do not silently alter definitions of `theta`, `pCrit`, `pTilde`, `phi`, finite exit probability, connectivity, or the finite Bernoulli product probability in a way that makes the final theorem easier but mathematically non-equivalent.

The proof strategy is finite-volume first:

- probabilities are finite Bernoulli product probabilities on finite edge supports;
- `theta` is the decreasing limit / infimum of finite exit probabilities;
- infinite product measure should not be introduced unless explicitly requested later;
- connectivity events must be local, with explicit finite supports.

## Lean engineering rules

- Prefer small named lemmas over long brittle proofs.
- Do not add `axiom`, `constant`, `unsafe`, global `set_option autoImplicit true`, or theorem-shaped assumptions to pass Lean.
- `sorry` is allowed only as a temporary marker on the exact supporting lemma that is not yet implemented.  If you leave a `sorry`, write a short comment above it explaining the missing mathematical fact.
- Never replace a theorem by `True`, `0 = 0`, or a vacuous hypothesis.
- Never weaken a theorem statement from an earlier milestone unless the user explicitly approves.
- Local `classical` is fine.  Global imports should be minimal but practical.
- After changing Lean files, run at least `lake env lean <file>` for touched files; run `lake build` when possible.
- If Lean fails, fix the first real error before rewriting large parts of the code.

## File strategy

Use the planned module structure unless the existing repository already has a better layout:

- `Sharpness/Zd.lean`
- `Sharpness/Bonds.lean`
- `Sharpness/FiniteGeometry.lean`
- `Sharpness/Paths.lean`
- `Sharpness/Clusters.lean`
- `Sharpness/FiniteBernoulli.lean`
- `Sharpness/LocalEvent.lean`
- `Sharpness/Independence.lean`
- `Sharpness/Monotonicity.lean`
- `Sharpness/Russo.lean`
- `Sharpness/Events.lean`
- `Sharpness/Phi.lean`
- `Sharpness/DiffIneq.lean`
- `Sharpness/OdeComparison.lean`
- `Sharpness/Supercritical.lean`
- `Sharpness/BoundaryIneq.lean`
- `Sharpness/Subcritical.lean`
- `Sharpness/CriticalPoint.lean`
- `Sharpness/Main.lean`

If a file or namespace already exists, extend it rather than duplicating definitions.

## Proof dependency graph

Foundations:

1. `Z^d` geometry, bonds, boxes, translations, boundary endpoints.
2. Paths, connectivity, first/last exit, clusters.
3. Finite Bernoulli product probability, local events, support extension, independence, monotonicity.

Sharpness modules:

1. Russo closed-pivotal formula.
2. `phi p S`, `pTilde`, and order lemmas below/above `pTilde`.
3. Random shield set support separation and pivotal equivalence.
4. Fundamental differential inequality.
5. ODE/log comparison and supercritical lower bound.
6. Boundary inequality.
7. Subcritical recurrence and exponential decay.
8. `theta`, `pCrit`, `pTilde = pCrit`, final theorem.

## Stage discipline

When the prompt names a milestone, modify only files needed for that milestone and its immediate dependencies.  Do not attempt to close the whole theorem during an early milestone.

At the end of each turn, summarize:

- files changed;
- Lean commands run and whether they passed;
- remaining `sorry` locations in the touched files;
- any theorem statement you changed, with justification.

<!-- sharpness-agent-end -->
