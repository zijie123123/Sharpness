# Milestone M0: project skeleton and exact theorem statements

Goal: create a compiling Lean skeleton for the entire formalization, with exact theorem statements and temporary `by sorry` proofs where necessary.

Tasks:

1. Inspect the existing Lean project structure (`lakefile.*`, root module file, existing `*.lean` files).
2. Create the module tree if it does not exist:
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
3. Add root imports in `Sharpness.lean` or the existing root file.
4. Define stable namespaces, preferably `namespace Sharpness`.
5. Add core definitions/stubs with mathematically meaningful types:
   - vertices as `Fin d -> Int` or a clearly equivalent representation;
   - bonds and configurations;
   - finite local events and finite Bernoulli probabilities;
   - connectivity and finite exit probabilities;
   - `phi`, `pTilde`, `theta`, `pCrit`;
   - theorem stubs for Russo, Lemma 2, Lemma 3, Lemma 4, Lemma 5, `pTilde_eq_pCrit`, and the final sharpness theorem.
6. The final theorem must express exactly:
   - if `p < pCrit`, then there exists `c > 0` such that finite box exit probabilities are at most `Real.exp (-(c * n))` for all `n`;
   - if `pCrit < p` and `p < 1`, then `theta p >= (p - pCrit) / (p * (1 - pCrit))`.

Allowed in M0: `by sorry` in theorem bodies, provided the statements are not vacuous.
Forbidden: `axiom`, `constant`, fake theorem statements, replacing probability by trivial definitions just to pass.

Run:

```bash
lake build
```

If imports are slow, at least run `lake env lean` on the root and changed files.
