# Milestone M1: finite probability API

Focus files:

- `Sharpness/FiniteBernoulli.lean`
- `Sharpness/LocalEvent.lean`
- `Sharpness/Independence.lean`
- `Sharpness/Monotonicity.lean`

Goal: prove as much of the finite product probability layer as possible, independently of percolation geometry.

Required results:

1. Finite Bernoulli product probability over a finite coordinate type or a `Finset` support.
2. Weight nonnegativity for `0 <= p <= 1`.
3. Total mass is `1`.
4. Probability of complement, monotonicity under event inclusion, and finite union bound.
5. Local events with `DependsOn support pred`.
6. Probability invariant under support extension.
7. Disjoint-support independence for two local events.
8. Pairwise-disjoint support independence for three local events.
9. Increasing events and monotonicity of probability in `p`.

Implementation hints:

- It is acceptable to first prove everything for a finite type `α` with assignments `α -> Bool`, then wrap a `Finset` support by using its subtype.
- Keep probabilities in `Real`, not `ENNReal`.
- Use `by classical` locally.
- If full monotonicity in `p` is too hard, isolate the hard induction in one named lemma with `sorry`, but prove all algebraic lemmas around it.
- Do not import or mention percolation files except where local event support uses the configuration type.

Run targeted checks:

```bash
lake env lean Sharpness/FiniteBernoulli.lean
lake env lean Sharpness/LocalEvent.lean
lake env lean Sharpness/Independence.lean
lake env lean Sharpness/Monotonicity.lean
lake build
```
