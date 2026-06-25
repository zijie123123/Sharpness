# Milestone M5: ODE comparison, Lemma 3, and Lemma 4

Focus files:

- `Sharpness/OdeComparison.lean`
- `Sharpness/Supercritical.lean`
- `Sharpness/BoundaryIneq.lean`

Goal A: prove the supercritical lower bound above `pTilde`.

1. In `OdeComparison.lean`, prove a generic real-analysis lemma:
   if `0 < q < p < 1`, `f t < 1`, and
   `f'(t) >= (1 - f t) / (t * (1 - t))` on the interval, then

```text
1 - f p <= (1 - f q) * q * (1 - p) / (p * (1 - q))
```

2. In `Supercritical.lean`, use Lemma 2 and the above-`pTilde` order lemma to prove:

```text
theta p >= (p - pTilde) / (p * (1 - pTilde))
```

for `pTilde < p < 1`.

3. Include the finite-event side condition `exitProb q Lam < 1` for `q < 1`, proved by closing all boundary edges.

Goal B: prove the boundary inequality Lemma 4.

In `BoundaryIneq.lean`, prove the finite-volume boundary inequality.  Use the cluster `C_S(u)`, decompose by possible cluster values `C0`, take the last exit from `C0`, and apply three-event independence:

- `{C_S(u)=C0}` uses internal `S`-edges incident to `C0`;
- `{xy open}` uses the one boundary bond;
- `{y ↔ B avoiding C0}` uses no edge incident to `C0`.

Then drop the avoidance condition and sum over `C0`.

If the fully general `B ⊂ Z^d` statement is too heavy, prove the exact finite-volume form needed for `B = Lambda_n^c` / finite exit events, but preserve a theorem name that `Subcritical.lean` can use.

Run:

```bash
lake env lean Sharpness/OdeComparison.lean
lake env lean Sharpness/Supercritical.lean
lake env lean Sharpness/BoundaryIneq.lean
lake build
```
