# Milestone M6: Lemma 5, critical point identification, and final theorem

Focus files:

- `Sharpness/Subcritical.lean`
- `Sharpness/CriticalPoint.lean`
- `Sharpness/Main.lean`

Goal 1: prove exponential decay below `pTilde`.

Proof chain:

1. If `p = 0`, handle separately.
2. For `0 < p < pTilde`, use the below-`pTilde` order lemma to choose finite `S ∋ 0` with `rho = phi p S < 1`.
3. Choose `L >= 1` with `S ⊆ Lambda (L-1)`.
4. Boundary endpoints of `∂E S` lie in `Lambda L`.
5. Apply the boundary inequality to `a_n = Prob p (0 ↔ Lambda_n^c)` for `n >= L`.
6. Use the translation-to-origin estimate to show
   `Prob p (y ↔ Lambda_n^c) <= a_(n-L)` for every boundary endpoint `y ∈ Lambda L`.
7. Obtain recurrence `a_n <= rho * a_(n-L)`.
8. Iterate to get `a_n <= rho ^ floor(n/L)` and convert to `Real.exp (-(c*n))`.
9. Handle finitely many small `n` by closing all boundary edges, proving `a_n < 1`.

Goal 2: define `theta` and `pCrit`, then prove `pTilde = pCrit`.

- Define `theta p` as the infimum / limit of decreasing finite exit probabilities.
- Define `pCrit = inf {p ∈ [0,1] | theta p > 0}`.
- Prove `pCrit <= pTilde` using the supercritical theorem.  Handle the endpoint `pTilde = 1` separately.
- Prove `pTilde <= pCrit` using subcritical exponential decay and `theta p = 0`.

Goal 3: prove the final sharpness theorem with `pCrit`.

Do not change the final theorem statement.  If previous modules still contain `sorry`, preserve the final theorem statement and report the remaining blockers.

Run:

```bash
lake env lean Sharpness/Subcritical.lean
lake env lean Sharpness/CriticalPoint.lean
lake env lean Sharpness/Main.lean
lake build
```
