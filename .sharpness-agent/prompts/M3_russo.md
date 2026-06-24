# Milestone M3: Russo closed-pivotal formula

Focus file:

- `Sharpness/Russo.lean`

Goal: prove Lemma 1, the closed-pivotal Russo formula, in the finite local-event setting.

Mathematical target:

For an increasing local event `A` depending on a finite support and `0 < p < 1`,

```text
deriv (fun q => Prob q A) p
  = (1 / (1 - p)) * ∑ e in support(A), Prob p (closedPivotalEvent A e)
```

Proof strategy:

1. Prove a generic theorem for events on a finite Boolean product, preferably a finite type `α`.
2. Define the influence event `B_e`: changing coordinate `e` changes whether `A` occurs.
3. Prove the single-coordinate decomposition:
   `Prob p A = (1-p) * Prob p (A | e=false) + p * Prob p (A | e=true)`.
4. Differentiate this expression by induction over the finite coordinate list or by explicit polynomial expansion.
5. For increasing `A`, prove that `closedPivotal e` equals `e=false` together with `B_e`, and hence
   `Prob p (closedPivotal e) = (1-p) * Prob p B_e`.
6. Sum over `e`.

Lean hints:

- It is okay to prove the probability function is a polynomial in `p` first.
- If `deriv` is too painful, use `HasDerivAt` as the main theorem and derive `deriv` later.
- Keep all hard calculus facts in small named lemmas.
- Do not change the public interface expected by `DiffIneq.lean` unless you also update callers consistently.

If this remains too hard in one run, leave exactly one localized `sorry` at the core finite-product derivative lemma and prove all definitional equivalences around it.

Run:

```bash
lake env lean Sharpness/Russo.lean
lake build
```
