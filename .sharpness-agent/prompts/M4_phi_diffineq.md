# Milestone M4: finite-set criterion, random shield, and Lemma 2

Focus files:

- `Sharpness/Phi.lean`
- `Sharpness/DiffIneq.lean`

Goal: implement `phi`, `pTilde`, the order consequences of `pTilde`, and the fundamental differential inequality.

Required results in `Phi.lean`:

1. Define `phi p S = p * ∑_(x,y)∈∂E S Prob p (0 ↔_S x)`.
2. Prove `phi` is monotone in `p` for fixed finite `S`.
3. Define `pTilde` as the supremum of `p ∈ [0,1]` for which some finite `S ∋ 0` has `phi p S < 1`.
4. Prove below-`pTilde` order lemma:
   if `p < pTilde`, then there exists finite `S ∋ 0` with `phi p S < 1`.
5. Prove above-`pTilde` order lemma:
   if `p > pTilde`, then for every finite `S ∋ 0`, `1 <= phi p S`.

Required results in `DiffIneq.lean`:

1. Define the random shield set for finite `Lam`:
   `Shield(omega) = {x ∈ Lam | x is not connected to Lamᶜ}`.
2. Prove `0 ∈ Shield(omega)` iff the finite exit event `A_Lam` fails.
3. Prove support separation for `{Shield = S}`:
   it depends only on edges not internal to `S`.
   Use the deleted-internal-edge characterization and the last-exit lemma.
4. Prove pivotal equivalence:
   on `{Shield = S}`, for `(x,y) ∈ ∂E S`, the bond `xy` is closed-pivotal for `A_Lam` iff `0 ↔_S x`.
5. Assemble Lemma 2:

```text
f_Lam'(p) >= (1 / (p * (1 - p))) * phiMinIn p Lam * (1 - f_Lam p)
```

where `phiMinIn` is the finite minimum over `S ⊆ Lam`, `0 ∈ S`.

Proof chain for Lemma 2 must follow the article:

- apply Russo;
- decompose by `Shield = S`;
- restrict to boundary edges oriented from `S` to `Sᶜ`;
- use pivotal equivalence;
- use independence from support separation;
- identify the boundary sum with `phi p S / p`;
- lower-bound by the finite minimum;
- sum `Prob(Shield=S)` over `0∈S` to obtain `1 - f_Lam(p)`.

Run:

```bash
lake env lean Sharpness/Phi.lean
lake env lean Sharpness/DiffIneq.lean
lake build
```
