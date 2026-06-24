Implemented M4 scaffolding and the `Phi` order layer.

Changed files:
- [Sharpness/Phi.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Phi.lean)
- [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean)

What changed:
- Added `pTildeSet`, nonempty/bounded facts, `zero_le_pTilde`, `pTilde_le_one`.
- Proved `phi_mono`.
- Proved the below/above `pTilde` order lemmas on the intended `[0,1]` parameter domain.
- Added shield definitions: `ExitFromPred`, `Shield`, `closeInternalEdges`, `shieldSupport`, `shieldEvent`.
- Proved `0 ∈ Shield ↔ ¬ ExitPred`, ambient shield locality, support disjointness, and `phiMinIn_le_phi`.
- Made `differential_inequality` derive from Russo plus the named shield-decomposition lower bound.

Checks run:
- `lake env lean Sharpness/Phi.lean` passed.
- `lake env lean Sharpness/DiffIneq.lean` passed with expected `sorry` warnings.
- `lake build` passed with existing style/proof-debt warnings.

Remaining `sorry`s in touched files:
- [DiffIneq.lean:107](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:107) `shield_eq_iff_deleted_internal`
- [DiffIneq.lean:118](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:118) `shield_dependsOn_noninternal`
- [DiffIneq.lean:141](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:141) `closedPivotal_exit_iff_connIn_on_shield`
- [DiffIneq.lean:167](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:167) `exit_russo_sum_lower_bound`

Theorem statement changes:
- `exists_phi_lt_one_of_lt_pTilde` now has `0 <= p`.
- `one_le_phi_of_pTilde_lt` now has `p <= 1`.

Justification: the defining set for `pTilde` is explicitly restricted to `p ∈ [0,1]`; the previous all-real above-`pTilde` statement is false outside that interval. No definitions of `phi`, `pTilde`, probabilities, connectivity, or exit events were weakened.