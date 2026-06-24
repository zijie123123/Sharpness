Implemented a partial M6 repair.

Changed files:
- [Sharpness/BoundaryIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/BoundaryIneq.lean): completed the finite-volume boundary inequality cluster expansion. Added private finite-probability union helpers, support-disjointness lemmas, singleton edge-open probability, cluster partition bound, and the three-event independence assembly.
- [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean): added private support/injectivity/nonnegativity helpers toward the remaining shield decomposition proof. The theorem statement was not changed.

Checks run:
- `lake env lean Sharpness/BoundaryIneq.lean` passed
- `lake env lean Sharpness/DiffIneq.lean` passed, with `sorry` warning
- `lake env lean Sharpness/Subcritical.lean` passed
- `lake env lean Sharpness/CriticalPoint.lean` passed
- `lake env lean Sharpness/Main.lean` passed
- `lake build` passed, with existing style/header warnings

Remaining proof debt:
- [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:918): `exit_russo_sum_lower_bound`, the shield decomposition lower bound for the Russo pivotal sum.

No public theorem statements or mathematical definitions were weakened or changed. No `axiom`, `constant`, or `unsafe` shortcut was added.