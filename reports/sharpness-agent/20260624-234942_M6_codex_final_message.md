Implemented a partial repair in [Sharpness/BoundaryIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/BoundaryIneq.lean:8): added private finite-probability union/monotonicity helpers, cluster-local event helpers, and deterministic last-exit/cluster-boundary witness lemmas for the Lemma 4 proof. I did not change any theorem statements or mathematical definitions.

Checks run:
- `lake env lean Sharpness/BoundaryIneq.lean` passed, with existing `sorry` warning
- `lake env lean Sharpness/Subcritical.lean` passed
- `lake env lean Sharpness/CriticalPoint.lean` passed
- `lake env lean Sharpness/Main.lean` passed
- `lake env lean Sharpness/DiffIneq.lean` passed, with existing `sorry` warnings
- `lake build` passed, with existing style/header warnings

Remaining `sorry` locations:
- [Sharpness/BoundaryIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/BoundaryIneq.lean:314)
- [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:475)
- [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:501)

M6 still is not fully discharged because Lemma 4’s cluster expansion and Lemma 2’s shield decomposition lower bound remain as proof debt.