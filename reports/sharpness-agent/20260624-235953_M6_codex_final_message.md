Implemented a partial M6 repair in [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean): closed the `closedPivotal_exit_iff_connIn_on_shield` proof by adding finite path concatenation, first-exit, force-open transfer, and boundary bond endpoint helpers. I did not change theorem statements or mathematical definitions.

Checks run:
- `lake env lean Sharpness/Subcritical.lean` passed
- `lake env lean Sharpness/CriticalPoint.lean` passed
- `lake env lean Sharpness/Main.lean` passed
- `lake env lean Sharpness/DiffIneq.lean` passed, with remaining `sorry` warning
- `lake env lean Sharpness/BoundaryIneq.lean` passed, with remaining `sorry` warning
- `lake build` passed, with existing style/header warnings

Remaining `sorry` locations:
- [Sharpness/BoundaryIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/BoundaryIneq.lean:314): Lemma 4 cluster expansion
- [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:851): Lemma 2 shield decomposition lower bound

M6 is still not fully discharged because those two finite probability decomposition proofs remain.