Implemented one proof-debt repair in [Sharpness/DiffIneq.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:115): `shield_dependsOn_noninternal` is now proved from the deleted-internal-edge characterization plus `ExitFromPred` locality. No theorem statements were changed.

Checks run:
- `lake env lean Sharpness/DiffIneq.lean` passed, with remaining `sorry` warnings
- `lake env lean Sharpness/Subcritical.lean` passed
- `lake env lean Sharpness/CriticalPoint.lean` passed
- `lake env lean Sharpness/Main.lean` passed
- `lake env lean Sharpness/BoundaryIneq.lean` passed, with remaining `sorry` warning
- `lake build` passed, with existing style/header warnings

Remaining `sorry` locations:
- [Sharpness/DiffIneq.lean:107](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:107)
- [Sharpness/DiffIneq.lean:174](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:174)
- [Sharpness/DiffIneq.lean:200](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/DiffIneq.lean:200)
- [Sharpness/BoundaryIneq.lean:25](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/BoundaryIneq.lean:25)

The M6 files still compile and the final theorem statement is preserved, but the no-unauthorized-`sorry` criterion is still not satisfied.