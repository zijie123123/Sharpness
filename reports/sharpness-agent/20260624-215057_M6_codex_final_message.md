Implemented M6 recurrence closure in [Sharpness/Subcritical.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Subcritical.lean:795).

What changed:
- Proved the box recurrence `boxExitProb d p n <= phi p S * boxExitProb d p (n - L)`.
- Added private finite-probability event inclusion, path first-exit, and translation/reindexing helpers needed for the recurrence.
- Left `CriticalPoint.lean` and `Main.lean` theorem statements unchanged.

Checks run:
- `lake env lean Sharpness/Subcritical.lean` passed
- `lake env lean Sharpness/CriticalPoint.lean` passed
- `lake env lean Sharpness/Main.lean` passed
- `lake build` passed, with existing style/header warnings

Remaining `sorry` locations:
- None in touched file `Sharpness/Subcritical.lean`
- Pre-existing upstream placeholders remain:
  - `Sharpness/Clusters.lean:33`
  - `Sharpness/DiffIneq.lean:107`
  - `Sharpness/DiffIneq.lean:118`
  - `Sharpness/DiffIneq.lean:141`
  - `Sharpness/DiffIneq.lean:167`
  - `Sharpness/BoundaryIneq.lean:25`

Theorem statements changed: none.