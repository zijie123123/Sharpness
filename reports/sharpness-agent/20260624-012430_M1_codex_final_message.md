Implemented M1 finite probability API work.

Files changed:
- [FiniteBernoulli.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/FiniteBernoulli.lean): generic finite Boolean product API, nonnegativity, total mass, complement, event inclusion monotonicity, union bound, reindexing, unused-coordinate marginalization, and two-block factorization.
- [LocalEvent.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/LocalEvent.lean): support-extension invariance proof.
- [Independence.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Independence.lean): two-event and three-event disjoint-support independence.
- [Monotonicity.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Monotonicity.lean): finite/local increasing-event wrapper for monotonicity in `p`.

Checks run:
- `lake env lean Sharpness/FiniteBernoulli.lean` passed.
- `lake env lean Sharpness/LocalEvent.lean` passed.
- `lake env lean Sharpness/Independence.lean` passed.
- `lake env lean Sharpness/Monotonicity.lean` passed, with the intentional `sorry` warning.
- `lake build` passed, with existing project warnings and existing later-stage `sorry`s.

Remaining `sorry` in touched files:
- [Monotonicity.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Monotonicity.lean:30): `bernProb_mono_parameter`, the isolated finite Boolean-cube induction/coupling proof allowed by the milestone prompt.

No existing theorem statements were weakened or changed. I added helper definitions/lemmas and kept the public M1 theorem meanings intact.