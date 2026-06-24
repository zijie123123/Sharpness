Implemented M3 in [Sharpness/Russo.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Russo.lean:1).

What changed:
- Proved a generic finite Boolean-cube closed-pivotal Russo formula.
- Proved `closedPivotal_dependsOn`.
- Transferred the generic Boolean result to the existing `LocalEvent` theorem `russo_closed_pivotal`.
- Kept the public `russo_closed_pivotal` statement unchanged.

Checks run:
- `lake env lean Sharpness/Russo.lean` passed cleanly.
- `lake build` passed. It still reports existing style/sorry warnings in other files, but no build errors.

Remaining `sorry` locations in touched files:
- None in `Sharpness/Russo.lean`.

Theorem statement changes:
- None.