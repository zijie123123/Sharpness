Implemented the M6 repair pass.

Changed files:
- `Sharpness/CriticalPoint.lean`: removed the endpoint `sorry` by proving finite box exit probability is `1` at `p = 1` in positive dimension, using an explicit axis path and finite product probability.
- `Sharpness/Subcritical.lean`: proved the `p = 0` case; remaining gap is narrowed to the positive-parameter Lemma 5 recurrence/iteration proof.
- `Sharpness/Events.lean`: proved `le_theta_of_le_boxExitProb`.
- `Sharpness/Main.lean`: remains modified from the M6 assembly layer to pass `0 < d` from `2 <= d`.

Commands run:
- `lake env lean Sharpness/Events.lean` passed, with existing `sorry` warnings.
- `lake env lean Sharpness/Subcritical.lean` passed, with one `sorry` warning.
- `lake env lean Sharpness/CriticalPoint.lean` passed.
- `lake env lean Sharpness/Main.lean` passed.
- `lake build` passed.

Remaining `sorry` locations:
- Touched files: `Sharpness/Events.lean:170`, `Sharpness/Events.lean:178`, `Sharpness/Subcritical.lean:74`.
- Other existing blockers: `BoundaryIneq.lean:25`, `Monotonicity.lean:30`, `Clusters.lean:33`, `DiffIneq.lean:107`, `118`, `141`, `167`.

The final theorem statement in `Sharpness/Main.lean` was not changed.