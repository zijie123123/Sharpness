Implemented a repair pass, but M6 is still not fully discharged because Lemma 5’s positive-parameter proof remains.

Changed in this pass:
- `Sharpness/Monotonicity.lean`: proved `bernProb_mono_parameter` by finite Boolean-cube induction.
- `Sharpness/Events.lean`: proved finite exit nonnegativity, `theta_nonneg`, `theta_le_boxExitProb`, `theta_eq_zero_of_exponential_decay`, and `le_theta_of_le_boxExitProb`.
- `Sharpness/CriticalPoint.lean`: updated the `theta_eq_zero_of_exponential_decay` call to pass `0 <= p` and `p <= 1`.

Theorem statement changed:
- `theta_le_boxExitProb` and `theta_eq_zero_of_exponential_decay` now require `0 <= p` and `p <= 1`. The previous all-real statements were false outside the Bernoulli probability regime; finite Bernoulli weights are not generally nonnegative for arbitrary real `p`. Final theorem `sharpness_zd` was not changed.

Commands run:
- `lake env lean Sharpness/Monotonicity.lean` passed.
- `lake env lean Sharpness/Events.lean` passed.
- `lake build Sharpness.Events` passed.
- `lake build Sharpness.Monotonicity` passed.
- `lake env lean Sharpness/Subcritical.lean` passed with the existing `sorry` warning.
- `lake env lean Sharpness/CriticalPoint.lean` passed.
- `lake env lean Sharpness/Main.lean` passed.
- `lake build` passed.

Remaining `sorry` locations:
- `Sharpness/Subcritical.lean:74`
- `Sharpness/Clusters.lean:33`
- `Sharpness/BoundaryIneq.lean:25`
- `Sharpness/DiffIneq.lean:107`
- `Sharpness/DiffIneq.lean:118`
- `Sharpness/DiffIneq.lean:141`
- `Sharpness/DiffIneq.lean:167`

Main remaining M6 blocker: the positive-parameter subcritical proof still needs the finite-volume translation-to-origin estimate plus recurrence iteration infrastructure.