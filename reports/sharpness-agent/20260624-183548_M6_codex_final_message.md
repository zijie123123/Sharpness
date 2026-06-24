Implemented the M6 assembly layer.

Changed files:
- [Sharpness/Subcritical.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Subcritical.lean): moved Lemma 5’s remaining proof gap into named `exponential_decay_below_pTilde_core`; public theorem now wraps it.
- [Sharpness/CriticalPoint.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/CriticalPoint.lean): added `sInf` order lemmas, proved the pCrit/pTilde assembly modulo endpoint support, and rewrote sub/supercritical bounds via `pCrit`.
- [Sharpness/Main.lean](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Main.lean): final theorem statement unchanged; now passes `2 <= d` as positive dimension to the critical-point layer.

Commands run:
- `lake env lean Sharpness/Subcritical.lean` passed, with one intended `sorry` warning.
- `lake env lean Sharpness/CriticalPoint.lean` passed, with one intended `sorry` warning.
- `lake env lean Sharpness/Main.lean` passed.
- `lake build Sharpness.Main` passed.
- `lake build` passed.

Remaining `sorry` locations:
- Touched files: [Subcritical.lean:20](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/Subcritical.lean:20), [CriticalPoint.lean:22](/Users/zhuangzijie/Desktop/Leanproject/Sharpness/CriticalPoint.lean:22).
- Pre-existing blockers remain in `Events.lean`, `Monotonicity.lean`, `Clusters.lean`, `DiffIneq.lean`, and `BoundaryIneq.lean`.

Theorem statement change:
- Internal helper theorems `pTilde_eq_pCrit`, `exponential_decay_below_pCrit`, and `supercritical_lower_bound_above_pCrit` now require `0 < d`. The final theorem already assumes `2 <= d`, and the old all-`Nat` critical-point equality is not appropriate for degenerate dimension.