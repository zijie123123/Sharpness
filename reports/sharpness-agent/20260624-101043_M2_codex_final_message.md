Implemented M2 deterministic layer updates.

Changed files:
- `Sharpness/Zd.lean`: proved ball membership, origin membership, `l1` triangle helpers, adjacency symmetry/translation invariance, exact neighbor membership, and `translate_ball_exit`.
- `Sharpness/Bonds.lean`: proved canonical bond construction lemmas, oriented boundary membership, bond support membership, and internal/exit disjointness.
- `Sharpness/FiniteGeometry.lean`: proved boundary endpoint bound.
- `Sharpness/Paths.lean`: moved to `List.IsChain`, proved reversal, translation, first-exit crossing, and connectivity symmetry.
- `Sharpness/Events.lean`: proved connection/exit/target locality and increasingness.
- `Sharpness/Clusters.lean`: kept the exact sharp cluster support theorem with a localized `sorry` comment.

Statement changes:
- `boundary_endpoint_mem_ball` now requires `0 < L`. Without this it is false for `L = 0` because Nat subtraction makes `L - 1 = 0`.
- `connIn_translate` now requires an explicit hypothesis that translated open edges remain open. The previous arbitrary-configuration statement was false.

Commands run:
- `lake env lean Sharpness/Zd.lean` passed
- `lake env lean Sharpness/Bonds.lean` passed
- `lake env lean Sharpness/FiniteGeometry.lean` passed
- `lake env lean Sharpness/Paths.lean` passed
- `lake env lean Sharpness/Clusters.lean` passed with expected `sorry`
- `lake env lean Sharpness/Events.lean` passed with expected `sorry`s
- `lake build` passed

Remaining `sorry`s in touched files:
- `Sharpness/Clusters.lean:33` sharp cluster incident-support theorem
- `Sharpness/Events.lean:170` `theta_le_boxExitProb`
- `Sharpness/Events.lean:178` `theta_eq_zero_of_exponential_decay`
- `Sharpness/Events.lean:185` `le_theta_of_le_boxExitProb`