import Sharpness.Subcritical
import Sharpness.Supercritical

namespace Sharpness

/-- The percolation critical point defined from `theta`. -/
noncomputable def pCrit (d : Nat) : Real :=
  sInf {p : Real | 0 <= p /\ p <= 1 /\ 0 < theta d p}

-- M0 stub: the finite-set critical point equals the `theta` critical point.
theorem pTilde_eq_pCrit (d : Nat) : pTilde d = pCrit d := by
  sorry

-- M0 stub: subcritical exponential decay rewritten with `pCrit`.
theorem exponential_decay_below_pCrit {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp : p < pCrit d) :
    exists c : Real, 0 < c /\
      forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real))) := by
  sorry

-- M0 stub: supercritical density lower bound rewritten with `pCrit`.
theorem supercritical_lower_bound_above_pCrit {d : Nat} {p : Real}
    (hp : pCrit d < p) (hp1 : p < 1) :
    theta d p >= (p - pCrit d) / (p * (1 - pCrit d)) := by
  sorry

end Sharpness
