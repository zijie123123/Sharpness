import Sharpness.BoundaryIneq
import Sharpness.FiniteGeometry
import Sharpness.Phi

namespace Sharpness

-- M0 stub: Lemma 5, exponential decay below the finite-set critical point.
theorem exponential_decay_below_pTilde {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp : p < pTilde d) :
    exists c : Real, 0 < c /\
      forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real))) := by
  sorry

end Sharpness
