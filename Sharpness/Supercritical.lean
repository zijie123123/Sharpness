import Sharpness.DiffIneq
import Sharpness.OdeComparison

namespace Sharpness

-- M0 stub: Lemma 3, the lower bound above the finite-set critical point.
theorem supercritical_lower_bound_above_pTilde {d : Nat} {p : Real}
    (hp : pTilde d < p) (hp1 : p < 1) :
    theta d p >= (p - pTilde d) / (p * (1 - pTilde d)) := by
  sorry

end Sharpness
