import Sharpness.Phi
import Sharpness.Russo

namespace Sharpness

-- M0 stub: Lemma 2, the fundamental finite-volume differential inequality.
theorem differential_inequality {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun q => exitProb q Lam h0) p >=
      (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) := by
  sorry

end Sharpness
