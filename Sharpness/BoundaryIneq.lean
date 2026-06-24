import Sharpness.Clusters
import Sharpness.Events
import Sharpness.Independence

namespace Sharpness

open scoped BigOperators

-- M0 stub: Lemma 4, finite-volume boundary expansion inequality.
theorem boundary_inequality {d : Nat}
    (T S B : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ S) (hST : S <= T) (hBT : B <= T) (hBS : Disjoint B S)
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p (connToSetInEvent T u B) <=
      (orientedBoundary S).sum
        (fun e => p * Prob p (connInEvent S u e.1) *
          Prob p (connToSetInEvent T e.2 B)) := by
  sorry

end Sharpness
