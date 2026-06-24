import Sharpness.Clusters
import Sharpness.Events
import Sharpness.Independence

namespace Sharpness

open scoped BigOperators

/--
Cluster last-exit expansion for the finite-volume boundary inequality.

Missing mathematical fact: formalize the decomposition by possible cluster values
`C_S(u)=C0`, choose the last exit from `C0`, apply the three-event independence
for the cluster event, the boundary bond, and the avoiding connection from the
outside endpoint to `B`, then drop the avoidance condition and sum over `C0`.
-/
private theorem boundary_inequality_cluster_expansion {d : Nat}
    (T S B : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ S) (hST : S <= T) (hBT : B <= T) (hBS : Disjoint B S)
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p (connToSetInEvent T u B) <=
      (orientedBoundary S).sum
        (fun e => p * Prob p (connInEvent S u e.1) *
          Prob p (connToSetInEvent T e.2 B)) := by
  sorry

/-- Lemma 4, finite-volume boundary expansion inequality. -/
theorem boundary_inequality {d : Nat}
    (T S B : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ S) (hST : S <= T) (hBT : B <= T) (hBS : Disjoint B S)
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p (connToSetInEvent T u B) <=
      (orientedBoundary S).sum
        (fun e => p * Prob p (connInEvent S u e.1) *
          Prob p (connToSetInEvent T e.2 B)) := by
  exact boundary_inequality_cluster_expansion T S B u hu hST hBT hBS hp0 hp1

end Sharpness
