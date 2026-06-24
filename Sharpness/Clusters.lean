import Sharpness.LocalEvent
import Sharpness.Paths

namespace Sharpness

/-- The open cluster of `u` inside a finite vertex set `S`. -/
noncomputable def clusterIn {d : Nat} (omega : Config d)
    (S : Finset (Vertex d)) (u : Vertex d) : Finset (Vertex d) := by
  classical
  exact S.filter fun x => ConnIn omega S u x

/-- Predicate that the finite cluster inside `S` is exactly `C`. -/
def ClusterEqPred {d : Nat} (S C : Finset (Vertex d)) (u : Vertex d)
    (omega : Config d) : Prop :=
  clusterIn omega S u = C

/-- Bonds inside `S` with at least one endpoint ∈ the candidate cluster `C`. -/
noncomputable def clusterIncidentBonds {d : Nat}
    (S C : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact ((S.product S).filter fun e : Vertex d × Vertex d =>
    e.1 ≠ e.2 /\ Adj e.1 e.2 /\ (e.1 ∈ C \/ e.2 ∈ C)).attach.image
      fun e => bondOfAdj ((Finset.mem_filter.mp e.property).2.2.1)

-- M0 stub: the event `C_S(u) = C` depends only on internal bonds incident to `C`.
theorem cluster_eq_dependsOn_incident {d : Nat}
    (S C : Finset (Vertex d)) (u : Vertex d) :
    DependsOn (clusterIncidentBonds S C) (ClusterEqPred S C u) := by
  sorry

end Sharpness
