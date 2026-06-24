import Sharpness.LocalEvent
import Sharpness.Paths

namespace Sharpness

/-- Predicate for the finite-volume exit event from `Lam`. -/
def ExitPred {d : Nat} (Lam : Finset (Vertex d)) (omega : Config d) : Prop :=
  exists e, exists he : e ∈ orientedBoundary Lam,
    ConnIn omega Lam (0 : Vertex d) e.1 /\
    omega (bondOfAdj (orientedBoundary_adj he)) = true

-- M0 stub: finite-set connectivity depends only on bonds internal to the finite set.
theorem connIn_dependsOn {d : Nat} (S : Finset (Vertex d)) (x y : Vertex d) :
    DependsOn (internalBonds S) (fun omega => ConnIn omega S x y) := by
  sorry

/-- Local event for `x` connected to `y` inside `S`. -/
noncomputable def connInEvent {d : Nat} (S : Finset (Vertex d)) (x y : Vertex d) :
    LocalEvent d :=
  { support := internalBonds S
    pred := fun omega => ConnIn omega S x y
    isLocal := connIn_dependsOn S x y }

-- M0 stub: the finite exit event is local on internal and boundary bonds of `Lam`.
theorem exitEvent_dependsOn {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) :
    DependsOn (internalBonds Lam ∪ exitBonds Lam) (ExitPred Lam) := by
  sorry

/-- Local event that `0` exits the finite vertex set `Lam`. -/
noncomputable def exitEvent {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) : LocalEvent d :=
  { support := internalBonds Lam ∪ exitBonds Lam
    pred := ExitPred Lam
    isLocal := exitEvent_dependsOn Lam h0 }

/-- Finite Bernoulli probability of the finite exit event from `Lam`. -/
noncomputable def exitProb {d : Nat} (p : Real) (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) : Real :=
  Prob p (exitEvent Lam h0)

/-- Finite box exit probability `P_p(0 <-> Lambda_n^c)`. -/
noncomputable def boxExitProb (d : Nat) (p : Real) (n : Nat) : Real :=
  exitProb p (ball d n) (zero_mem_ball d n)

/-- Connectivity from a vertex to a finite target set inside a finite ambient set. -/
def ConnToSetIn {d : Nat} (omega : Config d) (T : Finset (Vertex d))
    (u : Vertex d) (B : Finset (Vertex d)) : Prop :=
  exists b, b ∈ B /\ ConnIn omega T u b

-- M0 stub: finite target connectivity is local on the ambient internal bonds.
theorem connToSetIn_dependsOn {d : Nat} (T : Finset (Vertex d))
    (u : Vertex d) (B : Finset (Vertex d)) :
    DependsOn (internalBonds T) (fun omega => ConnToSetIn omega T u B) := by
  sorry

/-- Local event that `u` connects to the finite target set `B` inside `T`. -/
noncomputable def connToSetInEvent {d : Nat} (T : Finset (Vertex d))
    (u : Vertex d) (B : Finset (Vertex d)) : LocalEvent d :=
  { support := internalBonds T
    pred := fun omega => ConnToSetIn omega T u B
    isLocal := connToSetIn_dependsOn T u B }

/-- Infinite-cluster density defined as the decreasing-limit infimum of finite exit probabilities. -/
noncomputable def theta (d : Nat) (p : Real) : Real :=
  sInf (Set.range fun n : Nat => boxExitProb d p n)

-- M0 stub: `theta` is bounded above by every finite box exit probability.
theorem theta_le_boxExitProb (d : Nat) (p : Real) (n : Nat) :
    theta d p <= boxExitProb d p n := by
  sorry

-- M0 stub: an exponential upper bound on all finite exit probabilities forces `theta = 0`.
theorem theta_eq_zero_of_exponential_decay {d : Nat} {p c : Real}
    (hc : 0 < c)
    (hdecay : forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real)))) :
    theta d p = 0 := by
  sorry

-- M0 stub: uniform lower bounds on finite exit probabilities pass to `theta`.
theorem le_theta_of_le_boxExitProb {d : Nat} {p b : Real}
    (hb : forall n : Nat, b <= boxExitProb d p n) :
    b <= theta d p := by
  sorry

end Sharpness
