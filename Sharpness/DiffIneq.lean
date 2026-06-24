import Sharpness.Phi
import Sharpness.Russo

namespace Sharpness

open scoped BigOperators

/-- Finite-volume exit from a vertex `x` through the oriented boundary of `Lam`. -/
def ExitFromPred {d : Nat} (Lam : Finset (Vertex d)) (x : Vertex d)
    (omega : Config d) : Prop :=
  exists e, exists he : e ∈ orientedBoundary Lam,
    ConnIn omega Lam x e.1 /\
    omega (bondOfAdj (orientedBoundary_adj he)) = true

/-- Exit from the origin is the finite exit predicate used by `exitEvent`. -/
theorem exitFrom_zero_iff_exitPred {d : Nat} (Lam : Finset (Vertex d))
    (omega : Config d) :
    ExitFromPred Lam (0 : Vertex d) omega <-> ExitPred Lam omega :=
  Iff.rfl

/-- Exit from a fixed vertex is local on the finite exit support of `Lam`. -/
theorem exitFrom_dependsOn {d : Nat} (Lam : Finset (Vertex d)) (x : Vertex d) :
    DependsOn (internalBonds Lam ∪ exitBonds Lam) (ExitFromPred Lam x) := by
  intro omega omega' hsame
  constructor
  · rintro ⟨e, he, hconn, hopen⟩
    have hconn' : ConnIn omega' Lam x e.1 :=
      (connIn_dependsOn Lam x e.1 (by
        intro b hb
        exact hsame b (Finset.mem_union.mpr (Or.inl hb)))).mp hconn
    have hb : bondOfAdj (orientedBoundary_adj he) ∈ exitBonds Lam :=
      bondOfAdj_mem_exitBonds he
    exact ⟨e, he, hconn', by
      simpa [hsame _ (Finset.mem_union.mpr (Or.inr hb))] using hopen⟩
  · rintro ⟨e, he, hconn, hopen⟩
    have hconn' : ConnIn omega Lam x e.1 :=
      (connIn_dependsOn Lam x e.1 (by
        intro b hb
        exact hsame b (Finset.mem_union.mpr (Or.inl hb)))).mpr hconn
    have hb : bondOfAdj (orientedBoundary_adj he) ∈ exitBonds Lam :=
      bondOfAdj_mem_exitBonds he
    exact ⟨e, he, hconn', by
      simpa [hsame _ (Finset.mem_union.mpr (Or.inr hb))] using hopen⟩

/-- The random shield set `{x ∈ Lam | x` is not connected to `Lamᶜ`}. -/
noncomputable def Shield {d : Nat} (Lam : Finset (Vertex d))
    (omega : Config d) : Finset (Vertex d) := by
  classical
  exact Lam.filter fun x => ¬ ExitFromPred Lam x omega

/-- The origin belongs to the shield exactly when the finite exit event fails. -/
theorem zero_mem_shield_iff_not_exit {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) (omega : Config d) :
    (0 : Vertex d) ∈ Shield Lam omega <-> ¬ ExitPred Lam omega := by
  simp [Shield, h0, exitFrom_zero_iff_exitPred]

/-- Closing all internal edges of `S`. -/
noncomputable def closeInternalEdges {d : Nat} (S : Finset (Vertex d))
    (omega : Config d) : Config d :=
  fun e => if e ∈ internalBonds S then false else omega e

/-- The finite support for `{Shield = S}` after deleting internal `S`-edges. -/
noncomputable def shieldSupport {d : Nat} (Lam S : Finset (Vertex d)) :
    Finset (Bond d) :=
  (internalBonds Lam ∪ exitBonds Lam) \ internalBonds S

/-- Internal `S`-bonds are disjoint from the support used by the shield event. -/
theorem disjoint_internalBonds_shieldSupport {d : Nat}
    (Lam S : Finset (Vertex d)) :
    Disjoint (internalBonds S) (shieldSupport Lam S) := by
  rw [Finset.disjoint_left]
  intro b hbInt hbSupp
  exact (Finset.mem_sdiff.mp hbSupp).2 hbInt

/-- The shield value is local on the ambient finite exit support. -/
theorem shield_dependsOn_ambient {d : Nat} (Lam S : Finset (Vertex d)) :
    DependsOn (internalBonds Lam ∪ exitBonds Lam)
      (fun omega => Shield Lam omega = S) := by
  intro omega omega' hsame
  have hmem : forall x, x ∈ Shield Lam omega <-> x ∈ Shield Lam omega' := by
    intro x
    by_cases hx : x ∈ Lam
    · have hExit := exitFrom_dependsOn Lam x hsame
      simp [Shield, hx, hExit]
    · simp [Shield, hx]
  have hshield : Shield Lam omega = Shield Lam omega' := by
    exact Finset.ext hmem
  constructor
  · intro h
    exact hshield.symm.trans h
  · intro h
    exact hshield.trans h

/--
Deleted-internal-edge characterization of `{Shield = S}`.

Missing mathematical fact: prove the last-exit argument showing that, after closing all
internal `S`-edges, shield equality is equivalent to no `S`-vertex exiting and every
`Lam \ S` vertex exiting.
-/
theorem shield_eq_iff_deleted_internal {d : Nat}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam) (omega : Config d) :
    Shield Lam omega = S <->
      ((forall x, x ∈ S -> ¬ ExitFromPred Lam x (closeInternalEdges S omega)) /\
        (forall x, x ∈ Lam -> x ∉ S ->
          ExitFromPred Lam x (closeInternalEdges S omega))) := by
  sorry

/--
Support separation for the shield event `{Shield = S}`.

Missing mathematical fact: combine `shield_eq_iff_deleted_internal` with locality of finite
exit events in the deleted configuration to show that internal `S`-edges are irrelevant.
-/
theorem shield_dependsOn_noninternal {d : Nat}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam) :
    DependsOn (shieldSupport Lam S) (fun omega => Shield Lam omega = S) := by
  sorry

/-- Local event for a fixed shield value, using the separated support. -/
noncomputable def shieldEvent {d : Nat} (Lam S : Finset (Vertex d))
    (hS : S <= Lam) : LocalEvent d :=
  { support := shieldSupport Lam S
    pred := fun omega => Shield Lam omega = S
    isLocal := shield_dependsOn_noninternal Lam S hS }

/--
Pivotal equivalence on a fixed shield value.

Missing mathematical fact: prove the boundary-edge argument from the note: on
`{Shield = S}`, an oriented boundary bond `(x,y) ∈ ∂E S` is closed-pivotal for
`A_Lam` iff `0` is connected to `x` inside `S`.
-/
theorem closedPivotal_exit_iff_connIn_on_shield {d : Nat}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    {e : OrientedEdge d} (he : e ∈ orientedBoundary S) {omega : Config d}
    (hshield : Shield Lam omega = S) :
    ClosedPivotal (exitEvent Lam (hS h0S))
        (bondOfAdj (orientedBoundary_adj he)) omega <->
      ConnIn omega S (0 : Vertex d) e.1 := by
  sorry

/-- The finite minimum is below each admissible `phi p S`. -/
theorem phiMinIn_le_phi {d : Nat} {p : Real} {Lam S : Finset (Vertex d)}
    (h0 : (0 : Vertex d) ∈ Lam) (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S) :
    phiMinIn p Lam h0 <= phi p S := by
  classical
  exact Finset.inf'_le (f := phi p)
    (by
      rw [finiteSubsetsWithZero, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hS, h0S⟩)

/--
The shield decomposition lower bound for the Russo closed-pivotal sum.

Missing mathematical fact: formalize the finite sum decomposition over shield values, use
`closedPivotal_exit_iff_connIn_on_shield`, apply disjoint-support independence from
`shield_dependsOn_noninternal`, identify the boundary sum with `phi p S / p`, and sum
`Prob(Shield = S)` over `0 ∈ S` to get `1 - exitProb p Lam h0`.
-/
theorem exit_russo_sum_lower_bound {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) <=
      (1 / (1 - p)) *
        ((exitEvent Lam h0).support.sum
          fun e => Prob p (closedPivotalEvent (exitEvent Lam h0) e)) := by
  sorry

/-- Lemma 2, the fundamental finite-volume differential inequality. -/
theorem differential_inequality {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun q => exitProb q Lam h0) p >=
      (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) := by
  classical
  have hRusso := russo_closed_pivotal (exitEvent Lam h0)
    (exitEvent_increasing Lam h0) hp0 hp1
  have hderiv :
      deriv (fun q => Prob q (exitEvent Lam h0)) p =
        (1 / (1 - p)) *
          ((exitEvent Lam h0).support.sum
            fun e => Prob p (closedPivotalEvent (exitEvent Lam h0) e)) :=
    hRusso.deriv
  change
    (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) <=
      deriv (fun q => Prob q (exitEvent Lam h0)) p
  rw [hderiv]
  exact exit_russo_sum_lower_bound Lam h0 hp0 hp1

end Sharpness
