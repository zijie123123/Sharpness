import Sharpness.FiniteBernoulli

namespace Sharpness

open scoped BigOperators

/-- A global event depends only on the finite support `F`. -/
def DependsOn {d : Nat} (F : Finset (Bond d)) (A : Config d -> Prop) : Prop :=
  forall ⦃omega omega' : Config d⦄,
    (forall e, e ∈ F -> omega e = omega' e) -> (A omega <-> A omega')

/-- A local event is a global predicate together with an explicit finite bond support. -/
structure LocalEvent (d : Nat) where
  support : Finset (Bond d)
  pred : Config d -> Prop
  isLocal : DependsOn support pred

/-- Extend an assignment on a finite support to a global configuration. -/
noncomputable def extendConfig {d : Nat} (F : Finset (Bond d))
    (sigma : F -> Bool) : Config d :=
  fun e => if h : e ∈ F then sigma ⟨e, h⟩ else false

/-- Probability of a local event, computed on its explicit finite support. -/
noncomputable def Prob {d : Nat} (p : Real) (E : LocalEvent d) : Real :=
  ProbOn p E.support fun sigma => E.pred (extendConfig E.support sigma)

private noncomputable def supportExtensionEquiv {d : Nat}
    (F G : Finset (Bond d)) (hsub : F <= G) : ↥F ⊕ ↥(G \ F) ≃ ↥G where
  toFun x :=
    match x with
    | Sum.inl e => ⟨e.1, hsub e.2⟩
    | Sum.inr e => ⟨e.1, (Finset.mem_sdiff.mp e.2).1⟩
  invFun e :=
    if he : e.1 ∈ F then
      Sum.inl ⟨e.1, he⟩
    else
      Sum.inr ⟨e.1, Finset.mem_sdiff.mpr ⟨e.2, he⟩⟩
  left_inv := by
    rintro (e | e)
    · simp
    · have heF : e.1 ∉ F := (Finset.mem_sdiff.mp e.2).2
      simp [heF]
  right_inv := by
    intro e
    by_cases heF : e.1 ∈ F
    · simp [heF]
    · simp [heF]

private theorem supportExtensionEquiv_symm_left {d : Nat}
    (F G : Finset (Bond d)) (hsub : F <= G) {e : Bond d} (he : e ∈ F) :
    (supportExtensionEquiv F G hsub).symm ⟨e, hsub he⟩ = Sum.inl ⟨e, he⟩ := by
  classical
  simp [supportExtensionEquiv, he]

/-- Complement of a local event. -/
def LocalEvent.compl {d : Nat} (E : LocalEvent d) : LocalEvent d :=
  { support := E.support
    pred := fun omega => ¬ E.pred omega
    isLocal := by
      intro omega omega' hsame
      exact not_congr (E.isLocal hsame) }

/-- Intersection of two local events. -/
def LocalEvent.inter {d : Nat} (E F : LocalEvent d) : LocalEvent d :=
  { support := E.support ∪ F.support
    pred := fun omega => E.pred omega /\ F.pred omega
    isLocal := by
      intro omega omega' hsame
      constructor
      · intro h
        exact ⟨(E.isLocal (by
          intro e he
          exact hsame e (Finset.mem_union.mpr (Or.inl he)))).mp h.1,
          (F.isLocal (by
            intro e he
            exact hsame e (Finset.mem_union.mpr (Or.inr he)))).mp h.2⟩
      · intro h
        exact ⟨(E.isLocal (by
          intro e he
          exact hsame e (Finset.mem_union.mpr (Or.inl he)))).mpr h.1,
          (F.isLocal (by
            intro e he
            exact hsame e (Finset.mem_union.mpr (Or.inr he)))).mpr h.2⟩ }

/-- Union of two local events. -/
def LocalEvent.union {d : Nat} (E F : LocalEvent d) : LocalEvent d :=
  { support := E.support ∪ F.support
    pred := fun omega => E.pred omega \/ F.pred omega
    isLocal := by
      intro omega omega' hsame
      constructor
      · intro h
        cases h with
        | inl hE =>
            exact Or.inl ((E.isLocal (by
              intro e he
              exact hsame e (Finset.mem_union.mpr (Or.inl he)))).mp hE)
        | inr hF =>
            exact Or.inr ((F.isLocal (by
              intro e he
              exact hsame e (Finset.mem_union.mpr (Or.inr he)))).mp hF)
      · intro h
        cases h with
        | inl hE =>
            exact Or.inl ((E.isLocal (by
              intro e he
              exact hsame e (Finset.mem_union.mpr (Or.inl he)))).mpr hE)
        | inr hF =>
            exact Or.inr ((F.isLocal (by
              intro e he
              exact hsame e (Finset.mem_union.mpr (Or.inr he)))).mpr hF) }

theorem prob_support_mono {d : Nat} {p : Real} (E : LocalEvent d)
    {G : Finset (Bond d)} (hsub : E.support <= G) :
    Prob p E =
      ProbOn p G (fun sigma => E.pred (extendConfig G sigma)) := by
  classical
  let eCoord := supportExtensionEquiv E.support G hsub
  have hlocal :
      (fun sigma : ↥E.support ⊕ ↥(G \ E.support) -> Bool =>
          E.pred (extendConfig G (fun g : G => sigma (eCoord.symm g)))) =
        (fun sigma : ↥E.support ⊕ ↥(G \ E.support) -> Bool =>
          E.pred (extendConfig E.support (fun f : E.support => sigma (Sum.inl f)))) := by
    funext sigma
    exact propext (E.isLocal (by
      intro e he
      have hG : e ∈ G := hsub he
      simp [extendConfig, hG, he, supportExtensionEquiv_symm_left E.support G hsub he, eCoord]))
  calc
    Prob p E
        = bernProb p
            (fun sigma : E.support -> Bool =>
              E.pred (extendConfig E.support sigma)) := rfl
    _ = bernProb p
            (fun sigma : ↥E.support ⊕ ↥(G \ E.support) -> Bool =>
              E.pred (extendConfig E.support (fun f : E.support => sigma (Sum.inl f)))) := by
          exact (bernProb_sum_left (α := E.support) (β := ↥(G \ E.support)) p
            (fun sigma : E.support -> Bool =>
              E.pred (extendConfig E.support sigma))).symm
    _ = bernProb p
            (fun sigma : ↥E.support ⊕ ↥(G \ E.support) -> Bool =>
              E.pred (extendConfig G (fun g : G => sigma (eCoord.symm g)))) := by
          rw [hlocal]
    _ = bernProb p
            (fun sigma : G -> Bool => E.pred (extendConfig G sigma)) := by
          exact bernProb_reindex (α := ↥E.support ⊕ ↥(G \ E.support)) (β := G)
            p eCoord (fun sigma : G -> Bool => E.pred (extendConfig G sigma))
    _ = ProbOn p G (fun sigma => E.pred (extendConfig G sigma)) := rfl

end Sharpness
