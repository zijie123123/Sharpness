/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.Independence
import Sharpness.Monotonicity

/-!
# Russo's Formula

This file proves finite Boolean-cube identities culminating in Russo's
closed-pivotal formula.
-/

namespace Sharpness

open scoped BigOperators

section BooleanCube

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Real-valued indicator, with classical decidability kept out of theorem statements. -/
noncomputable def indic (P : Prop) (x : Real) : Real := by
  classical
  exact if P then x else 0

/-- Force one Boolean coordinate to a chosen value. -/
def forceBool (e : α) (b : Bool) (sigma : α -> Bool) : α -> Bool :=
  fun f => if f = e then b else sigma f

/-- Closed-pivotality on a finite Boolean cube. -/
def ClosedPivotalBool (A : (α -> Bool) -> Prop) (e : α)
    (sigma : α -> Bool) : Prop :=
  sigma e = false /\ ¬ A sigma /\ A (forceBool e true sigma)

/-- Rebuild a configuration from one coordinate and an assignment of the other coordinates. -/
def configAt (e : α) (b : Bool) (tau : {f : α // f ≠ e} -> Bool) : α -> Bool :=
  fun f => if h : f = e then b else tau ⟨f, h⟩

/-- Delete one coordinate from an assignment. -/
def deleteCoord (e : α) (sigma : α -> Bool) : {f : α // f ≠ e} -> Bool :=
  fun f => sigma f.1

omit [Fintype α] in
@[simp] lemma configAt_self (e : α) (b : Bool)
    (tau : {f : α // f ≠ e} -> Bool) :
    configAt e b tau e = b := by
  simp [configAt]

omit [Fintype α] in
@[simp] lemma configAt_ne (e f : α) (hfe : f ≠ e) (b : Bool)
    (tau : {f : α // f ≠ e} -> Bool) :
    configAt e b tau f = tau ⟨f, hfe⟩ := by
  simp [configAt, hfe]

omit [Fintype α] in
@[simp] lemma deleteCoord_configAt (e : α) (b : Bool)
    (tau : {f : α // f ≠ e} -> Bool) :
    deleteCoord e (configAt e b tau) = tau := by
  funext f
  simp [deleteCoord, configAt, f.2]

omit [Fintype α] in
@[simp] lemma forceBool_configAt_false (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    forceBool e true (configAt e false tau) = configAt e true tau := by
  funext f
  by_cases h : f = e
  · subst f
    simp [forceBool]
  · simp [forceBool, h]

/-- The one-site Bernoulli factor. -/
def boolFactor (sigma : α -> Bool) (e : α) (q : Real) : Real :=
  if sigma e then q else 1 - q

/-- Derivative contribution of one coordinate in one configuration. -/
noncomputable def bernWeightScoreCoord (p : Real) (sigma : α -> Bool)
    (e : α) : Real :=
  bernWeight p (deleteCoord e sigma) * (if sigma e then (1 : Real) else -1)

lemma erase_prod_boolFactor_eq_deleteCoord (p : Real) (sigma : α -> Bool) (e : α) :
    ((Finset.univ.erase e).prod fun f : α => boolFactor sigma f p) =
      bernWeight p (deleteCoord e sigma) := by
  classical
  calc
    ((Finset.univ.erase e).prod fun f : α => boolFactor sigma f p)
        = Finset.univ.prod fun f : {f : α // f ≠ e} =>
            boolFactor sigma f.1 p := by
          exact Finset.prod_subtype (s := Finset.univ.erase e)
            (p := fun f : α => f ≠ e)
            (h := by intro f; simp [Finset.mem_erase])
            (f := fun f : α => boolFactor sigma f p)
    _ = bernWeight p (deleteCoord e sigma) := by
          rfl

lemma bernWeight_hasDerivAt_score (sigma : α -> Bool) (p : Real) :
    HasDerivAt (fun q : Real => bernWeight q sigma)
      (Finset.univ.sum fun e : α => bernWeightScoreCoord p sigma e) p := by
  classical
  have hprod :
      HasDerivAt (fun q : Real => Finset.univ.prod fun e : α => boolFactor sigma e q)
        (Finset.univ.sum fun e : α =>
          ((Finset.univ.erase e).prod fun f : α => boolFactor sigma f p) *
            (if sigma e then (1 : Real) else -1)) p := by
    simpa [smul_eq_mul] using
      (HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset α))
        (f := fun e q => boolFactor sigma e q)
        (f' := fun e => if sigma e then (1 : Real) else -1)
        (x := p)
        (by
          intro e _he
          by_cases h : sigma e
          · simpa [boolFactor, h] using (hasDerivAt_id' p)
          · simpa [boolFactor, h] using ((hasDerivAt_id' p).const_sub (1 : Real))))
  convert hprod using 1
  · ext q
    simp [bernWeight, boolFactor]
  · refine Finset.sum_congr rfl ?_
    intro e _he
    by_cases h : sigma e
    · simp [bernWeightScoreCoord, h, erase_prod_boolFactor_eq_deleteCoord]
    · simp [bernWeightScoreCoord, h, erase_prod_boolFactor_eq_deleteCoord]

@[simp] lemma bernWeight_configAt_false (p : Real) (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    bernWeight p (configAt e false tau) = (1 - p) * bernWeight p tau := by
  classical
  calc
    bernWeight p (configAt e false tau)
        = (if configAt e false tau e then p else 1 - p) *
            (Finset.univ.prod fun f : {f : α // f ≠ e} =>
              if configAt e false tau f.1 then p else 1 - p) := by
          dsimp [bernWeight]
          rw [Fintype.prod_eq_mul_prod_subtype_ne]
    _ = (1 - p) * bernWeight p tau := by
          have hrest :
              (Finset.univ.prod fun f : {f : α // f ≠ e} =>
                if configAt e false tau f.1 then p else 1 - p) = bernWeight p tau := by
            dsimp [bernWeight]
            refine Finset.prod_congr rfl ?_
            intro f _hf
            simp [configAt, f.2]
          simp [hrest]

@[simp] lemma bernWeight_configAt_true (p : Real) (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    bernWeight p (configAt e true tau) = p * bernWeight p tau := by
  classical
  calc
    bernWeight p (configAt e true tau)
        = (if configAt e true tau e then p else 1 - p) *
            (Finset.univ.prod fun f : {f : α // f ≠ e} =>
              if configAt e true tau f.1 then p else 1 - p) := by
          dsimp [bernWeight]
          rw [Fintype.prod_eq_mul_prod_subtype_ne]
    _ = p * bernWeight p tau := by
          have hrest :
              (Finset.univ.prod fun f : {f : α // f ≠ e} =>
                if configAt e true tau f.1 then p else 1 - p) = bernWeight p tau := by
            dsimp [bernWeight]
            refine Finset.prod_congr rfl ?_
            intro f _hf
            simp [configAt, f.2]
          simp [hrest]

@[simp] lemma scoreCoord_configAt_false (p : Real) (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    bernWeightScoreCoord p (configAt e false tau) e = -bernWeight p tau := by
  simp [bernWeightScoreCoord]

@[simp] lemma scoreCoord_configAt_true (p : Real) (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    bernWeightScoreCoord p (configAt e true tau) e = bernWeight p tau := by
  simp [bernWeightScoreCoord]

/-- Split a Boolean assignment into the distinguished coordinate and the other coordinates. -/
def splitAt (e : α) : (α -> Bool) ≃ Bool × ({f : α // f ≠ e} -> Bool) where
  toFun sigma := (sigma e, deleteCoord e sigma)
  invFun x := configAt e x.1 x.2
  left_inv sigma := by
    funext f
    by_cases h : f = e
    · subst f
      simp
    · simp [deleteCoord, h]
  right_inv x := by
    rcases x with ⟨b, tau⟩
    apply Prod.ext
    · simp
    · funext f
      simp [deleteCoord, configAt, f.2]

lemma score_pair_eq_pivotal (A : (α -> Bool) -> Prop)
    (hinc : IncreasingBoolEvent A) (p : Real) (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    indic (A (configAt e false tau)) (bernWeightScoreCoord p (configAt e false tau) e) +
      indic (A (configAt e true tau)) (bernWeightScoreCoord p (configAt e true tau) e) =
    indic (ClosedPivotalBool A e (configAt e false tau)) (bernWeight p tau) := by
  classical
  have hle : BoolAssignmentLE (configAt e false tau) (configAt e true tau) := by
    intro f hf
    by_cases h : f = e
    · subst f
      simp at hf
    · simpa [h] using hf
  have hmono : A (configAt e false tau) -> A (configAt e true tau) := hinc hle
  by_cases hF : A (configAt e false tau)
  · have hT : A (configAt e true tau) := hmono hF
    have hnotCP : ¬ ClosedPivotalBool A e (configAt e false tau) := by
      intro hcp
      exact hcp.2.1 hF
    simp [indic, hF, hT, hnotCP]
  · by_cases hT : A (configAt e true tau)
    · have hCP : ClosedPivotalBool A e (configAt e false tau) := by
        refine ⟨?_, hF, ?_⟩
        · simp
        · simpa using hT
      simp [indic, hF, hT, hCP]
    · have hnotCP : ¬ ClosedPivotalBool A e (configAt e false tau) := by
        intro hcp
        exact hT (by simpa using hcp.2.2)
      simp [indic, hF, hT, hnotCP]

omit [Fintype α] in
lemma closedPivotal_configAt_true_false (A : (α -> Bool) -> Prop) (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    ¬ ClosedPivotalBool A e (configAt e true tau) := by
  intro h
  simpa using h.1

lemma closedPivotal_prob_pair (A : (α -> Bool) -> Prop) (p : Real) (e : α)
    (tau : {f : α // f ≠ e} -> Bool) :
    indic (ClosedPivotalBool A e (configAt e false tau))
        (bernWeight p (configAt e false tau)) +
      indic (ClosedPivotalBool A e (configAt e true tau))
        (bernWeight p (configAt e true tau)) =
    (1 - p) * indic (ClosedPivotalBool A e (configAt e false tau))
        (bernWeight p tau) := by
  classical
  have htrue : ¬ ClosedPivotalBool A e (configAt e true tau) :=
    closedPivotal_configAt_true_false A e tau
  by_cases hcp : ClosedPivotalBool A e (configAt e false tau)
  · simp [indic, hcp, htrue]
  · simp [indic, hcp, htrue]

lemma scoreCoord_sum_eq_closedPivotal (A : (α -> Bool) -> Prop)
    (hinc : IncreasingBoolEvent A) {p : Real} (hp1 : p < 1) (e : α) :
    (Finset.univ.sum fun sigma : α -> Bool =>
      indic (A sigma) (bernWeightScoreCoord p sigma e)) =
    (1 / (1 - p)) * bernProb p (ClosedPivotalBool A e) := by
  classical
  let split := splitAt e
  have hscoreSplit :
      (Finset.univ.sum fun sigma : α -> Bool =>
        indic (A sigma) (bernWeightScoreCoord p sigma e)) =
      Finset.univ.sum fun x : Bool × ({f : α // f ≠ e} -> Bool) =>
        indic (A (split.symm x)) (bernWeightScoreCoord p (split.symm x) e) := by
    refine Fintype.sum_equiv split
      (fun sigma : α -> Bool => indic (A sigma) (bernWeightScoreCoord p sigma e))
      (fun x : Bool × ({f : α // f ≠ e} -> Bool) =>
        indic (A (split.symm x)) (bernWeightScoreCoord p (split.symm x) e)) ?_
    intro sigma
    simp [split]
  have hprobSplit :
      bernProb p (ClosedPivotalBool A e) =
      Finset.univ.sum fun x : Bool × ({f : α // f ≠ e} -> Bool) =>
        indic (ClosedPivotalBool A e (split.symm x)) (bernWeight p (split.symm x)) := by
    dsimp [bernProb]
    exact Fintype.sum_equiv split
      (fun sigma : α -> Bool =>
        indic (ClosedPivotalBool A e sigma) (bernWeight p sigma))
      (fun x : Bool × ({f : α // f ≠ e} -> Bool) =>
        indic (ClosedPivotalBool A e (split.symm x)) (bernWeight p (split.symm x)))
      (by intro sigma; simp [split, indic])
  have hscoreFib :
      (Finset.univ.sum fun x : Bool × ({f : α // f ≠ e} -> Bool) =>
        indic (A (split.symm x)) (bernWeightScoreCoord p (split.symm x) e)) =
      Finset.univ.sum fun tau : {f : α // f ≠ e} -> Bool =>
        indic (A (configAt e true tau)) (bernWeightScoreCoord p (configAt e true tau) e) +
        indic (A (configAt e false tau)) (bernWeightScoreCoord p (configAt e false tau) e) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl ?_
    intro tau _htau
    simp [splitAt, split]
  have hprobFib :
      (Finset.univ.sum fun x : Bool × ({f : α // f ≠ e} -> Bool) =>
        indic (ClosedPivotalBool A e (split.symm x)) (bernWeight p (split.symm x))) =
      Finset.univ.sum fun tau : {f : α // f ≠ e} -> Bool =>
        indic (ClosedPivotalBool A e (configAt e true tau)) (bernWeight p (configAt e true tau)) +
        indic (ClosedPivotalBool A e (configAt e false tau)) (bernWeight p (configAt e false tau)) := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl ?_
    intro tau _htau
    simp [splitAt, split]
  have hpne : 1 - p ≠ 0 := sub_ne_zero.mpr (ne_of_gt hp1)
  rw [hscoreSplit, hprobSplit, hscoreFib, hprobFib]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro tau _htau
  rw [add_comm
    (indic (ClosedPivotalBool A e (configAt e true tau))
      (bernWeight p (configAt e true tau)))
    (indic (ClosedPivotalBool A e (configAt e false tau))
      (bernWeight p (configAt e false tau)))]
  rw [closedPivotal_prob_pair]
  rw [add_comm
    (indic (A (configAt e true tau))
      (bernWeightScoreCoord p (configAt e true tau) e))
    (indic (A (configAt e false tau))
      (bernWeightScoreCoord p (configAt e false tau) e))]
  rw [← score_pair_eq_pivotal A hinc]
  field_simp [hpne]

omit [DecidableEq α] in
lemma indic_sum (P : Prop) (f : α -> Real) :
    indic P (Finset.univ.sum f) = Finset.univ.sum fun e : α => indic P (f e) := by
  classical
  by_cases hP : P <;> simp [indic, hP]

lemma bernProb_hasDerivAt_score (A : (α -> Bool) -> Prop) (p : Real) :
    HasDerivAt (fun q : Real => bernProb q A)
      (Finset.univ.sum fun sigma : α -> Bool =>
        indic (A sigma) (Finset.univ.sum fun e : α => bernWeightScoreCoord p sigma e)) p := by
  classical
  dsimp [bernProb]
  refine HasDerivAt.fun_sum ?_
  intro sigma _hsigma
  by_cases hA : A sigma
  · simpa [indic, hA] using bernWeight_hasDerivAt_score sigma p
  · simpa [indic, hA] using (hasDerivAt_const (x := p)
      (c := (0 : Real)))

lemma score_total_eq_closedPivotal (A : (α -> Bool) -> Prop)
    (hinc : IncreasingBoolEvent A) {p : Real} (hp1 : p < 1) :
    (Finset.univ.sum fun sigma : α -> Bool =>
      indic (A sigma) (Finset.univ.sum fun e : α => bernWeightScoreCoord p sigma e)) =
    (1 / (1 - p)) *
      (Finset.univ.sum fun e : α => bernProb p (ClosedPivotalBool A e)) := by
  classical
  calc
    (Finset.univ.sum fun sigma : α -> Bool =>
      indic (A sigma) (Finset.univ.sum fun e : α => bernWeightScoreCoord p sigma e))
        = Finset.univ.sum fun sigma : α -> Bool =>
            Finset.univ.sum fun e : α => indic (A sigma) (bernWeightScoreCoord p sigma e) := by
          refine Finset.sum_congr rfl ?_
          intro sigma _hsigma
          exact indic_sum (A sigma) (fun e : α => bernWeightScoreCoord p sigma e)
    _ = Finset.univ.sum fun e : α =>
          Finset.univ.sum fun sigma : α -> Bool =>
            indic (A sigma) (bernWeightScoreCoord p sigma e) := by
          rw [Finset.sum_comm]
    _ = Finset.univ.sum fun e : α =>
          (1 / (1 - p)) * bernProb p (ClosedPivotalBool A e) := by
          refine Finset.sum_congr rfl ?_
          intro e _he
          exact scoreCoord_sum_eq_closedPivotal A hinc hp1 e
    _ = (1 / (1 - p)) *
          (Finset.univ.sum fun e : α => bernProb p (ClosedPivotalBool A e)) := by
          rw [Finset.mul_sum]

/-- Russo's formula on a finite Boolean product in closed-pivotal form. -/
theorem bernProb_russo_closed_pivotal (A : (α -> Bool) -> Prop)
    (hinc : IncreasingBoolEvent A) {p : Real} (_hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q : Real => bernProb q A)
      ((1 / (1 - p)) *
        (Finset.univ.sum fun e : α => bernProb p (ClosedPivotalBool A e))) p := by
  convert bernProb_hasDerivAt_score A p using 1
  exact (score_total_eq_closedPivotal A hinc hp1).symm

end BooleanCube

/-- Force a bond to be open in a configuration. -/
def forceOpen {d : Nat} (e : Bond d) (omega : Config d) : Config d :=
  fun f => if f = e then true else omega f

/-- Closed-pivotal event for an increasing local event. -/
def ClosedPivotal {d : Nat} (E : LocalEvent d) (e : Bond d)
    (omega : Config d) : Prop :=
  omega e = false /\ ¬ E.pred omega /\ E.pred (forceOpen e omega)

theorem closedPivotal_dependsOn {d : Nat} (E : LocalEvent d) (e : Bond d) :
    DependsOn (insert e E.support) (ClosedPivotal E e) := by
  intro omega omega' hsame
  have hsameE : forall f, f ∈ E.support -> omega f = omega' f := by
    intro f hf
    exact hsame f (Finset.mem_insert_of_mem hf)
  have hsameForce :
      forall f, f ∈ E.support -> forceOpen e omega f = forceOpen e omega' f := by
    intro f hf
    by_cases hfe : f = e
    · simp [forceOpen, hfe]
    · simp [forceOpen, hfe, hsameE f hf]
  constructor
  · rintro ⟨hclosed, hnot, hopen⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hsame e (Finset.mem_insert_self e E.support)] using hclosed
    · intro hE'
      exact hnot ((E.isLocal hsameE).mpr hE')
    · exact (E.isLocal hsameForce).mp hopen
  · rintro ⟨hclosed, hnot, hopen⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [hsame e (Finset.mem_insert_self e E.support)] using hclosed
    · intro hE
      exact hnot ((E.isLocal hsameE).mp hE)
    · exact (E.isLocal hsameForce).mpr hopen

/-- Local event that a fixed bond is closed-pivotal. -/
def closedPivotalEvent {d : Nat} (E : LocalEvent d) (e : Bond d) : LocalEvent d :=
  { support := insert e E.support
    pred := ClosedPivotal E e
    isLocal := closedPivotal_dependsOn E e }

lemma closedPivotal_restrict_iff {d : Nat} (E : LocalEvent d) {e : Bond d}
    (he : e ∈ E.support) (sigma : E.support -> Bool) :
    ClosedPivotal E e (extendConfig E.support sigma) <->
      ClosedPivotalBool
        (fun sigma : E.support -> Bool => E.pred (extendConfig E.support sigma))
        ⟨e, he⟩ sigma := by
  classical
  have hsame :
      forall f, f ∈ E.support ->
        forceOpen e (extendConfig E.support sigma) f =
          extendConfig E.support (forceBool ⟨e, he⟩ true sigma) f := by
    intro f hf
    by_cases hfe : f = e
    · subst f
      simp [forceOpen, forceBool, extendConfig, he]
    · have hsub : (⟨f, hf⟩ : E.support) ≠ ⟨e, he⟩ := by
        intro h
        exact hfe (Subtype.ext_iff.mp h)
      simp [forceOpen, forceBool, extendConfig, hf, hfe, hsub]
  constructor
  · rintro ⟨hclosed, hnot, hopen⟩
    refine ⟨?_, hnot, ?_⟩
    · simpa [extendConfig, he] using hclosed
    · exact (E.isLocal hsame).mp hopen
  · rintro ⟨hclosed, hnot, hopen⟩
    refine ⟨?_, hnot, ?_⟩
    · simpa [extendConfig, he] using hclosed
    · exact (E.isLocal hsame).mpr hopen

lemma closedPivotal_prob_restrict {d : Nat} (E : LocalEvent d) {p : Real}
    (e : E.support) :
    bernProb p
        (ClosedPivotalBool
          (fun sigma : E.support -> Bool => E.pred (extendConfig E.support sigma)) e) =
      Prob p (closedPivotalEvent E e.1) := by
  classical
  have hsub : insert e.1 E.support <= E.support := by
    intro f hf
    rcases Finset.mem_insert.mp hf with h | h
    · subst f
      exact e.2
    · exact h
  calc
    bernProb p
        (ClosedPivotalBool
          (fun sigma : E.support -> Bool => E.pred (extendConfig E.support sigma)) e)
        = ProbOn p E.support
            (fun sigma => ClosedPivotal E e.1 (extendConfig E.support sigma)) := by
          dsimp [ProbOn]
          congr
          funext sigma
          exact propext (closedPivotal_restrict_iff E e.2 sigma).symm
    _ = Prob p (closedPivotalEvent E e.1) := by
          exact (prob_support_mono (p := p) (closedPivotalEvent E e.1) hsub).symm

/-- Russo's formula in closed-pivotal form for finite local increasing events. -/
theorem russo_closed_pivotal {d : Nat} (E : LocalEvent d) (hinc : Increasing E)
    {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q => Prob q E)
      ((1 / (1 - p)) * (E.support.sum fun e => Prob p (closedPivotalEvent E e))) p := by
  classical
  let A : (E.support -> Bool) -> Prop :=
    fun sigma => E.pred (extendConfig E.support sigma)
  have hincA : IncreasingBoolEvent A := by
    intro sigma tau hle hsigma
    exact hinc (extendConfig_mono hle) hsigma
  have hgeneric := bernProb_russo_closed_pivotal (A := A) hincA hp0 hp1
  have hsum :
      (Finset.univ.sum fun e : E.support => bernProb p (ClosedPivotalBool A e)) =
        E.support.sum fun e => Prob p (closedPivotalEvent E e) := by
    calc
      (Finset.univ.sum fun e : E.support => bernProb p (ClosedPivotalBool A e))
          = Finset.univ.sum fun e : E.support => Prob p (closedPivotalEvent E e.1) := by
            refine Finset.sum_congr rfl ?_
            intro e _he
            exact closedPivotal_prob_restrict E e
      _ = E.support.sum fun e => Prob p (closedPivotalEvent E e) := by
            simpa using
              (Finset.sum_coe_sort E.support
                (fun e : Bond d => Prob p (closedPivotalEvent E e)))
  convert hgeneric using 1
  · rfl
  · rw [hsum]

end Sharpness
