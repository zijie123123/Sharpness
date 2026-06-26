/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.LocalEvent

/-!
# Monotonicity

This file proves monotonicity of increasing local events under Bernoulli
parameter comparison.
-/

namespace Sharpness

open scoped BigOperators

/-- Coordinatewise partial order on configurations. -/
def ConfigLE {d : Nat} (omega omega' : Config d) : Prop :=
  forall e, omega e = true -> omega' e = true

/-- A local event is increasing if opening more bonds preserves occurrence. -/
def Increasing {d : Nat} (E : LocalEvent d) : Prop :=
  forall ⦃omega omega' : Config d⦄, ConfigLE omega omega' -> E.pred omega -> E.pred omega'

/-- Coordinatewise partial order on finite Boolean assignments. -/
def BoolAssignmentLE {α : Type*} (sigma tau : α -> Bool) : Prop :=
  forall e, sigma e = true -> tau e = true

/-- Increasing event on a finite Boolean cube. -/
def IncreasingBoolEvent {α : Type*} (A : (α -> Bool) -> Prop) : Prop :=
  forall ⦃sigma tau : α -> Bool⦄, BoolAssignmentLE sigma tau -> A sigma -> A tau

private theorem bernWeight_fin_cons {n : Nat} (p : Real) (b : Bool)
    (tau : Fin n -> Bool) :
    bernWeight p (Fin.cons b tau) = (if b then p else 1 - p) * bernWeight p tau := by
  classical
  cases b
  · dsimp [bernWeight]
    rw [Fin.prod_univ_succ]
    rfl
  · dsimp [bernWeight]
    rw [Fin.prod_univ_succ]
    rfl

private theorem bernProb_fin_succ {n : Nat} (p : Real)
    (A : (Fin (n + 1) -> Bool) -> Prop) :
    bernProb p A =
      (1 - p) * bernProb p (fun tau : Fin n -> Bool => A (Fin.cons false tau)) +
        p * bernProb p (fun tau : Fin n -> Bool => A (Fin.cons true tau)) := by
  classical
  have hsplit :
      bernProb p A =
        Finset.univ.sum fun x : Bool × (Fin n -> Bool) =>
          if A (Fin.cons x.1 x.2) then bernWeight p (Fin.cons x.1 x.2) else 0 := by
    dsimp [bernProb]
    refine Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).symm
      (fun sigma : Fin (n + 1) -> Bool => if A sigma then bernWeight p sigma else 0)
      (fun x : Bool × (Fin n -> Bool) =>
        if A (Fin.cons x.1 x.2) then bernWeight p (Fin.cons x.1 x.2) else 0) ?_
    intro sigma
    simp [Fin.cons_self_tail]
  rw [hsplit]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_bool]
  dsimp [bernProb]
  rw [add_comm]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro tau _
    by_cases hA : A (Fin.cons false tau)
    · simp [hA, bernWeight_fin_cons]
    · simp [hA]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro tau _
    by_cases hA : A (Fin.cons true tau)
    · simp [hA, bernWeight_fin_cons]
    · simp [hA]

private theorem IncreasingBoolEvent_fin_tail_false {n : Nat}
    {A : (Fin (n + 1) -> Bool) -> Prop} (hinc : IncreasingBoolEvent A) :
    IncreasingBoolEvent (fun tau : Fin n -> Bool => A (Fin.cons false tau)) := by
  intro sigma tau hle hA
  apply hinc ?_ hA
  intro i hi
  cases i using Fin.cases with
  | zero => simp at hi
  | succ j => simpa [Fin.cons] using hle j hi

private theorem IncreasingBoolEvent_fin_tail_true {n : Nat}
    {A : (Fin (n + 1) -> Bool) -> Prop} (hinc : IncreasingBoolEvent A) :
    IncreasingBoolEvent (fun tau : Fin n -> Bool => A (Fin.cons true tau)) := by
  intro sigma tau hle hA
  apply hinc ?_ hA
  intro i hi
  cases i using Fin.cases with
  | zero => simp
  | succ j => simpa [Fin.cons] using hle j hi

private theorem fin_false_le_true {n : Nat} (tau : Fin n -> Bool) :
    BoolAssignmentLE (Fin.cons false tau) (Fin.cons true tau) := by
  intro i hi
  cases i using Fin.cases with
  | zero => simp
  | succ j => simpa [Fin.cons] using hi

private theorem bernProb_fin_mono_parameter (n : Nat)
    {p q : Real} {A : (Fin n -> Bool) -> Prop}
    (hinc : IncreasingBoolEvent A) (hp0 : 0 <= p) (hpq : p <= q) (hq1 : q <= 1) :
    bernProb p A <= bernProb q A := by
  induction n with
  | zero =>
      rw [show bernProb p A = bernProb q A by
        classical
        simp [bernProb, bernWeight]]
  | succ n ih =>
      rw [bernProb_fin_succ (n := n) p A, bernProb_fin_succ (n := n) q A]
      let Af : (Fin n -> Bool) -> Prop := fun tau => A (Fin.cons false tau)
      let At : (Fin n -> Bool) -> Prop := fun tau => A (Fin.cons true tau)
      have hAf : bernProb p Af <= bernProb q Af :=
        ih (A := Af) (IncreasingBoolEvent_fin_tail_false hinc)
      have hAt : bernProb p At <= bernProb q At :=
        ih (A := At) (IncreasingBoolEvent_fin_tail_true hinc)
      have hp1 : p <= 1 := hpq.trans hq1
      have hq0 : 0 <= q := hp0.trans hpq
      have hAt_le_Af : bernProb p Af <= bernProb p At := by
        exact bernProb_mono (fun tau h => hinc (fin_false_le_true tau) h) hp0 hp1
      have hfalse_part :
          (1 - p) * bernProb p Af <=
            (1 - q) * bernProb q Af + (q - p) * bernProb q At := by
        have h1q_nonneg : 0 <= 1 - q := sub_nonneg.mpr hq1
        have hqmp_nonneg : 0 <= q - p := sub_nonneg.mpr hpq
        calc
          (1 - p) * bernProb p Af
              = (1 - q) * bernProb p Af + (q - p) * bernProb p Af := by ring
          _ <= (1 - q) * bernProb q Af + (q - p) * bernProb q At := by
                exact add_le_add
                  (mul_le_mul_of_nonneg_left hAf h1q_nonneg)
                  (mul_le_mul_of_nonneg_left (hAt_le_Af.trans hAt) hqmp_nonneg)
      calc
        (1 - p) * bernProb p Af + p * bernProb p At
            <= ((1 - q) * bernProb q Af + (q - p) * bernProb q At) +
                p * bernProb q At := by
              exact add_le_add hfalse_part (mul_le_mul_of_nonneg_left hAt hp0)
        _ = (1 - q) * bernProb q Af + q * bernProb q At := by ring

theorem bernProb_mono_parameter {α : Type*} [DecidableEq α] [Fintype α]
    {p q : Real} {A : (α -> Bool) -> Prop}
    (hinc : IncreasingBoolEvent A) (hp0 : 0 <= p) (hpq : p <= q) (hq1 : q <= 1) :
    bernProb p A <= bernProb q A := by
  classical
  let e : α ≃ Fin (Fintype.card α) := Fintype.equivFin α
  let AFin : (Fin (Fintype.card α) -> Bool) -> Prop :=
    fun sigma => A (fun a => sigma (e a))
  have hincFin : IncreasingBoolEvent AFin := by
    intro sigma tau hle hsigma
    exact hinc (by intro a ha; exact hle (e a) ha) hsigma
  have hfin := bernProb_fin_mono_parameter (Fintype.card α)
    (A := AFin) hincFin hp0 hpq hq1
  have hp_reindex :
      bernProb p A = bernProb p AFin := by
    have h := bernProb_reindex (α := α) (β := Fin (Fintype.card α)) p e AFin
    have hleft :
        (fun sigma : α -> Bool => AFin (fun b : Fin (Fintype.card α) => sigma (e.symm b))) =
          A := by
      funext sigma
      have harg :
          (fun a : α => (fun b : Fin (Fintype.card α) => sigma (e.symm b)) (e a)) =
            sigma := by
        funext a
        simp
      simp [AFin]
    calc
      bernProb p A = bernProb p
          (fun sigma : α -> Bool => AFin (fun b : Fin (Fintype.card α) => sigma (e.symm b))) := by
            rw [hleft]
      _ = bernProb p AFin := h
  have hq_reindex :
      bernProb q A = bernProb q AFin := by
    have h := bernProb_reindex (α := α) (β := Fin (Fintype.card α)) q e AFin
    have hleft :
        (fun sigma : α -> Bool => AFin (fun b : Fin (Fintype.card α) => sigma (e.symm b))) =
          A := by
      funext sigma
      have harg :
          (fun a : α => (fun b : Fin (Fintype.card α) => sigma (e.symm b)) (e a)) =
            sigma := by
        funext a
        simp
      simp [AFin]
    calc
      bernProb q A = bernProb q
          (fun sigma : α -> Bool => AFin (fun b : Fin (Fintype.card α) => sigma (e.symm b))) := by
            rw [hleft]
      _ = bernProb q AFin := h
  exact hp_reindex.trans_le (hfin.trans_eq hq_reindex.symm)

theorem extendConfig_mono {d : Nat} {F : Finset (Bond d)} {sigma tau : F -> Bool}
    (hle : BoolAssignmentLE sigma tau) :
    ConfigLE (extendConfig F sigma) (extendConfig F tau) := by
  intro e heOpen
  by_cases he : e ∈ F
  · simp [extendConfig, he] at heOpen ⊢
    exact hle ⟨e, he⟩ heOpen
  · simp [extendConfig, he] at heOpen

theorem prob_mono {d : Nat} {p q : Real} (E : LocalEvent d)
    (hinc : Increasing E) (hp0 : 0 <= p) (hpq : p <= q) (hq1 : q <= 1) :
    Prob p E <= Prob q E := by
  classical
  exact bernProb_mono_parameter
    (A := fun sigma : E.support -> Bool => E.pred (extendConfig E.support sigma))
    (by
      intro sigma tau hle hsigma
      exact hinc (extendConfig_mono hle) hsigma)
    hp0 hpq hq1

end Sharpness
