import Sharpness.LocalEvent

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

-- Missing mathematical fact: prove the standard induction/coupling argument on a finite
-- Boolean product showing that increasing events have probability monotone in the Bernoulli
-- parameter.
theorem bernProb_mono_parameter {α : Type*} [DecidableEq α] [Fintype α]
    {p q : Real} {A : (α -> Bool) -> Prop}
    (hinc : IncreasingBoolEvent A) (hp0 : 0 <= p) (hpq : p <= q) (hq1 : q <= 1) :
    bernProb p A <= bernProb q A := by
  sorry

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
