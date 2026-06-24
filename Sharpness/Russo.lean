import Sharpness.Independence
import Sharpness.Monotonicity

namespace Sharpness

open scoped BigOperators

/-- Force a bond to be open ∈ a configuration. -/
def forceOpen {d : Nat} (e : Bond d) (omega : Config d) : Config d :=
  fun f => if f = e then true else omega f

/-- Closed-pivotal event for an increasing local event. -/
def ClosedPivotal {d : Nat} (E : LocalEvent d) (e : Bond d)
    (omega : Config d) : Prop :=
  omega e = false /\ ¬ E.pred omega /\ E.pred (forceOpen e omega)

-- M0 stub: closed-pivotality is local on `insert e E.support`.
theorem closedPivotal_dependsOn {d : Nat} (E : LocalEvent d) (e : Bond d) :
    DependsOn (insert e E.support) (ClosedPivotal E e) := by
  sorry

/-- Local event that a fixed bond is closed-pivotal. -/
def closedPivotalEvent {d : Nat} (E : LocalEvent d) (e : Bond d) : LocalEvent d :=
  { support := insert e E.support
    pred := ClosedPivotal E e
    isLocal := closedPivotal_dependsOn E e }

-- M0 stub: Russo's formula ∈ closed-pivotal form for finite local increasing events.
theorem russo_closed_pivotal {d : Nat} (E : LocalEvent d) (hinc : Increasing E)
    {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun q => Prob q E)
      ((1 / (1 - p)) * (E.support.sum fun e => Prob p (closedPivotalEvent E e))) p := by
  sorry

end Sharpness
