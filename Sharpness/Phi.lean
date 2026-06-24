import Sharpness.Events
import Sharpness.Monotonicity

namespace Sharpness

open scoped BigOperators

/-- The finite-set criterion quantity `phi_p(S)`. -/
noncomputable def phi {d : Nat} (p : Real) (S : Finset (Vertex d)) : Real :=
  p * (orientedBoundary S).sum fun e => Prob p (connInEvent S (0 : Vertex d) e.1)

/-- Finite subsets of `Lam` that contain the origin. -/
noncomputable def finiteSubsetsWithZero {d : Nat}
    (Lam : Finset (Vertex d)) : Finset (Finset (Vertex d)) :=
  Lam.powerset.filter fun S => (0 : Vertex d) ∈ S

/-- Finite minimum of `phi_p(S)` over `S subset Lam` with `0 ∈ S`. -/
noncomputable def phiMinIn {d : Nat} (p : Real) (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) : Real := by
  classical
  exact (finiteSubsetsWithZero Lam).inf'
    ⟨{(0 : Vertex d)}, by simp [finiteSubsetsWithZero, h0]⟩
    (phi p)

/-- The finite-set critical point `pTilde`. -/
noncomputable def pTilde (d : Nat) : Real :=
  sSup {p : Real | 0 <= p /\ p <= 1 /\
    exists S : Finset (Vertex d), (0 : Vertex d) ∈ S /\ phi p S < 1}

-- M0 stub: for each finite `S`, `phi_p(S)` is monotone ∈ the Bernoulli parameter.
theorem phi_mono {d : Nat} {p q : Real} (S : Finset (Vertex d))
    (hp0 : 0 <= p) (hpq : p <= q) (hq1 : q <= 1) :
    phi p S <= phi q S := by
  sorry

-- M0 stub: below `pTilde`, some finite set has `phi_p(S) < 1`.
theorem exists_phi_lt_one_of_lt_pTilde {d : Nat} {p : Real}
    (hp : p < pTilde d) :
    exists S : Finset (Vertex d), (0 : Vertex d) ∈ S /\ phi p S < 1 := by
  sorry

-- M0 stub: above `pTilde`, every finite set containing the origin has `phi_p(S) >= 1`.
theorem one_le_phi_of_pTilde_lt {d : Nat} {p : Real}
    (hp : pTilde d < p) (S : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ S) :
    1 <= phi p S := by
  sorry

end Sharpness
