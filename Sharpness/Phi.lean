/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.Events
import Sharpness.Monotonicity

/-!
# Finite-Set Criterion

This file defines `phi`, `pTilde`, and the basic order lemmas for the finite-set
criterion.
-/

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

/-- Parameters satisfying the finite-set criterion. -/
noncomputable def pTildeSet (d : Nat) : Set Real :=
  {p : Real | 0 <= p /\ p <= 1 /\
    exists S : Finset (Vertex d), (0 : Vertex d) ∈ S /\ phi p S < 1}

/-- The finite-set critical point `pTilde`. -/
noncomputable def pTilde (d : Nat) : Real :=
  sSup (pTildeSet d)

/-- `0` belongs to the defining set of `pTilde`. -/
theorem zero_mem_pTildeSet (d : Nat) : (0 : Real) ∈ pTildeSet d := by
  classical
  refine ⟨le_rfl, zero_le_one, ?_⟩
  refine ⟨{(0 : Vertex d)}, by simp, ?_⟩
  simp [phi]

/-- The defining set of `pTilde` is nonempty. -/
theorem pTildeSet_nonempty (d : Nat) : (pTildeSet d).Nonempty :=
  ⟨0, zero_mem_pTildeSet d⟩

/-- The defining set of `pTilde` is bounded above by `1`. -/
theorem pTildeSet_bddAbove (d : Nat) : BddAbove (pTildeSet d) := by
  refine ⟨1, ?_⟩
  intro p hp
  exact hp.2.1

/-- The finite-set critical point is nonnegative. -/
theorem zero_le_pTilde (d : Nat) : 0 <= pTilde d := by
  exact le_csSup (pTildeSet_bddAbove d) (zero_mem_pTildeSet d)

/-- The finite-set critical point is at most one. -/
theorem pTilde_le_one (d : Nat) : pTilde d <= 1 := by
  exact csSup_le (pTildeSet_nonempty d) fun p hp => hp.2.1

/-- For each finite `S`, `phi_p(S)` is monotone in the Bernoulli parameter on `[0,1]`. -/
theorem phi_mono {d : Nat} {p q : Real} (S : Finset (Vertex d))
    (hp0 : 0 <= p) (hpq : p <= q) (hq1 : q <= 1) :
    phi p S <= phi q S := by
  classical
  have hp1 : p <= 1 := hpq.trans hq1
  have hq0 : 0 <= q := hp0.trans hpq
  have hsum :
      (orientedBoundary S).sum
          (fun e => Prob p (connInEvent S (0 : Vertex d) e.1)) <=
        (orientedBoundary S).sum
          (fun e => Prob q (connInEvent S (0 : Vertex d) e.1)) := by
    refine Finset.sum_le_sum ?_
    intro e _he
    exact prob_mono (connInEvent S (0 : Vertex d) e.1)
      (connInEvent_increasing S (0 : Vertex d) e.1) hp0 hpq hq1
  have hsum_nonneg :
      0 <= (orientedBoundary S).sum
          (fun e => Prob p (connInEvent S (0 : Vertex d) e.1)) := by
    refine Finset.sum_nonneg ?_
    intro e _he
    exact probOn_nonneg
      (F := (connInEvent S (0 : Vertex d) e.1).support)
      (A := fun sigma : (connInEvent S (0 : Vertex d) e.1).support -> Bool =>
        (connInEvent S (0 : Vertex d) e.1).pred
          (extendConfig (connInEvent S (0 : Vertex d) e.1).support sigma))
      hp0 hp1
  dsimp [phi]
  exact (mul_le_mul_of_nonneg_right hpq hsum_nonneg).trans
    (mul_le_mul_of_nonneg_left hsum hq0)

/-- Below `pTilde`, some finite set satisfies the finite-set criterion. -/
theorem exists_phi_lt_one_of_lt_pTilde {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp : p < pTilde d) :
    exists S : Finset (Vertex d), (0 : Vertex d) ∈ S /\ phi p S < 1 := by
  classical
  rcases exists_lt_of_lt_csSup (pTildeSet_nonempty d) hp with
    ⟨q, hq, hpq⟩
  rcases hq with ⟨_hq0, hq1, S, h0S, hphi⟩
  exact ⟨S, h0S, (phi_mono S hp0 hpq.le hq1).trans_lt hphi⟩

/-- Above `pTilde`, every finite set containing the origin violates the finite-set criterion. -/
theorem one_le_phi_of_pTilde_lt {d : Nat} {p : Real}
    (hp : pTilde d < p) (hp1 : p <= 1) (S : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ S) :
    1 <= phi p S := by
  classical
  by_contra hnot
  have hphi : phi p S < 1 := lt_of_not_ge hnot
  have hp0 : 0 <= p := (zero_le_pTilde d).trans hp.le
  have hp_mem : p ∈ pTildeSet d := ⟨hp0, hp1, S, h0, hphi⟩
  have hle : p <= pTilde d := le_csSup (pTildeSet_bddAbove d) hp_mem
  exact not_lt_of_ge hle hp

end Sharpness
