/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.LocalEvent

/-!
# Independence

This file proves independence identities for local events with disjoint supports.
-/

namespace Sharpness

theorem prob_inter_eq_mul_of_disjoint {d : Nat} {p : Real}
    (E F : LocalEvent d) (hdisj : Disjoint E.support F.support)
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p (E.inter F) = Prob p E * Prob p F := by
  classical
  let U : Finset (Bond d) := E.support ∪ F.support
  let eCoord : E.support ⊕ F.support ≃ U :=
    Equiv.Finset.union E.support F.support hdisj
  have hlocalE :
      forall sigma : E.support ⊕ F.support -> Bool,
        E.pred (extendConfig U (fun g : U => sigma (eCoord.symm g))) <->
          E.pred (extendConfig E.support (fun e : E.support => sigma (Sum.inl e))) := by
    intro sigma
    exact E.isLocal (by
      intro e he
      have hU : e ∈ U := Finset.mem_union.mpr (Or.inl he)
      simp [extendConfig, U, eCoord, hU, he,
        Equiv.Finset.union_symm_left hdisj he hU])
  have hlocalF :
      forall sigma : E.support ⊕ F.support -> Bool,
        F.pred (extendConfig U (fun g : U => sigma (eCoord.symm g))) <->
          F.pred (extendConfig F.support (fun f : F.support => sigma (Sum.inr f))) := by
    intro sigma
    exact F.isLocal (by
      intro e he
      have hU : e ∈ U := Finset.mem_union.mpr (Or.inr he)
      simp [extendConfig, U, eCoord, hU, he,
        Equiv.Finset.union_symm_right hdisj he hU])
  have hpull :
      (fun sigma : E.support ⊕ F.support -> Bool =>
          E.pred (extendConfig U (fun g : U => sigma (eCoord.symm g))) /\
            F.pred (extendConfig U (fun g : U => sigma (eCoord.symm g)))) =
        (fun sigma : E.support ⊕ F.support -> Bool =>
          E.pred (extendConfig E.support (fun e : E.support => sigma (Sum.inl e))) /\
            F.pred (extendConfig F.support (fun f : F.support => sigma (Sum.inr f)))) := by
    funext sigma
    exact propext (and_congr (hlocalE sigma) (hlocalF sigma))
  calc
    Prob p (E.inter F)
        = bernProb p
            (fun sigma : U -> Bool =>
              E.pred (extendConfig U sigma) /\ F.pred (extendConfig U sigma)) := rfl
    _ = bernProb p
            (fun sigma : E.support ⊕ F.support -> Bool =>
              E.pred (extendConfig U (fun g : U => sigma (eCoord.symm g))) /\
                F.pred (extendConfig U (fun g : U => sigma (eCoord.symm g)))) := by
          exact (bernProb_reindex (α := E.support ⊕ F.support) (β := U) p eCoord
            (fun sigma : U -> Bool =>
              E.pred (extendConfig U sigma) /\ F.pred (extendConfig U sigma))).symm
    _ = bernProb p
            (fun sigma : E.support ⊕ F.support -> Bool =>
              E.pred (extendConfig E.support (fun e : E.support => sigma (Sum.inl e))) /\
                F.pred (extendConfig F.support (fun f : F.support => sigma (Sum.inr f)))) := by
          rw [hpull]
    _ = Prob p E * Prob p F := by
          exact bernProb_sum_inter (α := E.support) (β := F.support) p
            (fun sigma : E.support -> Bool => E.pred (extendConfig E.support sigma))
            (fun sigma : F.support -> Bool => F.pred (extendConfig F.support sigma))

-- M0 stub: three pairwise disjoint local events have multiplicative probability.
theorem prob_inter_three_eq_mul_of_pairwise_disjoint {d : Nat} {p : Real}
    (E F G : LocalEvent d)
    (hEF : Disjoint E.support F.support)
    (hEG : Disjoint E.support G.support)
    (hFG : Disjoint F.support G.support)
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p ((E.inter F).inter G) = Prob p E * Prob p F * Prob p G := by
  classical
  have hEFG : Disjoint (E.support ∪ F.support) G.support := hEG.sup_left hFG
  calc
    Prob p ((E.inter F).inter G)
        = Prob p (E.inter F) * Prob p G := by
          exact prob_inter_eq_mul_of_disjoint (E.inter F) G hEFG hp0 hp1
    _ = Prob p E * Prob p F * Prob p G := by
          rw [prob_inter_eq_mul_of_disjoint E F hEF hp0 hp1]

end Sharpness
