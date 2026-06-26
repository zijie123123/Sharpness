/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.DiffIneq
import Sharpness.OdeComparison

/-!
# Supercritical Lower Bound

This file proves the density lower bound above the finite-set critical point.
-/

namespace Sharpness

open scoped Topology

private theorem bernWeight_all_false_pos {α : Type*} [Fintype α]
    {p : Real} (hp1 : p < 1) :
    0 < bernWeight p (fun _ : α => false) := by
  classical
  dsimp [bernWeight]
  exact Finset.prod_pos (by
    intro e _he
    simp [sub_pos.mpr hp1])

private theorem bernProb_pos_of_all_false {α : Type*} [DecidableEq α] [Fintype α]
    {p : Real} {A : (α -> Bool) -> Prop} (hp0 : 0 <= p) (hp1 : p < 1)
    (hA : A (fun _ : α => false)) :
    0 < bernProb p A := by
  classical
  let sigma0 : α -> Bool := fun _ => false
  have hterm : 0 < (if A sigma0 then bernWeight p sigma0 else 0) := by
    simp [sigma0, hA, bernWeight_all_false_pos hp1]
  have hle :
      (if A sigma0 then bernWeight p sigma0 else 0) <=
        Finset.univ.sum (fun sigma : α -> Bool =>
          if A sigma then bernWeight p sigma else 0) := by
    simpa using (Finset.single_le_sum
      (s := (Finset.univ : Finset (α -> Bool)))
      (f := fun sigma : α -> Bool => (if A sigma then bernWeight p sigma else 0 : Real))
      (by
        intro sigma _hsigma
        by_cases hAsigma : A sigma
        · simp [hAsigma, bernWeight_nonneg hp0 hp1.le sigma]
        · simp [hAsigma])
      (Finset.mem_univ sigma0))
  exact lt_of_lt_of_le hterm hle

private theorem local_prob_lt_one_of_all_false_not {d : Nat} {p : Real}
    (E : LocalEvent d) (hp0 : 0 <= p) (hp1 : p < 1)
    (hfalse : ¬ E.pred (extendConfig E.support (fun _ : E.support => false))) :
    Prob p E < 1 := by
  classical
  let A : (E.support -> Bool) -> Prop := fun sigma => E.pred (extendConfig E.support sigma)
  have hcomp_pos : 0 < bernProb p (fun sigma : E.support -> Bool => ¬ A sigma) := by
    exact bernProb_pos_of_all_false hp0 hp1 (by simpa [A] using hfalse)
  have hcomp_eq : bernProb p (fun sigma : E.support -> Bool => ¬ A sigma) =
      1 - bernProb p A := by
    exact bernProb_compl (p := p) (A := A)
  have hprob : Prob p E = bernProb p A := rfl
  rw [hcomp_eq] at hcomp_pos
  rw [hprob]
  linarith

/-- Finite exit events have probability strictly below one when `p < 1`:
the all-closed assignment closes, in particular, every boundary edge. -/
theorem exitProb_lt_one_of_lt_one {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) {p : Real} (hp0 : 0 <= p) (hp1 : p < 1) :
    exitProb p Lam h0 < 1 := by
  classical
  unfold exitProb
  refine local_prob_lt_one_of_all_false_not (exitEvent Lam h0) hp0 hp1 ?_
  intro hexit
  rcases hexit with ⟨e, he, _hconn, hopen⟩
  have hb : bondOfAdj (orientedBoundary_adj he) ∈ (exitEvent Lam h0).support := by
    exact Finset.mem_union.mpr (Or.inr (bondOfAdj_mem_exitBonds he))
  simp [extendConfig, hb] at hopen

private theorem one_le_phiMinIn_of_pTilde_lt {d : Nat} {t : Real}
    (Lam : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Lam)
    (ht : pTilde d < t) (ht1 : t <= 1) :
    1 <= phiMinIn t Lam h0 := by
  classical
  unfold phiMinIn
  refine Finset.le_inf' (s := finiteSubsetsWithZero Lam)
    (H := ⟨{(0 : Vertex d)}, by simp [finiteSubsetsWithZero, h0]⟩)
    (f := phi t) (a := (1 : Real)) ?_
  intro S hS
  rw [finiteSubsetsWithZero, Finset.mem_filter, Finset.mem_powerset] at hS
  exact one_le_phi_of_pTilde_lt ht ht1 S hS.2

private theorem pTilde_endpoint_bound {a p x : Real}
    (ha0 : 0 <= a) (hap : a < p) (hp1 : p < 1)
    (hx : forall q, a < q -> q < p -> (p - q) / (p * (1 - q)) <= x) :
    (p - a) / (p * (1 - a)) <= x := by
  have hp0 : 0 < p := lt_of_le_of_lt ha0 hap
  have ha1 : a < 1 := lt_trans hap hp1
  have hden : p * (1 - a) ≠ 0 :=
    mul_ne_zero hp0.ne' (sub_ne_zero.mpr (ne_of_gt ha1))
  have hcont : ContinuousAt (fun q => (p - q) / (p * (1 - q))) a := by
    exact (continuousAt_const.sub continuousAt_id).div₀
      (continuousAt_const.mul (continuousAt_const.sub continuousAt_id)) hden
  refine le_of_tendsto (x := nhdsWithin a (Set.Ioi a))
    (hcont.tendsto.mono_left nhdsWithin_le_nhds) ?_
  have hltp : ∀ᶠ q : Real in nhdsWithin a (Set.Ioi a), q < p :=
    nhdsWithin_le_nhds (Iio_mem_nhds hap)
  filter_upwards [eventually_mem_nhdsWithin, hltp] with q hqa hqp
  exact hx q hqa hqp

private theorem finite_exit_lower_bound_above_q {d : Nat} {q p : Real}
    (Lam : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Lam)
    (hptq : pTilde d < q) (hqp : q < p) (hp1 : p < 1) :
    (p - q) / (p * (1 - q)) <= exitProb p Lam h0 := by
  classical
  have hq0 : 0 < q := lt_of_le_of_lt (zero_le_pTilde d) hptq
  have hq1 : q < 1 := lt_trans hqp hp1
  have hp0 : 0 < p := lt_trans hq0 hqp
  let f : Real -> Real := fun r => exitProb r Lam h0
  have hf_deriv : forall t, q <= t -> t <= p -> HasDerivAt f (deriv f t) t := by
    intro t hqt htp
    have ht0 : 0 < t := lt_of_lt_of_le hq0 hqt
    have ht1 : t < 1 := lt_of_le_of_lt htp hp1
    have hRusso := russo_closed_pivotal (exitEvent Lam h0)
      (exitEvent_increasing Lam h0) ht0 ht1
    change HasDerivAt (fun r => Prob r (exitEvent Lam h0))
      (deriv (fun r => Prob r (exitEvent Lam h0)) t) t
    rw [hRusso.deriv]
    exact hRusso
  have hf_lt_one : forall t, q <= t -> t <= p -> f t < 1 := by
    intro t hqt htp
    have ht0 : 0 <= t := (le_of_lt hq0).trans hqt
    have ht1 : t < 1 := lt_of_le_of_lt htp hp1
    exact exitProb_lt_one_of_lt_one Lam h0 ht0 ht1
  have hf_ineq : forall t, q < t -> t < p ->
      deriv f t >= (1 - f t) / (t * (1 - t)) := by
    intro t hqt htp
    have ht0 : 0 < t := lt_trans hq0 hqt
    have ht1 : t < 1 := lt_trans htp hp1
    have hdiff := differential_inequality Lam h0 ht0 ht1
    have hphi : 1 <= phiMinIn t Lam h0 :=
      one_le_phiMinIn_of_pTilde_lt Lam h0 (lt_trans hptq hqt) ht1.le
    have hden_pos : 0 < t * (1 - t) := mul_pos ht0 (sub_pos.mpr ht1)
    have hinv_nonneg : 0 <= 1 / (t * (1 - t)) :=
      le_of_lt (one_div_pos.mpr hden_pos)
    have htail_nonneg : 0 <= 1 - exitProb t Lam h0 :=
      le_of_lt (sub_pos.mpr (hf_lt_one t (le_of_lt hqt) (le_of_lt htp)))
    have hmul :
        (1 / (t * (1 - t))) * 1 * (1 - exitProb t Lam h0) <=
          (1 / (t * (1 - t))) * phiMinIn t Lam h0 *
            (1 - exitProb t Lam h0) := by
      have hleft :
          (1 / (t * (1 - t))) * 1 <=
            (1 / (t * (1 - t))) * phiMinIn t Lam h0 := by
        exact mul_le_mul_of_nonneg_left hphi hinv_nonneg
      exact mul_le_mul_of_nonneg_right hleft htail_nonneg
    have htarget :
        (1 - exitProb t Lam h0) / (t * (1 - t)) <=
          (1 / (t * (1 - t))) * phiMinIn t Lam h0 *
            (1 - exitProb t Lam h0) := by
      calc
        (1 - exitProb t Lam h0) / (t * (1 - t))
            = (1 / (t * (1 - t))) * 1 * (1 - exitProb t Lam h0) := by
                field_simp [hden_pos.ne']
        _ <= (1 / (t * (1 - t))) * phiMinIn t Lam h0 *
            (1 - exitProb t Lam h0) := hmul
    exact htarget.trans hdiff
  have hode := ode_log_comparison (f := f) hq0 hqp hp1 hf_deriv hf_lt_one hf_ineq
  have hfq_nonneg : 0 <= f q := by
    exact probOn_nonneg (F := (exitEvent Lam h0).support)
      (A := fun sigma : (exitEvent Lam h0).support -> Bool =>
        (exitEvent Lam h0).pred (extendConfig (exitEvent Lam h0).support sigma))
      (le_of_lt hq0) hq1.le
  have hfactor_nonneg : 0 <= q * (1 - p) / (p * (1 - q)) := by
    positivity
  have hode' : 1 - f p <= q * (1 - p) / (p * (1 - q)) := by
    have h1fq : 1 - f q <= 1 := by linarith
    exact hode.trans (by
      simpa [one_mul] using mul_le_mul_of_nonneg_right h1fq hfactor_nonneg)
  change (p - q) / (p * (1 - q)) <= f p
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  field_simp [hp0.ne', h1q.ne'] at hode'
  field_simp [hp0.ne', h1q.ne']
  nlinarith

/-- Lemma 3, the lower bound above the finite-set critical point. -/
theorem supercritical_lower_bound_above_pTilde {d : Nat} {p : Real}
    (hp : pTilde d < p) (hp1 : p < 1) :
    theta d p >= (p - pTilde d) / (p * (1 - pTilde d)) := by
  classical
  change (p - pTilde d) / (p * (1 - pTilde d)) <= theta d p
  refine le_theta_of_le_boxExitProb ?_
  intro n
  have hbox : (p - pTilde d) / (p * (1 - pTilde d)) <=
      boxExitProb d p n := by
    refine pTilde_endpoint_bound (zero_le_pTilde d) hp hp1 ?_
    intro q hptq hqp
    exact finite_exit_lower_bound_above_q (ball d n) (zero_mem_ball d n) hptq hqp hp1
  exact hbox

end Sharpness
