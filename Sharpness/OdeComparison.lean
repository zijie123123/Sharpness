import Mathlib

namespace Sharpness

/--
The real ODE/log comparison used in the supercritical argument.

The differentiability hypothesis is stated on the closed interval.  The endpoint
regularity is needed mathematically: derivative bounds only on `(q, p)` do not
control arbitrary jumps in the endpoint values of `f`.
-/
theorem ode_log_comparison {f : Real -> Real} {q p : Real}
    (hq0 : 0 < q) (hqp : q < p) (hp1 : p < 1)
    (hderiv : forall t, q <= t -> t <= p -> HasDerivAt f (deriv f t) t)
    (hlt : forall t, q <= t -> t <= p -> f t < 1)
    (hineq : forall t, q < t -> t < p ->
      deriv f t >= (1 - f t) / (t * (1 - t))) :
    1 - f p <= (1 - f q) * (q * (1 - p) / (p * (1 - q))) := by
  let g : Real -> Real := fun t => Real.log (1 - f t) + Real.log t - Real.log (1 - t)
  have hp0 : 0 < p := lt_trans hq0 hqp
  have hq1 : q < 1 := lt_trans hqp hp1
  have h1mp : 0 < 1 - p := sub_pos.mpr hp1
  have h1mq : 0 < 1 - q := sub_pos.mpr hq1
  have hg_cont : ContinuousOn g (Set.Icc q p) := by
    have hf_cont : ContinuousOn f (Set.Icc q p) := by
      intro t ht
      exact (hderiv t ht.1 ht.2).continuousAt.continuousWithinAt
    have hlog1mf : ContinuousOn (fun t => Real.log (1 - f t)) (Set.Icc q p) := by
      exact (continuousOn_const.sub hf_cont).log (by
        intro t ht
        exact ne_of_gt (sub_pos.mpr (hlt t ht.1 ht.2)))
    have hlogt : ContinuousOn (fun t : Real => Real.log t) (Set.Icc q p) := by
      exact continuousOn_id.log (by
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le hq0 ht.1))
    have hlog1mt : ContinuousOn (fun t : Real => Real.log (1 - t)) (Set.Icc q p) := by
      exact (continuousOn_const.sub continuousOn_id).log (by
        intro t ht
        exact ne_of_gt (sub_pos.mpr (lt_of_le_of_lt ht.2 hp1)))
    change ContinuousOn
      (fun t => Real.log (1 - f t) + Real.log t - Real.log (1 - t)) (Set.Icc q p)
    exact (hlog1mf.add hlogt).sub hlog1mt
  have hg_hasDerivAt : forall t, q < t -> t < p ->
      HasDerivAt g (-deriv f t / (1 - f t) + 1 / t - -(1 / (1 - t))) t := by
    intro t hqt htp
    have htqle : q <= t := le_of_lt hqt
    have htp_le : t <= p := le_of_lt htp
    have hfderiv := hderiv t htqle htp_le
    have h1mf_pos : 0 < 1 - f t := sub_pos.mpr (hlt t htqle htp_le)
    have ht_pos : 0 < t := lt_trans hq0 hqt
    have h1mt_pos : 0 < 1 - t := sub_pos.mpr (lt_trans htp hp1)
    have hlog1mf :
        HasDerivAt (fun s => Real.log (1 - f s)) (-deriv f t / (1 - f t)) t := by
      have hsub : HasDerivAt (fun s => 1 - f s) (0 - deriv f t) t :=
        (hasDerivAt_const (x := t) (c := (1 : Real))).sub hfderiv
      convert hsub.log (ne_of_gt h1mf_pos) using 1
      ring
    have hlogt : HasDerivAt (fun s : Real => Real.log s) (1 / t) t := by
      convert Real.hasDerivAt_log (ne_of_gt ht_pos) using 1
      field_simp [ht_pos.ne']
    have hlog1mt :
        HasDerivAt (fun s : Real => Real.log (1 - s)) (-(1 / (1 - t))) t := by
      have hsub : HasDerivAt (fun s : Real => 1 - s) (0 - 1) t :=
        (hasDerivAt_const (x := t) (c := (1 : Real))).sub (hasDerivAt_id t)
      have h := hsub.log (ne_of_gt h1mt_pos)
      convert h using 1
      field_simp [h1mt_pos.ne']
      ring
    have htotal := (hlog1mf.add hlogt).sub hlog1mt
    change HasDerivAt
      (fun s => Real.log (1 - f s) + Real.log s - Real.log (1 - s))
      (-deriv f t / (1 - f t) + 1 / t - -(1 / (1 - t))) t
    exact htotal
  have hg_diff : DifferentiableOn Real g (interior (Set.Icc q p)) := by
    intro t ht
    rw [interior_Icc] at ht
    exact (hg_hasDerivAt t ht.1 ht.2).differentiableAt.differentiableWithinAt
  have hg_deriv_nonpos : forall t, t ∈ interior (Set.Icc q p) -> deriv g t <= 0 := by
    intro t ht
    rw [interior_Icc] at ht
    have hqt : q < t := ht.1
    have htp : t < p := ht.2
    have htqle : q <= t := le_of_lt hqt
    have htp_le : t <= p := le_of_lt htp
    have h1mf_pos : 0 < 1 - f t := sub_pos.mpr (hlt t htqle htp_le)
    have ht_pos : 0 < t := lt_trans hq0 hqt
    have h1mt_pos : 0 < 1 - t := sub_pos.mpr (lt_trans htp hp1)
    have hgd := hg_hasDerivAt t hqt htp
    rw [hgd.deriv]
    have hineq_t := hineq t hqt htp
    field_simp [ht_pos.ne', h1mt_pos.ne', h1mf_pos.ne'] at hineq_t ⊢
    nlinarith
  have hg_anti : AntitoneOn g (Set.Icc q p) :=
    antitoneOn_of_deriv_nonpos (convex_Icc q p) hg_cont hg_diff hg_deriv_nonpos
  have hgle : g p <= g q := by
    exact hg_anti ⟨le_rfl, hqp.le⟩ ⟨hqp.le, le_rfl⟩ hqp.le
  have hratio : (1 - f p) * p / (1 - p) <= (1 - f q) * q / (1 - q) := by
    have hexp : Real.exp (g p) <= Real.exp (g q) := Real.exp_le_exp.mpr hgle
    have h1fp : 0 < 1 - f p := sub_pos.mpr (hlt p hqp.le le_rfl)
    have h1fq : 0 < 1 - f q := sub_pos.mpr (hlt q le_rfl hqp.le)
    have hgp : Real.exp (g p) = (1 - f p) * p / (1 - p) := by
      change Real.exp (Real.log (1 - f p) + Real.log p - Real.log (1 - p)) =
        (1 - f p) * p / (1 - p)
      rw [Real.exp_sub, Real.exp_add]
      simp [Real.exp_log, h1fp, hp0, h1mp]
    have hgq : Real.exp (g q) = (1 - f q) * q / (1 - q) := by
      change Real.exp (Real.log (1 - f q) + Real.log q - Real.log (1 - q)) =
        (1 - f q) * q / (1 - q)
      rw [Real.exp_sub, Real.exp_add]
      simp [Real.exp_log, h1fq, hq0, h1mq]
    simpa [hgp, hgq] using hexp
  field_simp [hp0.ne', h1mp.ne', h1mq.ne'] at hratio ⊢
  nlinarith

end Sharpness
