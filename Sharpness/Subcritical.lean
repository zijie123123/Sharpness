/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.BoundaryIneq
import Sharpness.FiniteGeometry
import Sharpness.Phi

/-!
# Subcritical Exponential Decay

This file proves exponential decay below the finite-set critical point.
-/

namespace Sharpness

open scoped BigOperators

/-!
Lemma 5, exponential decay below the finite-set critical point.
-/

private theorem bernWeight_zero_of_all_false {α : Type*} [Fintype α]
    (sigma : α -> Bool) (hsigma : forall e, sigma e = false) :
    bernWeight (0 : Real) sigma = 1 := by
  classical
  dsimp [bernWeight]
  simp [hsigma]

private theorem bernWeight_zero_of_exists_true {α : Type*} [Fintype α]
    (sigma : α -> Bool) (hsigma : exists e, sigma e = true) :
    bernWeight (0 : Real) sigma = 0 := by
  classical
  rcases hsigma with ⟨e, he⟩
  dsimp [bernWeight]
  exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

private theorem exists_true_of_ne_all_false {α : Type*} (sigma : α -> Bool)
    (hne : sigma ≠ fun _ => false) :
    exists e, sigma e = true := by
  classical
  by_contra hnot
  apply hne
  funext e
  cases hs : sigma e
  · rfl
  · exfalso
    exact hnot ⟨e, hs⟩

private theorem local_prob_zero_of_all_false_not {d : Nat} (E : LocalEvent d)
    (hfalse : ¬ E.pred (extendConfig E.support (fun _ : E.support => false))) :
    Prob (0 : Real) E = 0 := by
  classical
  let sigma0 : E.support -> Bool := fun _ => false
  dsimp [Prob, ProbOn, bernProb]
  rw [Finset.sum_eq_single sigma0]
  · simp [sigma0, hfalse]
  · intro sigma _hsigma hne
    have hex : exists e, sigma e = true := exists_true_of_ne_all_false sigma hne
    by_cases hA : E.pred (extendConfig E.support sigma)
    · simp [hA, bernWeight_zero_of_exists_true sigma hex]
    · simp [hA]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ sigma0))

private theorem boxExitProb_zero (d n : Nat) :
    boxExitProb d (0 : Real) n = 0 := by
  unfold boxExitProb exitProb
  refine local_prob_zero_of_all_false_not (exitEvent (ball d n) (zero_mem_ball d n)) ?_
  intro hexit
  rcases hexit with ⟨e, he, _hconn, hopen⟩
  have hb : bondOfAdj (orientedBoundary_adj he) ∈
      (exitEvent (ball d n) (zero_mem_ball d n)).support := by
    exact Finset.mem_union.mpr (Or.inr (bondOfAdj_mem_exitBonds he))
  simp [extendConfig, hb] at hopen

private theorem boxExitProb_le_one {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) (n : Nat) :
    boxExitProb d p n <= 1 := by
  unfold boxExitProb exitProb Prob
  exact probOn_le_one
    (F := (exitEvent (ball d n) (zero_mem_ball d n)).support)
    (A := fun sigma : (exitEvent (ball d n) (zero_mem_ball d n)).support -> Bool =>
      (exitEvent (ball d n) (zero_mem_ball d n)).pred
        (extendConfig (exitEvent (ball d n) (zero_mem_ball d n)).support sigma))
    hp0 hp1

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
      (f := fun sigma : α -> Bool =>
        (if A sigma then bernWeight p sigma else 0 : Real))
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
  let A : (E.support -> Bool) -> Prop :=
    fun sigma => E.pred (extendConfig E.support sigma)
  have hcomp_pos : 0 < bernProb p (fun sigma : E.support -> Bool => ¬ A sigma) := by
    exact bernProb_pos_of_all_false hp0 hp1 (by simpa [A] using hfalse)
  have hcomp_eq : bernProb p (fun sigma : E.support -> Bool => ¬ A sigma) =
      1 - bernProb p A := by
    exact bernProb_compl (p := p) (A := A)
  have hprob : Prob p E = bernProb p A := rfl
  rw [hcomp_eq] at hcomp_pos
  rw [hprob]
  linarith

private theorem boxExitProb_lt_one_of_lt_one {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p < 1) (n : Nat) :
    boxExitProb d p n < 1 := by
  classical
  unfold boxExitProb exitProb
  refine local_prob_lt_one_of_all_false_not
    (exitEvent (ball d n) (zero_mem_ball d n)) hp0 hp1 ?_
  intro hexit
  rcases hexit with ⟨e, he, _hconn, hopen⟩
  have hb : bondOfAdj (orientedBoundary_adj he) ∈
      (exitEvent (ball d n) (zero_mem_ball d n)).support := by
    exact Finset.mem_union.mpr (Or.inr (bondOfAdj_mem_exitBonds he))
  simp [extendConfig, hb] at hopen

private theorem div_step_eq {n L : Nat} (hL : 0 < L) (hn : L <= n) :
    (n - L) / L + 1 = n / L := by
  calc
    (n - L) / L + 1 = 1 + (n - L) / L := by omega
    _ = (L * 1 + (n - L)) / L := by
      rw [Nat.mul_add_div hL]
    _ = n / L := by
      congr 1
      omega

private theorem recurrence_iterate {a : Nat -> Real} {rho : Real} {L : Nat}
    (hL : 0 < L) (hrho0 : 0 <= rho)
    (hone : forall n : Nat, a n <= 1)
    (hrec : forall n : Nat, L <= n -> a n <= rho * a (n - L)) :
    forall n : Nat, a n <= rho ^ (n / L) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : L <= n
      · have hnpos : 0 < n := lt_of_lt_of_le hL hn
        have hsub_lt : n - L < n := Nat.sub_lt hnpos hL
        have hprev : a (n - L) <= rho ^ ((n - L) / L) := ih (n - L) hsub_lt
        calc
          a n <= rho * a (n - L) := hrec n hn
          _ <= rho * rho ^ ((n - L) / L) :=
            mul_le_mul_of_nonneg_left hprev hrho0
          _ = rho ^ (((n - L) / L) + 1) := by
            rw [pow_succ]
            ring
          _ = rho ^ (n / L) := by
            rw [div_step_eq hL hn]
      · have hdiv : n / L = 0 := by
          exact Nat.div_eq_of_lt (lt_of_not_ge hn)
        simpa [hdiv] using hone n

private noncomputable def expScale (a : Real) (n : Nat) : Real :=
  if n = 0 then 1 else if 0 < a then -Real.log a / (2 * (n : Real)) else 1

private theorem exp_bound_single {a c : Real} {n : Nat}
    (_ha0 : 0 <= a) (ha1 : a < 1) (_hc0 : 0 <= c)
    (hc : c <= expScale a n) :
    a <= Real.exp (-(c * (n : Real))) := by
  by_cases hn : n = 0
  · subst n
    simpa using ha1.le
  · have hnposNat : 0 < n := Nat.pos_of_ne_zero hn
    have hnpos : 0 < (n : Real) := by exact_mod_cast hnposNat
    by_cases hapos : 0 < a
    · have hlogneg : Real.log a < 0 := Real.log_neg hapos ha1
      have hc' : c <= -Real.log a / (2 * (n : Real)) := by
        simpa [expScale, hn, hapos] using hc
      have hlog_le : Real.log a <= -(c * (n : Real)) := by
        have hmul := mul_le_mul_of_nonneg_right hc' hnpos.le
        have hdenpos : 0 < 2 * (n : Real) := by positivity
        have hcalc :
            (-Real.log a / (2 * (n : Real))) * (n : Real) =
              -Real.log a / 2 := by
          field_simp [hdenpos.ne', hnpos.ne']
        rw [hcalc] at hmul
        nlinarith
      exact (Real.log_le_iff_le_exp hapos).mp hlog_le
    · have ha_nonpos : a <= 0 := le_of_not_gt hapos
      exact ha_nonpos.trans (Real.exp_pos _).le

private theorem exists_small_exp_bound {a : Nat -> Real} {L : Nat}
    (hnonneg : forall n : Nat, 0 <= a n)
    (hlt_one : forall n : Nat, n < L -> a n < 1) :
    exists c : Real, 0 < c /\
      forall n : Nat, n < L -> a n <= Real.exp (-(c * (n : Real))) := by
  classical
  let s : Finset Nat := Finset.range L
  let cFor : Nat -> Real := fun n => expScale (a n) n
  have hcFor_pos : forall n, n ∈ s -> 0 < cFor n := by
    intro n hn
    have hnL : n < L := by simpa [s] using hn
    dsimp [cFor]
    unfold expScale
    split_ifs with hnzero hpos
    · norm_num
    · have hnposNat : 0 < n := Nat.pos_of_ne_zero hnzero
      have hnpos : 0 < (n : Real) := by exact_mod_cast hnposNat
      have hlogneg : Real.log (a n) < 0 := Real.log_neg hpos (hlt_one n hnL)
      have hdenpos : 0 < 2 * (n : Real) := by positivity
      exact div_pos (neg_pos.mpr hlogneg) hdenpos
    · norm_num
  by_cases hs : s.Nonempty
  · let c : Real := s.inf' hs cFor
    have hcpos : 0 < c := by
      dsimp [c]
      rw [Finset.lt_inf'_iff]
      intro n hn
      exact hcFor_pos n hn
    refine ⟨c, hcpos, ?_⟩
    intro n hnL
    have hnmem : n ∈ s := by simpa [s] using hnL
    have hcle : c <= cFor n := by
      exact Finset.inf'_le (s := s) (f := cFor) hnmem
    exact exp_bound_single (hnonneg n) (hlt_one n hnL) hcpos.le hcle
  · have hL0 : L = 0 := by
      contrapose! hs
      exact ⟨0, by simp [s, Nat.pos_iff_ne_zero.mpr hs]⟩
    refine ⟨1, by norm_num, ?_⟩
    intro n hnL
    omega

private theorem rho_pow_le_exp {rho c : Real} {L n : Nat}
    (hL : 0 < L) (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hn : L <= n)
    (hc : c <= if rho = 0 then 1 else -Real.log rho / (2 * (L : Real))) :
    rho ^ (n / L) <= Real.exp (-(c * (n : Real))) := by
  by_cases hrhoz : rho = 0
  · subst rho
    have hdivpos : 0 < n / L := Nat.div_pos hn hL
    rw [zero_pow (Nat.ne_of_gt hdivpos)]
    positivity
  · have hrhopos : 0 < rho := lt_of_le_of_ne' hrho0 hrhoz
    have hlogneg : Real.log rho < 0 := Real.log_neg hrhopos hrho1
    have hLpos : 0 < (L : Real) := by exact_mod_cast hL
    have hc' : c <= -Real.log rho / (2 * (L : Real)) := by
      simpa [hrhoz] using hc
    have hlog_bound :
        ((n / L : Nat) : Real) * Real.log rho <= -(c * (n : Real)) := by
      have hlog_nonpos : Real.log rho <= 0 := le_of_lt hlogneg
      have hstep :
          (((n / L : Nat) : Real)) * Real.log rho <=
            ((n : Real) / (2 * (L : Real))) * Real.log rho := by
        have hfloor_lower :
            (n : Real) / (2 * (L : Real)) <= (((n / L : Nat) : Real)) := by
          let q : Nat := n / L
          have hqpos : 0 < q := Nat.div_pos hn hL
          have hlt : n < L * (q + 1) := by
            simpa [q] using Nat.lt_mul_div_succ n hL
          have hq_succ : q + 1 <= 2 * q := by omega
          have hlt2 : n < L * (2 * q) := hlt.trans_le (Nat.mul_le_mul_left L hq_succ)
          have hlt2R : (n : Real) < (L : Real) * (2 * (q : Real)) := by
            exact_mod_cast hlt2
          have hdenpos : 0 < 2 * (L : Real) := by positivity
          have hltdiv : (n : Real) / (2 * (L : Real)) < (q : Real) := by
            rw [div_lt_iff₀ hdenpos]
            nlinarith
          exact le_of_lt (by simpa [q, mul_comm, mul_left_comm, mul_assoc] using hltdiv)
        exact mul_le_mul_of_nonpos_right hfloor_lower hlog_nonpos
      have hmain :
          ((n : Real) / (2 * (L : Real))) * Real.log rho <=
            -(c * (n : Real)) := by
        have hmul' := mul_le_mul_of_nonneg_right hc' (by positivity : 0 <= (n : Real))
        have hrewrite :
            (-Real.log rho / (2 * (L : Real))) * (n : Real) =
              -(((n : Real) / (2 * (L : Real))) * Real.log rho) := by
          ring
        rw [hrewrite] at hmul'
        nlinarith
      exact hstep.trans hmain
    calc
      rho ^ (n / L) = rho ^ (((n / L : Nat) : Real)) := by
        rw [Real.rpow_natCast]
      _ = Real.exp (Real.log rho * (((n / L : Nat) : Real))) := by
        rw [Real.rpow_def_of_pos hrhopos]
      _ = Real.exp ((((n / L : Nat) : Real)) * Real.log rho) := by
        rw [mul_comm]
      _ <= Real.exp (-(c * (n : Real))) := Real.exp_le_exp.mpr hlog_bound

private theorem recurrence_exponential_bound {a : Nat -> Real} {rho : Real} {L : Nat}
    (hL : 0 < L) (hrho0 : 0 <= rho) (hrho1 : rho < 1)
    (hnonneg : forall n : Nat, 0 <= a n)
    (hone : forall n : Nat, a n <= 1)
    (hsmall : forall n : Nat, n < L -> a n < 1)
    (hrec : forall n : Nat, L <= n -> a n <= rho * a (n - L)) :
    exists c : Real, 0 < c /\
      forall n : Nat, a n <= Real.exp (-(c * (n : Real))) := by
  classical
  rcases exists_small_exp_bound (a := a) (L := L) hnonneg hsmall with
    ⟨cSmall, hcSmall, hSmall⟩
  let cLarge : Real := if rho = 0 then 1 else -Real.log rho / (2 * (L : Real))
  have hcLarge : 0 < cLarge := by
    by_cases hrhoz : rho = 0
    · simp [cLarge, hrhoz]
    · have hrhopos : 0 < rho := lt_of_le_of_ne' hrho0 hrhoz
      have hlogneg : Real.log rho < 0 := Real.log_neg hrhopos hrho1
      have hLpos : 0 < (L : Real) := by exact_mod_cast hL
      simp [cLarge, hrhoz, div_pos (neg_pos.mpr hlogneg) (by positivity : 0 < 2 * (L : Real))]
  let c : Real := min cSmall cLarge
  have hc : 0 < c := lt_min hcSmall hcLarge
  refine ⟨c, hc, ?_⟩
  intro n
  by_cases hnsmall : n < L
  · exact (hSmall n hnsmall).trans (Real.exp_le_exp.mpr (by
      have hc_le : c <= cSmall := min_le_left _ _
      nlinarith [mul_le_mul_of_nonneg_right hc_le (by exact_mod_cast Nat.zero_le n :
        0 <= (n : Real))]))
  · have hnL : L <= n := le_of_not_gt hnsmall
    have hiter := recurrence_iterate hL hrho0 hone hrec n
    have hpow := rho_pow_le_exp hL hrho0 hrho1 hnL
      (min_le_right cSmall cLarge : c <= cLarge)
      (n := n)
    exact hiter.trans hpow

private theorem prob_le_of_pred_imp {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (E F : LocalEvent d) (himp : forall omega, E.pred omega -> F.pred omega) :
    Prob p E <= Prob p F := by
  classical
  let G : Finset (Bond d) := E.support ∪ F.support
  have hEsub : E.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inl he)
  have hFsub : F.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inr he)
  calc
    Prob p E = ProbOn p G (fun sigma => E.pred (extendConfig G sigma)) :=
      prob_support_mono E hEsub
    _ <= ProbOn p G (fun sigma => F.pred (extendConfig G sigma)) := by
      exact probOn_mono (fun sigma h => himp (extendConfig G sigma) h) hp0 hp1
    _ = Prob p F := (prob_support_mono F hFsub).symm

private def translateVertexEmbedding {d : Nat} (a : Vertex d) : Vertex d ↪ Vertex d where
  toFun := translateVertex a
  inj' := by
    intro x y h
    funext i
    have hi := congrFun h i
    dsimp [translateVertex] at hi
    change x i + a i = y i + a i at hi
    omega

private theorem translateVertex_neg_apply {d : Nat} (a x : Vertex d) :
    translateVertex (-a) (translateVertex a x) = x := by
  funext i
  change x i + a i + (-a i) = x i
  ring

private theorem translateVertex_neg_self {d : Nat} (x : Vertex d) :
    translateVertex (-x) x = (0 : Vertex d) := by
  funext i
  change x i + -x i = 0
  ring

private theorem translateVertex_neg_eq_sub {d : Nat} (x y : Vertex d) :
    translateVertex (-y) x = x - y := by
  funext i
  change x i + -y i = x i - y i
  ring

private theorem translateVertex_neg_image {d : Nat} (a : Vertex d) (S : Finset (Vertex d)) :
    (S.image (translateVertex a)).image (translateVertex (-a)) = S := by
  classical
  ext x
  constructor
  · intro hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨y, hy, hxy⟩
    rw [Finset.mem_image] at hy
    rcases hy with ⟨z, hz, rfl⟩
    have hxz : x = z := by
      rw [← hxy]
      exact translateVertex_neg_apply a z
    simpa [hxz] using hz
  · intro hx
    rw [Finset.mem_image]
    refine ⟨translateVertex a x, ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨x, hx, rfl⟩
    · exact translateVertex_neg_apply a x

private def translateBond {d : Nat} (a : Vertex d) (b : Bond d) : Bond d where
  carrier := b.carrier.map (translateVertexEmbedding a)
  card_two := by
    rw [Finset.card_map]
    exact b.card_two
  adj_pair := by
    intro u hu v hv huv
    rw [Finset.mem_map] at hu hv
    rcases hu with ⟨u0, hu0, rfl⟩
    rcases hv with ⟨v0, hv0, hvEq⟩
    subst hvEq
    have huv0 : u0 ≠ v0 := by
      intro h
      apply huv
      simp [h]
    exact (adj_translate_iff (a := a)).mpr (b.adj_pair u0 hu0 v0 hv0 huv0)

private theorem translateBond_neg_apply {d : Nat} (a : Vertex d) (b : Bond d) :
    translateBond (-a) (translateBond a b) = b := by
  cases b with
  | mk carrier card_two adj_pair =>
      simp [translateBond]
      ext x
      constructor
      · intro hx
        rw [Finset.mem_map] at hx
        rcases hx with ⟨y, hy, hxy⟩
        rw [Finset.mem_map] at hy
        rcases hy with ⟨z, hz, rfl⟩
        have hxz : x = z := by
          rw [← hxy]
          exact translateVertex_neg_apply a z
        simpa [hxz] using hz
      · intro hx
        rw [Finset.mem_map]
        refine ⟨translateVertex a x, ?_, ?_⟩
        · rw [Finset.mem_map]
          exact ⟨x, hx, rfl⟩
        · exact translateVertex_neg_apply a x

private theorem translateBond_bondOfAdj {d : Nat} (a : Vertex d)
    {x y : Vertex d} (hxy : Adj x y) :
    translateBond a (bondOfAdj hxy) =
      bondOfAdj ((adj_translate_iff (a := a) (x := x) (y := y)).mpr hxy) := by
  simp [translateBond, bondOfAdj]
  ext z
  simp [translateVertexEmbedding]

private theorem translateBond_mem_internalBonds {d : Nat} {a : Vertex d}
    {S : Finset (Vertex d)} {b : Bond d}
    (hb : b ∈ internalBonds S) :
    translateBond a b ∈ internalBonds (S.image (translateVertex a)) := by
  classical
  rw [internalBonds] at hb ⊢
  rcases Finset.mem_image.mp hb with ⟨e, _he, rfl⟩
  have hfilter := Finset.mem_filter.mp e.property
  let x : Vertex d := e.1.1
  let y : Vertex d := e.1.2
  have hxS : x ∈ S := (Finset.mem_product.mp hfilter.1).1
  have hyS : y ∈ S := (Finset.mem_product.mp hfilter.1).2
  have hxy : Adj x y := hfilter.2.2
  refine Finset.mem_image.mpr ?_
  let et : {e : Vertex d × Vertex d //
      e ∈ ((S.image (translateVertex a)).product (S.image (translateVertex a))).filter
        fun e : Vertex d × Vertex d => e.1 ≠ e.2 ∧ Adj e.1 e.2} :=
    ⟨(translateVertex a x, translateVertex a y), by
      refine Finset.mem_filter.mpr ?_
      refine ⟨Finset.mem_product.mpr ?_, ?_, (adj_translate_iff (a := a)).mpr hxy⟩
      · exact ⟨Finset.mem_image.mpr ⟨x, hxS, rfl⟩,
          Finset.mem_image.mpr ⟨y, hyS, rfl⟩⟩
      · intro h
        have : x = y := (translateVertexEmbedding a).injective h
        exact hfilter.2.1 this⟩
  refine ⟨et, by simp [et], ?_⟩
  dsimp [et, x, y]
  rw [translateBond_bondOfAdj]

private theorem translateBond_mem_internalBonds_neg {d : Nat} {a : Vertex d}
    {S : Finset (Vertex d)} {b : Bond d}
    (hb : b ∈ internalBonds (S.image (translateVertex a))) :
    translateBond (-a) b ∈ internalBonds S := by
  have h := translateBond_mem_internalBonds (a := -a) (S := S.image (translateVertex a)) hb
  simpa [translateVertex_neg_image] using h

private def translateInternalBondsEquiv {d : Nat} (a : Vertex d) (S : Finset (Vertex d)) :
    internalBonds S ≃ internalBonds (S.image (translateVertex a)) where
  toFun b := ⟨translateBond a b.1, translateBond_mem_internalBonds (a := a) b.2⟩
  invFun b := ⟨translateBond (-a) b.1, translateBond_mem_internalBonds_neg (a := a) b.2⟩
  left_inv := by
    intro b
    apply Subtype.ext
    exact translateBond_neg_apply a b.1
  right_inv := by
    intro b
    apply Subtype.ext
    have h := translateBond_neg_apply (-a) b.1
    simpa using h

private theorem openPath_translate_config {d : Nat} {omega omega' : Config d}
    {a : Vertex d} {gamma : List (Vertex d)}
    (hopen_translate : forall {u v : Vertex d} (huv : Adj u v),
      omega (bondOfAdj huv) = true ->
      omega' (bondOfAdj ((adj_translate_iff (a := a) (x := u) (y := v)).mpr huv)) = true)
    (hgamma : OpenPath omega gamma) :
    OpenPath omega' (gamma.map (translateVertex a)) := by
  rw [OpenPath, List.isChain_map]
  exact hgamma.imp fun {_ _} h => by
    rcases h with ⟨huv, hopen⟩
    exact ⟨(adj_translate_iff (a := a)).mpr huv, hopen_translate huv hopen⟩

private theorem connIn_translate_config {d : Nat} {omega omega' : Config d}
    {S : Finset (Vertex d)} {a x y : Vertex d}
    (hopen_translate : forall {u v : Vertex d} (huv : Adj u v),
      omega (bondOfAdj huv) = true ->
      omega' (bondOfAdj ((adj_translate_iff (a := a) (x := u) (y := v)).mpr huv)) = true)
    (hxy : ConnIn omega S x y) :
    ConnIn omega' (S.image (translateVertex a)) (translateVertex a x) (translateVertex a y) := by
  rcases hxy with ⟨gamma, hpath, hS, hopen⟩
  exact ⟨gamma.map (translateVertex a), pathFromTo_translate hpath,
    pathIn_translate hS, openPath_translate_config hopen_translate hopen⟩

private theorem connToSetIn_translate_assignment {d : Nat} {a : Vertex d}
    {T B : Finset (Vertex d)} {u : Vertex d}
    (tau : internalBonds (T.image (translateVertex a)) -> Bool) :
    let sigma : internalBonds T -> Bool := fun b => tau (translateInternalBondsEquiv a T b)
    ConnToSetIn (extendConfig (internalBonds T) sigma) T u B ->
      ConnToSetIn (extendConfig (internalBonds (T.image (translateVertex a))) tau)
        (T.image (translateVertex a)) (translateVertex a u) (B.image (translateVertex a)) := by
  classical
  intro sigma hconn
  rcases hconn with ⟨b, hb, hconnub⟩
  refine ⟨translateVertex a b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, ?_⟩
  refine connIn_translate_config ?_ hconnub
  intro x y hxy hopen
  by_cases hbxy : bondOfAdj hxy ∈ internalBonds T
  · have hopen_sigma : sigma ⟨bondOfAdj hxy, hbxy⟩ = true := by
      simpa [extendConfig, hbxy] using hopen
    let hxy' : Adj (translateVertex a x) (translateVertex a y) :=
      (adj_translate_iff (a := a)).mpr hxy
    have hbxy' : bondOfAdj hxy' ∈ internalBonds (T.image (translateVertex a)) := by
      have hmem := translateBond_mem_internalBonds (a := a) hbxy
      simpa [translateBond_bondOfAdj (a := a) hxy] using hmem
    have hidx :
        (⟨bondOfAdj hxy', hbxy'⟩ : internalBonds (T.image (translateVertex a))) =
          translateInternalBondsEquiv a T ⟨bondOfAdj hxy, hbxy⟩ := by
      apply Subtype.ext
      exact (translateBond_bondOfAdj (a := a) hxy).symm
    change extendConfig (internalBonds (T.image (translateVertex a))) tau
      (bondOfAdj hxy') = true
    simpa [extendConfig, hbxy', hidx] using hopen_sigma
  · simp [extendConfig, hbxy] at hopen

private theorem prob_connToSetIn_le_translate {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) (a : Vertex d)
    (T B : Finset (Vertex d)) (u : Vertex d) :
    Prob p (connToSetInEvent T u B) <=
      Prob p (connToSetInEvent (T.image (translateVertex a)) (translateVertex a u)
        (B.image (translateVertex a))) := by
  classical
  let F : Finset (Bond d) := internalBonds T
  let G : Finset (Bond d) := internalBonds (T.image (translateVertex a))
  let e : F ≃ G := translateInternalBondsEquiv a T
  let A : (F -> Bool) -> Prop := fun sigma => ConnToSetIn (extendConfig F sigma) T u B
  let A' : (G -> Bool) -> Prop := fun tau =>
    ConnToSetIn (extendConfig G tau) (T.image (translateVertex a)) (translateVertex a u)
      (B.image (translateVertex a))
  have hmono : bernProb p A <= bernProb p
      (fun sigma : F -> Bool => A' (fun g : G => sigma (e.symm g))) := by
    refine bernProb_mono ?_ hp0 hp1
    intro sigma hA
    have hforward := connToSetIn_translate_assignment (a := a) (T := T) (B := B)
      (u := u) (fun g : G => sigma (e.symm g))
    dsimp [A']
    dsimp at hforward
    have hsigeq : (fun b : internalBonds T => (fun g : G => sigma (e.symm g))
        (translateInternalBondsEquiv a T b)) = sigma := by
      funext b
      simp [e]
    have hA' : ConnToSetIn (extendConfig (internalBonds T)
        (fun b : internalBonds T => (fun g : G => sigma (e.symm g))
          (translateInternalBondsEquiv a T b))) T u B := by
      simpa [hsigeq, A, F] using hA
    simpa [F, G, e] using hforward hA'
  calc
    Prob p (connToSetInEvent T u B) = bernProb p A := rfl
    _ <= bernProb p (fun sigma : F -> Bool => A' (fun g : G => sigma (e.symm g))) :=
      hmono
    _ = bernProb p A' := by
      exact bernProb_reindex (α := F) (β := G) p e A'
    _ = Prob p (connToSetInEvent (T.image (translateVertex a)) (translateVertex a u)
        (B.image (translateVertex a))) := rfl

private theorem connIn_single {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {x : Vertex d} (hx : x ∈ S) : ConnIn omega S x x := by
  refine ⟨[x], ?_, ?_, ?_⟩
  · simp [PathFromTo, IsPath]
  · intro z hz
    have hzx : z = x := by simpa using hz
    simpa [hzx] using hx
  · simp [OpenPath]

private theorem connIn_prepend_open_adj {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {x y z : Vertex d}
    (hxS : x ∈ S) (hxy : Adj x y) (hopen : omega (bondOfAdj hxy) = true)
    (hconn : ConnIn omega S y z) : ConnIn omega S x z := by
  rcases hconn with ⟨gamma, hpath, hS, hopenPath⟩
  rcases hpath with ⟨hhead, hlast, hpathChain⟩
  cases gamma with
  | nil => simp at hhead
  | cons a rest =>
      have hay : a = y := by simpa using hhead
      subst a
      refine ⟨x :: y :: rest, ?_, ?_, ?_⟩
      · constructor
        · simp
        · constructor
          · simpa using hlast
          · rw [IsPath, List.isChain_cons_cons]
            exact ⟨hxy, hpathChain⟩
      · intro w hw
        simp at hw
        rcases hw with rfl | hw
        · exact hxS
        · exact hS w (by simpa using hw)
      · rw [OpenPath, List.isChain_cons_cons]
        exact ⟨⟨hxy, hopen⟩, hopenPath⟩

private theorem connIn_append_open_adj {d : Nat} {omega : Config d}
    {S T : Finset (Vertex d)} {x y z : Vertex d}
    (hST : S <= T) (hzT : z ∈ T) (hyz : Adj y z)
    (hopen : omega (bondOfAdj hyz) = true)
    (hconn : ConnIn omega S x y) :
    ConnIn omega T x z := by
  rcases hconn with ⟨gamma, hpath, hS, hopenPath⟩
  rcases hpath with ⟨hhead, hlast, hpathChain⟩
  refine ⟨gamma ++ [z], ?_, ?_, ?_⟩
  · constructor
    · rw [List.head?_append]
      simp [hhead]
    · constructor
      · simp
      · rw [IsPath, List.isChain_append]
        refine ⟨hpathChain, by simp, ?_⟩
        intro a ha b hb
        have hay : y = a := by simpa [hlast] using ha
        have hzb : z = b := by simpa using hb
        subst a
        subst b
        exact hyz
  · intro w hw
    rw [List.mem_append] at hw
    rcases hw with hw | hw
    · exact hST (hS w hw)
    · have hwz : w = z := by simpa using hw
      simpa [hwz] using hzT
  · rw [OpenPath, List.isChain_append]
    refine ⟨hopenPath, by simp, ?_⟩
    intro a ha b hb
    have hay : y = a := by simpa [hlast] using ha
    have hzb : z = b := by simpa using hb
    subst a
    subst b
    exact ⟨hyz, hopen⟩

private theorem exitPred_of_connIn_to_not_mem {d : Nat} {omega : Config d}
    {S T : Finset (Vertex d)} {x z : Vertex d}
    (hxS : x ∈ S) (hzS : z ∉ S)
    (hconn : ConnIn omega T x z) :
    exists e, exists he : e ∈ orientedBoundary S,
      ConnIn omega S x e.1 /\
      omega (bondOfAdj (orientedBoundary_adj he)) = true := by
  rcases hconn with ⟨gamma, hpath, hT, hopenPath⟩
  revert x z
  induction gamma with
  | nil =>
      intro x z hxS hzS hpath
      rcases hpath with ⟨hhead, _hlast, _hchain⟩
      simp at hhead
  | cons a rest ih =>
      intro x z hxS hzS hpath
      rcases hpath with ⟨hhead, hlast, hchain⟩
      cases rest with
      | nil =>
          have hax : a = x := by simpa using hhead
          have haz : a = z := by simpa using hlast
          exact False.elim (hzS (by simpa [← hax, ← haz] using hxS))
      | cons b tail =>
          have hax : a = x := by simpa using hhead
          subst x
          have haS : a ∈ S := hxS
          have hchain' := List.isChain_cons_cons.mp hchain
          have hopen' := List.isChain_cons_cons.mp hopenPath
          by_cases hbS : b ∈ S
          · have htail_path : PathFromTo (b :: tail) b z := by
              exact ⟨rfl, by simpa using hlast, hchain'.2⟩
            have htail_T : PathIn T (b :: tail) := by
              intro w hw
              exact hT w (by simp [hw])
            rcases ih htail_T hopen'.2 hbS hzS htail_path with ⟨e, he, hconn, hopenEdge⟩
            refine ⟨e, he, ?_, hopenEdge⟩
            exact connIn_prepend_open_adj haS hchain'.1 hopen'.1.choose_spec hconn
          · let e : OrientedEdge d := (a, b)
            have he : e ∈ orientedBoundary S := by
              rw [mem_orientedBoundary_iff]
              exact ⟨haS, hbS, hchain'.1⟩
            refine ⟨e, he, ?_, ?_⟩
            · dsimp [e]
              exact connIn_single haS
            · dsimp [e]
              have hbEq : bondOfAdj (orientedBoundary_adj he) = bondOfAdj hchain'.1 := by
                apply bondOfAdj_same
              simpa [hbEq] using hopen'.1.choose_spec

private noncomputable def boxExitTargets (d n : Nat) : Finset (Vertex d) :=
  (orientedBoundary (ball d n)).image Prod.snd

private noncomputable def boxExitAmbient (d n : Nat) : Finset (Vertex d) :=
  ball d n ∪ boxExitTargets d n

private theorem mem_boxExitTargets_not_ball {d n : Nat} {x : Vertex d}
    (hx : x ∈ boxExitTargets d n) : x ∉ ball d n := by
  classical
  rw [boxExitTargets] at hx
  rcases Finset.mem_image.mp hx with ⟨e, he, rfl⟩
  exact (mem_orientedBoundary_iff.mp he).2.1

private theorem boxExitProb_le_boundary_conn {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) (n : Nat) :
    boxExitProb d p n <=
      Prob p (connToSetInEvent (boxExitAmbient d n) (0 : Vertex d) (boxExitTargets d n)) := by
  classical
  unfold boxExitProb exitProb
  refine prob_le_of_pred_imp hp0 hp1
    (exitEvent (ball d n) (zero_mem_ball d n))
    (connToSetInEvent (boxExitAmbient d n) (0 : Vertex d) (boxExitTargets d n)) ?_
  intro omega hexit
  rcases hexit with ⟨e, he, hconn, hopen⟩
  refine ⟨e.2, ?_, ?_⟩
  · rw [boxExitTargets]
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  · exact connIn_append_open_adj
      (S := ball d n) (T := boxExitAmbient d n)
      (by
        intro x hx
        exact Finset.mem_union.mpr (Or.inl hx))
      (Finset.mem_union.mpr (Or.inr (by
        rw [boxExitTargets]
        exact Finset.mem_image.mpr ⟨e, he, rfl⟩)))
      (orientedBoundary_adj he) hopen hconn

private theorem connToSetIn_le_boxExitProb_of_targets_outside {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) (T B : Finset (Vertex d)) (k : Nat)
    (hB : forall z, z ∈ B -> z ∉ ball d k) :
    Prob p (connToSetInEvent T (0 : Vertex d) B) <= boxExitProb d p k := by
  classical
  unfold boxExitProb exitProb
  refine prob_le_of_pred_imp hp0 hp1
    (connToSetInEvent T (0 : Vertex d) B)
    (exitEvent (ball d k) (zero_mem_ball d k)) ?_
  intro omega hconn
  rcases hconn with ⟨z, hz, hconnz⟩
  exact exitPred_of_connIn_to_not_mem (zero_mem_ball d k) (hB z hz) hconnz

private theorem connToBoxBoundary_le_shifted_boxExitProb {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) {L n : Nat} {y : Vertex d}
    (hy : y ∈ ball d L) (hn : L <= n) :
    Prob p (connToSetInEvent (boxExitAmbient d n) y (boxExitTargets d n)) <=
      boxExitProb d p (n - L) := by
  classical
  let a : Vertex d := -y
  have htranslate := prob_connToSetIn_le_translate hp0 hp1 a
    (boxExitAmbient d n) (boxExitTargets d n) y
  have htargets :
      forall z, z ∈ (boxExitTargets d n).image (translateVertex a) ->
        z ∉ ball d (n - L) := by
    intro z hz
    rw [Finset.mem_image] at hz
    rcases hz with ⟨w, hw, rfl⟩
    have hwout : w ∉ ball d n := mem_boxExitTargets_not_ball hw
    have hgeom := translate_ball_exit (d := d) (n := n) (L := L) (y := y) (z := w)
      hy hwout hn
    simpa [a, translateVertex_neg_eq_sub] using hgeom
  have hle_exit := connToSetIn_le_boxExitProb_of_targets_outside hp0 hp1
    ((boxExitAmbient d n).image (translateVertex a))
    ((boxExitTargets d n).image (translateVertex a)) (n - L) htargets
  have hstart : translateVertex a y = (0 : Vertex d) := by
    simpa [a] using translateVertex_neg_self y
  exact htranslate.trans (by simpa [hstart] using hle_exit)

private theorem boxExitProb_recurrence_of_phi_lt_one {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) (S : Finset (Vertex d)) (L : Nat)
    (hL : 0 < L) (hS : forall x, x ∈ S -> x ∈ ball d (L - 1))
    (h0S : (0 : Vertex d) ∈ S) (_hphi : phi p S < 1) :
    forall n : Nat, L <= n ->
      boxExitProb d p n <= phi p S * boxExitProb d p (n - L) := by
  classical
  intro n hn
  let B : Finset (Vertex d) := boxExitTargets d n
  let T : Finset (Vertex d) := boxExitAmbient d n
  have hST : S <= T := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inl (by
      rw [mem_ball_iff]
      have hxL : l1 x <= L - 1 := mem_ball_iff.mp (hS x hx)
      omega))
  have hBT : B <= T := by
    intro x hx
    exact Finset.mem_union.mpr (Or.inr hx)
  have hBS : Disjoint B S := by
    rw [Finset.disjoint_left]
    intro x hxB hxS
    have hxnot : x ∉ ball d n := mem_boxExitTargets_not_ball (d := d) (n := n) (x := x)
      (by simpa [B] using hxB)
    apply hxnot
    rw [mem_ball_iff]
    have hxL : l1 x <= L - 1 := mem_ball_iff.mp (hS x hxS)
    omega
  have hbox_to_conn :
      boxExitProb d p n <= Prob p (connToSetInEvent T (0 : Vertex d) B) := by
    simpa [T, B] using boxExitProb_le_boundary_conn (d := d) (p := p) hp0 hp1 n
  have hboundary :
      Prob p (connToSetInEvent T (0 : Vertex d) B) <=
        (orientedBoundary S).sum
          (fun e => p * Prob p (connInEvent S (0 : Vertex d) e.1) *
            Prob p (connToSetInEvent T e.2 B)) := by
    exact boundary_inequality T S B (0 : Vertex d) h0S hST hBT hBS hp0 hp1
  have hterm :
      (orientedBoundary S).sum
          (fun e => p * Prob p (connInEvent S (0 : Vertex d) e.1) *
            Prob p (connToSetInEvent T e.2 B)) <=
        (orientedBoundary S).sum
          (fun e => p * Prob p (connInEvent S (0 : Vertex d) e.1) *
            boxExitProb d p (n - L)) := by
    refine Finset.sum_le_sum ?_
    intro e he
    have hy : e.2 ∈ ball d L := boundary_endpoint_mem_ball hL hS he
    have hconn_le :
        Prob p (connToSetInEvent T e.2 B) <= boxExitProb d p (n - L) := by
      simpa [T, B] using
        connToBoxBoundary_le_shifted_boxExitProb (d := d) (p := p) hp0 hp1 hy hn
    have hcoef_nonneg :
        0 <= p * Prob p (connInEvent S (0 : Vertex d) e.1) := by
      exact mul_nonneg hp0 (probOn_nonneg
        (F := (connInEvent S (0 : Vertex d) e.1).support)
        (A := fun sigma : (connInEvent S (0 : Vertex d) e.1).support -> Bool =>
          (connInEvent S (0 : Vertex d) e.1).pred
            (extendConfig (connInEvent S (0 : Vertex d) e.1).support sigma))
        hp0 hp1)
    exact mul_le_mul_of_nonneg_left hconn_le hcoef_nonneg
  have hfactor :
      (orientedBoundary S).sum
          (fun e => p * Prob p (connInEvent S (0 : Vertex d) e.1) *
            boxExitProb d p (n - L)) =
        phi p S * boxExitProb d p (n - L) := by
    simp [phi, Finset.mul_sum, mul_comm, mul_left_comm]
  exact hbox_to_conn.trans (hboundary.trans (hterm.trans_eq hfactor))

private theorem exists_ball_bound_for_finset {d : Nat} (S : Finset (Vertex d)) :
    exists L : Nat, 0 < L /\ forall x, x ∈ S -> x ∈ ball d (L - 1) := by
  classical
  let M : Nat := (S.image l1).sup id
  refine ⟨M + 1, by omega, ?_⟩
  intro x hx
  rw [mem_ball_iff]
  have hxM : l1 x <= M := by
    exact Finset.le_sup (s := S.image l1) (f := id) (by
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  simpa using hxM

private theorem exponential_decay_below_pTilde_core {d : Nat} {p : Real}
    (hp0 : 0 < p) (hp : p < pTilde d) :
    exists c : Real, 0 < c /\
      forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real))) := by
  classical
  have hp0le : 0 <= p := hp0.le
  have hp1 : p < 1 := hp.trans_le (pTilde_le_one d)
  have hp1le : p <= 1 := hp1.le
  rcases exists_phi_lt_one_of_lt_pTilde hp0le hp with ⟨S, h0S, hphi⟩
  rcases exists_ball_bound_for_finset S with ⟨L, hL, hS⟩
  have hrec := boxExitProb_recurrence_of_phi_lt_one hp0le hp1le S L hL hS h0S hphi
  refine recurrence_exponential_bound (a := fun n => boxExitProb d p n)
    (rho := phi p S) (L := L) hL ?_ hphi ?_ ?_ ?_ hrec
  · dsimp [phi]
    exact mul_nonneg hp0le (Finset.sum_nonneg (by
      intro e _he
      exact probOn_nonneg
        (F := (connInEvent S (0 : Vertex d) e.1).support)
        (A := fun sigma : (connInEvent S (0 : Vertex d) e.1).support -> Bool =>
          (connInEvent S (0 : Vertex d) e.1).pred
            (extendConfig (connInEvent S (0 : Vertex d) e.1).support sigma))
        hp0le hp1le))
  · intro n
    exact boxExitProb_nonneg hp0le hp1le n
  · intro n
    exact boxExitProb_le_one hp0le hp1le n
  · intro n _hn
    exact boxExitProb_lt_one_of_lt_one hp0le hp1 n

/-- Lemma 5, exponential decay below the finite-set critical point. -/
theorem exponential_decay_below_pTilde {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp : p < pTilde d) :
    exists c : Real, 0 < c /\
      forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real))) := by
  by_cases hpzero : p = 0
  · subst p
    refine ⟨1, by norm_num, ?_⟩
    intro n
    rw [boxExitProb_zero]
    positivity
  · exact exponential_decay_below_pTilde_core (lt_of_le_of_ne' hp0 hpzero) hp

end Sharpness
