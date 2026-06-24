import Sharpness.BoundaryIneq
import Sharpness.FiniteGeometry
import Sharpness.Phi

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

/--
Missing mathematical fact: combine Lemma 4 with the box translation estimate to
obtain the finite-volume recurrence `a_n <= rho * a_(n-L)` for the finite box
exit probabilities, where `rho = phi p S < 1`.
-/
private theorem boxExitProb_recurrence_of_phi_lt_one {d : Nat} {p : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) (S : Finset (Vertex d)) (L : Nat)
    (_hL : 0 < L) (_hS : forall x, x ∈ S -> x ∈ ball d (L - 1))
    (_h0S : (0 : Vertex d) ∈ S) (_hphi : phi p S < 1) :
    forall n : Nat, L <= n ->
      boxExitProb d p n <= phi p S * boxExitProb d p (n - L) := by
  sorry

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
