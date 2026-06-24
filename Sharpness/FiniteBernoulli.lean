import Sharpness.Bonds

namespace Sharpness

open scoped BigOperators

section Generic

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Bernoulli product weight on an arbitrary finite coordinate type. -/
noncomputable def bernWeight (p : Real) (sigma : α -> Bool) : Real :=
  Finset.univ.prod fun e : α => if sigma e then p else 1 - p

/-- Bernoulli product probability on an arbitrary finite coordinate type. -/
noncomputable def bernProb (p : Real) (A : (α -> Bool) -> Prop) : Real := by
  classical
  exact Finset.univ.sum fun sigma : α -> Bool =>
    if A sigma then bernWeight p sigma else 0

omit [DecidableEq α] in
theorem bernWeight_nonneg {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (sigma : α -> Bool) : 0 <= bernWeight p sigma := by
  classical
  dsimp [bernWeight]
  refine Finset.prod_nonneg ?_
  intro e he
  by_cases h : sigma e
  · simp [h, hp0]
  · have hp' : 0 <= 1 - p := sub_nonneg.mpr hp1
    simp [h, hp']

theorem bernWeight_total (p : Real) :
    (Finset.univ.sum fun sigma : α -> Bool => bernWeight p sigma) = 1 := by
  classical
  have hprod :=
    (Finset.prod_univ_sum (R := Real)
      (fun _ : α => (Finset.univ : Finset Bool))
      (fun e b => if b then p else 1 - p))
  have hsum :
      (Finset.sum (Fintype.piFinset fun _ : α => (Finset.univ : Finset Bool))
        fun sigma : α -> Bool => Finset.univ.prod fun e : α =>
          if sigma e then p else 1 - p) = 1 := by
    rw [← hprod]
    simp
  rw [Fintype.piFinset_univ] at hsum
  simpa [bernWeight] using hsum

theorem bernProb_nonneg {p : Real} {A : (α -> Bool) -> Prop}
    (hp0 : 0 <= p) (hp1 : p <= 1) : 0 <= bernProb p A := by
  classical
  dsimp [bernProb]
  refine Finset.sum_nonneg ?_
  intro sigma hsigma
  by_cases hA : A sigma
  · simp [hA, bernWeight_nonneg hp0 hp1 sigma]
  · simp [hA]

theorem bernProb_le_one {p : Real} {A : (α -> Bool) -> Prop}
    (hp0 : 0 <= p) (hp1 : p <= 1) : bernProb p A <= 1 := by
  classical
  rw [← bernWeight_total (α := α) p]
  dsimp [bernProb]
  refine Finset.sum_le_sum ?_
  intro sigma hsigma
  by_cases hA : A sigma
  · simp [hA]
  · simp [hA, bernWeight_nonneg hp0 hp1 sigma]

theorem bernProb_univ {p : Real} :
    bernProb p (fun _ : α -> Bool => True) = 1 := by
  classical
  simpa [bernProb] using bernWeight_total (α := α) p

theorem bernProb_compl {p : Real} {A : (α -> Bool) -> Prop} :
    bernProb p (fun sigma => ¬ A sigma) = 1 - bernProb p A := by
  classical
  rw [← bernProb_univ (α := α) (p := p)]
  dsimp [bernProb]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro sigma hsigma
  by_cases hA : A sigma <;> simp [hA]

theorem bernProb_mono {p : Real} {A B : (α -> Bool) -> Prop}
    (hAB : forall sigma, A sigma -> B sigma) (hp0 : 0 <= p) (hp1 : p <= 1) :
    bernProb p A <= bernProb p B := by
  classical
  dsimp [bernProb]
  refine Finset.sum_le_sum ?_
  intro sigma hsigma
  by_cases hA : A sigma
  · have hB : B sigma := hAB sigma hA
    simp [hA, hB]
  · by_cases hB : B sigma
    · simp [hA, hB, bernWeight_nonneg hp0 hp1 sigma]
    · simp [hA, hB]

theorem bernProb_union_bound {p : Real} {A B : (α -> Bool) -> Prop}
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    bernProb p (fun sigma => A sigma \/ B sigma) <= bernProb p A + bernProb p B := by
  classical
  dsimp [bernProb]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum ?_
  intro sigma hsigma
  have hw : 0 <= bernWeight p sigma := bernWeight_nonneg hp0 hp1 sigma
  by_cases hA : A sigma <;> by_cases hB : B sigma <;> simp [hA, hB, hw]

theorem bernWeight_reindex {β : Type*} [DecidableEq β] [Fintype β]
    (p : Real) (e : α ≃ β) (sigma : β -> Bool) :
    bernWeight p (fun a : α => sigma (e a)) = bernWeight p sigma := by
  classical
  dsimp [bernWeight]
  exact Fintype.prod_equiv e
    (fun a : α => if sigma (e a) then p else 1 - p)
    (fun b : β => if sigma b then p else 1 - p)
    (by intro a; rfl)

theorem bernProb_reindex {β : Type*} [DecidableEq β] [Fintype β]
    (p : Real) (e : α ≃ β) (A : (β -> Bool) -> Prop) :
    bernProb p (fun sigma : α -> Bool => A (fun b : β => sigma (e.symm b))) =
      bernProb p A := by
  classical
  let eFun : (α -> Bool) ≃ (β -> Bool) := Equiv.arrowCongr e (Equiv.refl Bool)
  dsimp [bernProb]
  refine Fintype.sum_equiv eFun
    (fun sigma : α -> Bool =>
      if A (fun b : β => sigma (e.symm b)) then bernWeight p sigma else 0)
    (fun tau : β -> Bool => if A tau then bernWeight p tau else 0) ?_
  intro sigma
  have hsigma : (fun b : β => sigma (e.symm b)) = eFun sigma := by
    funext b
    rfl
  by_cases hA : A (fun b : β => sigma (e.symm b))
  · have hA' : A (eFun sigma) := by simpa [hsigma] using hA
    have hweight :
        bernWeight p sigma = bernWeight p (eFun sigma) := by
      calc
        bernWeight p sigma =
            bernWeight p (fun b : β => sigma (e.symm b)) := by
          simpa using
            (bernWeight_reindex (α := β) (β := α) p e.symm sigma).symm
        _ = bernWeight p (eFun sigma) := by rw [hsigma]
    simp [hA, hA', hweight]
  · have hA' : ¬ A (eFun sigma) := by simpa [hsigma] using hA
    simp [hA, hA']

theorem bernWeight_sum {β : Type*} [DecidableEq β] [Fintype β]
    (p : Real) (sigma : α ⊕ β -> Bool) :
    bernWeight p sigma =
      bernWeight p (fun a : α => sigma (Sum.inl a)) *
        bernWeight p (fun b : β => sigma (Sum.inr b)) := by
  classical
  dsimp [bernWeight]
  exact Fintype.prod_sum_type fun x : α ⊕ β =>
    if sigma x then p else 1 - p

theorem bernProb_sum_left {β : Type*} [DecidableEq β] [Fintype β]
    (p : Real) (A : (α -> Bool) -> Prop) :
    bernProb p (fun sigma : α ⊕ β -> Bool => A (fun a : α => sigma (Sum.inl a))) =
      bernProb p A := by
  classical
  let eFun := Equiv.sumPiEquivProdPi (fun _ : α ⊕ β => Bool)
  have hsplit :
      bernProb p (fun sigma : α ⊕ β -> Bool => A (fun a : α => sigma (Sum.inl a))) =
        Finset.univ.sum
          (fun x : (α -> Bool) × (β -> Bool) =>
            if A x.1 then bernWeight p x.1 * bernWeight p x.2 else 0) := by
    dsimp [bernProb]
    refine Fintype.sum_equiv eFun
      (fun sigma : α ⊕ β -> Bool =>
        if A (fun a : α => sigma (Sum.inl a)) then bernWeight p sigma else 0)
      (fun x : (α -> Bool) × (β -> Bool) =>
        if A x.1 then bernWeight p x.1 * bernWeight p x.2 else 0) ?_
    intro sigma
    by_cases hA : A (fun a : α => sigma (Sum.inl a))
    · simp [hA, eFun, bernWeight_sum]
    · simp [hA, eFun]
  rw [hsplit]
  rw [Fintype.sum_prod_type]
  dsimp [bernProb]
  refine Finset.sum_congr rfl ?_
  intro sigma hsigma
  by_cases hA : A sigma
  · simp [hA]
    rw [← Finset.mul_sum]
    rw [bernWeight_total (α := β) p]
    simp
  · simp [hA]

theorem bernProb_sum_inter {β : Type*} [DecidableEq β] [Fintype β]
    (p : Real) (A : (α -> Bool) -> Prop) (B : (β -> Bool) -> Prop) :
    bernProb p
        (fun sigma : α ⊕ β -> Bool =>
          A (fun a : α => sigma (Sum.inl a)) /\
            B (fun b : β => sigma (Sum.inr b))) =
      bernProb p A * bernProb p B := by
  classical
  let eFun := Equiv.sumPiEquivProdPi (fun _ : α ⊕ β => Bool)
  let P : (α ⊕ β -> Bool) -> Prop :=
    fun sigma =>
      A (fun a : α => sigma (Sum.inl a)) /\
        B (fun b : β => sigma (Sum.inr b))
  let Q : ((α -> Bool) × (β -> Bool)) -> Prop :=
    fun x => A x.1 /\ B x.2
  have hsplit :
      bernProb p
          (fun sigma : α ⊕ β -> Bool =>
            A (fun a : α => sigma (Sum.inl a)) /\
              B (fun b : β => sigma (Sum.inr b))) =
        Finset.univ.sum
          (fun x : (α -> Bool) × (β -> Bool) =>
            @ite Real (Q x) (Classical.propDecidable (Q x))
              (bernWeight p x.1 * bernWeight p x.2) 0) := by
    dsimp [bernProb]
    change (Finset.univ.sum fun sigma : α ⊕ β -> Bool =>
        @ite Real
          (A (fun a : α => sigma (Sum.inl a)) /\
            B (fun b : β => sigma (Sum.inr b)))
          (Classical.propDecidable
            (A (fun a : α => sigma (Sum.inl a)) /\
              B (fun b : β => sigma (Sum.inr b))))
          (bernWeight p sigma) 0) =
      (Finset.univ.sum fun x : (α -> Bool) × (β -> Bool) =>
        @ite Real (Q x) (Classical.propDecidable (Q x))
          (bernWeight p x.1 * bernWeight p x.2) 0)
    refine Fintype.sum_equiv eFun
      (fun sigma : α ⊕ β -> Bool =>
        @ite Real
          (A (fun a : α => sigma (Sum.inl a)) /\
            B (fun b : β => sigma (Sum.inr b)))
          (Classical.propDecidable
            (A (fun a : α => sigma (Sum.inl a)) /\
              B (fun b : β => sigma (Sum.inr b))))
          (bernWeight p sigma) 0)
      (fun x : (α -> Bool) × (β -> Bool) =>
        @ite Real (Q x) (Classical.propDecidable (Q x))
          (bernWeight p x.1 * bernWeight p x.2) 0) ?_
    intro sigma
    by_cases hP :
      A (fun a : α => sigma (Sum.inl a)) /\
        B (fun b : β => sigma (Sum.inr b))
    · have hQ : Q (eFun sigma) := by
        simpa [P, Q, eFun] using hP
      have hQ' :
          Q (fun a : α => sigma (Sum.inl a), fun b : β => sigma (Sum.inr b)) := by
        simpa [Q] using hP
      simp [hP, hQ', eFun, bernWeight_sum]
    · have hQ : ¬ Q (eFun sigma) := by
        simpa [P, Q, eFun] using hP
      simp [hP, hQ]
  rw [hsplit]
  calc
    (Finset.univ.sum fun x : (α -> Bool) × (β -> Bool) =>
        @ite Real (Q x) (Classical.propDecidable (Q x))
          (bernWeight p x.1 * bernWeight p x.2) 0)
        = Finset.univ.sum fun sigma : α -> Bool =>
            Finset.univ.sum fun tau : β -> Bool =>
              if A sigma /\ B tau then bernWeight p sigma * bernWeight p tau else 0 := by
          rw [Fintype.sum_prod_type]
          simp [Q]
    _ = Finset.univ.sum fun sigma : α -> Bool =>
          Finset.univ.sum fun tau : β -> Bool =>
            (if A sigma then bernWeight p sigma else 0) *
              (if B tau then bernWeight p tau else 0) := by
          refine Finset.sum_congr rfl ?_
          intro sigma hsigma
          refine Finset.sum_congr rfl ?_
          intro tau htau
          by_cases hA : A sigma <;> by_cases hB : B tau <;> simp [hA, hB]
    _ = bernProb p A * bernProb p B := by
          dsimp [bernProb]
          rw [← Fintype.sum_mul_sum]

end Generic

/-- Bernoulli product weight of an assignment on a finite bond support. -/
noncomputable def weight {d : Nat} (p : Real) (F : Finset (Bond d))
    (sigma : F -> Bool) : Real :=
  bernWeight p sigma

/-- Finite Bernoulli product probability on an explicit finite bond support. -/
noncomputable def ProbOn {d : Nat} (p : Real) (F : Finset (Bond d))
    (A : (F -> Bool) -> Prop) : Real := by
  classical
  exact bernProb p A

theorem probOn_nonneg {d : Nat} {p : Real} {F : Finset (Bond d)}
    {A : (F -> Bool) -> Prop} (hp0 : 0 <= p) (hp1 : p <= 1) :
    0 <= ProbOn p F A := by
  exact bernProb_nonneg hp0 hp1

theorem probOn_le_one {d : Nat} {p : Real} {F : Finset (Bond d)}
    {A : (F -> Bool) -> Prop} (hp0 : 0 <= p) (hp1 : p <= 1) :
    ProbOn p F A <= 1 := by
  exact bernProb_le_one hp0 hp1

theorem probOn_univ {d : Nat} {p : Real} {F : Finset (Bond d)}
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    ProbOn p F (fun _ => True) = 1 := by
  exact bernProb_univ

theorem probOn_compl {d : Nat} {p : Real} {F : Finset (Bond d)}
    {A : (F -> Bool) -> Prop} (hp0 : 0 <= p) (hp1 : p <= 1) :
    ProbOn p F (fun sigma => ¬ A sigma) = 1 - ProbOn p F A := by
  exact bernProb_compl

theorem probOn_mono {d : Nat} {p : Real} {F : Finset (Bond d)}
    {A B : (F -> Bool) -> Prop} (hAB : forall sigma, A sigma -> B sigma)
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    ProbOn p F A <= ProbOn p F B := by
  exact bernProb_mono hAB hp0 hp1

theorem probOn_union_bound {d : Nat} {p : Real} {F : Finset (Bond d)}
    {A B : (F -> Bool) -> Prop} (hp0 : 0 <= p) (hp1 : p <= 1) :
    ProbOn p F (fun sigma => A sigma \/ B sigma) <=
      ProbOn p F A + ProbOn p F B := by
  exact bernProb_union_bound hp0 hp1

end Sharpness
