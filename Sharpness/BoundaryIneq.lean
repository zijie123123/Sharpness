/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.Clusters
import Sharpness.Events
import Sharpness.Independence

/-!
# Boundary Inequality

This file proves the finite-volume boundary expansion inequality used in the
sharpness argument.
-/

namespace Sharpness

open scoped BigOperators

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

private theorem prob_union_le {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (E F : LocalEvent d) :
    Prob p (E.union F) <= Prob p E + Prob p F := by
  classical
  let G : Finset (Bond d) := E.support ∪ F.support
  have hEsub : E.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inl he)
  have hFsub : F.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inr he)
  calc
    Prob p (E.union F)
        = ProbOn p G
            (fun sigma => E.pred (extendConfig G sigma) \/
              F.pred (extendConfig G sigma)) := rfl
    _ <= ProbOn p G (fun sigma => E.pred (extendConfig G sigma)) +
          ProbOn p G (fun sigma => F.pred (extendConfig G sigma)) :=
      probOn_union_bound hp0 hp1
    _ = Prob p E + Prob p F := by
      rw [← prob_support_mono E hEsub, ← prob_support_mono F hFsub]

private noncomputable def finsetUnionEvent {d : Nat} {α : Type*}
    (s : Finset α) (E : α -> LocalEvent d) : LocalEvent d :=
  { support := s.biUnion fun i => (E i).support
    pred := fun omega => exists i, i ∈ s /\ (E i).pred omega
    isLocal := by
      intro omega omega' hsame
      constructor
      · rintro ⟨i, hi, hEi⟩
        refine ⟨i, hi, ?_⟩
        exact ((E i).isLocal (by
          intro e he
          exact hsame e (Finset.mem_biUnion.mpr ⟨i, hi, he⟩))).mp hEi
      · rintro ⟨i, hi, hEi⟩
        refine ⟨i, hi, ?_⟩
        exact ((E i).isLocal (by
          intro e he
          exact hsame e (Finset.mem_biUnion.mpr ⟨i, hi, he⟩))).mpr hEi }

private theorem prob_finsetUnionEvent_le_sum {d : Nat} {α : Type*} [DecidableEq α]
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (s : Finset α) (E : α -> LocalEvent d) :
    Prob p (finsetUnionEvent s E) <= s.sum fun i => Prob p (E i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · change Prob p (finsetUnionEvent (∅ : Finset α) E) <= 0
    unfold Prob ProbOn bernProb finsetUnionEvent
    simp
  · intro a s has ih
    have hpred :
        forall omega,
          (finsetUnionEvent (insert a s) E).pred omega ->
            ((E a).union (finsetUnionEvent s E)).pred omega := by
      intro omega h
      rcases h with ⟨i, hi, hEi⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact Or.inl hEi
      · exact Or.inr ⟨i, hi, hEi⟩
    calc
      Prob p (finsetUnionEvent (insert a s) E)
          <= Prob p ((E a).union (finsetUnionEvent s E)) :=
        prob_le_of_pred_imp hp0 hp1 _ _ hpred
      _ <= Prob p (E a) + Prob p (finsetUnionEvent s E) :=
        prob_union_le hp0 hp1 (E a) (finsetUnionEvent s E)
      _ <= Prob p (E a) + s.sum (fun i => Prob p (E i)) :=
        by
          simpa [add_comm] using add_le_add_left ih (Prob p (E a))
      _ = (insert a s).sum (fun i => Prob p (E i)) := by
        rw [Finset.sum_insert has]

private noncomputable def clusterEvent {d : Nat}
    (S C : Finset (Vertex d)) (u : Vertex d) : LocalEvent d :=
  { support := clusterIncidentBonds S C
    pred := ClusterEqPred S C u
    isLocal := cluster_eq_dependsOn_incident S C u }

private noncomputable def edgeOpenEvent {d : Nat} (b : Bond d) : LocalEvent d :=
  { support := {b}
    pred := fun omega => omega b = true
    isLocal := by
      intro omega omega' hsame
      constructor <;> intro h
      · simpa [hsame b (by simp)] using h
      · simpa [hsame b (by simp)] using h }

private theorem prob_nonneg {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (E : LocalEvent d) : 0 <= Prob p E := by
  unfold Prob
  exact probOn_nonneg hp0 hp1

private theorem prob_edgeOpenEvent_eq {d : Nat} (p : Real) (b : Bond d) :
    Prob p (edgeOpenEvent b) = p := by
  classical
  let e : ({b} : Finset (Bond d)) ≃ Unit := Equiv.ofUnique _ _
  let unitEvent : (Unit -> Bool) -> Prop := fun sigma => sigma () = true
  have hpred :
      (fun sigma : ({b} : Finset (Bond d)) -> Bool =>
          (edgeOpenEvent b).pred (extendConfig {b} sigma)) =
        (fun sigma : ({b} : Finset (Bond d)) -> Bool =>
          unitEvent (fun u : Unit => sigma (e.symm u))) := by
    funext sigma
    have hcoord : (⟨b, by simp⟩ : ({b} : Finset (Bond d))) = e.symm () :=
      Subsingleton.elim _ _
    simp [edgeOpenEvent, extendConfig, unitEvent, hcoord]
  have hunit : bernProb p unitEvent = p := by
    let eFun : (Unit -> Bool) ≃ Bool := Equiv.funUnique Unit Bool
    let f : (Unit -> Bool) -> Real := fun sigma =>
      if sigma () = true then
        (Finset.univ.prod fun u : Unit => if sigma u then p else 1 - p)
      else 0
    let g : Bool -> Real := fun b => if b = true then (if b then p else 1 - p) else 0
    have hsum : (Finset.univ.sum f) = Finset.univ.sum g := by
      refine Fintype.sum_equiv eFun f g ?_
      intro sigma
      simp [f, g, eFun]
    calc
      bernProb p unitEvent = Finset.univ.sum f := by
        simp [bernProb, bernWeight, unitEvent, f]
      _ = Finset.univ.sum g := hsum
      _ = p := by
        rw [Fintype.sum_bool]
        simp
  calc
    Prob p (edgeOpenEvent b)
        = bernProb p
            (fun sigma : ({b} : Finset (Bond d)) -> Bool =>
              (edgeOpenEvent b).pred (extendConfig {b} sigma)) := rfl
    _ = bernProb p (fun sigma : ({b} : Finset (Bond d)) -> Bool =>
          unitEvent (fun u : Unit => sigma (e.symm u))) := by
      rw [hpred]
    _ = bernProb p unitEvent := by
      exact bernProb_reindex (α := ({b} : Finset (Bond d))) (β := Unit) p e unitEvent
    _ = p := hunit

private theorem mem_of_mem_internalBonds_carrier {d : Nat}
    {S : Finset (Vertex d)} {b : Bond d} {x : Vertex d}
    (hb : b ∈ internalBonds S) (hx : x ∈ b.carrier) : x ∈ S := by
  classical
  rw [internalBonds] at hb
  rcases Finset.mem_image.mp hb with ⟨ein, _hein, hbeq⟩
  let a : Vertex d := ein.1.1
  let c : Vertex d := ein.1.2
  have hfilter := Finset.mem_filter.mp ein.property
  have haS : a ∈ S := (Finset.mem_product.mp hfilter.1).1
  have hcS : c ∈ S := (Finset.mem_product.mp hfilter.1).2
  have hxpair : x ∈ ({a, c} : Finset (Vertex d)) := by
    change x ∈ (bondOfAdj ((Finset.mem_filter.mp ein.property).2.2)).carrier
    rw [hbeq]
    exact hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxpair
  rcases hxpair with hxa | hxc
  · simpa [a, hxa] using haS
  · simpa [c, hxc] using hcS

private theorem clusterIncidentBonds_subset_internalBonds {d : Nat}
    {S C : Finset (Vertex d)} :
    clusterIncidentBonds S C <= internalBonds S := by
  classical
  intro b hb
  rw [clusterIncidentBonds] at hb
  rcases Finset.mem_image.mp hb with ⟨ein, _hein, hbeq⟩
  let a : Vertex d := ein.1.1
  let c : Vertex d := ein.1.2
  have hfilter := Finset.mem_filter.mp ein.property
  have haS : a ∈ S := (Finset.mem_product.mp hfilter.1).1
  have hcS : c ∈ S := (Finset.mem_product.mp hfilter.1).2
  have hac : Adj a c := hfilter.2.2.1
  have hmem : bondOfAdj hac ∈ internalBonds S :=
    bondOfAdj_mem_internalBonds haS hcS hac
  simpa [a, c, hbeq] using hmem

private theorem exists_carrier_mem_of_clusterIncidentBonds {d : Nat}
    {S C : Finset (Vertex d)} {b : Bond d}
    (hb : b ∈ clusterIncidentBonds S C) :
    exists x, x ∈ b.carrier /\ x ∈ C := by
  classical
  rw [clusterIncidentBonds] at hb
  rcases Finset.mem_image.mp hb with ⟨ein, _hein, hbeq⟩
  let a : Vertex d := ein.1.1
  let c : Vertex d := ein.1.2
  have hfilter := Finset.mem_filter.mp ein.property
  have hinc : a ∈ C \/ c ∈ C := hfilter.2.2.2
  rcases hinc with haC | hcC
  · refine ⟨a, ?_, haC⟩
    rw [← hbeq]
    change a ∈ ({a, c} : Finset (Vertex d))
    simp
  · refine ⟨c, ?_, hcC⟩
    rw [← hbeq]
    change c ∈ ({a, c} : Finset (Vertex d))
    simp

private theorem disjoint_clusterIncident_boundaryBond {d : Nat}
    {S C : Finset (Vertex d)} {e : OrientedEdge d}
    (he : e ∈ orientedBoundary S) :
    Disjoint (clusterIncidentBonds S C)
      ({bondOfAdj (orientedBoundary_adj he)} : Finset (Bond d)) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbCluster hbSingle
  have hbEq : b = bondOfAdj (orientedBoundary_adj he) := by
    simpa using hbSingle
  subst b
  have hbInt : bondOfAdj (orientedBoundary_adj he) ∈ internalBonds S :=
    clusterIncidentBonds_subset_internalBonds hbCluster
  have hyCarrier :
      e.2 ∈ (bondOfAdj (orientedBoundary_adj he)).carrier := by
    change e.2 ∈ ({e.1, e.2} : Finset (Vertex d))
    simp
  exact (mem_orientedBoundary_iff.mp he).2.1
    (mem_of_mem_internalBonds_carrier hbInt hyCarrier)

private theorem disjoint_clusterIncident_internal_sdiff {d : Nat}
    (T S C : Finset (Vertex d)) :
    Disjoint (clusterIncidentBonds S C) (internalBonds (T \ C)) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbCluster hbAvoid
  rcases exists_carrier_mem_of_clusterIncidentBonds hbCluster with ⟨x, hxCarrier, hxC⟩
  have hxAvoid : x ∈ T \ C := mem_of_mem_internalBonds_carrier hbAvoid hxCarrier
  exact (Finset.mem_sdiff.mp hxAvoid).2 hxC

private theorem disjoint_boundaryBond_internal_sdiff {d : Nat}
    {T S C : Finset (Vertex d)} {e : OrientedEdge d}
    (he : e ∈ orientedBoundary S) (hxC : e.1 ∈ C) :
    Disjoint ({bondOfAdj (orientedBoundary_adj he)} : Finset (Bond d))
      (internalBonds (T \ C)) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbSingle hbAvoid
  have hbEq : b = bondOfAdj (orientedBoundary_adj he) := by
    simpa using hbSingle
  subst b
  have hxCarrier :
      e.1 ∈ (bondOfAdj (orientedBoundary_adj he)).carrier := by
    change e.1 ∈ ({e.1, e.2} : Finset (Vertex d))
    simp
  have hxAvoid : e.1 ∈ T \ C :=
    mem_of_mem_internalBonds_carrier hbAvoid hxCarrier
  exact (Finset.mem_sdiff.mp hxAvoid).2 hxC

private theorem target_mem_of_connIn {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {u x : Vertex d}
    (hconn : ConnIn omega S u x) : x ∈ S := by
  rcases hconn with ⟨gamma, hpath, hS, _hopen⟩
  exact hS x (List.mem_of_getLast? hpath.2.1)

private theorem clusterIn_subset {d : Nat} (omega : Config d)
    (S : Finset (Vertex d)) (u : Vertex d) :
    clusterIn omega S u <= S := by
  classical
  intro x hx
  exact (Finset.mem_filter.mp hx).1

private theorem connIn_subset {d : Nat} {omega : Config d}
    {S T : Finset (Vertex d)} {x y : Vertex d}
    (hST : S <= T) (hconn : ConnIn omega S x y) :
    ConnIn omega T x y := by
  rcases hconn with ⟨gamma, hpath, hS, hopen⟩
  exact ⟨gamma, hpath, fun z hz => hST (hS z hz), hopen⟩

private theorem connToSetIn_subset {d : Nat} {omega : Config d}
    {S T B : Finset (Vertex d)} {u : Vertex d}
    (hST : S <= T) (hconn : ConnToSetIn omega S u B) :
    ConnToSetIn omega T u B := by
  rcases hconn with ⟨b, hb, hub⟩
  exact ⟨b, hb, connIn_subset hST hub⟩

private theorem connToSetIn_sdiff_subset {d : Nat} {omega : Config d}
    {T C B : Finset (Vertex d)} {u : Vertex d}
    (hconn : ConnToSetIn omega (T \ C) u B) :
    ConnToSetIn omega T u B :=
  connToSetIn_subset (by intro x hx; exact (Finset.mem_sdiff.mp hx).1) hconn

private theorem connIn_single {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {x : Vertex d} (hx : x ∈ S) : ConnIn omega S x x := by
  refine ⟨[x], ?_, ?_, ?_⟩
  · simp [PathFromTo, IsPath]
  · intro z hz
    have hzx : z = x := by simpa using hz
    simpa [hzx] using hx
  · simp [OpenPath]

private theorem cluster_subset {d : Nat} {omega : Config d}
    {S C : Finset (Vertex d)} {u x : Vertex d}
    (hC : ClusterEqPred S C u omega) (hxC : x ∈ C) : x ∈ S := by
  classical
  unfold ClusterEqPred at hC
  rw [← hC] at hxC
  exact (Finset.mem_filter.mp hxC).1

private theorem conn_of_mem_cluster {d : Nat} {omega : Config d}
    {S C : Finset (Vertex d)} {u x : Vertex d}
    (hC : ClusterEqPred S C u omega) (hxC : x ∈ C) :
    ConnIn omega S u x := by
  classical
  unfold ClusterEqPred at hC
  rw [← hC] at hxC
  exact (Finset.mem_filter.mp hxC).2

private theorem mem_cluster_of_conn {d : Nat} {omega : Config d}
    {S C : Finset (Vertex d)} {u x : Vertex d}
    (hC : ClusterEqPred S C u omega) (hconn : ConnIn omega S u x) :
    x ∈ C := by
  classical
  unfold ClusterEqPred at hC
  rw [← hC]
  exact Finset.mem_filter.mpr ⟨target_mem_of_connIn hconn, hconn⟩

private theorem sum_clusterEvent_le_connIn {d : Nat}
    (S : Finset (Vertex d)) (u x : Vertex d) {p : Real} :
    ((S.powerset.filter fun C => x ∈ C).sum
        (fun C => Prob p (clusterEvent S C u))) <=
      Prob p (connInEvent S u x) := by
  classical
  let G : Finset (Bond d) := internalBonds S
  have hrewrite :
      ((S.powerset.filter fun C => x ∈ C).sum
          (fun C => Prob p (clusterEvent S C u))) =
        (Finset.univ.sum fun sigma : G -> Bool =>
          (S.powerset.filter fun C => x ∈ C).sum fun C =>
            if ClusterEqPred S C u (extendConfig G sigma) then
              bernWeight p sigma
            else 0) := by
    calc
      ((S.powerset.filter fun C => x ∈ C).sum
          (fun C => Prob p (clusterEvent S C u)))
          =
        (S.powerset.filter fun C => x ∈ C).sum
          (fun C => ProbOn p G
            (fun sigma : G -> Bool =>
              ClusterEqPred S C u (extendConfig G sigma))) := by
          refine Finset.sum_congr rfl ?_
          intro C hC
          exact prob_support_mono (clusterEvent S C u)
            (clusterIncidentBonds_subset_internalBonds (S := S) (C := C))
      _ =
        (S.powerset.filter fun C => x ∈ C).sum
          (fun C => Finset.univ.sum fun sigma : G -> Bool =>
            if ClusterEqPred S C u (extendConfig G sigma) then
              bernWeight p sigma
            else 0) := by
          rfl
      _ =
        (Finset.univ.sum fun sigma : G -> Bool =>
          (S.powerset.filter fun C => x ∈ C).sum fun C =>
            if ClusterEqPred S C u (extendConfig G sigma) then
              bernWeight p sigma
            else 0) := by
          rw [Finset.sum_comm]
  rw [hrewrite]
  change
    (Finset.univ.sum fun sigma : G -> Bool =>
      (S.powerset.filter fun C => x ∈ C).sum fun C =>
        if ClusterEqPred S C u (extendConfig G sigma) then bernWeight p sigma else 0) <=
      Finset.univ.sum fun sigma : G -> Bool =>
        if ConnIn (extendConfig G sigma) S u x then bernWeight p sigma else 0
  refine Finset.sum_le_sum ?_
  intro sigma _hsigma
  let omega : Config d := extendConfig G sigma
  by_cases hconn : ConnIn omega S u x
  · have hxCluster : x ∈ clusterIn omega S u := by
      exact Finset.mem_filter.mpr ⟨target_mem_of_connIn hconn, hconn⟩
    have hclusterMem :
        clusterIn omega S u ∈ S.powerset.filter fun C => x ∈ C := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (clusterIn_subset omega S u), hxCluster⟩
    have hsum :
        ((S.powerset.filter fun C => x ∈ C).sum fun C =>
          if ClusterEqPred S C u omega then bernWeight p sigma else 0) =
            bernWeight p sigma := by
      have hsum' :
          ((S.powerset.filter fun C => x ∈ C).sum fun C =>
            if ClusterEqPred S C u omega then bernWeight p sigma else 0) =
              (if ClusterEqPred S (clusterIn omega S u) u omega then
                bernWeight p sigma
              else 0) := by
        refine Finset.sum_eq_single
          (s := S.powerset.filter fun C => x ∈ C)
          (f := fun C : Finset (Vertex d) =>
            if ClusterEqPred S C u omega then bernWeight p sigma else (0 : Real))
          (clusterIn omega S u) ?_ ?_
        · intro C hC hne
          have hne' : ¬ ClusterEqPred S C u omega := by
            intro hEq
            exact hne (by simpa [ClusterEqPred] using hEq.symm)
          simp [hne']
        · intro hnot
          exact False.elim (hnot hclusterMem)
      simpa [ClusterEqPred] using hsum'
    simp [omega, hconn, hsum]
  · have hsum :
        ((S.powerset.filter fun C => x ∈ C).sum fun C =>
          if ClusterEqPred S C u omega then bernWeight p sigma else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro C hC
      have hxC : x ∈ C := (Finset.mem_filter.mp hC).2
      have hnotEq : ¬ ClusterEqPred S C u omega := by
        intro hEq
        exact hconn (conn_of_mem_cluster hEq hxC)
      simp [hnotEq]
    simp [omega, hconn, hsum]

private theorem connIn_append_open_adj_same {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {x y z : Vertex d}
    (hzS : z ∈ S) (hyz : Adj y z)
    (hopen : omega (bondOfAdj hyz) = true)
    (hconn : ConnIn omega S x y) :
    ConnIn omega S x z := by
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
    · exact hS w hw
    · have hwz : w = z := by simpa using hw
      simpa [hwz] using hzS
  · rw [OpenPath, List.isChain_append]
    refine ⟨hopenPath, by simp, ?_⟩
    intro a ha b hb
    have hay : y = a := by simpa [hlast] using ha
    have hzb : z = b := by simpa using hb
    subst a
    subst b
    exact ⟨hyz, hopen⟩

private theorem cluster_closed_under_open_adj {d : Nat} {omega : Config d}
    {S C : Finset (Vertex d)} {u x y : Vertex d}
    (hC : ClusterEqPred S C u omega) (hxC : x ∈ C) (hyS : y ∈ S)
    (hxy : Adj x y) (hopen : omega (bondOfAdj hxy) = true) : y ∈ C := by
  have hconnx : ConnIn omega S u x := conn_of_mem_cluster hC hxC
  exact mem_cluster_of_conn hC (connIn_append_open_adj_same hyS hxy hopen hconnx)

private theorem path_last_exit_cluster {d : Nat} {omega : Config d}
    {C T : Finset (Vertex d)} :
    forall {gamma : List (Vertex d)} {x b : Vertex d},
      PathFromTo gamma x b -> PathIn T gamma -> OpenPath omega gamma ->
      (exists z, z ∈ gamma /\ z ∈ C) -> b ∉ C ->
      exists a y : Vertex d,
        exists hxy : Adj a y,
          a ∈ C /\ y ∉ C /\ omega (bondOfAdj hxy) = true /\
            ConnIn omega (T \ C) y b := by
  intro gamma
  induction gamma with
  | nil =>
      intro x b hpath _hT _hopen hex _hbC
      rcases hpath with ⟨hhead, _hlast, _hchain⟩
      simp at hhead
  | cons a rest ih =>
      intro x b hpath hT hopen hex hbC
      by_cases hrest : exists z, z ∈ rest /\ z ∈ C
      · cases rest with
        | nil =>
            rcases hrest with ⟨z, hz, _⟩
            simp at hz
        | cons y tail =>
            rcases hpath with ⟨_hhead, hlast, hchain⟩
            have hchainTail : IsPath (y :: tail) :=
              (List.isChain_cons_cons.mp hchain).2
            have hopenTail : OpenPath omega (y :: tail) :=
              (List.isChain_cons_cons.mp hopen).2
            have hTTail : PathIn T (y :: tail) := by
              intro z hz
              exact hT z (by simp [hz])
            have hpathTail : PathFromTo (y :: tail) y b :=
              ⟨rfl, by simpa using hlast, hchainTail⟩
            exact ih hpathTail hTTail hopenTail hrest hbC
      · have haC : a ∈ C := by
          rcases hex with ⟨z, hz, hzC⟩
          simp only [List.mem_cons] at hz
          rcases hz with hza | hzrest
          · simpa [hza] using hzC
          · exact False.elim (hrest ⟨z, hzrest, hzC⟩)
        cases rest with
        | nil =>
            rcases hpath with ⟨_hhead, hlast, _hchain⟩
            have hab : a = b := by simpa using hlast
            exact False.elim (hbC (by simpa [hab] using haC))
        | cons y tail =>
            have hyC : y ∉ C := by
              intro hyC
              exact hrest ⟨y, by simp, hyC⟩
            rcases hpath with ⟨_hhead, hlast, hchain⟩
            have hchain' := List.isChain_cons_cons.mp hchain
            have hopen' := List.isChain_cons_cons.mp hopen
            refine ⟨a, y, hchain'.1, haC, hyC, ?_, ?_⟩
            · exact hopen'.1.choose_spec
            · refine ⟨y :: tail, ?_, ?_, ?_⟩
              · exact ⟨rfl, by simpa using hlast, hchain'.2⟩
              · intro z hz
                refine Finset.mem_sdiff.mpr ?_
                constructor
                · exact hT z (by simp [hz])
                · intro hzC
                  exact hrest ⟨z, by simpa using hz, hzC⟩
              · exact hopen'.2

private theorem connToSet_cluster_boundary_witness {d : Nat}
    {T S B C : Finset (Vertex d)} {u : Vertex d} {omega : Config d}
    (hu : u ∈ S) (hBS : Disjoint B S)
    (hconn : ConnToSetIn omega T u B) (hC : ClusterEqPred S C u omega) :
    exists e, exists he : e ∈ orientedBoundary S,
      e.1 ∈ C /\ omega (bondOfAdj (orientedBoundary_adj he)) = true /\
        ConnToSetIn omega (T \ C) e.2 B := by
  classical
  rcases hconn with ⟨b, hb, hconnub⟩
  have huC : u ∈ C := by
    exact mem_cluster_of_conn hC (connIn_single hu)
  have hbS : b ∉ S := by
    rw [Finset.disjoint_left] at hBS
    exact hBS hb
  have hbC : b ∉ C := by
    intro hbC
    exact hbS (cluster_subset hC hbC)
  rcases hconnub with ⟨gamma, hpath, hT, hopen⟩
  have hexC : exists z, z ∈ gamma /\ z ∈ C :=
    ⟨u, List.mem_of_head? hpath.1, huC⟩
  rcases path_last_exit_cluster hpath hT hopen hexC hbC with
    ⟨x, y, hxy, hxC, hyC, hopenxy, htail⟩
  have hyS : y ∉ S := by
    intro hyS
    exact hyC (cluster_closed_under_open_adj hC hxC hyS hxy hopenxy)
  let e : OrientedEdge d := (x, y)
  have he : e ∈ orientedBoundary S := by
    rw [mem_orientedBoundary_iff]
    exact ⟨cluster_subset hC hxC, hyS, hxy⟩
  refine ⟨e, he, by simpa [e] using hxC, ?_, ?_⟩
  · have hbEq : bondOfAdj (orientedBoundary_adj he) = bondOfAdj hxy := by
      apply bondOfAdj_same
    simpa [e, hbEq] using hopenxy
  · exact ⟨b, hb, by simpa [e] using htail⟩

private theorem boundary_triple_prob_le {d : Nat}
    (T S B C : Finset (Vertex d)) (u : Vertex d)
    {e : OrientedEdge d} (he : e ∈ orientedBoundary S) (hxC : e.1 ∈ C)
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p (((clusterEvent S C u).inter
        (edgeOpenEvent (bondOfAdj (orientedBoundary_adj he)))).inter
        (connToSetInEvent (T \ C) e.2 B)) <=
      Prob p (clusterEvent S C u) * p *
        Prob p (connToSetInEvent T e.2 B) := by
  classical
  have hprob :=
    prob_inter_three_eq_mul_of_pairwise_disjoint
      (clusterEvent S C u)
      (edgeOpenEvent (bondOfAdj (orientedBoundary_adj he)))
      (connToSetInEvent (T \ C) e.2 B)
      (disjoint_clusterIncident_boundaryBond (S := S) (C := C) he)
      (disjoint_clusterIncident_internal_sdiff T S C)
      (disjoint_boundaryBond_internal_sdiff (T := T) (S := S) (C := C) he hxC)
      hp0 hp1
  have havoid :
      Prob p (connToSetInEvent (T \ C) e.2 B) <=
        Prob p (connToSetInEvent T e.2 B) := by
    exact prob_le_of_pred_imp hp0 hp1 _ _
      (fun omega h => connToSetIn_sdiff_subset h)
  have hcoef_nonneg :
      0 <= Prob p (clusterEvent S C u) * p := by
    exact mul_nonneg (prob_nonneg hp0 hp1 _) hp0
  calc
    Prob p (((clusterEvent S C u).inter
        (edgeOpenEvent (bondOfAdj (orientedBoundary_adj he)))).inter
        (connToSetInEvent (T \ C) e.2 B))
        = Prob p (clusterEvent S C u) *
          Prob p (edgeOpenEvent (bondOfAdj (orientedBoundary_adj he))) *
          Prob p (connToSetInEvent (T \ C) e.2 B) := hprob
    _ = Prob p (clusterEvent S C u) * p *
          Prob p (connToSetInEvent (T \ C) e.2 B) := by
        rw [prob_edgeOpenEvent_eq]
    _ <= Prob p (clusterEvent S C u) * p *
          Prob p (connToSetInEvent T e.2 B) := by
        exact mul_le_mul_of_nonneg_left havoid hcoef_nonneg

private theorem boundary_cluster_value_bound {d : Nat}
    (T S B C : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ S) (hBS : Disjoint B S)
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p ((clusterEvent S C u).inter (connToSetInEvent T u B)) <=
      (orientedBoundary S).sum
        (fun e =>
          if _ : e.1 ∈ C then
            Prob p (clusterEvent S C u) * p *
              Prob p (connToSetInEvent T e.2 B)
          else 0) := by
  classical
  let edgesC : Finset (OrientedEdge d) :=
    (orientedBoundary S).filter fun e => e.1 ∈ C
  let triple : {e // e ∈ edgesC} -> LocalEvent d := fun e =>
    let he : e.1 ∈ orientedBoundary S := (Finset.mem_filter.mp e.2).1
    (((clusterEvent S C u).inter
      (edgeOpenEvent (bondOfAdj (orientedBoundary_adj he)))).inter
      (connToSetInEvent (T \ C) e.1.2 B))
  have himp :
      forall omega,
        (((clusterEvent S C u).inter (connToSetInEvent T u B)).pred omega) ->
          (finsetUnionEvent edgesC.attach triple).pred omega := by
    intro omega h
    rcases h with ⟨hCluster, hconn⟩
    rcases connToSet_cluster_boundary_witness hu hBS hconn hCluster with
      ⟨e, he, hxC, hopen, htail⟩
    have hec : e ∈ edgesC := Finset.mem_filter.mpr ⟨he, hxC⟩
    refine ⟨⟨e, hec⟩, by simp, ?_⟩
    dsimp [triple]
    exact ⟨⟨hCluster, hopen⟩, htail⟩
  calc
    Prob p ((clusterEvent S C u).inter (connToSetInEvent T u B))
        <= Prob p (finsetUnionEvent edgesC.attach triple) :=
      prob_le_of_pred_imp hp0 hp1 _ _ himp
    _ <= edgesC.attach.sum fun e => Prob p (triple e) :=
      prob_finsetUnionEvent_le_sum hp0 hp1 edgesC.attach triple
    _ <= edgesC.attach.sum fun e =>
          Prob p (clusterEvent S C u) * p *
            Prob p (connToSetInEvent T e.1.2 B) := by
      refine Finset.sum_le_sum ?_
      intro e heAttach
      have he : e.1 ∈ orientedBoundary S := (Finset.mem_filter.mp e.2).1
      have hxC : e.1.1 ∈ C := (Finset.mem_filter.mp e.2).2
      simpa [triple] using
        boundary_triple_prob_le T S B C u he hxC hp0 hp1
    _ = edgesC.sum fun e =>
          Prob p (clusterEvent S C u) * p *
            Prob p (connToSetInEvent T e.2 B) := by
      exact Finset.sum_attach edgesC
        (fun e =>
          Prob p (clusterEvent S C u) * p *
            Prob p (connToSetInEvent T e.2 B))
    _ = (orientedBoundary S).sum
        (fun e =>
          if _ : e.1 ∈ C then
            Prob p (clusterEvent S C u) * p *
              Prob p (connToSetInEvent T e.2 B)
          else 0) := by
      simp [edgesC, Finset.sum_filter]

/--
Cluster last-exit expansion for the finite-volume boundary inequality.
-/
private theorem boundary_inequality_cluster_expansion {d : Nat}
    (T S B : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ S) (_hST : S <= T) (_hBT : B <= T) (hBS : Disjoint B S)
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p (connToSetInEvent T u B) <=
      (orientedBoundary S).sum
        (fun e => p * Prob p (connInEvent S u e.1) *
          Prob p (connToSetInEvent T e.2 B)) := by
  classical
  let clusterConn : Finset (Vertex d) -> LocalEvent d := fun C =>
    (clusterEvent S C u).inter (connToSetInEvent T u B)
  have hdecomp :
      Prob p (connToSetInEvent T u B) <=
        S.powerset.sum fun C => Prob p (clusterConn C) := by
    have himp :
        forall omega,
          (connToSetInEvent T u B).pred omega ->
            (finsetUnionEvent S.powerset clusterConn).pred omega := by
      intro omega hconn
      refine ⟨clusterIn omega S u,
        Finset.mem_powerset.mpr (clusterIn_subset omega S u), ?_⟩
      exact ⟨rfl, hconn⟩
    calc
      Prob p (connToSetInEvent T u B)
          <= Prob p (finsetUnionEvent S.powerset clusterConn) :=
        prob_le_of_pred_imp hp0 hp1 _ _ himp
      _ <= S.powerset.sum fun C => Prob p (clusterConn C) :=
        prob_finsetUnionEvent_le_sum hp0 hp1 S.powerset clusterConn
  have hclusters :
      S.powerset.sum (fun C => Prob p (clusterConn C)) <=
        S.powerset.sum fun C =>
            (orientedBoundary S).sum
              (fun e =>
                if _ : e.1 ∈ C then
                  Prob p (clusterEvent S C u) * p *
                    Prob p (connToSetInEvent T e.2 B)
                else 0) := by
    refine Finset.sum_le_sum ?_
    intro C hC
    exact boundary_cluster_value_bound T S B C u hu hBS hp0 hp1
  have hswap :
      S.powerset.sum
          (fun C =>
            (orientedBoundary S).sum
              (fun e =>
                if _ : e.1 ∈ C then
                  Prob p (clusterEvent S C u) * p *
                    Prob p (connToSetInEvent T e.2 B)
                else 0)) =
        (orientedBoundary S).sum
          (fun e =>
            S.powerset.sum
              (fun C =>
                if hxC : e.1 ∈ C then
                  Prob p (clusterEvent S C u) * p *
                    Prob p (connToSetInEvent T e.2 B)
                else 0)) := by
    rw [Finset.sum_comm]
  have hinner :
      (orientedBoundary S).sum
          (fun e =>
            S.powerset.sum
              (fun C =>
                if _ : e.1 ∈ C then
                  Prob p (clusterEvent S C u) * p *
                    Prob p (connToSetInEvent T e.2 B)
                else 0)) <=
        (orientedBoundary S).sum
          (fun e =>
            p * Prob p (connInEvent S u e.1) *
              Prob p (connToSetInEvent T e.2 B)) := by
    refine Finset.sum_le_sum ?_
    intro e he
    let q : Real := Prob p (connToSetInEvent T e.2 B)
    have hfilter :
        S.powerset.sum
              (fun C =>
                if _ : e.1 ∈ C then
                  Prob p (clusterEvent S C u) * p *
                    Prob p (connToSetInEvent T e.2 B)
                else 0) =
          (S.powerset.filter fun C => e.1 ∈ C).sum
            (fun C =>
                Prob p (clusterEvent S C u) * p *
                  Prob p (connToSetInEvent T e.2 B)) := by
      exact (Finset.sum_filter
        (s := S.powerset)
        (p := fun C : Finset (Vertex d) => e.1 ∈ C)
        (f := fun C =>
          Prob p (clusterEvent S C u) * p *
            Prob p (connToSetInEvent T e.2 B))).symm
    have hfactor :
        (S.powerset.filter fun C => e.1 ∈ C).sum
            (fun C =>
              Prob p (clusterEvent S C u) * p *
                Prob p (connToSetInEvent T e.2 B)) =
          ((S.powerset.filter fun C => e.1 ∈ C).sum
            (fun C => Prob p (clusterEvent S C u))) *
              (p * Prob p (connToSetInEvent T e.2 B)) := by
      calc
        (S.powerset.filter fun C => e.1 ∈ C).sum
            (fun C =>
              Prob p (clusterEvent S C u) * p *
                Prob p (connToSetInEvent T e.2 B))
            =
          (S.powerset.filter fun C => e.1 ∈ C).sum
            (fun C =>
              Prob p (clusterEvent S C u) *
                (p * Prob p (connToSetInEvent T e.2 B))) := by
            refine Finset.sum_congr rfl ?_
            intro C hC
            ring
        _ =
          ((S.powerset.filter fun C => e.1 ∈ C).sum
            (fun C => Prob p (clusterEvent S C u))) *
              (p * Prob p (connToSetInEvent T e.2 B)) := by
            rw [Finset.sum_mul]
    have hpart := sum_clusterEvent_le_connIn S u e.1 (p := p)
    have hconst_nonneg :
        0 <= p * Prob p (connToSetInEvent T e.2 B) := by
      exact mul_nonneg hp0 (prob_nonneg hp0 hp1 _)
    calc
      S.powerset.sum
            (fun C =>
              if hxC : e.1 ∈ C then
                Prob p (clusterEvent S C u) * p *
                  Prob p (connToSetInEvent T e.2 B)
              else 0)
          = ((S.powerset.filter fun C => e.1 ∈ C).sum
            (fun C => Prob p (clusterEvent S C u))) *
              (p * Prob p (connToSetInEvent T e.2 B)) := by
            rw [hfilter, hfactor]
      _ <= Prob p (connInEvent S u e.1) *
              (p * Prob p (connToSetInEvent T e.2 B)) :=
            mul_le_mul_of_nonneg_right hpart hconst_nonneg
      _ = p * Prob p (connInEvent S u e.1) *
              Prob p (connToSetInEvent T e.2 B) := by
            ring
  exact hdecomp.trans (hclusters.trans (by
    rw [hswap]
    exact hinner))

/-- Lemma 4, finite-volume boundary expansion inequality. -/
theorem boundary_inequality {d : Nat}
    (T S B : Finset (Vertex d)) (u : Vertex d)
    (hu : u ∈ S) (hST : S <= T) (hBT : B <= T) (hBS : Disjoint B S)
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p (connToSetInEvent T u B) <=
      (orientedBoundary S).sum
        (fun e => p * Prob p (connInEvent S u e.1) *
          Prob p (connToSetInEvent T e.2 B)) := by
  exact boundary_inequality_cluster_expansion T S B u hu hST hBT hBS hp0 hp1

end Sharpness
