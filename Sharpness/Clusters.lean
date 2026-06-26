/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.LocalEvent
import Sharpness.Paths

/-!
# Clusters

This file defines finite-volume open clusters and their basic locality and
connectivity properties.
-/

namespace Sharpness

/-- The open cluster of `u` inside a finite vertex set `S`. -/
noncomputable def clusterIn {d : Nat} (omega : Config d)
    (S : Finset (Vertex d)) (u : Vertex d) : Finset (Vertex d) := by
  classical
  exact S.filter fun x => ConnIn omega S u x

/-- Predicate that the finite cluster inside `S` is exactly `C`. -/
def ClusterEqPred {d : Nat} (S C : Finset (Vertex d)) (u : Vertex d)
    (omega : Config d) : Prop :=
  clusterIn omega S u = C

/-- Bonds inside `S` with at least one endpoint ∈ the candidate cluster `C`. -/
noncomputable def clusterIncidentBonds {d : Nat}
    (S C : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact ((S.product S).filter fun e : Vertex d × Vertex d =>
    e.1 ≠ e.2 /\ Adj e.1 e.2 /\ (e.1 ∈ C \/ e.2 ∈ C)).attach.image
      fun e => bondOfAdj ((Finset.mem_filter.mp e.property).2.2.1)

private theorem bondOfAdj_mem_clusterIncidentBonds {d : Nat}
    {S C : Finset (Vertex d)} {x y : Vertex d}
    (hxS : x ∈ S) (hyS : y ∈ S) (hxy : Adj x y)
    (hinc : x ∈ C ∨ y ∈ C) :
    bondOfAdj hxy ∈ clusterIncidentBonds S C := by
  classical
  rw [clusterIncidentBonds]
  refine Finset.mem_image.mpr ?_
  let e : {e : Vertex d × Vertex d //
      e ∈ (S.product S).filter fun e : Vertex d × Vertex d =>
        e.1 ≠ e.2 /\ Adj e.1 e.2 /\ (e.1 ∈ C \/ e.2 ∈ C)} :=
    ⟨(x, y), by
      refine Finset.mem_filter.mpr ?_
      exact ⟨Finset.mem_product.mpr ⟨hxS, hyS⟩, ne_of_adj hxy, hxy, hinc⟩⟩
  refine ⟨e, by simp [e], ?_⟩
  simp [e]

private theorem connIn_single {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {x : Vertex d} (hx : x ∈ S) : ConnIn omega S x x := by
  refine ⟨[x], ?_, ?_, ?_⟩
  · simp [PathFromTo, IsPath]
  · intro z hz
    have hzx : z = x := by simpa using hz
    simpa [hzx] using hx
  · simp [OpenPath]

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

private theorem mem_cluster_of_conn {d : Nat} {omega : Config d}
    {S C : Finset (Vertex d)} {u x : Vertex d}
    (hC : clusterIn omega S u = C) (hconn : ConnIn omega S u x) :
    x ∈ C := by
  classical
  rw [← hC]
  rcases hconn with ⟨gamma, hpath, hS, hopen⟩
  rcases hpath with ⟨_hhead, hlast, _hchain⟩
  have hxgamma : x ∈ gamma := List.mem_of_getLast? hlast
  exact Finset.mem_filter.mpr ⟨hS x hxgamma, ⟨gamma, ⟨_hhead, hlast, _hchain⟩, hS, hopen⟩⟩

private theorem conn_of_mem_cluster {d : Nat} {omega : Config d}
    {S C : Finset (Vertex d)} {u x : Vertex d}
    (hC : clusterIn omega S u = C) (hxC : x ∈ C) :
    ConnIn omega S u x := by
  classical
  rw [← hC] at hxC
  exact (Finset.mem_filter.mp hxC).2

private theorem target_mem_of_connIn {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {u x : Vertex d}
    (hconn : ConnIn omega S u x) : x ∈ S := by
  rcases hconn with ⟨gamma, hpath, hS, _hopen⟩
  exact hS x (List.mem_of_getLast? hpath.2.1)

private theorem mem_clusterIn_of_conn {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {u x : Vertex d}
    (hconn : ConnIn omega S u x) : x ∈ clusterIn omega S u := by
  classical
  exact Finset.mem_filter.mpr ⟨target_mem_of_connIn hconn, hconn⟩

private theorem openPath_transfer_from_cluster_eq {d : Nat}
    {omega omega' : Config d} {S C : Finset (Vertex d)} {u : Vertex d}
    (hsame : forall e, e ∈ clusterIncidentBonds S C -> omega e = omega' e)
    (hC : clusterIn omega S u = C)
    {gamma : List (Vertex d)}
    (hS : PathIn S gamma) (hchain : IsPath gamma)
    (hopen : OpenPath omega gamma)
    (hheadC : forall a, gamma.head? = some a -> a ∈ C) :
    OpenPath omega' gamma := by
  induction gamma with
  | nil =>
      simp [OpenPath] at hopen ⊢
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [OpenPath]
      | cons b tail =>
          have haS : a ∈ S := hS a (by simp)
          have hchain' := List.isChain_cons_cons.mp hchain
          have hopen' := List.isChain_cons_cons.mp hopen
          have haC : a ∈ C := hheadC a rfl
          have hbS : b ∈ S := hS b (by simp)
          have hbC : b ∈ C := by
            have hconn_a : ConnIn omega S u a := conn_of_mem_cluster hC haC
            have hconn_b : ConnIn omega S u b :=
              connIn_append_open_adj_same hbS hchain'.1 hopen'.1.choose_spec hconn_a
            exact mem_cluster_of_conn hC hconn_b
          have hbond : bondOfAdj hchain'.1 ∈ clusterIncidentBonds S C :=
            bondOfAdj_mem_clusterIncidentBonds haS hbS hchain'.1 (Or.inl haC)
          have hopenEdge' : omega' (bondOfAdj hchain'.1) = true := by
            simpa [hsame _ hbond] using hopen'.1.choose_spec
          rw [OpenPath, List.isChain_cons_cons]
          refine ⟨⟨hchain'.1, hopenEdge'⟩, ?_⟩
          have htail_S : PathIn S (b :: tail) := by
            intro z hz
            exact hS z (by simp [hz])
          have htail_headC : forall z, (b :: tail).head? = some z -> z ∈ C := by
            intro z hz
            have hzb : b = z := by simpa using hz
            simpa [← hzb] using hbC
          exact ih htail_S hchain'.2 hopen'.2 htail_headC

private theorem openPath_transfer_to_cluster_eq {d : Nat}
    {omega omega' : Config d} {S C : Finset (Vertex d)} {u : Vertex d}
    (hsame : forall e, e ∈ clusterIncidentBonds S C -> omega e = omega' e)
    (hC : clusterIn omega S u = C)
    {gamma : List (Vertex d)}
    (hS : PathIn S gamma) (hchain : IsPath gamma)
    (hopen' : OpenPath omega' gamma)
    (hheadC : forall a, gamma.head? = some a -> a ∈ C) :
    OpenPath omega gamma := by
  induction gamma with
  | nil =>
      simp [OpenPath] at hopen' ⊢
  | cons a rest ih =>
      cases rest with
      | nil =>
          simp [OpenPath]
      | cons b tail =>
          have haS : a ∈ S := hS a (by simp)
          have hchain' := List.isChain_cons_cons.mp hchain
          have hopenEdge' := (List.isChain_cons_cons.mp hopen').1
          have hopenTail' := (List.isChain_cons_cons.mp hopen').2
          have haC : a ∈ C := hheadC a rfl
          have hbS : b ∈ S := hS b (by simp)
          have hbond : bondOfAdj hchain'.1 ∈ clusterIncidentBonds S C :=
            bondOfAdj_mem_clusterIncidentBonds haS hbS hchain'.1 (Or.inl haC)
          have hopenEdge : omega (bondOfAdj hchain'.1) = true := by
            simpa [hsame _ hbond] using hopenEdge'.choose_spec
          have hbC : b ∈ C := by
            have hconn_a : ConnIn omega S u a := conn_of_mem_cluster hC haC
            have hconn_b : ConnIn omega S u b :=
              connIn_append_open_adj_same hbS hchain'.1 hopenEdge hconn_a
            exact mem_cluster_of_conn hC hconn_b
          rw [OpenPath, List.isChain_cons_cons]
          refine ⟨⟨hchain'.1, hopenEdge⟩, ?_⟩
          have htail_S : PathIn S (b :: tail) := by
            intro z hz
            exact hS z (by simp [hz])
          have htail_headC : forall z, (b :: tail).head? = some z -> z ∈ C := by
            intro z hz
            have hzb : b = z := by simpa using hz
            simpa [← hzb] using hbC
          exact ih htail_S hchain'.2 hopenTail' htail_headC

private theorem connIn_transfer_of_cluster_eq {d : Nat}
    {omega omega' : Config d} {S C : Finset (Vertex d)} {u x : Vertex d}
    (hsame : forall e, e ∈ clusterIncidentBonds S C -> omega e = omega' e)
    (hC : clusterIn omega S u = C)
    (hconn : ConnIn omega S u x) :
    ConnIn omega' S u x := by
  rcases hconn with ⟨gamma, hpath, hS, hopen⟩
  rcases hpath with ⟨hhead, hlast, hchain⟩
  have hheadC : forall a, gamma.head? = some a -> a ∈ C := by
    intro a ha
    have hau : a = u := by
      rw [ha] at hhead
      simpa using hhead
    subst a
    have huS : u ∈ S := hS u (List.mem_of_head? hhead)
    exact mem_cluster_of_conn hC (connIn_single huS)
  exact ⟨gamma, ⟨hhead, hlast, hchain⟩, hS,
    openPath_transfer_from_cluster_eq hsame hC hS hchain hopen hheadC⟩

private theorem connIn_other_subset_cluster {d : Nat}
    {omega omega' : Config d} {S C : Finset (Vertex d)} {u x : Vertex d}
    (hsame : forall e, e ∈ clusterIncidentBonds S C -> omega e = omega' e)
    (hC : clusterIn omega S u = C)
    (hconn' : ConnIn omega' S u x) :
    x ∈ C := by
  rcases hconn' with ⟨gamma, hpath, hS, hopen'⟩
  rcases hpath with ⟨hhead, hlast, hchain⟩
  have hheadC : forall a, gamma.head? = some a -> a ∈ C := by
    intro a ha
    have hau : a = u := by
      rw [ha] at hhead
      simpa using hhead
    subst a
    have huS : u ∈ S := hS u (List.mem_of_head? hhead)
    exact mem_cluster_of_conn hC (connIn_single huS)
  have hopen : OpenPath omega gamma :=
    openPath_transfer_to_cluster_eq hsame hC hS hchain hopen' hheadC
  have hconn : ConnIn omega S u x := ⟨gamma, ⟨hhead, hlast, hchain⟩, hS, hopen⟩
  exact mem_cluster_of_conn hC hconn

theorem cluster_eq_dependsOn_incident {d : Nat}
    (S C : Finset (Vertex d)) (u : Vertex d) :
    DependsOn (clusterIncidentBonds S C) (ClusterEqPred S C u) := by
  classical
  intro omega omega' hsame
  constructor
  · intro hC
    unfold ClusterEqPred at hC ⊢
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hconn' : ConnIn omega' S u x := (Finset.mem_filter.mp hx).2
      exact connIn_other_subset_cluster hsame hC hconn'
    · intro hx
      have hconn : ConnIn omega S u x := conn_of_mem_cluster hC hx
      have hconn' : ConnIn omega' S u x :=
        connIn_transfer_of_cluster_eq hsame hC hconn
      exact mem_clusterIn_of_conn hconn'
  · intro hC'
    unfold ClusterEqPred at hC' ⊢
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hconn : ConnIn omega S u x := (Finset.mem_filter.mp hx).2
      have hsame' : forall e, e ∈ clusterIncidentBonds S C -> omega' e = omega e := by
        intro e he
        exact (hsame e he).symm
      exact connIn_other_subset_cluster (omega := omega') (omega' := omega) hsame' hC' hconn
    · intro hx
      have hconn' : ConnIn omega' S u x := conn_of_mem_cluster hC' hx
      have hsame' : forall e, e ∈ clusterIncidentBonds S C -> omega' e = omega e := by
        intro e he
        exact (hsame e he).symm
      have hconn : ConnIn omega S u x :=
        connIn_transfer_of_cluster_eq (omega := omega') (omega' := omega) hsame' hC' hconn'
      exact mem_clusterIn_of_conn hconn

end Sharpness
