/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.Zd

/-!
# Bonds

This file defines unoriented nearest-neighbor bonds, configurations, and finite
sets of internal and boundary bonds.
-/

namespace Sharpness

/-- An unoriented nearest-neighbor bond, represented by its two-point carrier. -/
structure Bond (d : Nat) where
  carrier : Finset (Vertex d)
  card_two : carrier.card = 2
  adj_pair : forall x, x ∈ carrier -> forall y, y ∈ carrier -> x ≠ y -> Adj x y
deriving DecidableEq

/-- Global percolation configurations, indexed by unoriented bonds. -/
abbrev Config (d : Nat) := Bond d -> Bool

/-- Adjacent vertices form a two-point finite carrier. -/
theorem bondOfAdj_card_two {d : Nat} {x y : Vertex d} (hxy : Adj x y) :
    ({x, y} : Finset (Vertex d)).card = 2 := by
  simp [ne_of_adj hxy]

/-- Every distinct pair in the carrier `{x,y}` is adjacent when `x` and `y` are adjacent. -/
theorem bondOfAdj_adj_pair {d : Nat} {x y : Vertex d} (hxy : Adj x y) :
    forall u, u ∈ ({x, y} : Finset (Vertex d)) ->
      forall v, v ∈ ({x, y} : Finset (Vertex d)) -> u ≠ v -> Adj u v := by
  intro u hu v hv huv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact False.elim (huv rfl)
  · exact hxy
  · exact adj_symm hxy
  · exact False.elim (huv rfl)

/-- The unoriented bond associated to an adjacent ordered pair. -/
def bondOfAdj {d : Nat} {x y : Vertex d} (hxy : Adj x y) : Bond d :=
  { carrier := {x, y}
    card_two := bondOfAdj_card_two hxy
    adj_pair := bondOfAdj_adj_pair hxy }

/-- An oriented edge is a pair of vertices. Boundary sums use this orientation. -/
abbrev OrientedEdge (d : Nat) := Vertex d × Vertex d

/-- Oriented boundary edges from a finite vertex set to its complement. -/
noncomputable def orientedBoundary {d : Nat} (S : Finset (Vertex d)) :
    Finset (OrientedEdge d) := by
  classical
  exact Finset.biUnion S fun x =>
    ((neighbors x).filter fun y => y ∉ S).map
      ⟨(fun y => (x, y)), by
        intro y z h
        exact congrArg Prod.snd h⟩

/-- The finite neighbor construction exactly enumerates oriented nearest-neighbor boundary edges. -/
theorem mem_orientedBoundary_iff {d : Nat} {S : Finset (Vertex d)} {e : OrientedEdge d} :
    e ∈ orientedBoundary S <-> e.1 ∈ S /\ e.2 ∉ S /\ Adj e.1 e.2 := by
  classical
  constructor
  · intro he
    rw [orientedBoundary] at he
    rcases Finset.mem_biUnion.mp he with ⟨x, hxS, hx⟩
    rcases Finset.mem_map.mp hx with ⟨y, hy, hxy⟩
    have hfst : e.1 = x := congrArg Prod.fst hxy.symm
    have hsnd : e.2 = y := congrArg Prod.snd hxy.symm
    have hy' := Finset.mem_filter.mp hy
    subst hfst
    subst hsnd
    exact ⟨hxS, hy'.2, (mem_neighbors_iff.mp hy'.1)⟩
  · intro h
    rcases h with ⟨hxS, hyS, hxy⟩
    rw [orientedBoundary]
    refine Finset.mem_biUnion.mpr ?_
    refine ⟨e.1, hxS, ?_⟩
    refine Finset.mem_map.mpr ?_
    refine ⟨e.2, Finset.mem_filter.mpr ⟨mem_neighbors_iff.mpr hxy, hyS⟩, rfl⟩

/-- Adjacency proof extracted from membership ∈ the oriented boundary. -/
theorem orientedBoundary_adj {d : Nat} {S : Finset (Vertex d)} {e : OrientedEdge d}
    (he : e ∈ orientedBoundary S) : Adj e.1 e.2 :=
  (mem_orientedBoundary_iff.mp he).2.2

/-- A boundary edge with its orientation and membership proofs. -/
structure OEdgeBoundary {d : Nat} (S : Finset (Vertex d)) where
  x : Vertex d
  y : Vertex d
  hx : x ∈ S
  hy : y ∉ S
  hxy : Adj x y

/-- Forget the orientation of a boundary edge. -/
def OEdgeBoundary.bond {d : Nat} {S : Finset (Vertex d)} (e : OEdgeBoundary S) : Bond d :=
  bondOfAdj e.hxy

theorem bondOfAdj_same {d : Nat} {x y : Vertex d} {h h' : Adj x y} :
    bondOfAdj h = bondOfAdj h' := by
  simp [bondOfAdj]

theorem bondOfAdj_symm {d : Nat} {x y : Vertex d} (hxy : Adj x y) :
    bondOfAdj (adj_symm hxy) = bondOfAdj hxy := by
  simp [bondOfAdj, Finset.pair_comm]

/-- Bonds with both endpoints ∈ a finite vertex set. -/
noncomputable def internalBonds {d : Nat} (S : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact ((S.product S).filter fun e : Vertex d × Vertex d => e.1 ≠ e.2 /\ Adj e.1 e.2).attach.image
    fun e => bondOfAdj ((Finset.mem_filter.mp e.property).2.2)

theorem bondOfAdj_mem_internalBonds {d : Nat} {S : Finset (Vertex d)}
    {x y : Vertex d} (hx : x ∈ S) (hy : y ∈ S) (hxy : Adj x y) :
    bondOfAdj hxy ∈ internalBonds S := by
  classical
  rw [internalBonds]
  refine Finset.mem_image.mpr ?_
  let p : {e : Vertex d × Vertex d //
      e ∈ (S.product S).filter fun e : Vertex d × Vertex d =>
        e.1 ≠ e.2 /\ Adj e.1 e.2} :=
    ⟨(x, y), by
      refine Finset.mem_filter.mpr ?_
      exact ⟨Finset.mem_product.mpr ⟨hx, hy⟩, ne_of_adj hxy, hxy⟩⟩
  refine ⟨p, by simp [p], ?_⟩
  simp [p]

/-- Unoriented bonds crossing the boundary of a finite vertex set. -/
noncomputable def exitBonds {d : Nat} (S : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact (orientedBoundary S).attach.image fun e => bondOfAdj (orientedBoundary_adj e.property)

theorem bondOfAdj_mem_exitBonds {d : Nat} {S : Finset (Vertex d)} {e : OrientedEdge d}
    (he : e ∈ orientedBoundary S) :
    bondOfAdj (orientedBoundary_adj he) ∈ exitBonds S := by
  classical
  rw [exitBonds]
  refine Finset.mem_image.mpr ?_
  refine ⟨⟨e, he⟩, by simp, rfl⟩

/-- Internal and exit bonds of the same finite set are disjoint. -/
theorem disjoint_internal_exit {d : Nat} (S : Finset (Vertex d)) :
    Disjoint (internalBonds S) (exitBonds S) := by
  classical
  rw [Finset.disjoint_left]
  intro b hbInt hbExit
  rw [internalBonds] at hbInt
  rw [exitBonds] at hbExit
  rcases Finset.mem_image.mp hbInt with ⟨ein, _hein, hbin⟩
  rcases Finset.mem_image.mp hbExit with ⟨eout, _heout, hbout⟩
  let a : Vertex d := ein.1.1
  let c : Vertex d := ein.1.2
  let x : Vertex d := eout.1.1
  let y : Vertex d := eout.1.2
  have hin_filter := Finset.mem_filter.mp ein.property
  have haS : a ∈ S := (Finset.mem_product.mp hin_filter.1).1
  have hcS : c ∈ S := (Finset.mem_product.mp hin_filter.1).2
  have hout_boundary : eout.1 ∈ orientedBoundary S := eout.property
  have hyS : y ∉ S := (mem_orientedBoundary_iff.mp hout_boundary).2.1
  have hcar :
      (bondOfAdj ((Finset.mem_filter.mp ein.property).2.2)).carrier =
        (bondOfAdj (orientedBoundary_adj eout.property)).carrier := by
    exact congrArg Bond.carrier (hbin.trans hbout.symm)
  have hy_mem_pair : y ∈ ({a, c} : Finset (Vertex d)) := by
    change y ∈ (bondOfAdj ((Finset.mem_filter.mp ein.property).2.2)).carrier
    rw [hcar]
    change y ∈ ({x, y} : Finset (Vertex d))
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy_mem_pair
  rcases hy_mem_pair with hya | hyc
  · exact hyS (by simpa [hya] using haS)
  · exact hyS (by simpa [hyc] using hcS)

end Sharpness
