import Sharpness.Zd

namespace Sharpness

/-- An unoriented nearest-neighbor bond, represented by its two-point carrier. -/
structure Bond (d : Nat) where
  carrier : Finset (Vertex d)
  card_two : carrier.card = 2
  adj_pair : forall x, x ∈ carrier -> forall y, y ∈ carrier -> x ≠ y -> Adj x y
deriving DecidableEq

/-- Global percolation configurations, indexed by unoriented bonds. -/
abbrev Config (d : Nat) := Bond d -> Bool

-- M0 stub: adjacent vertices form a two-point finite carrier.
theorem bondOfAdj_card_two {d : Nat} {x y : Vertex d} (hxy : Adj x y) :
    ({x, y} : Finset (Vertex d)).card = 2 := by
  sorry

-- M0 stub: every distinct pair ∈ the carrier `{x,y}` is adjacent when `x` and `y` are adjacent.
theorem bondOfAdj_adj_pair {d : Nat} {x y : Vertex d} (hxy : Adj x y) :
    forall u, u ∈ ({x, y} : Finset (Vertex d)) ->
      forall v, v ∈ ({x, y} : Finset (Vertex d)) -> u ≠ v -> Adj u v := by
  sorry

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

-- M0 stub: the finite neighbor construction exactly enumerates oriented nearest-neighbor boundary edges.
theorem mem_orientedBoundary_iff {d : Nat} {S : Finset (Vertex d)} {e : OrientedEdge d} :
    e ∈ orientedBoundary S <-> e.1 ∈ S /\ e.2 ∉ S /\ Adj e.1 e.2 := by
  sorry

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

/-- Bonds with both endpoints ∈ a finite vertex set. -/
noncomputable def internalBonds {d : Nat} (S : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact ((S.product S).filter fun e : Vertex d × Vertex d => e.1 ≠ e.2 /\ Adj e.1 e.2).attach.image
    fun e => bondOfAdj ((Finset.mem_filter.mp e.property).2.2)

/-- Unoriented bonds crossing the boundary of a finite vertex set. -/
noncomputable def exitBonds {d : Nat} (S : Finset (Vertex d)) : Finset (Bond d) := by
  classical
  exact (orientedBoundary S).attach.image fun e => bondOfAdj (orientedBoundary_adj e.property)

-- M0 stub: internal and exit bonds of the same finite set are disjoint.
theorem disjoint_internal_exit {d : Nat} (S : Finset (Vertex d)) :
    Disjoint (internalBonds S) (exitBonds S) := by
  sorry

end Sharpness
