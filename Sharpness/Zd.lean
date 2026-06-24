import Mathlib

namespace Sharpness

open scoped BigOperators

/-- Vertices of nearest-neighbor bond percolation on `Z^d`. -/
abbrev Vertex (d : Nat) := Fin d -> Int

/-- The `l^1` norm on `Z^d`, valued ∈ `Nat`. -/
def l1 {d : Nat} (x : Vertex d) : Nat :=
  Finset.univ.sum fun i => Int.natAbs (x i)

/-- Nearest-neighbor adjacency on `Z^d`. -/
def Adj {d : Nat} (x y : Vertex d) : Prop :=
  l1 (x - y) = 1

/-- Translate a vertex by another vertex. -/
def translateVertex {d : Nat} (a x : Vertex d) : Vertex d :=
  x + a

/-- A single positive or negative coordinate step. -/
def coordStep {d : Nat} (i : Fin d) (positive : Bool) : Vertex d :=
  fun j => if j = i then (if positive then (1 : Int) else (-1 : Int)) else 0

/-- The finite set of nearest-neighbor candidates of a vertex. -/
def neighbors {d : Nat} (x : Vertex d) : Finset (Vertex d) :=
  ((Finset.univ : Finset (Fin d)).product ({true, false} : Finset Bool)).image
    (fun ib => x + coordStep ib.1 ib.2)

/-- Integer coordinates available ∈ the cube containing the `l^1` ball. -/
noncomputable def coordRange (n : Nat) : Finset Int :=
  Finset.Icc (-(n : Int)) (n : Int)

/-- The finite coordinate cube `[-n,n]^d`. -/
noncomputable def cube (d n : Nat) : Finset (Vertex d) := by
  classical
  exact (Finset.univ : Finset (Fin d -> {z : Int // z ∈ coordRange n})).map
    ⟨(fun f i => (f i).1), by
      intro f g h
      funext i
      apply Subtype.ext
      exact congrFun h i⟩

/-- The finite `l^1` box `Lambda_n = {x : Z^d | ||x||_1 <= n}`. -/
noncomputable def ball (d n : Nat) : Finset (Vertex d) :=
  (cube d n).filter fun x => l1 x <= n

@[simp] theorem translateVertex_apply {d : Nat} (a x : Vertex d) (i : Fin d) :
    translateVertex a x i = x i + a i := by
  rfl

-- M0 stub: characterize membership ∈ the finite `l^1` ball constructed from the bounded cube.
theorem mem_ball_iff {d n : Nat} {x : Vertex d} :
    x ∈ ball d n <-> l1 x <= n := by
  sorry

-- M0 stub: the origin belongs to every finite `l^1` ball.
theorem zero_mem_ball (d n : Nat) : (0 : Vertex d) ∈ ball d n := by
  sorry

-- M0 stub: nearest-neighbor adjacency is invariant under translations.
theorem adj_translate_iff {d : Nat} {a x y : Vertex d} :
    Adj (translateVertex a x) (translateVertex a y) <-> Adj x y := by
  sorry

-- M0 stub: the triangle estimate used to compare translated exit events.
theorem translate_ball_exit {d n L : Nat} {y z : Vertex d}
    (hy : y ∈ ball d L) (hz : z ∉ ball d n) (hLn : L <= n) :
    z - y ∉ ball d (n - L) := by
  sorry

end Sharpness
