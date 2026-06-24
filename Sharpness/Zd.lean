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

/-- The finite set of nearest-neighbor candidates of a vertex. -/
noncomputable def neighbors {d : Nat} (x : Vertex d) : Finset (Vertex d) := by
  classical
  exact (ball d (l1 x + 1)).filter fun y => Adj x y

@[simp] theorem translateVertex_apply {d : Nat} (a x : Vertex d) (i : Fin d) :
    translateVertex a x i = x i + a i := by
  rfl

theorem l1_zero {d : Nat} : l1 (0 : Vertex d) = 0 := by
  simp [l1]

theorem l1_neg {d : Nat} (x : Vertex d) : l1 (-x) = l1 x := by
  simp [l1]

theorem l1_add_le {d : Nat} (x y : Vertex d) : l1 (x + y) <= l1 x + l1 y := by
  classical
  unfold l1
  calc
    (Finset.univ.sum fun i : Fin d => Int.natAbs ((x + y) i))
        <= Finset.univ.sum fun i : Fin d => Int.natAbs (x i) + Int.natAbs (y i) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          simpa [Pi.add_apply] using Int.natAbs_add_le (x i) (y i)
    _ = (Finset.univ.sum fun i : Fin d => Int.natAbs (x i)) +
        (Finset.univ.sum fun i : Fin d => Int.natAbs (y i)) := by
          rw [Finset.sum_add_distrib]

theorem l1_sub_comm {d : Nat} (x y : Vertex d) : l1 (x - y) = l1 (y - x) := by
  have h : y - x = -(x - y) := by
    funext i
    change y i - x i = -(x i - y i)
    ring
  rw [h, l1_neg]

theorem adj_symm {d : Nat} {x y : Vertex d} (hxy : Adj x y) : Adj y x := by
  simpa [Adj, l1_sub_comm] using hxy

theorem ne_of_adj {d : Nat} {x y : Vertex d} (hxy : Adj x y) : x ≠ y := by
  intro h
  subst y
  simp [Adj, l1] at hxy

theorem mem_cube_iff {d n : Nat} {x : Vertex d} :
    x ∈ cube d n <-> forall i : Fin d, x i ∈ coordRange n := by
  classical
  constructor
  · intro hx i
    rw [cube] at hx
    rcases Finset.mem_map.mp hx with ⟨f, _hf, hfx⟩
    have hi : x i = (f i).1 := (congrFun hfx i).symm
    rw [hi]
    exact (f i).2
  · intro hx
    rw [cube]
    refine Finset.mem_map.mpr ?_
    refine ⟨(fun i => ⟨x i, hx i⟩), Finset.mem_univ _, ?_⟩
    rfl

theorem coord_natAbs_le_l1 {d : Nat} (x : Vertex d) (i : Fin d) :
    Int.natAbs (x i) <= l1 x := by
  classical
  unfold l1
  exact Finset.single_le_sum
    (s := Finset.univ) (f := fun j : Fin d => Int.natAbs (x j))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

theorem coord_mem_coordRange_of_l1_le {d n : Nat} {x : Vertex d}
    (hx : l1 x <= n) (i : Fin d) : x i ∈ coordRange n := by
  classical
  have hnat : Int.natAbs (x i) <= n := (coord_natAbs_le_l1 x i).trans hx
  have hint : |x i| <= (n : Int) := by
    have hcast : ((Int.natAbs (x i) : Nat) : Int) <= (n : Int) := by
      exact_mod_cast hnat
    simpa [Int.natCast_natAbs] using hcast
  exact (Finset.mem_Icc).mpr (by
    simpa [coordRange, Int.abs_eq_natAbs] using (abs_le.mp hint))

/-- Characterize membership in the finite `l^1` ball constructed from the bounded cube. -/
theorem mem_ball_iff {d n : Nat} {x : Vertex d} :
    x ∈ ball d n <-> l1 x <= n := by
  classical
  constructor
  · intro hx
    exact (Finset.mem_filter.mp hx).2
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨mem_cube_iff.mpr (coord_mem_coordRange_of_l1_le hx), hx⟩

/-- The origin belongs to every finite `l^1` ball. -/
theorem zero_mem_ball (d n : Nat) : (0 : Vertex d) ∈ ball d n := by
  rw [mem_ball_iff]
  simp [l1]

/-- Nearest-neighbor adjacency is invariant under translations. -/
theorem adj_translate_iff {d : Nat} {a x y : Vertex d} :
    Adj (translateVertex a x) (translateVertex a y) <-> Adj x y := by
  have hsub : translateVertex a x - translateVertex a y = x - y := by
    funext i
    change x i + a i - (y i + a i) = x i - y i
    ring
  simp [Adj, hsub]

/-- Nearest-neighbor candidates are exactly adjacent vertices. -/
theorem mem_neighbors_iff {d : Nat} {x y : Vertex d} :
    y ∈ neighbors x <-> Adj x y := by
  classical
  constructor
  · intro hy
    rw [neighbors] at hy
    exact (Finset.mem_filter.mp hy).2
  · intro hxy
    have hyx : Adj y x := adj_symm hxy
    have hdecomp : x + (y - x) = y := by
      funext i
      change x i + (y i - x i) = y i
      ring
    have hle : l1 y <= l1 x + 1 := by
      calc
        l1 y = l1 (x + (y - x)) := by rw [hdecomp]
        _ <= l1 x + l1 (y - x) := l1_add_le x (y - x)
        _ = l1 x + 1 := by rw [hyx]
    rw [neighbors]
    exact Finset.mem_filter.mpr ⟨(mem_ball_iff).mpr hle, hxy⟩

/-- The triangle estimate used to compare translated exit events. -/
theorem translate_ball_exit {d n L : Nat} {y z : Vertex d}
    (hy : y ∈ ball d L) (hz : z ∉ ball d n) (hLn : L <= n) :
    z - y ∉ ball d (n - L) := by
  intro hzy
  have hy_l1 : l1 y <= L := (mem_ball_iff.mp hy)
  have hzy_l1 : l1 (z - y) <= n - L := (mem_ball_iff.mp hzy)
  have hdecomp : (z - y) + y = z := by
    funext i
    change (z i - y i) + y i = z i
    ring
  have hz_l1 : l1 z <= n := by
    calc
      l1 z = l1 ((z - y) + y) := by rw [hdecomp]
      _ <= l1 (z - y) + l1 y := l1_add_le (z - y) y
      _ <= (n - L) + L := Nat.add_le_add hzy_l1 hy_l1
      _ = n := Nat.sub_add_cancel hLn
  exact hz ((mem_ball_iff).mpr hz_l1)

end Sharpness
