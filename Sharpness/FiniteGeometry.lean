/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.Bonds

/-!
# Finite Geometry

This file records finite box bond sets and boundary geometry estimates.
-/

namespace Sharpness

/-- Internal bonds of the box `Lambda_n`. -/
noncomputable def boxInternalBonds (d n : Nat) : Finset (Bond d) :=
  internalBonds (ball d n)

/-- Exit bonds crossing from `Lambda_n` to its complement. -/
noncomputable def boxExitBonds (d n : Nat) : Finset (Bond d) :=
  exitBonds (ball d n)

/-- Boundary endpoints of a finite set contained in `Lambda_(L-1)` lie in `Lambda_L`.

The positivity hypothesis is needed because `Nat` subtraction saturates: at `L = 0`,
`L - 1 = 0`, while a boundary endpoint of `{0}` need not be in `Lambda_0`.
-/
theorem boundary_endpoint_mem_ball {d L : Nat} {S : Finset (Vertex d)} {e : OrientedEdge d}
    (hL : 0 < L)
    (hS : forall x, x ∈ S -> x ∈ ball d (L - 1))
    (he : e ∈ orientedBoundary S) :
    e.2 ∈ ball d L := by
  have hxS : e.1 ∈ S := (mem_orientedBoundary_iff.mp he).1
  have hxy : Adj e.1 e.2 := (mem_orientedBoundary_iff.mp he).2.2
  have hx_l1 : l1 e.1 <= L - 1 := mem_ball_iff.mp (hS e.1 hxS)
  have hle : l1 e.2 <= L := by
    calc
      l1 e.2 <= l1 e.1 + 1 := by
        have hdecomp : e.1 + (e.2 - e.1) = e.2 := by
          funext i
          change e.1 i + (e.2 i - e.1 i) = e.2 i
          ring
        calc
          l1 e.2 = l1 (e.1 + (e.2 - e.1)) := by rw [hdecomp]
          _ <= l1 e.1 + l1 (e.2 - e.1) := l1_add_le e.1 (e.2 - e.1)
          _ = l1 e.1 + 1 := by rw [adj_symm hxy]
      _ <= (L - 1) + 1 := Nat.add_le_add_right hx_l1 1
      _ = L := Nat.sub_add_cancel hL
  exact mem_ball_iff.mpr hle

end Sharpness
