import Sharpness.Bonds

namespace Sharpness

/-- Internal bonds of the box `Lambda_n`. -/
noncomputable def boxInternalBonds (d n : Nat) : Finset (Bond d) :=
  internalBonds (ball d n)

/-- Exit bonds crossing from `Lambda_n` to its complement. -/
noncomputable def boxExitBonds (d n : Nat) : Finset (Bond d) :=
  exitBonds (ball d n)

-- M0 stub: boundary endpoints of a finite set contained ∈ `Lambda_(L-1)` lie ∈ `Lambda_L`.
theorem boundary_endpoint_mem_ball {d L : Nat} {S : Finset (Vertex d)} {e : OrientedEdge d}
    (hS : forall x, x ∈ S -> x ∈ ball d (L - 1))
    (he : e ∈ orientedBoundary S) :
    e.2 ∈ ball d L := by
  sorry

end Sharpness
