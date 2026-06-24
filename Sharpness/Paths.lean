import Sharpness.FiniteGeometry

namespace Sharpness

/-- A list of vertices with adjacent consecutive entries. -/
def IsPath {d : Nat} (gamma : List (Vertex d)) : Prop :=
  List.Chain' (Adj (d := d)) gamma

/-- A path from `x` to `y`, represented as a finite list. -/
def PathFromTo {d : Nat} (gamma : List (Vertex d)) (x y : Vertex d) : Prop :=
  gamma.head? = some x /\ gamma.getLast? = some y /\ IsPath gamma

/-- Every vertex of the path lies ∈ the finite set `S`. -/
def PathIn {d : Nat} (S : Finset (Vertex d)) (gamma : List (Vertex d)) : Prop :=
  forall z, z ∈ gamma -> z ∈ S

/-- Every consecutive bond of the path is open ∈ the configuration. -/
def OpenPath {d : Nat} (omega : Config d) (gamma : List (Vertex d)) : Prop :=
  List.Chain' (fun x y => exists hxy : Adj x y, omega (bondOfAdj hxy) = true) gamma

/-- Open connectivity inside a finite vertex set. -/
def ConnIn {d : Nat} (omega : Config d) (S : Finset (Vertex d))
    (x y : Vertex d) : Prop :=
  exists gamma,
    PathFromTo gamma x y /\ PathIn S gamma /\ OpenPath omega gamma

-- M0 stub: reversing a path preserves open connectivity.
theorem connIn_symm {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {x y : Vertex d} (hxy : ConnIn omega S x y) :
    ConnIn omega S y x := by
  sorry

-- M0 stub: translated paths preserve nearest-neighbor connectivity.
theorem connIn_translate {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {a x y : Vertex d} (hxy : ConnIn omega S x y) :
    ConnIn omega (S.image (translateVertex a))
      (translateVertex a x) (translateVertex a y) := by
  sorry

end Sharpness
