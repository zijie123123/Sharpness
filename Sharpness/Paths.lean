/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.FiniteGeometry

/-!
# Paths

This file defines finite paths, path containment, open paths, and connectivity.
-/

namespace Sharpness

/-- A list of vertices with adjacent consecutive entries. -/
def IsPath {d : Nat} (gamma : List (Vertex d)) : Prop :=
  List.IsChain (Adj (d := d)) gamma

/-- A path from `x` to `y`, represented as a finite list. -/
def PathFromTo {d : Nat} (gamma : List (Vertex d)) (x y : Vertex d) : Prop :=
  gamma.head? = some x /\ gamma.getLast? = some y /\ IsPath gamma

/-- Every vertex of the path lies ∈ the finite set `S`. -/
def PathIn {d : Nat} (S : Finset (Vertex d)) (gamma : List (Vertex d)) : Prop :=
  forall z, z ∈ gamma -> z ∈ S

/-- Every consecutive bond of the path is open ∈ the configuration. -/
def OpenPath {d : Nat} (omega : Config d) (gamma : List (Vertex d)) : Prop :=
  List.IsChain (fun x y => exists hxy : Adj x y, omega (bondOfAdj hxy) = true) gamma

/-- Open connectivity inside a finite vertex set. -/
def ConnIn {d : Nat} (omega : Config d) (S : Finset (Vertex d))
    (x y : Vertex d) : Prop :=
  exists gamma,
    PathFromTo gamma x y /\ PathIn S gamma /\ OpenPath omega gamma

/-- A path that starts in `S` and ends outside `S` has a crossing step. -/
theorem first_exit_step_of_path {d : Nat} {S : Finset (Vertex d)}
    {gamma : List (Vertex d)} {x y : Vertex d}
    (hgamma : PathFromTo gamma x y) (hx : x ∈ S) (hy : y ∉ S) :
    exists u v : Vertex d,
      u ∈ gamma /\ v ∈ gamma /\ Adj u v /\ u ∈ S /\ v ∉ S := by
  classical
  revert x y
  induction gamma with
  | nil =>
      intro x y hgamma hx hy
      rcases hgamma with ⟨hhead, _hlast, _hpath⟩
      simp at hhead
  | cons a rest ih =>
      intro x y hgamma hx hy
      rcases hgamma with ⟨hhead, hlast, hpath⟩
      cases rest with
      | nil =>
          have hax : a = x := by simpa using hhead
          have hay : a = y := by simpa using hlast
          exact False.elim (hy (by simpa [← hax, ← hay] using hx))
      | cons b tail =>
          have hax : a = x := by simpa using hhead
          have haS : a ∈ S := by simpa [hax] using hx
          have hchain := List.isChain_cons_cons.mp hpath
          by_cases hbS : b ∈ S
          · have htail_last : (b :: tail).getLast? = some y := by simpa using hlast
            have htail_path : IsPath (b :: tail) := hchain.2
            rcases ih ⟨rfl, htail_last, htail_path⟩ hbS hy with
              ⟨u, v, hu, hv, huv, huS, hvS⟩
            exact ⟨u, v, by simp [hu], by simp [hv], huv, huS, hvS⟩
          · exact ⟨a, b, by simp, by simp, hchain.1, haS, hbS⟩

/-- A path crossing from `S` to its complement has a boundary step; this alias is used for
last-exit arguments before the later proof refines the chosen crossing. -/
theorem last_exit_step_of_path {d : Nat} {S : Finset (Vertex d)}
    {gamma : List (Vertex d)} {x y : Vertex d}
    (hgamma : PathFromTo gamma x y) (hx : x ∈ S) (hy : y ∉ S) :
    exists u v : Vertex d,
      u ∈ gamma /\ v ∈ gamma /\ Adj u v /\ u ∈ S /\ v ∉ S :=
  first_exit_step_of_path hgamma hx hy

theorem isPath_reverse {d : Nat} {gamma : List (Vertex d)}
    (hgamma : IsPath gamma) : IsPath gamma.reverse := by
  rw [IsPath, List.isChain_reverse]
  exact hgamma.imp fun {_ _} hxy => adj_symm hxy

theorem pathFromTo_reverse {d : Nat} {gamma : List (Vertex d)}
    {x y : Vertex d} (hgamma : PathFromTo gamma x y) :
    PathFromTo gamma.reverse y x := by
  rcases hgamma with ⟨hhead, hlast, hpath⟩
  exact ⟨by simpa [List.head?_reverse] using hlast,
    by simpa [List.getLast?_reverse] using hhead,
    isPath_reverse hpath⟩

theorem pathIn_reverse {d : Nat} {S : Finset (Vertex d)} {gamma : List (Vertex d)}
    (hgamma : PathIn S gamma) : PathIn S gamma.reverse := by
  intro z hz
  exact hgamma z (List.mem_reverse.mp hz)

theorem openPath_reverse {d : Nat} {omega : Config d} {gamma : List (Vertex d)}
    (hgamma : OpenPath omega gamma) : OpenPath omega gamma.reverse := by
  rw [OpenPath, List.isChain_reverse]
  exact hgamma.imp fun {_ _} h => by
    rcases h with ⟨hxy, hopen⟩
    exact ⟨adj_symm hxy, by simpa [bondOfAdj_symm hxy] using hopen⟩

/-- Reversing a path preserves open connectivity. -/
theorem connIn_symm {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {x y : Vertex d} (hxy : ConnIn omega S x y) :
    ConnIn omega S y x := by
  rcases hxy with ⟨gamma, hpath, hS, hopen⟩
  exact ⟨gamma.reverse, pathFromTo_reverse hpath, pathIn_reverse hS, openPath_reverse hopen⟩

theorem isPath_translate {d : Nat} {a : Vertex d} {gamma : List (Vertex d)}
    (hgamma : IsPath gamma) : IsPath (gamma.map (translateVertex a)) := by
  rw [IsPath, List.isChain_map]
  exact hgamma.imp fun {_ _} hxy => (adj_translate_iff (a := a)).mpr hxy

theorem pathFromTo_translate {d : Nat} {a x y : Vertex d}
    {gamma : List (Vertex d)} (hgamma : PathFromTo gamma x y) :
    PathFromTo (gamma.map (translateVertex a))
      (translateVertex a x) (translateVertex a y) := by
  rcases hgamma with ⟨hhead, hlast, hpath⟩
  exact ⟨by simp [hhead], by simp [hlast], isPath_translate hpath⟩

theorem pathIn_translate {d : Nat} {a : Vertex d} {S : Finset (Vertex d)}
    {gamma : List (Vertex d)} (hgamma : PathIn S gamma) :
    PathIn (S.image (translateVertex a)) (gamma.map (translateVertex a)) := by
  classical
  intro z hz
  rcases List.mem_map.mp hz with ⟨w, hw, rfl⟩
  exact Finset.mem_image.mpr ⟨w, hgamma w hw, rfl⟩

theorem openPath_translate_of_edge_open {d : Nat} {omega : Config d} {a : Vertex d}
    {gamma : List (Vertex d)}
    (hopen_translate : forall {u v : Vertex d} (huv : Adj u v),
      omega (bondOfAdj huv) = true ->
      omega (bondOfAdj ((adj_translate_iff (a := a) (x := u) (y := v)).mpr huv)) = true)
    (hgamma : OpenPath omega gamma) :
    OpenPath omega (gamma.map (translateVertex a)) := by
  rw [OpenPath, List.isChain_map]
  exact hgamma.imp fun {_ _} h => by
    rcases h with ⟨huv, hopen⟩
    exact ⟨(adj_translate_iff (a := a)).mpr huv, hopen_translate huv hopen⟩

/-- Translated paths preserve open connectivity when translated open edges remain open. -/
theorem connIn_translate {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {a x y : Vertex d}
    (hopen_translate : forall {u v : Vertex d} (huv : Adj u v),
      omega (bondOfAdj huv) = true ->
      omega (bondOfAdj ((adj_translate_iff (a := a) (x := u) (y := v)).mpr huv)) = true)
    (hxy : ConnIn omega S x y) :
    ConnIn omega (S.image (translateVertex a))
      (translateVertex a x) (translateVertex a y) := by
  rcases hxy with ⟨gamma, hpath, hS, hopen⟩
  exact ⟨gamma.map (translateVertex a), pathFromTo_translate hpath,
    pathIn_translate hS, openPath_translate_of_edge_open hopen_translate hopen⟩

end Sharpness
