/-
Copyright (c) 2026 Zijie Zhuang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zijie Zhuang
-/

import Sharpness.LocalEvent
import Sharpness.Monotonicity
import Sharpness.Paths

/-!
# Events

This file defines finite-volume exit and connectivity events and the finite
exit probabilities used to define `theta`.
-/

namespace Sharpness

open Filter
open scoped Topology

/-- Predicate for the finite-volume exit event from `Lam`. -/
def ExitPred {d : Nat} (Lam : Finset (Vertex d)) (omega : Config d) : Prop :=
  exists e, exists he : e ∈ orientedBoundary Lam,
    ConnIn omega Lam (0 : Vertex d) e.1 /\
    omega (bondOfAdj (orientedBoundary_adj he)) = true

theorem openPath_dependsOn_of_pathIn {d : Nat} {S : Finset (Vertex d)}
    {gamma : List (Vertex d)} {omega omega' : Config d}
    (hsame : forall e, e ∈ internalBonds S -> omega e = omega' e)
    (hS : PathIn S gamma) :
    OpenPath omega gamma <-> OpenPath omega' gamma := by
  change
    List.IsChain (fun x y => exists hxy : Adj x y, omega (bondOfAdj hxy) = true) gamma <->
      List.IsChain (fun x y => exists hxy : Adj x y, omega' (bondOfAdj hxy) = true) gamma
  apply List.IsChain.iff_of_mem_imp
  intro x y hx hy
  constructor
  · rintro ⟨hxy, hopen⟩
    have hb : bondOfAdj hxy ∈ internalBonds S :=
      bondOfAdj_mem_internalBonds (hS x hx) (hS y hy) hxy
    exact ⟨hxy, by simpa [hsame _ hb] using hopen⟩
  · rintro ⟨hxy, hopen⟩
    have hb : bondOfAdj hxy ∈ internalBonds S :=
      bondOfAdj_mem_internalBonds (hS x hx) (hS y hy) hxy
    exact ⟨hxy, by simpa [hsame _ hb] using hopen⟩

/-- Finite-set connectivity depends only on bonds internal to the finite set. -/
theorem connIn_dependsOn {d : Nat} (S : Finset (Vertex d)) (x y : Vertex d) :
    DependsOn (internalBonds S) (fun omega => ConnIn omega S x y) := by
  intro omega omega' hsame
  constructor
  · rintro ⟨gamma, hpath, hS, hopen⟩
    exact ⟨gamma, hpath, hS, (openPath_dependsOn_of_pathIn hsame hS).mp hopen⟩
  · rintro ⟨gamma, hpath, hS, hopen⟩
    exact ⟨gamma, hpath, hS, (openPath_dependsOn_of_pathIn hsame hS).mpr hopen⟩

/-- Local event for `x` connected to `y` inside `S`. -/
noncomputable def connInEvent {d : Nat} (S : Finset (Vertex d)) (x y : Vertex d) :
    LocalEvent d :=
  { support := internalBonds S
    pred := fun omega => ConnIn omega S x y
    isLocal := connIn_dependsOn S x y }

theorem openPath_mono {d : Nat} {omega omega' : Config d} {gamma : List (Vertex d)}
    (hle : ConfigLE omega omega') (hgamma : OpenPath omega gamma) :
    OpenPath omega' gamma := by
  change
    List.IsChain (fun x y => exists hxy : Adj x y, omega' (bondOfAdj hxy) = true) gamma
  exact hgamma.imp fun {_ _} h => by
    rcases h with ⟨hxy, hopen⟩
    exact ⟨hxy, hle (bondOfAdj hxy) hopen⟩

theorem connIn_mono {d : Nat} {omega omega' : Config d} {S : Finset (Vertex d)}
    {x y : Vertex d} (hle : ConfigLE omega omega') (hconn : ConnIn omega S x y) :
    ConnIn omega' S x y := by
  rcases hconn with ⟨gamma, hpath, hS, hopen⟩
  exact ⟨gamma, hpath, hS, openPath_mono hle hopen⟩

theorem connInEvent_increasing {d : Nat} (S : Finset (Vertex d)) (x y : Vertex d) :
    Increasing (connInEvent S x y) := by
  intro omega omega' hle hconn
  exact connIn_mono hle hconn

/-- The finite exit event is local on internal and boundary bonds of `Lam`. -/
theorem exitEvent_dependsOn {d : Nat} (Lam : Finset (Vertex d))
    (_h0 : (0 : Vertex d) ∈ Lam) :
    DependsOn (internalBonds Lam ∪ exitBonds Lam) (ExitPred Lam) := by
  intro omega omega' hsame
  constructor
  · rintro ⟨e, he, hconn, hopen⟩
    have hconn' : ConnIn omega' Lam (0 : Vertex d) e.1 :=
      (connIn_dependsOn Lam (0 : Vertex d) e.1 (by
        intro b hb
        exact hsame b (Finset.mem_union.mpr (Or.inl hb)))).mp hconn
    have hb : bondOfAdj (orientedBoundary_adj he) ∈ exitBonds Lam :=
      bondOfAdj_mem_exitBonds he
    exact ⟨e, he, hconn', by
      simpa [hsame _ (Finset.mem_union.mpr (Or.inr hb))] using hopen⟩
  · rintro ⟨e, he, hconn, hopen⟩
    have hconn' : ConnIn omega Lam (0 : Vertex d) e.1 :=
      (connIn_dependsOn Lam (0 : Vertex d) e.1 (by
        intro b hb
        exact hsame b (Finset.mem_union.mpr (Or.inl hb)))).mpr hconn
    have hb : bondOfAdj (orientedBoundary_adj he) ∈ exitBonds Lam :=
      bondOfAdj_mem_exitBonds he
    exact ⟨e, he, hconn', by
      simpa [hsame _ (Finset.mem_union.mpr (Or.inr hb))] using hopen⟩

/-- Local event that `0` exits the finite vertex set `Lam`. -/
noncomputable def exitEvent {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) : LocalEvent d :=
  { support := internalBonds Lam ∪ exitBonds Lam
    pred := ExitPred Lam
    isLocal := exitEvent_dependsOn Lam h0 }

theorem exitPred_mono {d : Nat} {Lam : Finset (Vertex d)}
    {omega omega' : Config d} (hle : ConfigLE omega omega')
    (hexit : ExitPred Lam omega) : ExitPred Lam omega' := by
  rcases hexit with ⟨e, he, hconn, hopen⟩
  exact ⟨e, he, connIn_mono hle hconn,
    hle (bondOfAdj (orientedBoundary_adj he)) hopen⟩

theorem exitEvent_increasing {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) : Increasing (exitEvent Lam h0) := by
  intro omega omega' hle hexit
  exact exitPred_mono hle hexit

/-- Finite Bernoulli probability of the finite exit event from `Lam`. -/
noncomputable def exitProb {d : Nat} (p : Real) (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) : Real :=
  Prob p (exitEvent Lam h0)

/-- Finite box exit probability `P_p(0 <-> Lambda_n^c)`. -/
noncomputable def boxExitProb (d : Nat) (p : Real) (n : Nat) : Real :=
  exitProb p (ball d n) (zero_mem_ball d n)

/-- Connectivity from a vertex to a finite target set inside a finite ambient set. -/
def ConnToSetIn {d : Nat} (omega : Config d) (T : Finset (Vertex d))
    (u : Vertex d) (B : Finset (Vertex d)) : Prop :=
  exists b, b ∈ B /\ ConnIn omega T u b

/-- Finite target connectivity is local on the ambient internal bonds. -/
theorem connToSetIn_dependsOn {d : Nat} (T : Finset (Vertex d))
    (u : Vertex d) (B : Finset (Vertex d)) :
    DependsOn (internalBonds T) (fun omega => ConnToSetIn omega T u B) := by
  intro omega omega' hsame
  constructor
  · rintro ⟨b, hb, hconn⟩
    exact ⟨b, hb, (connIn_dependsOn T u b hsame).mp hconn⟩
  · rintro ⟨b, hb, hconn⟩
    exact ⟨b, hb, (connIn_dependsOn T u b hsame).mpr hconn⟩

/-- Local event that `u` connects to the finite target set `B` inside `T`. -/
noncomputable def connToSetInEvent {d : Nat} (T : Finset (Vertex d))
    (u : Vertex d) (B : Finset (Vertex d)) : LocalEvent d :=
  { support := internalBonds T
    pred := fun omega => ConnToSetIn omega T u B
    isLocal := connToSetIn_dependsOn T u B }

theorem connToSetIn_mono {d : Nat} {omega omega' : Config d}
    {T : Finset (Vertex d)} {u : Vertex d} {B : Finset (Vertex d)}
    (hle : ConfigLE omega omega') (hconn : ConnToSetIn omega T u B) :
    ConnToSetIn omega' T u B := by
  rcases hconn with ⟨b, hb, hconn⟩
  exact ⟨b, hb, connIn_mono hle hconn⟩

theorem connToSetInEvent_increasing {d : Nat} (T : Finset (Vertex d))
    (u : Vertex d) (B : Finset (Vertex d)) :
    Increasing (connToSetInEvent T u B) := by
  intro omega omega' hle hconn
  exact connToSetIn_mono hle hconn

/--
Infinite-cluster density defined as the decreasing-limit infimum of finite exit
probabilities.
-/
noncomputable def theta (d : Nat) (p : Real) : Real :=
  sInf (Set.range fun n : Nat => boxExitProb d p n)

theorem boxExitProb_nonneg {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (n : Nat) : 0 <= boxExitProb d p n := by
  unfold boxExitProb exitProb Prob
  exact probOn_nonneg (F := (exitEvent (ball d n) (zero_mem_ball d n)).support)
    (A := fun sigma : (exitEvent (ball d n) (zero_mem_ball d n)).support -> Bool =>
      (exitEvent (ball d n) (zero_mem_ball d n)).pred
        (extendConfig (exitEvent (ball d n) (zero_mem_ball d n)).support sigma))
    hp0 hp1

theorem theta_nonneg {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1) :
    0 <= theta d p := by
  unfold theta
  refine le_csInf (Set.range_nonempty (fun n : Nat => boxExitProb d p n)) ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact boxExitProb_nonneg hp0 hp1 n

theorem theta_le_boxExitProb (d : Nat) (p : Real) (n : Nat)
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    theta d p <= boxExitProb d p n := by
  unfold theta
  refine csInf_le ?_ ⟨n, rfl⟩
  refine ⟨0, ?_⟩
  intro x hx
  rcases hx with ⟨m, rfl⟩
  exact boxExitProb_nonneg hp0 hp1 m

theorem theta_eq_zero_of_exponential_decay {d : Nat} {p c : Real}
    (hp0 : 0 <= p) (hp1 : p <= 1) (hc : 0 < c)
    (hdecay : forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real)))) :
    theta d p = 0 := by
  refine le_antisymm ?_ (theta_nonneg hp0 hp1)
  have hlim :
      Tendsto (fun n : Nat => Real.exp (-(c * (n : Real)))) atTop (nhds 0) := by
    have harg : Tendsto (fun n : Nat => (-c) * (n : Real)) atTop atBot := by
      exact Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_natCast_atTop_atTop
    have h := Real.tendsto_exp_atBot.comp harg
    convert h using 1
    ext n
    change Real.exp (-(c * (n : Real))) = Real.exp ((-c) * (n : Real))
    congr 1
    ring
  have hconst : Tendsto (fun _ : Nat => theta d p) atTop (nhds (theta d p)) :=
    tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hconst hlim ?_
  exact Filter.Eventually.of_forall fun n =>
    (theta_le_boxExitProb d p n hp0 hp1).trans (hdecay n)

-- Missing later real-order/probability fact: prove lower bounds pass to the infimum of the
-- finite-exit sequence.
theorem le_theta_of_le_boxExitProb {d : Nat} {p b : Real}
    (hb : forall n : Nat, b <= boxExitProb d p n) :
    b <= theta d p := by
  unfold theta
  refine le_csInf (Set.range_nonempty (fun n : Nat => boxExitProb d p n)) ?_
  intro x hx
  rcases hx with ⟨n, rfl⟩
  exact hb n

end Sharpness
