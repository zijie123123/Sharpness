import Sharpness.Phi
import Sharpness.Russo

namespace Sharpness

open scoped BigOperators

/-- Finite-volume exit from a vertex `x` through the oriented boundary of `Lam`. -/
def ExitFromPred {d : Nat} (Lam : Finset (Vertex d)) (x : Vertex d)
    (omega : Config d) : Prop :=
  exists e, exists he : e ∈ orientedBoundary Lam,
    ConnIn omega Lam x e.1 /\
    omega (bondOfAdj (orientedBoundary_adj he)) = true

/-- Exit from the origin is the finite exit predicate used by `exitEvent`. -/
theorem exitFrom_zero_iff_exitPred {d : Nat} (Lam : Finset (Vertex d))
    (omega : Config d) :
    ExitFromPred Lam (0 : Vertex d) omega <-> ExitPred Lam omega :=
  Iff.rfl

/-- Exit from a fixed vertex is local on the finite exit support of `Lam`. -/
theorem exitFrom_dependsOn {d : Nat} (Lam : Finset (Vertex d)) (x : Vertex d) :
    DependsOn (internalBonds Lam ∪ exitBonds Lam) (ExitFromPred Lam x) := by
  intro omega omega' hsame
  constructor
  · rintro ⟨e, he, hconn, hopen⟩
    have hconn' : ConnIn omega' Lam x e.1 :=
      (connIn_dependsOn Lam x e.1 (by
        intro b hb
        exact hsame b (Finset.mem_union.mpr (Or.inl hb)))).mp hconn
    have hb : bondOfAdj (orientedBoundary_adj he) ∈ exitBonds Lam :=
      bondOfAdj_mem_exitBonds he
    exact ⟨e, he, hconn', by
      simpa [hsame _ (Finset.mem_union.mpr (Or.inr hb))] using hopen⟩
  · rintro ⟨e, he, hconn, hopen⟩
    have hconn' : ConnIn omega Lam x e.1 :=
      (connIn_dependsOn Lam x e.1 (by
        intro b hb
        exact hsame b (Finset.mem_union.mpr (Or.inl hb)))).mpr hconn
    have hb : bondOfAdj (orientedBoundary_adj he) ∈ exitBonds Lam :=
      bondOfAdj_mem_exitBonds he
    exact ⟨e, he, hconn', by
      simpa [hsame _ (Finset.mem_union.mpr (Or.inr hb))] using hopen⟩

/-- The random shield set `{x ∈ Lam | x` is not connected to `Lamᶜ`}. -/
noncomputable def Shield {d : Nat} (Lam : Finset (Vertex d))
    (omega : Config d) : Finset (Vertex d) := by
  classical
  exact Lam.filter fun x => ¬ ExitFromPred Lam x omega

/-- The origin belongs to the shield exactly when the finite exit event fails. -/
theorem zero_mem_shield_iff_not_exit {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) (omega : Config d) :
    (0 : Vertex d) ∈ Shield Lam omega <-> ¬ ExitPred Lam omega := by
  simp [Shield, h0, exitFrom_zero_iff_exitPred]

/-- Closing all internal edges of `S`. -/
noncomputable def closeInternalEdges {d : Nat} (S : Finset (Vertex d))
    (omega : Config d) : Config d :=
  fun e => if e ∈ internalBonds S then false else omega e

/-- The finite support for `{Shield = S}` after deleting internal `S`-edges. -/
noncomputable def shieldSupport {d : Nat} (Lam S : Finset (Vertex d)) :
    Finset (Bond d) :=
  (internalBonds Lam ∪ exitBonds Lam) \ internalBonds S

private theorem bondOfAdj_mem_internalBonds_endpoints {d : Nat}
    {S : Finset (Vertex d)} {x y : Vertex d} {hxy : Adj x y}
    (hb : bondOfAdj hxy ∈ internalBonds S) : x ∈ S /\ y ∈ S := by
  classical
  rw [internalBonds] at hb
  rcases Finset.mem_image.mp hb with ⟨ein, _hein, hbeq⟩
  let a : Vertex d := ein.1.1
  let b : Vertex d := ein.1.2
  have hfilter := Finset.mem_filter.mp ein.property
  have haS : a ∈ S := (Finset.mem_product.mp hfilter.1).1
  have hbS : b ∈ S := (Finset.mem_product.mp hfilter.1).2
  have hcar :
      (bondOfAdj ((Finset.mem_filter.mp ein.property).2.2)).carrier =
        (bondOfAdj hxy).carrier := congrArg Bond.carrier hbeq
  have hxmem : x ∈ ({a, b} : Finset (Vertex d)) := by
    change x ∈ (bondOfAdj ((Finset.mem_filter.mp ein.property).2.2)).carrier
    rw [hcar]
    change x ∈ ({x, y} : Finset (Vertex d))
    simp
  have hymem : y ∈ ({a, b} : Finset (Vertex d)) := by
    change y ∈ (bondOfAdj ((Finset.mem_filter.mp ein.property).2.2)).carrier
    rw [hcar]
    change y ∈ ({x, y} : Finset (Vertex d))
    simp
  constructor
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
    rcases hxmem with hxa | hxb
    · simpa [hxa] using haS
    · simpa [hxb] using hbS
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hymem
    rcases hymem with hya | hyb
    · simpa [hya] using haS
    · simpa [hyb] using hbS

private theorem bondOfAdj_not_mem_internalBonds_of_not_both {d : Nat}
    {S : Finset (Vertex d)} {x y : Vertex d} (hxy : Adj x y)
    (hnot : ¬ (x ∈ S /\ y ∈ S)) :
    bondOfAdj hxy ∉ internalBonds S := by
  intro hb
  exact hnot (bondOfAdj_mem_internalBonds_endpoints hb)

private theorem openPath_of_closeInternalEdges {d : Nat}
    {S : Finset (Vertex d)} {omega : Config d} {gamma : List (Vertex d)}
    (hopen : OpenPath (closeInternalEdges S omega) gamma) :
    OpenPath omega gamma := by
  change
    List.IsChain (fun x y => exists hxy : Adj x y, omega (bondOfAdj hxy) = true)
      gamma
  change
    List.IsChain
      (fun x y => exists hxy : Adj x y,
        closeInternalEdges S omega (bondOfAdj hxy) = true) gamma at hopen
  exact hopen.imp fun {_ _} h => by
    rcases h with ⟨hxy, hopenEdge⟩
    by_cases hb : bondOfAdj hxy ∈ internalBonds S
    · simp [closeInternalEdges, hb] at hopenEdge
    · exact ⟨hxy, by simpa [closeInternalEdges, hb] using hopenEdge⟩

private theorem connIn_of_closeInternalEdges {d : Nat}
    {S Lam : Finset (Vertex d)} {omega : Config d} {x y : Vertex d}
    (hconn : ConnIn (closeInternalEdges S omega) Lam x y) :
    ConnIn omega Lam x y := by
  rcases hconn with ⟨gamma, hpath, hLam, hopen⟩
  exact ⟨gamma, hpath, hLam, openPath_of_closeInternalEdges hopen⟩

private theorem exitFrom_of_closeInternalEdges {d : Nat}
    {S Lam : Finset (Vertex d)} {omega : Config d} {x : Vertex d}
    (hexit : ExitFromPred Lam x (closeInternalEdges S omega)) :
    ExitFromPred Lam x omega := by
  rcases hexit with ⟨e, he, hconn, hopen⟩
  have hconn' : ConnIn omega Lam x e.1 := connIn_of_closeInternalEdges hconn
  by_cases hb : bondOfAdj (orientedBoundary_adj he) ∈ internalBonds S
  · simp [closeInternalEdges, hb] at hopen
  · exact ⟨e, he, hconn', by simpa [closeInternalEdges, hb] using hopen⟩

private theorem connIn_single {d : Nat} {omega : Config d} {S : Finset (Vertex d)}
    {x : Vertex d} (hx : x ∈ S) : ConnIn omega S x x := by
  refine ⟨[x], ?_, ?_, ?_⟩
  · simp [PathFromTo, IsPath]
  · intro z hz
    have hzx : z = x := by simpa using hz
    simpa [hzx] using hx
  · simp [OpenPath]

private theorem openPath_closeInternalEdges_of_no_internal {d : Nat}
    {S : Finset (Vertex d)} {omega : Config d} {gamma : List (Vertex d)}
    (hopen : OpenPath omega gamma)
    (hnotInternal : forall {x y : Vertex d}, x ∈ gamma -> y ∈ gamma ->
      forall hxy : Adj x y, bondOfAdj hxy ∉ internalBonds S) :
    OpenPath (closeInternalEdges S omega) gamma := by
  change
    List.IsChain
      (fun x y => exists hxy : Adj x y,
        closeInternalEdges S omega (bondOfAdj hxy) = true) gamma
  change
    List.IsChain (fun x y => exists hxy : Adj x y, omega (bondOfAdj hxy) = true)
      gamma at hopen
  have hiff :
      List.IsChain (fun x y => exists hxy : Adj x y, omega (bondOfAdj hxy) = true)
          gamma <->
        List.IsChain
          (fun x y => exists hxy : Adj x y,
            closeInternalEdges S omega (bondOfAdj hxy) = true) gamma := by
    apply List.IsChain.iff_of_mem_imp
    intro x y hx hy
    constructor
    · rintro ⟨hxy, hopenEdge⟩
      have hbnot : bondOfAdj hxy ∉ internalBonds S := hnotInternal hx hy hxy
      exact ⟨hxy, by simpa [closeInternalEdges, hbnot] using hopenEdge⟩
    · rintro ⟨hxy, hopenEdge⟩
      by_cases hb : bondOfAdj hxy ∈ internalBonds S
      · simp [closeInternalEdges, hb] at hopenEdge
      · exact ⟨hxy, by simpa [closeInternalEdges, hb] using hopenEdge⟩
  exact hiff.mp hopen

private theorem openPath_closeInternalEdges_of_unique_S {d : Nat}
    {S : Finset (Vertex d)} {omega : Config d} {gamma : List (Vertex d)}
    {u : Vertex d} (hopen : OpenPath omega gamma)
    (hunique : forall z, z ∈ gamma -> z ∈ S -> z = u) :
    OpenPath (closeInternalEdges S omega) gamma := by
  refine openPath_closeInternalEdges_of_no_internal hopen ?_
  intro x y hx hy hxy
  refine bondOfAdj_not_mem_internalBonds_of_not_both hxy ?_
  rintro ⟨hxS, hyS⟩
  have hxu : x = u := hunique x hx hxS
  have hyu : y = u := hunique y hy hyS
  exact ne_of_adj hxy (hxu.trans hyu.symm)

private theorem exists_closed_conn_from_last_S {d : Nat}
    {S Lam : Finset (Vertex d)} {omega : Config d} :
    forall {gamma : List (Vertex d)} {x y : Vertex d},
      PathFromTo gamma x y -> PathIn Lam gamma -> OpenPath omega gamma ->
      (exists z, z ∈ gamma /\ z ∈ S) -> y ∉ S ->
      exists u, u ∈ S /\ ConnIn (closeInternalEdges S omega) Lam u y := by
  intro gamma
  induction gamma with
  | nil =>
      intro x y hpath _hLam _hopen hex _hyS
      rcases hex with ⟨z, hz, _⟩
      simp at hz
  | cons a rest ih =>
      intro x y hpath hLam hopen hex hyS
      by_cases hrest : exists z, z ∈ rest /\ z ∈ S
      · cases rest with
        | nil =>
            rcases hrest with ⟨z, hz, _⟩
            simp at hz
        | cons b tail =>
            rcases hpath with ⟨_hhead, hlast, hchain⟩
            have hchainTail : IsPath (b :: tail) :=
              (List.isChain_cons_cons.mp hchain).2
            have hopenTail : OpenPath omega (b :: tail) :=
              (List.isChain_cons_cons.mp hopen).2
            have hLamTail : PathIn Lam (b :: tail) := by
              intro z hz
              exact hLam z (by simp [hz])
            have hpathTail : PathFromTo (b :: tail) b y := by
              exact ⟨rfl, by simpa using hlast, hchainTail⟩
            exact ih hpathTail hLamTail hopenTail hrest hyS
      · have haS : a ∈ S := by
          rcases hex with ⟨z, hz, hzS⟩
          simp only [List.mem_cons] at hz
          rcases hz with hza | hzrest
          · simpa [hza] using hzS
          · exact False.elim (hrest ⟨z, hzrest, hzS⟩)
        cases rest with
        | nil =>
            rcases hpath with ⟨_hhead, hlast, _hchain⟩
            have hay : a = y := by simpa using hlast
            exact False.elim (hyS (by simpa [hay] using haS))
        | cons b tail =>
            have hunique : forall z, z ∈ (a :: b :: tail) -> z ∈ S -> z = a := by
              intro z hz hzS
              simp only [List.mem_cons] at hz
              rcases hz with hza | hztail
              · exact hza
              · exact False.elim (hrest ⟨z, by simpa using hztail, hzS⟩)
            have hpathA : PathFromTo (a :: b :: tail) a y := by
              rcases hpath with ⟨_hhead, hlast, hchain⟩
              exact ⟨rfl, hlast, hchain⟩
            have hconn : ConnIn (closeInternalEdges S omega) Lam a y :=
              ⟨a :: b :: tail, hpathA, hLam,
                openPath_closeInternalEdges_of_unique_S hopen hunique⟩
            exact ⟨a, haS, hconn⟩

private theorem exists_exitFrom_close_of_exitFrom_from_S {d : Nat}
    {Lam S : Finset (Vertex d)} (hS : S <= Lam)
    {omega : Config d} {x : Vertex d} (hxS : x ∈ S)
    (hexit : ExitFromPred Lam x omega) :
    exists u, u ∈ S /\ ExitFromPred Lam u (closeInternalEdges S omega) := by
  rcases hexit with ⟨e, he, hconn, hopenBoundary⟩
  have hy_not_S : e.2 ∉ S := by
    intro hyS
    exact (mem_orientedBoundary_iff.mp he).2.1 (hS hyS)
  have hboundary_not_internal :
      bondOfAdj (orientedBoundary_adj he) ∉ internalBonds S := by
    refine bondOfAdj_not_mem_internalBonds_of_not_both (orientedBoundary_adj he) ?_
    intro hboth
    exact hy_not_S hboth.2
  by_cases hxBoundaryS : e.1 ∈ S
  · have hconnClosed : ConnIn (closeInternalEdges S omega) Lam e.1 e.1 :=
      connIn_single ((mem_orientedBoundary_iff.mp he).1)
    refine ⟨e.1, hxBoundaryS, e, he, hconnClosed, ?_⟩
    simpa [closeInternalEdges, hboundary_not_internal] using hopenBoundary
  · rcases hconn with ⟨gamma, hpath, hLam, hopen⟩
    have hexS : exists z, z ∈ gamma /\ z ∈ S := by
      refine ⟨x, List.mem_of_head? hpath.1, hxS⟩
    rcases exists_closed_conn_from_last_S hpath hLam hopen hexS hxBoundaryS with
      ⟨u, huS, hconnClosed⟩
    refine ⟨u, huS, e, he, hconnClosed, ?_⟩
    simpa [closeInternalEdges, hboundary_not_internal] using hopenBoundary

private theorem exitFrom_close_of_exitFrom_of_no_S_exit {d : Nat}
    {Lam S : Finset (Vertex d)} (hS : S <= Lam)
    {omega : Config d} {x : Vertex d}
    (hnoSExit : forall z, z ∈ S -> ¬ ExitFromPred Lam z omega)
    (hexit : ExitFromPred Lam x omega) :
    ExitFromPred Lam x (closeInternalEdges S omega) := by
  rcases hexit with ⟨e, he, hconn, hopenBoundary⟩
  have hy_not_S : e.2 ∉ S := by
    intro hyS
    exact (mem_orientedBoundary_iff.mp he).2.1 (hS hyS)
  have hboundary_not_internal :
      bondOfAdj (orientedBoundary_adj he) ∉ internalBonds S := by
    refine bondOfAdj_not_mem_internalBonds_of_not_both (orientedBoundary_adj he) ?_
    intro hboth
    exact hy_not_S hboth.2
  by_cases hxBoundaryS : e.1 ∈ S
  · have hconnClosed : ConnIn (closeInternalEdges S omega) Lam e.1 e.1 :=
      connIn_single ((mem_orientedBoundary_iff.mp he).1)
    have hexitBoundary : ExitFromPred Lam e.1 (closeInternalEdges S omega) :=
      ⟨e, he, hconnClosed, by
        simpa [closeInternalEdges, hboundary_not_internal] using hopenBoundary⟩
    exact False.elim (hnoSExit e.1 hxBoundaryS (exitFrom_of_closeInternalEdges hexitBoundary))
  · rcases hconn with ⟨gamma, hpath, hLam, hopen⟩
    have hnoGammaS : forall z, z ∈ gamma -> z ∉ S := by
      intro z hz hzS
      have hexS : exists w, w ∈ gamma /\ w ∈ S := ⟨z, hz, hzS⟩
      rcases exists_closed_conn_from_last_S hpath hLam hopen hexS hxBoundaryS with
        ⟨u, huS, hconnClosed⟩
      have hexitClosed : ExitFromPred Lam u (closeInternalEdges S omega) :=
        ⟨e, he, hconnClosed, by
          simpa [closeInternalEdges, hboundary_not_internal] using hopenBoundary⟩
      exact hnoSExit u huS (exitFrom_of_closeInternalEdges hexitClosed)
    have hconnClosed : ConnIn (closeInternalEdges S omega) Lam x e.1 := by
      refine ⟨gamma, hpath, hLam, ?_⟩
      refine openPath_closeInternalEdges_of_no_internal hopen ?_
      intro a b ha hb hxy
      refine bondOfAdj_not_mem_internalBonds_of_not_both hxy ?_
      intro hboth
      exact hnoGammaS a ha hboth.1
    exact ⟨e, he, hconnClosed, by
      simpa [closeInternalEdges, hboundary_not_internal] using hopenBoundary⟩

/-- Internal `S`-bonds are disjoint from the support used by the shield event. -/
theorem disjoint_internalBonds_shieldSupport {d : Nat}
    (Lam S : Finset (Vertex d)) :
    Disjoint (internalBonds S) (shieldSupport Lam S) := by
  rw [Finset.disjoint_left]
  intro b hbInt hbSupp
  exact (Finset.mem_sdiff.mp hbSupp).2 hbInt

/-- The shield value is local on the ambient finite exit support. -/
theorem shield_dependsOn_ambient {d : Nat} (Lam S : Finset (Vertex d)) :
    DependsOn (internalBonds Lam ∪ exitBonds Lam)
      (fun omega => Shield Lam omega = S) := by
  intro omega omega' hsame
  have hmem : forall x, x ∈ Shield Lam omega <-> x ∈ Shield Lam omega' := by
    intro x
    by_cases hx : x ∈ Lam
    · have hExit := exitFrom_dependsOn Lam x hsame
      simp [Shield, hx, hExit]
    · simp [Shield, hx]
  have hshield : Shield Lam omega = Shield Lam omega' := by
    exact Finset.ext hmem
  constructor
  · intro h
    exact hshield.symm.trans h
  · intro h
    exact hshield.trans h

/--
Deleted-internal-edge characterization of `{Shield = S}`.

After closing all internal `S`-edges, shield equality is equivalent to no `S`-vertex
exiting and every `Lam \ S` vertex exiting.
-/
theorem shield_eq_iff_deleted_internal {d : Nat}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam) (omega : Config d) :
    Shield Lam omega = S <->
      ((forall x, x ∈ S -> ¬ ExitFromPred Lam x (closeInternalEdges S omega)) /\
        (forall x, x ∈ Lam -> x ∉ S ->
          ExitFromPred Lam x (closeInternalEdges S omega))) := by
  classical
  constructor
  · intro hshield
    have hnoSExit : forall x, x ∈ S -> ¬ ExitFromPred Lam x omega := by
      intro x hxS hxExit
      have hxShield : x ∈ Shield Lam omega := by
        simpa [hshield] using hxS
      have hxShieldFilter :
          x ∈ Lam.filter (fun y => ¬ ExitFromPred Lam y omega) := by
        simpa [Shield] using hxShield
      have hxNoExit : ¬ ExitFromPred Lam x omega :=
        (Finset.mem_filter.mp hxShieldFilter).2
      exact hxNoExit hxExit
    constructor
    · intro x hxS hxExitClosed
      exact hnoSExit x hxS (exitFrom_of_closeInternalEdges hxExitClosed)
    · intro x hxLam hxS
      have hxNotShield : x ∉ Shield Lam omega := by
        intro hxShield
        exact hxS (by simpa [hshield] using hxShield)
      have hxExit : ExitFromPred Lam x omega := by
        by_contra hnot
        exact hxNotShield (by simp [Shield, hxLam, hnot])
      exact exitFrom_close_of_exitFrom_of_no_S_exit hS hnoSExit hxExit
  · intro hchar
    apply Finset.ext
    intro x
    constructor
    · intro hxShield
      have hxShieldFilter :
          x ∈ Lam.filter (fun y => ¬ ExitFromPred Lam y omega) := by
        simpa [Shield] using hxShield
      have hxLam : x ∈ Lam := (Finset.mem_filter.mp hxShieldFilter).1
      by_contra hxS
      have hxExitClosed : ExitFromPred Lam x (closeInternalEdges S omega) :=
        hchar.2 x hxLam hxS
      have hxExit : ExitFromPred Lam x omega :=
        exitFrom_of_closeInternalEdges hxExitClosed
      have hxNoExit : ¬ ExitFromPred Lam x omega :=
        (Finset.mem_filter.mp hxShieldFilter).2
      exact hxNoExit hxExit
    · intro hxS
      have hxLam : x ∈ Lam := hS hxS
      have hnoExit : ¬ ExitFromPred Lam x omega := by
        intro hxExit
        rcases exists_exitFrom_close_of_exitFrom_from_S hS hxS hxExit with
          ⟨u, huS, huExitClosed⟩
        exact hchar.1 u huS huExitClosed
      simp [Shield, hxLam, hnoExit]

/--
Support separation for the shield event `{Shield = S}`.

This combines `shield_eq_iff_deleted_internal` with locality of finite exit events in the
deleted configuration to show that internal `S`-edges are irrelevant.
-/
theorem shield_dependsOn_noninternal {d : Nat}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam) :
    DependsOn (shieldSupport Lam S) (fun omega => Shield Lam omega = S) := by
  intro omega omega' hsame
  have hclosedSame :
      forall e, e ∈ internalBonds Lam ∪ exitBonds Lam ->
        closeInternalEdges S omega e = closeInternalEdges S omega' e := by
    intro e hamb
    by_cases heS : e ∈ internalBonds S
    · simp [closeInternalEdges, heS]
    · simp [closeInternalEdges, heS, hsame e (Finset.mem_sdiff.mpr ⟨hamb, heS⟩)]
  have hExit :
      forall x,
        ExitFromPred Lam x (closeInternalEdges S omega) <->
          ExitFromPred Lam x (closeInternalEdges S omega') := by
    intro x
    exact exitFrom_dependsOn Lam x hclosedSame
  have hchar := shield_eq_iff_deleted_internal Lam S hS
  constructor
  · intro hshield
    change Shield Lam omega = S at hshield
    have hshield' := (hchar omega).mp hshield
    apply (hchar omega').mpr
    constructor
    · intro x hxS hxExit
      exact hshield'.1 x hxS ((hExit x).mpr hxExit)
    · intro x hxLam hxS
      exact (hExit x).mp (hshield'.2 x hxLam hxS)
  · intro hshield
    change Shield Lam omega' = S at hshield
    have hshield' := (hchar omega').mp hshield
    apply (hchar omega).mpr
    constructor
    · intro x hxS hxExit
      exact hshield'.1 x hxS ((hExit x).mp hxExit)
    · intro x hxLam hxS
      exact (hExit x).mpr (hshield'.2 x hxLam hxS)

/-- Local event for a fixed shield value, using the separated support. -/
noncomputable def shieldEvent {d : Nat} (Lam S : Finset (Vertex d))
    (hS : S <= Lam) : LocalEvent d :=
  { support := shieldSupport Lam S
    pred := fun omega => Shield Lam omega = S
    isLocal := shield_dependsOn_noninternal Lam S hS }

private theorem connIn_subset {d : Nat} {omega : Config d}
    {S T : Finset (Vertex d)} {x y : Vertex d}
    (hST : S <= T) (hconn : ConnIn omega S x y) :
    ConnIn omega T x y := by
  rcases hconn with ⟨gamma, hpath, hS, hopen⟩
  exact ⟨gamma, hpath, (fun z hz => hST (hS z hz)), hopen⟩

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

private theorem connIn_cons_open_adj {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {x y z : Vertex d}
    (hxS : x ∈ S) (hxy : Adj x y)
    (hopen : omega (bondOfAdj hxy) = true)
    (hconn : ConnIn omega S y z) :
    ConnIn omega S x z := by
  rcases hconn with ⟨gamma, hpath, hS, hopenPath⟩
  rcases hpath with ⟨hhead, hlast, hchain⟩
  cases gamma with
  | nil =>
      simp at hhead
  | cons a rest =>
      have hay : a = y := by simpa using hhead
      subst a
      refine ⟨x :: y :: rest, ?_, ?_, ?_⟩
      · exact ⟨rfl, by simpa using hlast, by
          rw [IsPath, List.isChain_cons_cons]
          exact ⟨hxy, hchain⟩⟩
      · intro w hw
        simp only [List.mem_cons] at hw
        rcases hw with hw | hw
        · simpa [hw] using hxS
        · exact hS w (by simpa using hw)
      · rw [OpenPath, List.isChain_cons_cons]
        exact ⟨⟨hxy, hopen⟩, hopenPath⟩

private theorem connIn_trans {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {x y z : Vertex d}
    (hxy : ConnIn omega S x y) (hyz : ConnIn omega S y z) :
    ConnIn omega S x z := by
  rcases hxy with ⟨gamma, hpathXY, hgammaS, hopenGamma⟩
  rcases hyz with ⟨delta, hpathYZ, hdeltaS, hopenDelta⟩
  rcases hpathXY with ⟨hheadX, hlastY, hchainGamma⟩
  rcases hpathYZ with ⟨hheadY, hlastZ, hchainDelta⟩
  cases delta with
  | nil =>
      simp at hheadY
  | cons a rest =>
      have hay : a = y := by simpa using hheadY
      subst a
      cases rest with
      | nil =>
          have hyz_eq : y = z := by simpa using hlastZ
          subst z
          exact ⟨gamma, ⟨hheadX, hlastY, hchainGamma⟩, hgammaS, hopenGamma⟩
      | cons b tail =>
          have hdeltaChain := List.isChain_cons_cons.mp hchainDelta
          have hopenDelta' := List.isChain_cons_cons.mp hopenDelta
          refine ⟨gamma ++ (b :: tail), ?_, ?_, ?_⟩
          · constructor
            · rw [List.head?_append]
              simp [hheadX]
            · constructor
              · rw [List.getLast?_append]
                simpa using hlastZ
              · rw [IsPath, List.isChain_append]
                refine ⟨hchainGamma, hdeltaChain.2, ?_⟩
                intro a ha c hc
                have hay' : y = a := by simpa [hlastY] using ha
                have hbc : b = c := by simpa using hc
                subst a
                subst c
                exact hdeltaChain.1
          · intro w hw
            rw [List.mem_append] at hw
            rcases hw with hw | hw
            · exact hgammaS w hw
            · exact hdeltaS w (by simp [hw])
          · rw [OpenPath, List.isChain_append]
            refine ⟨hopenGamma, hopenDelta'.2, ?_⟩
            intro a ha c hc
            have hay' : y = a := by simpa [hlastY] using ha
            have hbc : b = c := by simpa using hc
            subst a
            subst c
            exact hopenDelta'.1

private theorem connIn_forceOpen_of_connIn {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {x y : Vertex d} {b : Bond d}
    (hconn : ConnIn omega S x y) :
    ConnIn (forceOpen b omega) S x y := by
  exact connIn_mono (omega := omega) (omega' := forceOpen b omega)
    (by
      intro e he
      by_cases hbe : e = b
      · simp [forceOpen, hbe]
      · simp [forceOpen, hbe, he])
    hconn

private theorem connIn_of_forceOpen_of_not_internal {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} {x y : Vertex d} {b : Bond d}
    (hb : b ∉ internalBonds S)
    (hconn : ConnIn (forceOpen b omega) S x y) :
    ConnIn omega S x y := by
  exact ((connIn_dependsOn S x y (by
    intro e he
    by_cases heb : e = b
    · subst e
      exact False.elim (hb he)
    · simp [forceOpen, heb])).mp hconn)

private theorem first_exit_conn_of_path {d : Nat} {omega : Config d}
    {S : Finset (Vertex d)} :
    forall {gamma : List (Vertex d)} {x y : Vertex d},
      PathFromTo gamma x y -> OpenPath omega gamma ->
      x ∈ S -> y ∉ S ->
      exists a c : Vertex d,
        exists hac : Adj a c,
          ConnIn omega S x a /\ a ∈ S /\ c ∉ S /\
            omega (bondOfAdj hac) = true := by
  intro gamma
  induction gamma with
  | nil =>
      intro x y hpath _hopen _hxS _hyS
      rcases hpath with ⟨hhead, _hlast, _hchain⟩
      simp at hhead
  | cons a rest ih =>
      intro x y hpath hopen hxS hyS
      rcases hpath with ⟨hhead, hlast, hchain⟩
      have hax : a = x := by simpa using hhead
      have haS : a ∈ S := by simpa [hax] using hxS
      cases rest with
      | nil =>
          have hay : a = y := by simpa using hlast
          have hxy : x = y := hax.symm.trans hay
          exact False.elim (hyS (by simpa [hxy] using hxS))
      | cons b tail =>
          have hchain' := List.isChain_cons_cons.mp hchain
          have hopen' := List.isChain_cons_cons.mp hopen
          by_cases hbS : b ∈ S
          · have htailPath : PathFromTo (b :: tail) b y :=
              ⟨rfl, by simpa using hlast, hchain'.2⟩
            rcases ih htailPath hopen'.2 hbS hyS with
              ⟨u, v, huv, hconnBU, huS, hvS, hopenUV⟩
            refine ⟨u, v, huv, ?_, huS, hvS, hopenUV⟩
            have hconnAU : ConnIn omega S a u :=
              connIn_cons_open_adj haS hchain'.1 hopen'.1.choose_spec hconnBU
            simpa [hax] using hconnAU
          · refine ⟨a, b, hchain'.1, ?_, haS, hbS, ?_⟩
            · subst x
              exact connIn_single haS
            · exact hopen'.1.choose_spec

private theorem exitFrom_mono {d : Nat} {omega omega' : Config d}
    {Lam : Finset (Vertex d)} {x : Vertex d}
    (hle : ConfigLE omega omega') (hexit : ExitFromPred Lam x omega) :
    ExitFromPred Lam x omega' := by
  rcases hexit with ⟨e, he, hconn, hopen⟩
  exact ⟨e, he, connIn_mono hle hconn,
    hle (bondOfAdj (orientedBoundary_adj he)) hopen⟩

private theorem exitPred_of_connIn_boundary_open {d : Nat}
    (Lam S : Finset (Vertex d)) {omega : Config d} {e : OrientedEdge d}
    (hSLam : S <= Lam)
    (hout : forall y, y ∈ Lam -> y ∉ S -> ExitFromPred Lam y omega)
    (he : e ∈ orientedBoundary S)
    (hconn : ConnIn omega S (0 : Vertex d) e.1)
    (hopen : omega (bondOfAdj (orientedBoundary_adj he)) = true) :
    ExitPred Lam omega := by
  classical
  have hxLam : e.1 ∈ Lam := hSLam (mem_orientedBoundary_iff.mp he).1
  have hconnLam : ConnIn omega Lam (0 : Vertex d) e.1 :=
    connIn_subset hSLam hconn
  by_cases hyLam : e.2 ∈ Lam
  · have hyExit : ExitFromPred Lam e.2 omega :=
      hout e.2 hyLam (mem_orientedBoundary_iff.mp he).2.1
    rcases hyExit with ⟨f, hf, hconnY, hopenF⟩
    have hconnY' : ConnIn omega Lam e.1 e.2 :=
      connIn_append_open_adj_same hyLam (orientedBoundary_adj he) hopen
        (connIn_single hxLam)
    exact ⟨f, hf, connIn_trans (connIn_trans hconnLam hconnY') hconnY, hopenF⟩
  · have heLam : e ∈ orientedBoundary Lam :=
      mem_orientedBoundary_iff.mpr ⟨hxLam, hyLam, orientedBoundary_adj he⟩
    exact ⟨e, heLam, hconnLam, by
      have hb :
          bondOfAdj (orientedBoundary_adj heLam) =
            bondOfAdj (orientedBoundary_adj he) := by
        apply bondOfAdj_same
      simpa [hb] using hopen⟩

private theorem exitPred_of_connIn_shield_boundary_open {d : Nat}
    (Lam : Finset (Vertex d)) {omega : Config d} {e : OrientedEdge d}
    (he : e ∈ orientedBoundary (Shield Lam omega))
    (hconn : ConnIn omega (Shield Lam omega) (0 : Vertex d) e.1)
    (hopen : omega (bondOfAdj (orientedBoundary_adj he)) = true) :
    ExitPred Lam omega := by
  classical
  refine exitPred_of_connIn_boundary_open Lam (Shield Lam omega) ?_ ?_ he hconn hopen
  · intro x hx
    have hx' : x ∈ Lam.filter fun y => ¬ ExitFromPred Lam y omega := by
      simpa [Shield] using hx
    exact (Finset.mem_filter.mp hx').1
  · intro y hyLam hyShield
    by_contra hnot
    exact hyShield (by simp [Shield, hyLam, hnot])

private theorem boundary_left_eq_of_bond_eq {d : Nat}
    {S : Finset (Vertex d)} {a c : Vertex d} {hac : Adj a c}
    {e : OrientedEdge d} (he : e ∈ orientedBoundary S)
    (haS : a ∈ S) (hbond : bondOfAdj hac = bondOfAdj (orientedBoundary_adj he)) :
    a = e.1 := by
  classical
  have hcar := congrArg Bond.carrier hbond
  change ({a, c} : Finset (Vertex d)) = ({e.1, e.2} : Finset (Vertex d)) at hcar
  have ha_mem : a ∈ ({e.1, e.2} : Finset (Vertex d)) := by
    rw [← hcar]
    simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
  rcases ha_mem with ha | ha
  · exact ha
  · exact False.elim ((mem_orientedBoundary_iff.mp he).2.1 (by simpa [ha] using haS))

/--
Pivotal equivalence on a fixed shield value.

On `{Shield = S}`, an oriented boundary bond `(x,y) ∈ ∂E S` is closed-pivotal
for `A_Lam` iff `0` is connected to `x` inside `S`.
-/
theorem closedPivotal_exit_iff_connIn_on_shield {d : Nat}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    {e : OrientedEdge d} (he : e ∈ orientedBoundary S) {omega : Config d}
    (hshield : Shield Lam omega = S) :
    ClosedPivotal (exitEvent Lam (hS h0S))
        (bondOfAdj (orientedBoundary_adj he)) omega <->
      ConnIn omega S (0 : Vertex d) e.1 := by
  classical
  subst S
  constructor
  · intro hpiv
    rcases hpiv with ⟨_hclosed, hnotExit, hforcedExit⟩
    rcases hforcedExit with ⟨f, hf, hconnF, hopenF⟩
    rcases hconnF with ⟨gamma, hpathGamma, hLamGamma, hopenGamma⟩
    let omega' : Config d := forceOpen (bondOfAdj (orientedBoundary_adj he)) omega
    have hpathExit :
        PathFromTo (gamma ++ [f.2]) (0 : Vertex d) f.2 := by
      rcases hpathGamma with ⟨hhead, hlast, hchain⟩
      constructor
      · rw [List.head?_append]
        simp [hhead]
      · constructor
        · simp
        · rw [IsPath, List.isChain_append]
          refine ⟨hchain, by simp, ?_⟩
          intro a ha b hb
          have haf : f.1 = a := by simpa [hlast] using ha
          have hb2 : f.2 = b := by simpa using hb
          subst a
          subst b
          exact orientedBoundary_adj hf
    have hopenExit : OpenPath omega' (gamma ++ [f.2]) := by
      rcases hpathGamma with ⟨_hhead, hlast, _hchain⟩
      rw [OpenPath, List.isChain_append]
      refine ⟨hopenGamma, by simp, ?_⟩
      intro a ha b hb
      have haf : f.1 = a := by simpa [hlast] using ha
      have hb2 : f.2 = b := by simpa using hb
      subst a
      subst b
      exact ⟨orientedBoundary_adj hf, hopenF⟩
    have hf2_not_shield : f.2 ∉ Shield Lam omega := by
      intro hf2S
      exact (mem_orientedBoundary_iff.mp hf).2.1 (hS hf2S)
    rcases first_exit_conn_of_path (S := Shield Lam omega)
        hpathExit hopenExit h0S hf2_not_shield with
      ⟨a, c, hac, hconnForced, haS, hcS, hopenACForced⟩
    have hbNotInternal :
        bondOfAdj (orientedBoundary_adj he) ∉ internalBonds (Shield Lam omega) := by
      refine bondOfAdj_not_mem_internalBonds_of_not_both (orientedBoundary_adj he) ?_
      intro hboth
      exact (mem_orientedBoundary_iff.mp he).2.1 hboth.2
    have hconnPrefix : ConnIn omega (Shield Lam omega) (0 : Vertex d) a :=
      connIn_of_forceOpen_of_not_internal hbNotInternal hconnForced
    have heac : (a, c) ∈ orientedBoundary (Shield Lam omega) :=
      mem_orientedBoundary_iff.mpr ⟨haS, hcS, hac⟩
    have hbond :
        bondOfAdj hac = bondOfAdj (orientedBoundary_adj he) := by
      by_contra hne
      have hopenAC : omega (bondOfAdj hac) = true := by
        simpa [omega', forceOpen, hne] using hopenACForced
      have hExitOriginal : ExitPred Lam omega := by
        refine exitPred_of_connIn_boundary_open Lam (Shield Lam omega) hS ?_
          heac hconnPrefix hopenAC
        intro y hyLam hyShield
        by_contra hnot
        exact hyShield (by simp [Shield, hyLam, hnot])
      exact hnotExit hExitOriginal
    have ha_eq : a = e.1 :=
      boundary_left_eq_of_bond_eq he haS hbond
    simpa [ha_eq] using hconnPrefix
  · intro hconn
    have hnotExit : ¬ ExitPred Lam omega := by
      exact (zero_mem_shield_iff_not_exit Lam (hS h0S) omega).mp h0S
    refine ⟨?_, ?_, ?_⟩
    · by_contra hopenNe
      have hopen : omega (bondOfAdj (orientedBoundary_adj he)) = true := by
        cases h :
            omega (bondOfAdj (orientedBoundary_adj he)) <;> simp [h] at hopenNe ⊢
      exact hnotExit (exitPred_of_connIn_shield_boundary_open Lam he hconn hopen)
    · exact hnotExit
    · have hconnForced :
          ConnIn (forceOpen (bondOfAdj (orientedBoundary_adj he)) omega)
            (Shield Lam omega) (0 : Vertex d) e.1 :=
        connIn_forceOpen_of_connIn hconn
      have hopenForced :
          forceOpen (bondOfAdj (orientedBoundary_adj he)) omega
            (bondOfAdj (orientedBoundary_adj he)) = true := by
        simp [forceOpen]
      refine exitPred_of_connIn_boundary_open Lam (Shield Lam omega) hS ?_ he hconnForced
        hopenForced
      intro y hyLam hyShield
      have hyExit : ExitFromPred Lam y omega := by
        by_contra hnot
        exact hyShield (by simp [Shield, hyLam, hnot])
      exact exitFrom_mono
        (omega := omega) (omega' := forceOpen (bondOfAdj (orientedBoundary_adj he)) omega)
        (by
          intro b hb
          by_cases hbb : b = bondOfAdj (orientedBoundary_adj he)
          · simp [forceOpen, hbb]
          · simp [forceOpen, hbb, hb])
        hyExit

/-- The finite minimum is below each admissible `phi p S`. -/
theorem phiMinIn_le_phi {d : Nat} {p : Real} {Lam S : Finset (Vertex d)}
    (h0 : (0 : Vertex d) ∈ Lam) (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S) :
    phiMinIn p Lam h0 <= phi p S := by
  classical
  exact Finset.inf'_le (f := phi p)
    (by
      rw [finiteSubsetsWithZero, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hS, h0S⟩)

private theorem prob_nonneg {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (E : LocalEvent d) : 0 <= Prob p E := by
  unfold Prob
  exact probOn_nonneg hp0 hp1

private theorem prob_le_of_pred_imp {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (E F : LocalEvent d) (himp : forall omega, E.pred omega -> F.pred omega) :
    Prob p E <= Prob p F := by
  classical
  let G : Finset (Bond d) := E.support ∪ F.support
  have hEsub : E.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inl he)
  have hFsub : F.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inr he)
  calc
    Prob p E = ProbOn p G (fun sigma => E.pred (extendConfig G sigma)) :=
      prob_support_mono E hEsub
    _ <= ProbOn p G (fun sigma => F.pred (extendConfig G sigma)) := by
      exact probOn_mono (fun sigma h => himp (extendConfig G sigma) h) hp0 hp1
    _ = Prob p F := (prob_support_mono F hFsub).symm

private theorem prob_union_le {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (E F : LocalEvent d) :
    Prob p (E.union F) <= Prob p E + Prob p F := by
  classical
  let G : Finset (Bond d) := E.support ∪ F.support
  have hEsub : E.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inl he)
  have hFsub : F.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inr he)
  calc
    Prob p (E.union F)
        = ProbOn p G
            (fun sigma => E.pred (extendConfig G sigma) \/
              F.pred (extendConfig G sigma)) := rfl
    _ <= ProbOn p G (fun sigma => E.pred (extendConfig G sigma)) +
          ProbOn p G (fun sigma => F.pred (extendConfig G sigma)) :=
      probOn_union_bound hp0 hp1
    _ = Prob p E + Prob p F := by
      rw [← prob_support_mono E hEsub, ← prob_support_mono F hFsub]

private noncomputable def finsetUnionEvent {d : Nat} {α : Type*}
    (s : Finset α) (E : α -> LocalEvent d) : LocalEvent d :=
  { support := s.biUnion fun i => (E i).support
    pred := fun omega => exists i, i ∈ s /\ (E i).pred omega
    isLocal := by
      intro omega omega' hsame
      constructor
      · rintro ⟨i, hi, hEi⟩
        refine ⟨i, hi, ?_⟩
        exact ((E i).isLocal (by
          intro e he
          exact hsame e (Finset.mem_biUnion.mpr ⟨i, hi, he⟩))).mp hEi
      · rintro ⟨i, hi, hEi⟩
        refine ⟨i, hi, ?_⟩
        exact ((E i).isLocal (by
          intro e he
          exact hsame e (Finset.mem_biUnion.mpr ⟨i, hi, he⟩))).mpr hEi }

private theorem prob_finsetUnionEvent_le_sum {d : Nat} {α : Type*} [DecidableEq α]
    {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (s : Finset α) (E : α -> LocalEvent d) :
    Prob p (finsetUnionEvent s E) <= s.sum fun i => Prob p (E i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · change Prob p (finsetUnionEvent (∅ : Finset α) E) <= 0
    unfold Prob ProbOn bernProb finsetUnionEvent
    simp
  · intro a s has ih
    have hpred :
        forall omega,
          (finsetUnionEvent (insert a s) E).pred omega ->
            ((E a).union (finsetUnionEvent s E)).pred omega := by
      intro omega h
      rcases h with ⟨i, hi, hEi⟩
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact Or.inl hEi
      · exact Or.inr ⟨i, hi, hEi⟩
    calc
      Prob p (finsetUnionEvent (insert a s) E)
          <= Prob p ((E a).union (finsetUnionEvent s E)) :=
        prob_le_of_pred_imp hp0 hp1 _ _ hpred
      _ <= Prob p (E a) + Prob p (finsetUnionEvent s E) :=
        prob_union_le hp0 hp1 (E a) (finsetUnionEvent s E)
      _ <= Prob p (E a) + s.sum (fun i => Prob p (E i)) :=
        by
          simpa [add_comm] using add_le_add_left ih (Prob p (E a))
      _ = (insert a s).sum (fun i => Prob p (E i)) := by
        rw [Finset.sum_insert has]

private theorem sum_prob_le_prob_of_disjoint_subevents {d : Nat} {α : Type*}
    [DecidableEq α] {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (s : Finset α) (E : LocalEvent d) (F : α -> LocalEvent d)
    (hdisj : forall i, i ∈ s -> forall j, j ∈ s -> i ≠ j ->
      forall omega, (F i).pred omega -> (F j).pred omega -> False)
    (himp : forall i, i ∈ s -> forall omega, (F i).pred omega -> E.pred omega) :
    s.sum (fun i => Prob p (F i)) <= Prob p E := by
  classical
  let G : Finset (Bond d) := E.support ∪ s.biUnion fun i => (F i).support
  have hEsub : E.support <= G := by
    intro e he
    exact Finset.mem_union.mpr (Or.inl he)
  have hFsub : forall i, i ∈ s -> (F i).support <= G := by
    intro i hi e he
    exact Finset.mem_union.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, he⟩))
  have hrewrite :
      s.sum (fun i => Prob p (F i)) =
        Finset.univ.sum fun sigma : G -> Bool =>
          s.sum fun i =>
            if (F i).pred (extendConfig G sigma) then bernWeight p sigma else 0 := by
    calc
      s.sum (fun i => Prob p (F i))
          = s.sum (fun i =>
              ProbOn p G (fun sigma : G -> Bool =>
                (F i).pred (extendConfig G sigma))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact prob_support_mono (F i) (hFsub i hi)
      _ = s.sum (fun i =>
            Finset.univ.sum fun sigma : G -> Bool =>
              if (F i).pred (extendConfig G sigma) then bernWeight p sigma else 0) := rfl
      _ = Finset.univ.sum fun sigma : G -> Bool =>
            s.sum fun i =>
              if (F i).pred (extendConfig G sigma) then bernWeight p sigma else 0 := by
            rw [Finset.sum_comm]
  have hpoint :
      forall sigma : G -> Bool,
        s.sum (fun i =>
            if (F i).pred (extendConfig G sigma) then bernWeight p sigma else 0) <=
          if E.pred (extendConfig G sigma) then bernWeight p sigma else 0 := by
    intro sigma
    let omega : Config d := extendConfig G sigma
    let w : Real := bernWeight p sigma
    have hw : 0 <= w := bernWeight_nonneg hp0 hp1 sigma
    by_cases hE : E.pred omega
    · by_cases hex : exists i, i ∈ s /\ (F i).pred omega
      · rcases hex with ⟨i0, hi0, hFi0⟩
        have hsum :
            s.sum (fun i => if (F i).pred omega then w else 0) = w := by
          calc
            s.sum (fun i => if (F i).pred omega then w else 0)
                = (if (F i0).pred omega then w else 0) := by
                  refine Finset.sum_eq_single i0 ?_ ?_
                  · intro j hj hji
                    have hnot : ¬ (F j).pred omega := by
                      intro hFj
                      exact hdisj i0 hi0 j hj (Ne.symm hji) omega hFi0 hFj
                    simp [hnot]
                  · intro hnotMem
                    exact False.elim (hnotMem hi0)
            _ = w := by simp [hFi0]
        simp [omega, w, hE, hsum]
      · have hsum :
            s.sum (fun i => if (F i).pred omega then w else 0) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hnot : ¬ (F i).pred omega := by
            intro hFi
            exact hex ⟨i, hi, hFi⟩
          simp [hnot]
        simp [omega, w, hE, hsum, hw]
    · have hsum :
          s.sum (fun i => if (F i).pred omega then w else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have hnot : ¬ (F i).pred omega := by
          intro hFi
          exact hE (himp i hi omega hFi)
        simp [hnot]
      simp [omega, w, hE, hsum]
  calc
    s.sum (fun i => Prob p (F i))
        = Finset.univ.sum fun sigma : G -> Bool =>
          s.sum fun i =>
            if (F i).pred (extendConfig G sigma) then bernWeight p sigma else 0 := hrewrite
    _ <= Finset.univ.sum fun sigma : G -> Bool =>
          if E.pred (extendConfig G sigma) then bernWeight p sigma else 0 := by
        exact Finset.sum_le_sum fun sigma _ => hpoint sigma
    _ = ProbOn p G (fun sigma : G -> Bool => E.pred (extendConfig G sigma)) := rfl
    _ = Prob p E := (prob_support_mono E hEsub).symm

private theorem phi_nonneg {d : Nat} {p : Real} (hp0 : 0 <= p) (hp1 : p <= 1)
    (S : Finset (Vertex d)) : 0 <= phi p S := by
  classical
  unfold phi
  refine mul_nonneg hp0 ?_
  refine Finset.sum_nonneg ?_
  intro e _he
  exact prob_nonneg hp0 hp1 (connInEvent S (0 : Vertex d) e.1)

private theorem phiMinIn_nonneg {d : Nat} {p : Real} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) (hp0 : 0 <= p) (hp1 : p <= 1) :
    0 <= phiMinIn p Lam h0 := by
  classical
  unfold phiMinIn
  refine Finset.le_inf' _ _ ?_
  intro S _hS
  exact phi_nonneg hp0 hp1 S

private theorem subset_of_mem_finiteSubsetsWithZero {d : Nat}
    {Lam S : Finset (Vertex d)} (hS : S ∈ finiteSubsetsWithZero Lam) :
    S <= Lam := by
  classical
  exact (Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1)

private theorem zero_mem_of_mem_finiteSubsetsWithZero {d : Nat}
    {Lam S : Finset (Vertex d)} (hS : S ∈ finiteSubsetsWithZero Lam) :
    (0 : Vertex d) ∈ S := by
  classical
  exact (Finset.mem_filter.mp hS).2

private theorem prob_exit_compl_eq {d : Nat} {p : Real} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p ((exitEvent Lam h0).compl) = 1 - exitProb p Lam h0 := by
  unfold exitProb Prob
  exact probOn_compl hp0 hp1

private theorem one_sub_exitProb_le_sum_shield {d : Nat} {p : Real}
    (Lam : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Lam)
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    1 - exitProb p Lam h0 <=
      (finiteSubsetsWithZero Lam).attach.sum
        (fun S => Prob p (shieldEvent Lam S.1
          (subset_of_mem_finiteSubsetsWithZero S.2))) := by
  classical
  let Sset : Finset (Finset (Vertex d)) := finiteSubsetsWithZero Lam
  let shieldFor : {S // S ∈ Sset} -> LocalEvent d := fun S =>
    shieldEvent Lam S.1 (subset_of_mem_finiteSubsetsWithZero S.2)
  have hcompl :
      1 - exitProb p Lam h0 = Prob p ((exitEvent Lam h0).compl) :=
    (prob_exit_compl_eq Lam h0 hp0 hp1).symm
  rw [hcompl]
  have himp :
      forall omega,
        ((exitEvent Lam h0).compl).pred omega ->
          (finsetUnionEvent Sset.attach shieldFor).pred omega := by
    intro omega hnotExit
    have hmem : Shield Lam omega ∈ Sset := by
      change Shield Lam omega ∈ finiteSubsetsWithZero Lam
      rw [finiteSubsetsWithZero, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro x hx
        have hx' : x ∈ Lam.filter fun y => ¬ ExitFromPred Lam y omega := by
          simpa [Shield] using hx
        exact (Finset.mem_filter.mp hx').1
      · exact (zero_mem_shield_iff_not_exit Lam h0 omega).mpr hnotExit
    refine ⟨⟨Shield Lam omega, hmem⟩, by simp, ?_⟩
    rfl
  calc
    Prob p ((exitEvent Lam h0).compl)
        <= Prob p (finsetUnionEvent Sset.attach shieldFor) :=
      prob_le_of_pred_imp hp0 hp1 _ _ himp
    _ <= Sset.attach.sum fun S => Prob p (shieldFor S) :=
      prob_finsetUnionEvent_le_sum hp0 hp1 Sset.attach shieldFor

private theorem bondOfAdj_mem_exitSupport_of_boundary_subset {d : Nat}
    {Lam S : Finset (Vertex d)} (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    {e : OrientedEdge d} (he : e ∈ orientedBoundary S) :
    bondOfAdj (orientedBoundary_adj he) ∈ (exitEvent Lam (hS h0S)).support := by
  classical
  dsimp [exitEvent]
  by_cases hyLam : e.2 ∈ Lam
  · exact Finset.mem_union.mpr (Or.inl
      (bondOfAdj_mem_internalBonds (hS (mem_orientedBoundary_iff.mp he).1)
        hyLam (orientedBoundary_adj he)))
  · have heLam : e ∈ orientedBoundary Lam :=
      mem_orientedBoundary_iff.mpr
        ⟨hS (mem_orientedBoundary_iff.mp he).1, hyLam, orientedBoundary_adj he⟩
    exact Finset.mem_union.mpr (Or.inr (bondOfAdj_mem_exitBonds heLam))

private theorem orientedBoundary_bond_injective {d : Nat}
    {S : Finset (Vertex d)} {e f : OrientedEdge d}
    (he : e ∈ orientedBoundary S) (hf : f ∈ orientedBoundary S)
    (hbond : bondOfAdj (orientedBoundary_adj he) =
      bondOfAdj (orientedBoundary_adj hf)) : e = f := by
  classical
  have hcar := congrArg Bond.carrier hbond
  change ({e.1, e.2} : Finset (Vertex d)) =
      ({f.1, f.2} : Finset (Vertex d)) at hcar
  have he1mem : e.1 ∈ ({f.1, f.2} : Finset (Vertex d)) := by
    rw [← hcar]
    simp
  have he2mem : e.2 ∈ ({f.1, f.2} : Finset (Vertex d)) := by
    rw [← hcar]
    simp
  have he1_eq_f1 : e.1 = f.1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he1mem
    rcases he1mem with h | h
    · exact h
    · exact False.elim ((mem_orientedBoundary_iff.mp hf).2.1
        (by simpa [h] using (mem_orientedBoundary_iff.mp he).1))
  have he2_eq_f2 : e.2 = f.2 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at he2mem
    rcases he2mem with h | h
    · exact False.elim ((mem_orientedBoundary_iff.mp he).2.1
        (by simpa [h] using (mem_orientedBoundary_iff.mp hf).1))
    · exact h
  exact Prod.ext he1_eq_f1 he2_eq_f2

private theorem conn_shield_prob_eq_mul {d : Nat} {p : Real}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam)
    (e : {e // e ∈ orientedBoundary S})
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p ((connInEvent S (0 : Vertex d) e.1.1).inter (shieldEvent Lam S hS)) =
      Prob p (connInEvent S (0 : Vertex d) e.1.1) *
        Prob p (shieldEvent Lam S hS) := by
  classical
  exact prob_inter_eq_mul_of_disjoint
    (connInEvent S (0 : Vertex d) e.1.1)
    (shieldEvent Lam S hS)
    (disjoint_internalBonds_shieldSupport Lam S)
    hp0 hp1

private theorem conn_shield_le_closedPivotal_shield {d : Nat} {p : Real}
    (Lam S : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Lam)
    (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    (e : {e // e ∈ orientedBoundary S}) (hp0 : 0 <= p) (hp1 : p <= 1) :
    Prob p ((connInEvent S (0 : Vertex d) e.1.1).inter (shieldEvent Lam S hS)) <=
      Prob p (((closedPivotalEvent (exitEvent Lam h0)
        (bondOfAdj (orientedBoundary_adj e.2))).inter (shieldEvent Lam S hS))) := by
  classical
  refine prob_le_of_pred_imp hp0 hp1 _ _ ?_
  intro omega h
  rcases h with ⟨hconn, hshield⟩
  have hpiv' :
      ClosedPivotal (exitEvent Lam (hS h0S))
          (bondOfAdj (orientedBoundary_adj e.2)) omega :=
    (closedPivotal_exit_iff_connIn_on_shield Lam S hS h0S e.2 hshield).mpr hconn
  have hpiv :
      ClosedPivotal (exitEvent Lam h0)
          (bondOfAdj (orientedBoundary_adj e.2)) omega := by
    simpa [ClosedPivotal, exitEvent] using hpiv'
  exact ⟨hpiv, hshield⟩

private theorem shield_phiMin_div_mul_le_boundary_pivotal {d : Nat} {p : Real}
    (Lam S : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Lam)
    (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    (hp0 : 0 < p) (hp1 : p <= 1) :
    (phiMinIn p Lam h0 / p) * Prob p (shieldEvent Lam S hS) <=
      (orientedBoundary S).attach.sum
        (fun e => Prob p (((closedPivotalEvent (exitEvent Lam h0)
          (bondOfAdj (orientedBoundary_adj e.2))).inter (shieldEvent Lam S hS)))) := by
  classical
  have hp0le : 0 <= p := hp0.le
  have hshield_nonneg : 0 <= Prob p (shieldEvent Lam S hS) :=
    prob_nonneg hp0le hp1 _
  have hmin_le : phiMinIn p Lam h0 <= phi p S :=
    phiMinIn_le_phi h0 hS h0S
  have hcoef_le : phiMinIn p Lam h0 / p <= phi p S / p := by
    exact div_le_div_of_nonneg_right hmin_le hp0le
  have hphi_div :
      phi p S / p =
        (orientedBoundary S).sum
          (fun e => Prob p (connInEvent S (0 : Vertex d) e.1)) := by
    unfold phi
    field_simp [ne_of_gt hp0]
  calc
    (phiMinIn p Lam h0 / p) * Prob p (shieldEvent Lam S hS)
        <= (phi p S / p) * Prob p (shieldEvent Lam S hS) :=
      mul_le_mul_of_nonneg_right hcoef_le hshield_nonneg
    _ =
        (orientedBoundary S).attach.sum
          (fun e =>
            Prob p (connInEvent S (0 : Vertex d) e.1.1) *
              Prob p (shieldEvent Lam S hS)) := by
      rw [hphi_div]
      calc
        ((orientedBoundary S).sum
            (fun e => Prob p (connInEvent S (0 : Vertex d) e.1))) *
            Prob p (shieldEvent Lam S hS)
            =
          (orientedBoundary S).sum
            (fun e =>
              Prob p (connInEvent S (0 : Vertex d) e.1) *
                Prob p (shieldEvent Lam S hS)) := by
            rw [Finset.sum_mul]
        _ =
          (orientedBoundary S).attach.sum
            (fun e =>
              Prob p (connInEvent S (0 : Vertex d) e.1.1) *
                Prob p (shieldEvent Lam S hS)) := by
            exact (Finset.sum_attach (orientedBoundary S)
              (fun e =>
                Prob p (connInEvent S (0 : Vertex d) e.1) *
                  Prob p (shieldEvent Lam S hS))).symm
    _ =
        (orientedBoundary S).attach.sum
          (fun e =>
            Prob p ((connInEvent S (0 : Vertex d) e.1.1).inter
              (shieldEvent Lam S hS))) := by
      refine Finset.sum_congr rfl ?_
      intro e _he
      rw [conn_shield_prob_eq_mul Lam S hS e hp0le hp1]
    _ <=
        (orientedBoundary S).attach.sum
          (fun e => Prob p (((closedPivotalEvent (exitEvent Lam h0)
            (bondOfAdj (orientedBoundary_adj e.2))).inter (shieldEvent Lam S hS)))) := by
      refine Finset.sum_le_sum ?_
      intro e _he
      exact conn_shield_le_closedPivotal_shield Lam S h0 hS h0S e hp0le hp1

private theorem boundary_pivotal_shield_sum_le_support_sum {d : Nat} {p : Real}
    (Lam S : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Lam)
    (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    (hp0 : 0 <= p) (hp1 : p <= 1) :
    (orientedBoundary S).attach.sum
        (fun e => Prob p (((closedPivotalEvent (exitEvent Lam h0)
          (bondOfAdj (orientedBoundary_adj e.2))).inter (shieldEvent Lam S hS)))) <=
      (exitEvent Lam h0).support.sum
        (fun b => Prob p (((closedPivotalEvent (exitEvent Lam h0) b).inter
          (shieldEvent Lam S hS)))) := by
  classical
  let bOf : {e // e ∈ orientedBoundary S} -> Bond d := fun e =>
    bondOfAdj (orientedBoundary_adj e.2)
  let f : Bond d -> Real := fun b =>
    Prob p (((closedPivotalEvent (exitEvent Lam h0) b).inter (shieldEvent Lam S hS)))
  have hinj : Set.InjOn bOf (orientedBoundary S).attach := by
    intro e _he f' _hf hbond
    apply Subtype.ext
    exact orientedBoundary_bond_injective e.2 f'.2 hbond
  have hsub : (orientedBoundary S).attach.image bOf <= (exitEvent Lam h0).support := by
    intro b hb
    rcases Finset.mem_image.mp hb with ⟨e, _heAttach, rfl⟩
    have hb' :
        bondOfAdj (orientedBoundary_adj e.2) ∈
          (exitEvent Lam (hS h0S)).support :=
      bondOfAdj_mem_exitSupport_of_boundary_subset hS h0S e.2
    simpa [exitEvent] using hb'
  have himage :
      ((orientedBoundary S).attach.image bOf).sum f =
        (orientedBoundary S).attach.sum (fun e => f (bOf e)) :=
    Finset.sum_image (s := (orientedBoundary S).attach) (g := bOf) (f := f) hinj
  calc
    (orientedBoundary S).attach.sum
        (fun e => Prob p (((closedPivotalEvent (exitEvent Lam h0)
          (bondOfAdj (orientedBoundary_adj e.2))).inter (shieldEvent Lam S hS))))
        = (orientedBoundary S).attach.sum (fun e => f (bOf e)) := rfl
    _ = ((orientedBoundary S).attach.image bOf).sum f := himage.symm
    _ <= (exitEvent Lam h0).support.sum f := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub
        (by
          intro b _hbSupport _hbNotImage
          exact prob_nonneg hp0 hp1 _)

private theorem shield_phiMin_div_mul_le_support_pivotal {d : Nat} {p : Real}
    (Lam S : Finset (Vertex d)) (h0 : (0 : Vertex d) ∈ Lam)
    (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    (hp0 : 0 < p) (hp1 : p <= 1) :
    (phiMinIn p Lam h0 / p) * Prob p (shieldEvent Lam S hS) <=
      (exitEvent Lam h0).support.sum
        (fun b => Prob p (((closedPivotalEvent (exitEvent Lam h0) b).inter
          (shieldEvent Lam S hS)))) := by
  exact (shield_phiMin_div_mul_le_boundary_pivotal Lam S h0 hS h0S hp0 hp1).trans
    (boundary_pivotal_shield_sum_le_support_sum Lam S h0 hS h0S hp0.le hp1)

/--
The shield decomposition lower bound for the Russo closed-pivotal sum.

The proof decomposes over finite shield values containing the origin, uses pivotal
equivalence on each oriented shield boundary edge, applies the separated-support
independence between internal `S` connections and `{Shield = S}`, and then
partitions the closed-pivotal events by the shield value.
-/
theorem exit_russo_sum_lower_bound {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) <=
      (1 / (1 - p)) *
        ((exitEvent Lam h0).support.sum
          fun e => Prob p (closedPivotalEvent (exitEvent Lam h0) e)) := by
  classical
  have hp0le : 0 <= p := hp0.le
  have hp1le : p <= 1 := hp1.le
  let Sset : Finset (Finset (Vertex d)) := finiteSubsetsWithZero Lam
  let shieldFor : {S // S ∈ Sset} -> LocalEvent d := fun S =>
    shieldEvent Lam S.1 (subset_of_mem_finiteSubsetsWithZero S.2)
  let cpEvent : Bond d -> LocalEvent d := fun b =>
    closedPivotalEvent (exitEvent Lam h0) b
  let cpShield : Bond d -> {S // S ∈ Sset} -> LocalEvent d := fun b S =>
    (cpEvent b).inter (shieldFor S)
  let m : Real := phiMinIn p Lam h0
  let q : Real := 1 - exitProb p Lam h0
  let R : Real := (exitEvent Lam h0).support.sum fun b => Prob p (cpEvent b)
  change (1 / (p * (1 - p))) * m * q <= (1 / (1 - p)) * R
  have hnonexit :
      q <= Sset.attach.sum fun S => Prob p (shieldFor S) := by
    simpa [q, Sset, shieldFor] using
      one_sub_exitProb_le_sum_shield Lam h0 hp0le hp1le
  have hm_nonneg : 0 <= m := by
    simpa [m] using phiMinIn_nonneg Lam h0 hp0le hp1le
  have hcoef_nonneg : 0 <= m / p := div_nonneg hm_nonneg hp0le
  have hbase :
      (m / p) * q <=
        Sset.attach.sum
          (fun S => (exitEvent Lam h0).support.sum fun b => Prob p (cpShield b S)) := by
    calc
      (m / p) * q
          <= (m / p) * (Sset.attach.sum fun S => Prob p (shieldFor S)) :=
        mul_le_mul_of_nonneg_left hnonexit hcoef_nonneg
      _ =
          Sset.attach.sum
            (fun S => (m / p) * Prob p (shieldFor S)) := by
        rw [Finset.mul_sum]
      _ <=
          Sset.attach.sum
            (fun S => (exitEvent Lam h0).support.sum fun b => Prob p (cpShield b S)) := by
        refine Finset.sum_le_sum ?_
        intro S _hS
        exact shield_phiMin_div_mul_le_support_pivotal Lam S.1 h0
          (subset_of_mem_finiteSubsetsWithZero S.2)
          (zero_mem_of_mem_finiteSubsetsWithZero S.2) hp0 hp1le
  have hpartition :
      Sset.attach.sum
          (fun S => (exitEvent Lam h0).support.sum fun b => Prob p (cpShield b S)) <=
        R := by
    dsimp [R]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum ?_
    intro b hb
    refine sum_prob_le_prob_of_disjoint_subevents hp0le hp1le Sset.attach
      (cpEvent b) (fun S => cpShield b S) ?_ ?_
    · intro S _hS T _hT hne omega hS hT
      have hshieldS : (shieldFor S).pred omega := hS.2
      have hshieldT : (shieldFor T).pred omega := hT.2
      have hval : S.1 = T.1 := hshieldS.symm.trans hshieldT
      exact hne (Subtype.ext hval)
    · intro S _hS omega h
      exact h.1
  have hinner : (m / p) * q <= R := hbase.trans hpartition
  have hden_pos : 0 < 1 - p := sub_pos.mpr hp1
  have hfactor_nonneg : 0 <= 1 / (1 - p) := by
    exact one_div_nonneg.mpr hden_pos.le
  calc
    (1 / (p * (1 - p))) * m * q
        = (1 / (1 - p)) * ((m / p) * q) := by
      field_simp [ne_of_gt hp0, ne_of_gt hden_pos]
    _ <= (1 / (1 - p)) * R :=
      mul_le_mul_of_nonneg_left hinner hfactor_nonneg

/-- Lemma 2, the fundamental finite-volume differential inequality. -/
theorem differential_inequality {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    deriv (fun q => exitProb q Lam h0) p >=
      (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) := by
  classical
  have hRusso := russo_closed_pivotal (exitEvent Lam h0)
    (exitEvent_increasing Lam h0) hp0 hp1
  have hderiv :
      deriv (fun q => Prob q (exitEvent Lam h0)) p =
        (1 / (1 - p)) *
          ((exitEvent Lam h0).support.sum
            fun e => Prob p (closedPivotalEvent (exitEvent Lam h0) e)) :=
    hRusso.deriv
  change
    (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) <=
      deriv (fun q => Prob q (exitEvent Lam h0)) p
  rw [hderiv]
  exact exit_russo_sum_lower_bound Lam h0 hp0 hp1

end Sharpness
