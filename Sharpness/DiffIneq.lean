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

/--
Pivotal equivalence on a fixed shield value.

Missing mathematical fact: prove the boundary-edge argument from the note: on
`{Shield = S}`, an oriented boundary bond `(x,y) ∈ ∂E S` is closed-pivotal for
`A_Lam` iff `0` is connected to `x` inside `S`.
-/
theorem closedPivotal_exit_iff_connIn_on_shield {d : Nat}
    (Lam S : Finset (Vertex d)) (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S)
    {e : OrientedEdge d} (he : e ∈ orientedBoundary S) {omega : Config d}
    (hshield : Shield Lam omega = S) :
    ClosedPivotal (exitEvent Lam (hS h0S))
        (bondOfAdj (orientedBoundary_adj he)) omega <->
      ConnIn omega S (0 : Vertex d) e.1 := by
  sorry

/-- The finite minimum is below each admissible `phi p S`. -/
theorem phiMinIn_le_phi {d : Nat} {p : Real} {Lam S : Finset (Vertex d)}
    (h0 : (0 : Vertex d) ∈ Lam) (hS : S <= Lam) (h0S : (0 : Vertex d) ∈ S) :
    phiMinIn p Lam h0 <= phi p S := by
  classical
  exact Finset.inf'_le (f := phi p)
    (by
      rw [finiteSubsetsWithZero, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hS, h0S⟩)

/--
The shield decomposition lower bound for the Russo closed-pivotal sum.

Missing mathematical fact: formalize the finite sum decomposition over shield values, use
`closedPivotal_exit_iff_connIn_on_shield`, apply disjoint-support independence from
`shield_dependsOn_noninternal`, identify the boundary sum with `phi p S / p`, and sum
`Prob(Shield = S)` over `0 ∈ S` to get `1 - exitProb p Lam h0`.
-/
theorem exit_russo_sum_lower_bound {d : Nat} (Lam : Finset (Vertex d))
    (h0 : (0 : Vertex d) ∈ Lam) {p : Real} (hp0 : 0 < p) (hp1 : p < 1) :
    (1 / (p * (1 - p))) * phiMinIn p Lam h0 * (1 - exitProb p Lam h0) <=
      (1 / (1 - p)) *
        ((exitEvent Lam h0).support.sum
          fun e => Prob p (closedPivotalEvent (exitEvent Lam h0) e)) := by
  sorry

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
