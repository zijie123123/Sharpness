import Sharpness.Subcritical
import Sharpness.Supercritical

namespace Sharpness

/-- The percolation critical point defined from `theta`. -/
noncomputable def pCrit (d : Nat) : Real :=
  sInf {p : Real | 0 <= p /\ p <= 1 /\ 0 < theta d p}

private theorem pCritSet_bddBelow (d : Nat) :
    BddBelow {p : Real | 0 <= p /\ p <= 1 /\ 0 < theta d p} :=
  ⟨0, by
    intro p hp
    exact hp.1⟩

private theorem bernWeight_one_of_all_true {α : Type*} [Fintype α]
    (sigma : α -> Bool) (hsigma : forall e, sigma e = true) :
    bernWeight (1 : Real) sigma = 1 := by
  classical
  dsimp [bernWeight]
  simp [hsigma]

private theorem bernWeight_one_of_exists_false {α : Type*} [Fintype α]
    (sigma : α -> Bool) (hsigma : exists e, sigma e = false) :
    bernWeight (1 : Real) sigma = 0 := by
  classical
  rcases hsigma with ⟨e, he⟩
  dsimp [bernWeight]
  exact Finset.prod_eq_zero (Finset.mem_univ e) (by simp [he])

private theorem exists_false_of_ne_all_true {α : Type*} (sigma : α -> Bool)
    (hne : sigma ≠ fun _ => true) :
    exists e, sigma e = false := by
  classical
  by_contra hnot
  apply hne
  funext e
  cases hs : sigma e
  · exfalso
    exact hnot ⟨e, hs⟩
  · rfl

private theorem local_prob_one_of_all_true {d : Nat} (E : LocalEvent d)
    (htrue : E.pred (extendConfig E.support (fun _ : E.support => true))) :
    Prob (1 : Real) E = 1 := by
  classical
  let sigma1 : E.support -> Bool := fun _ => true
  dsimp [Prob, ProbOn, bernProb]
  rw [Finset.sum_eq_single sigma1]
  · simp [sigma1, htrue, bernWeight_one_of_all_true]
  · intro sigma _hsigma hne
    have hex : exists e, sigma e = false := exists_false_of_ne_all_true sigma hne
    by_cases hA : E.pred (extendConfig E.support sigma)
    · simp [hA, bernWeight_one_of_exists_false sigma hex]
    · simp [hA]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ sigma1))

private def axisVertex {d : Nat} (i : Fin d) (k : Nat) : Vertex d :=
  fun j => if j = i then (k : Int) else 0

private theorem axisVertex_zero {d : Nat} (i : Fin d) :
    axisVertex i 0 = (0 : Vertex d) := by
  funext j
  simp [axisVertex]

private theorem axisVertex_l1 {d : Nat} (i : Fin d) (k : Nat) :
    l1 (axisVertex i k) = k := by
  classical
  unfold axisVertex l1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private theorem axisVertex_adj_succ {d : Nat} (i : Fin d) (k : Nat) :
    Adj (axisVertex i k) (axisVertex i (k + 1)) := by
  classical
  unfold Adj axisVertex l1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

private theorem List_range_succ_head (n : Nat) :
    (List.range (n + 1)).head? = some 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [show n.succ + 1 = Nat.succ (n + 1) by omega]
      rw [List.range_succ]
      rw [List.head?_append]
      simp [ih]

private theorem axisPath_isPath {d : Nat} (i : Fin d) (n : Nat) :
    IsPath ((List.range (n + 1)).map (axisVertex i)) := by
  rw [IsPath, List.isChain_map]
  rw [show n + 1 = n.succ by omega]
  rw [List.isChain_range_succ]
  intro m _hm
  simpa [Nat.succ_eq_add_one] using axisVertex_adj_succ (d := d) i m

private theorem axisPath_head {d : Nat} (i : Fin d) (n : Nat) :
    ((List.range (n + 1)).map (axisVertex i)).head? = some (0 : Vertex d) := by
  rw [List.head?_map, List_range_succ_head n]
  simp [axisVertex_zero]

private theorem axisPath_last {d : Nat} (i : Fin d) (n : Nat) :
    ((List.range (n + 1)).map (axisVertex i)).getLast? = some (axisVertex i n) := by
  rw [List.getLast?_map, List.getLast?_range]
  simp

private theorem axisPath_pathFromTo {d : Nat} (i : Fin d) (n : Nat) :
    PathFromTo ((List.range (n + 1)).map (axisVertex i))
      (0 : Vertex d) (axisVertex i n) := by
  exact ⟨axisPath_head i n, axisPath_last i n, axisPath_isPath i n⟩

private theorem axisPath_pathIn {d : Nat} (i : Fin d) (n : Nat) :
    PathIn (ball d n) ((List.range (n + 1)).map (axisVertex i)) := by
  intro z hz
  rcases List.mem_map.mp hz with ⟨k, hk, rfl⟩
  rw [mem_ball_iff, axisVertex_l1]
  rw [List.mem_range] at hk
  omega

private theorem axisPath_open_extend_exitSupport {d : Nat} (i : Fin d) (n : Nat) :
    OpenPath
      (extendConfig (exitEvent (ball d n) (zero_mem_ball d n)).support (fun _ => true))
      ((List.range (n + 1)).map (axisVertex i)) := by
  change List.IsChain
    (fun x y => exists hxy : Adj x y,
      extendConfig (exitEvent (ball d n) (zero_mem_ball d n)).support (fun _ => true)
        (bondOfAdj hxy) = true)
    ((List.range (n + 1)).map (axisVertex i))
  rw [List.isChain_map]
  rw [show n + 1 = n.succ by omega]
  rw [List.isChain_range_succ]
  intro m hm
  let hxy : Adj (axisVertex i m) (axisVertex i m.succ) := by
    simpa [Nat.succ_eq_add_one] using axisVertex_adj_succ (d := d) i m
  refine ⟨hxy, ?_⟩
  have hmle : m <= n := by omega
  have hmsle : m.succ <= n := by omega
  have hx : axisVertex i m ∈ ball d n := by
    rw [mem_ball_iff, axisVertex_l1]
    exact hmle
  have hy : axisVertex i m.succ ∈ ball d n := by
    rw [mem_ball_iff, axisVertex_l1]
    exact hmsle
  have hb : bondOfAdj hxy ∈ internalBonds (ball d n) :=
    bondOfAdj_mem_internalBonds hx hy hxy
  have hsupp : bondOfAdj hxy ∈ (exitEvent (ball d n) (zero_mem_ball d n)).support := by
    exact Finset.mem_union.mpr (Or.inl hb)
  simp [extendConfig, hsupp]

private theorem exitPred_all_open_support {d : Nat} (hd : 0 < d) (n : Nat) :
    ExitPred (ball d n)
      (extendConfig (exitEvent (ball d n) (zero_mem_ball d n)).support (fun _ => true)) := by
  classical
  let i : Fin d := ⟨0, hd⟩
  let e : OrientedEdge d := (axisVertex i n, axisVertex i (n + 1))
  have hx : e.1 ∈ ball d n := by
    rw [mem_ball_iff]
    dsimp [e]
    rw [axisVertex_l1]
  have hy : e.2 ∉ ball d n := by
    rw [mem_ball_iff]
    dsimp [e]
    rw [axisVertex_l1]
    omega
  have hxy : Adj e.1 e.2 := by
    dsimp [e]
    exact axisVertex_adj_succ i n
  have he : e ∈ orientedBoundary (ball d n) :=
    mem_orientedBoundary_iff.mpr ⟨hx, hy, hxy⟩
  refine ⟨e, he, ?_, ?_⟩
  · refine ⟨(List.range (n + 1)).map (axisVertex i), axisPath_pathFromTo i n,
      axisPath_pathIn i n, axisPath_open_extend_exitSupport i n⟩
  · have hb :
        bondOfAdj (orientedBoundary_adj he) ∈
          (exitEvent (ball d n) (zero_mem_ball d n)).support := by
      exact Finset.mem_union.mpr (Or.inr (bondOfAdj_mem_exitBonds he))
    simp [extendConfig, hb]

private theorem boxExitProb_one_of_pos_dim {d : Nat} (hd : 0 < d) (n : Nat) :
    boxExitProb d (1 : Real) n = 1 := by
  unfold boxExitProb exitProb
  exact local_prob_one_of_all_true (exitEvent (ball d n) (zero_mem_ball d n))
    (exitPred_all_open_support hd n)

private theorem pCritSet_nonempty_of_pos_dim {d : Nat} (_hd : 0 < d) :
    ({p : Real | 0 <= p /\ p <= 1 /\ 0 < theta d p} : Set Real).Nonempty := by
  refine ⟨1, by norm_num, by norm_num, ?_⟩
  have hle : (1 : Real) <= theta d 1 := by
    refine le_theta_of_le_boxExitProb ?_
    intro n
    rw [boxExitProb_one_of_pos_dim _hd n]
  linarith

private theorem pCrit_le_one (d : Nat) : pCrit d <= 1 := by
  classical
  unfold pCrit
  let A : Set Real := {p : Real | 0 <= p /\ p <= 1 /\ 0 < theta d p}
  change sInf A <= 1
  by_cases hne : A.Nonempty
  · rcases hne with ⟨p, hp⟩
    have hbdd : BddBelow A := ⟨0, by
      intro q hq
      exact hq.1⟩
    exact (csInf_le hbdd hp).trans hp.2.1
  · have hempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp

private theorem pCrit_le_of_mem {d : Nat} {p : Real}
    (hp : 0 <= p /\ p <= 1 /\ 0 < theta d p) : pCrit d <= p := by
  unfold pCrit
  exact csInf_le (pCritSet_bddBelow d) hp

private theorem pCrit_le_pTilde (d : Nat) : pCrit d <= pTilde d := by
  classical
  by_cases htop : pTilde d = 1
  · exact (pCrit_le_one d).trans_eq htop.symm
  · have hpt1 : pTilde d < 1 := lt_of_le_of_ne (pTilde_le_one d) htop
    by_contra hnot
    have hlt : pTilde d < pCrit d := lt_of_not_ge hnot
    let q : Real := (pTilde d + pCrit d) / 2
    have hptq : pTilde d < q := by
      dsimp [q]
      linarith
    have hqcrit : q < pCrit d := by
      dsimp [q]
      linarith
    have hq1 : q < 1 := lt_of_lt_of_le hqcrit (pCrit_le_one d)
    have hq0 : 0 <= q := (zero_le_pTilde d).trans hptq.le
    have htheta :=
      supercritical_lower_bound_above_pTilde (d := d) (p := q) hptq hq1
    have hrhs_pos : 0 < (q - pTilde d) / (q * (1 - pTilde d)) := by
      have hqpos : 0 < q := lt_of_le_of_lt (zero_le_pTilde d) hptq
      have hnum : 0 < q - pTilde d := sub_pos.mpr hptq
      have hden : 0 < q * (1 - pTilde d) := mul_pos hqpos (sub_pos.mpr hpt1)
      exact div_pos hnum hden
    have htheta_pos : 0 < theta d q := lt_of_lt_of_le hrhs_pos htheta
    have hmem : 0 <= q /\ q <= 1 /\ 0 < theta d q := ⟨hq0, hq1.le, htheta_pos⟩
    have hpcleq : pCrit d <= q := pCrit_le_of_mem hmem
    exact not_lt_of_ge hpcleq hqcrit

private theorem pTilde_le_pCrit {d : Nat} (hd : 0 < d) : pTilde d <= pCrit d := by
  classical
  unfold pCrit
  refine le_csInf (pCritSet_nonempty_of_pos_dim hd) ?_
  intro q hq
  rcases hq with ⟨hq0, hq1, htheta_pos⟩
  by_contra hnot
  have hq_lt : q < pTilde d := lt_of_not_ge hnot
  rcases exponential_decay_below_pTilde (d := d) (p := q) hq0 hq_lt with
    ⟨c, hc, hdecay⟩
  have htheta0 : theta d q = 0 := theta_eq_zero_of_exponential_decay hq0 hq1 hc hdecay
  rw [htheta0] at htheta_pos
  exact (lt_irrefl (0 : Real)) htheta_pos

/-- The finite-set critical point equals the `theta` critical point in nontrivial dimension. -/
theorem pTilde_eq_pCrit {d : Nat} (hd : 0 < d) : pTilde d = pCrit d := by
  exact le_antisymm (pTilde_le_pCrit hd) (pCrit_le_pTilde d)

/-- Subcritical exponential decay rewritten with `pCrit`. -/
theorem exponential_decay_below_pCrit {d : Nat} {p : Real}
    (hd : 0 < d) (hp0 : 0 <= p) (hp : p < pCrit d) :
    exists c : Real, 0 < c /\
      forall n : Nat, boxExitProb d p n <= Real.exp (-(c * (n : Real))) := by
  have hpTilde : p < pTilde d := by
    simpa [pTilde_eq_pCrit (d := d) hd] using hp
  exact exponential_decay_below_pTilde (d := d) hp0 hpTilde

/-- Supercritical density lower bound rewritten with `pCrit`. -/
theorem supercritical_lower_bound_above_pCrit {d : Nat} {p : Real}
    (hd : 0 < d) (hp : pCrit d < p) (hp1 : p < 1) :
    theta d p >= (p - pCrit d) / (p * (1 - pCrit d)) := by
  have hpTilde : pTilde d < p := by
    simpa [pTilde_eq_pCrit (d := d) hd] using hp
  simpa [pTilde_eq_pCrit (d := d) hd] using
    supercritical_lower_bound_above_pTilde (d := d) (p := p) hpTilde hp1

end Sharpness
