module

public import GraphMinor.Compute.CrossingCleanInit
public import GraphMinor.Crossing.CutSec2Fan
public import GraphMinor.Crossing.CutSec3
public import GraphMinor.Crossing.LinkLift

/-!
# Strengthened Initial Cleaning (Part 1: Counterexample and Phase 1)

`InitialCleaningRecProgClaim` (`GraphMinor/Compute/SpecsCrossingRec.lean`) states that
initial cleaning produces a clean instance `(G', S', D)` with `IsHistoryFin G S D recs G' S' D`
and `ContractionsLong recs`. Because `IsHistory` permits `CrossRecord.del G₁ S₁` records (which
only require `G₁ ≤ G` and `D` to remain a cycle in `G₁`), the postcondition of
`InitialCleaningRecProgClaim` implies the reverse implication
`HP25.IsCrossed G' D → HP25.IsCrossed G D` (via `liftHistory_proved`), but does **not** imply the
forward implication `HP25.IsCrossed G D → HP25.IsCrossed G' D` needed when `Classify` returns `0`
(`NO`, `¬ HP25.IsCrossed G' D`).

In fact, `initialCleaningProg` (`GraphMinor/Compute/CrossingCleanInit.lean`) only appends valid
`CrossRecord.repl r` records, each of which preserves `HP25.IsCrossed` in the forward direction by
`lemma1Forward_proved` (`GraphMinor/Crossing/CutSec3.lean`).

This file:
* proves `not_isCrossed_of_initialCleaning_postcond` on `Fin 4`: a concrete counterexample
  (`G = ⊤`, `D = [0, 1, 2, 3]`, `G'` the 4-cycle without diagonals, `recs = [CrossRecord.del G' S']`)
  satisfying all postconditions of `InitialCleaningRecProgClaim` while `HP25.IsCrossed G D` holds
  and `HP25.IsCrossed G' D` is false;
* defines `AllRepl recs` (every record in `recs` is a `CrossRecord.repl`) and proves
  `isCrossed_iff_of_allRepl` (`HP25.IsCrossed G D ↔ HP25.IsCrossed G' D` for any history of
  replacement records);
* proves `phase1BodyProg_exec_full` and `phase1Prog_exec_full`, adding `AllRepl recs₁` to
  `phase1Prog_exec`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### 1. Counterexample to forward crossing preservation from `IsHistoryFin` alone -/

/-- The 4-cycle `0 - 1 - 2 - 3 - 0` on `Fin 4` without diagonals. -/
def cleanCounterCycleGraph : SimpleGraph (Fin 4) where
  Adj a b :=
    (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨
    (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
    (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨
    (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3)
  symm := ⟨fun _ _ h => by tauto⟩
  loopless := ⟨fun a h => by revert a h; decide⟩

instance : DecidableRel cleanCounterCycleGraph.Adj := fun a b => by
  change Decidable ((a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) ∨ (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) ∨
    (a = 2 ∧ b = 3) ∨ (a = 3 ∧ b = 2) ∨ (a = 3 ∧ b = 0) ∨ (a = 0 ∧ b = 3))
  infer_instance

/-- The cycle list `D = [0, 1, 2, 3]` on `Fin 4`. -/
def cleanCounterCycle : List (Fin 4) := [0, 1, 2, 3]

private lemma mem_cleanCounterCycle (u : Fin 4) : u ∈ cleanCounterCycle := by
  revert u; decide

private lemma isClean_cleanCounterCycleGraph :
    IsClean cleanCounterCycleGraph ((Finset.univ : Finset (Fin 4)) : Set (Fin 4))
      cleanCounterCycle := by
  intro X hXsub _
  let T : Set (Option (Fin 4)) :=
    apexVerts ((Finset.univ : Finset (Fin 4)) : Set (Fin 4)) \ (X : Set (Option (Fin 4)))
  have hnone_not_X : (none : Option (Fin 4)) ∉ X := fun h => (hXsub h).2 rfl
  have hnone_mem : (none : Option (Fin 4)) ∈ T := ⟨Or.inl rfl, hnone_not_X⟩
  have hreach_none : ∀ z ∈ T, ReachIn (apex cleanCounterCycleGraph cleanCounterCycle) T z none := by
    intro z hz
    rcases z with _ | u
    · exact ReachIn.refl hnone_mem
    · have hadj : (apex cleanCounterCycleGraph cleanCounterCycle).Adj (some u) none :=
        mem_cleanCounterCycle u
      exact ⟨.cons hadj .nil, fun y hy => by
        simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
          or_false] at hy
        rcases hy with rfl | rfl
        · exact hz
        · exact hnone_mem⟩
  exact ⟨⟨none, hnone_mem⟩, fun a ha b hb =>
    (hreach_none a ha).trans (hreach_none b hb).symm⟩

private lemma isHistoryFin_cleanCounter :
    IsHistoryFin (⊤ : SimpleGraph (Fin 4)) Finset.univ cleanCounterCycle
      [CrossRecord.del cleanCounterCycleGraph ((Finset.univ : Finset (Fin 4)) : Set (Fin 4))]
      cleanCounterCycleGraph Finset.univ cleanCounterCycle := by
  refine ⟨le_top, Set.Subset.rfl, fun _ _ _ => Finset.mem_coe.mpr (Finset.mem_univ _),
    fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _), ?_, rfl⟩
  rintro a b ⟨p, hp, hp_eq⟩
  revert a b p hp hp_eq; decide

private lemma isCrossed_top_cleanCounterCycle :
    HP25.IsCrossed (⊤ : SimpleGraph (Fin 4)) cleanCounterCycle := by
  let Q : (⊤ : SimpleGraph (Fin 4)).Walk 0 2 :=
    .cons (show (⊤ : SimpleGraph (Fin 4)).Adj 0 2 by decide) .nil
  let R : (⊤ : SimpleGraph (Fin 4)).Walk 1 3 :=
    .cons (show (⊤ : SimpleGraph (Fin 4)).Adj 1 3 by decide) .nil
  refine ⟨0, 2, 1, 3, Q, R, ⟨0, 1, 2, 3, by omega, by omega, by omega, rfl, rfl, rfl, rfl⟩,
    ?_, ?_, ?_⟩
  · refine ⟨Walk.IsPath.cons .nil (by decide), by decide, by decide, ?_⟩
    intro x hx hx0 hx2
    simp only [Q, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact (hx0 rfl).elim
    · exact (hx2 rfl).elim
  · refine ⟨Walk.IsPath.cons .nil (by decide), by decide, by decide, ?_⟩
    intro x hx hx1 hx3
    simp only [R, Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hx
    rcases hx with rfl | rfl
    · exact (hx1 rfl).elim
    · exact (hx3 rfl).elim
  · intro x hxQ hxR
    revert x hxQ hxR; decide

private lemma not_isCrossed_cleanCounterCycleGraph :
    ¬ HP25.IsCrossed cleanCounterCycleGraph cleanCounterCycle := by
  rintro ⟨a, b, c, d, Q, _, ⟨i, r_idx, j, s, hir, hrj, hjs, ha, hc, hb, hd⟩, hQ, _, _⟩
  have hs_lt : s < 4 := by
    have ⟨h, _⟩ := List.getElem?_eq_some_iff.mp hd
    simpa [cleanCounterCycle] using h
  have hi0 : i = 0 := by omega
  have hj2 : j = 2 := by omega
  subst hi0 hj2
  have ha0 : a = 0 := Option.some.inj ha.symm
  have hb2 : b = 2 := Option.some.inj hb.symm
  subst ha0 hb2
  cases Q with
  | @cons _ w _ hadj Q_rest =>
    by_cases hw2 : w = 2
    · subst hw2
      exact absurd hadj (by decide)
    · have hw_supp : w ∈ (Walk.cons hadj Q_rest).support :=
        List.mem_cons_of_mem _ (Walk.start_mem_support _)
      have hw0 : w ≠ 0 := (cleanCounterCycleGraph.ne_of_adj hadj).symm
      have hw_not_D := (hQ.2.2.2 w hw_supp hw0 hw2).1
      exact hw_not_D (mem_cleanCounterCycle w)

/-- The postconditions of `InitialCleaningRecProgClaim` (`IsClean`, `IsHistoryFin`,
`ContractionsLong`, and the edge bound) do not imply the forward crossing implication
`HP25.IsCrossed G D → HP25.IsCrossed G' D`. -/
theorem not_isCrossed_of_initialCleaning_postcond :
    ∃ (G G' : SimpleGraph (Fin 4)) (S S' : Finset (Fin 4)) (D : List (Fin 4))
      (recs : List (CrossRecord (Fin 4))),
      HP25.IsSupportedOn G (S : Set (Fin 4)) ∧
      HP25.IsCycleList G D ∧
      IsClean G' (S' : Set (Fin 4)) D ∧
      IsHistoryFin G S D recs G' S' D ∧
      ContractionsLong recs ∧
      G'.edgeSet.ncard ≤ G.edgeSet.ncard + 3 * 4 ∧
      HP25.IsCrossed G D ∧
      ¬ HP25.IsCrossed G' D := by
  refine ⟨⊤, cleanCounterCycleGraph, Finset.univ, Finset.univ, cleanCounterCycle,
    [CrossRecord.del cleanCounterCycleGraph ((Finset.univ : Finset (Fin 4)) : Set (Fin 4))],
    fun _ _ _ => Finset.mem_coe.mpr (Finset.mem_univ _), ?_, isClean_cleanCounterCycleGraph,
    isHistoryFin_cleanCounter, ?_, ?_, isCrossed_top_cleanCounterCycle,
    not_isCrossed_cleanCounterCycleGraph⟩
  · refine ⟨by decide, by decide, fun p hp => ?_⟩
    revert p hp; decide
  · intro r hr
    simp at hr
  · have hle : cleanCounterCycleGraph.edgeSet.ncard ≤ (⊤ : SimpleGraph (Fin 4)).edgeSet.ncard :=
      Set.ncard_le_ncard (SimpleGraph.edgeSet_mono le_top) (Set.toFinite _)
    omega

/-! ### 2. Histories of replacement records preserve `HP25.IsCrossed` in both directions -/

/-- Every record in `recs` is a replacement record `CrossRecord.repl r`. -/
def AllRepl {V : Type*} (recs : List (CrossRecord V)) : Prop :=
  ∀ rec ∈ recs, ∃ r : ReplRecord V, rec = CrossRecord.repl r

theorem AllRepl.nil {V : Type*} : AllRepl ([] : List (CrossRecord V)) := by
  intro _ h; cases h

theorem AllRepl.append_repl {V : Type*} {recs : List (CrossRecord V)} {r : ReplRecord V}
    (h : AllRepl recs) : AllRepl (recs ++ [CrossRecord.repl r]) := by
  intro rec hrec
  rcases List.mem_append.mp hrec with h1 | h1
  · exact h rec h1
  · simp only [List.mem_singleton] at h1
    exact ⟨r, h1⟩

/-- A history consisting only of valid replacement records preserves `HP25.IsCrossed` in the
forward direction (`lemma1Forward_proved`). -/
theorem isCrossed_of_allRepl_isHistory {V : Type*} [DecidableEq V]
    {recs : List (CrossRecord V)} :
    ∀ {G G' : SimpleGraph V} {S S' : Set V} {D D' : List V},
      HP25.IsSupportedOn G S →
      HP25.IsCycleList G D →
      IsHistory (G, S, D) recs (G', S', D') →
      AllRepl recs →
      HP25.IsCrossed G D →
      HP25.IsCrossed G' D'
  | _, _, _, _, _, _, _, _, hhist, _, hcross => by
    rcases recs with _ | ⟨rec, rs⟩
    · injection hhist with hG hSD
      injection hSD with hS hD
      subst hG hD
      exact hcross
    · obtain ⟨r, rfl⟩ := ‹AllRepl (rec :: rs)› rec List.mem_cons_self
      obtain ⟨rfl, rfl, hval, hrest⟩ := hhist
      have hsupp' : HP25.IsSupportedOn r.newGraph r.newVerts :=
        _root_.GraphMinor.Crossing.ReplRecord.isSupportedOn_newGraph
          ‹HP25.IsSupportedOn r.graph r.verts› hval
      have hD' : HP25.IsCycleList r.newGraph _ :=
        ReplRecord.isCycleList_newGraph ‹HP25.IsCycleList r.graph _› hval
      have hcross' : HP25.IsCrossed r.newGraph _ :=
        lemma1Forward_proved r _ ‹HP25.IsSupportedOn r.graph r.verts›
          ‹HP25.IsCycleList r.graph _› hval hcross
      exact isCrossed_of_allRepl_isHistory hsupp' hD' hrest
        (fun x hx => ‹AllRepl (CrossRecord.repl r :: rs)› x (List.mem_cons_of_mem _ hx)) hcross'

/-- Any valid history with `ContractionsLong` preserves `HP25.IsCrossed` in the reverse direction
(via `liftHistory_proved`). -/
theorem isCrossed_of_isHistoryFin_reverse {N : ℕ}
    {G G' : SimpleGraph (Fin N)} {S S' : Finset (Fin N)} {D D' : List (Fin N)}
    {recs : List (CrossRecord (Fin N))}
    (hG : HP25.IsSupportedOn G (S : Set (Fin N)))
    (hD : HP25.IsCycleList G D)
    (hD' : HP25.IsCycleList G' D')
    (hhist : IsHistoryFin G S D recs G' S' D')
    (hlong : ContractionsLong recs)
    (hcross' : HP25.IsCrossed G' D') :
    HP25.IsCrossed G D := by
  obtain ⟨a, b, c, d, Q, R, hQR⟩ := hcross'
  have hpair' : IsCrossingPair G' D' Q.support R.support :=
    isCrossingPair_of_isCrossing hD'.2.1 hQR
  obtain ⟨⟨P', hL'⟩, hpair_of_lift⟩ :=
    liftHistory_proved G (S : Set (Fin N)) D recs G' (S' : Set (Fin N)) D'
      Q.support R.support (Set.toFinite _) hG hD hhist hlong hpair'
  exact (hpair_of_lift P' hL').isCrossed

/-- For a history of replacement records, `HP25.IsCrossed G D ↔ HP25.IsCrossed G' D`. -/
theorem isCrossed_iff_of_allRepl {N : ℕ}
    {G G' : SimpleGraph (Fin N)} {S S' : Finset (Fin N)} {D : List (Fin N)}
    {recs : List (CrossRecord (Fin N))}
    (hG : HP25.IsSupportedOn G (S : Set (Fin N)))
    (hD : HP25.IsCycleList G D)
    (hD' : HP25.IsCycleList G' D)
    (hhist : IsHistoryFin G S D recs G' S' D)
    (hlong : ContractionsLong recs)
    (hrepl : AllRepl recs) :
    HP25.IsCrossed G D ↔ HP25.IsCrossed G' D :=
  ⟨isCrossed_of_allRepl_isHistory hG hD hhist hrepl,
   isCrossed_of_isHistoryFin_reverse hG hD hD' hhist hlong⟩

/-! ### 3. Phase 1 with `AllRepl` -/

open Classical in
/-- Execution of `phase1BodyProg` at vertex `v = ⟨j, hj⟩`, tracking `AllRepl recs'`. -/
theorem phase1BodyProg_exec_full {w N : ℕ} (a : InstArrs) (a_rec r_rec a_base r_base : ℕ)
    (harrs : ArrsOk (a.list ++ [a_rec]) a_base) (hr_rec : r_rec < r_base)
    {P_repl : Cmd} {C_R c_R : ℕ}
    (hP_repl : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (r : ReplRecord (Fin N)) (recs : List (CrossRecord (Fin N)))
      (S' : Finset (Fin N)) (k : ℕ) (s : State),
      wordSize c_R (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → r.graph = G → r.verts = S → r.IsValid D →
      (S' : Set (Fin N)) = r.newVerts →
      IsSetListAt (a_base + 2) r.deleted s → IsSetListAt (a_base + 3) (r.boundary : Set (Fin N)) s →
      IsSetListAt (a_base + 4) r.rep s →
      IsRecBufAt a_rec r_rec recs k s → C_R * instSize N G ≤ k →
      ∃ s' t, Exec w P_repl s s' t ∧ t ≤ C_R * instSize N G ∧
        KeepsBelow (r_base + 3) (a_base + 10) [r_rec] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a r.newGraph S' D s' ∧
        ∃ k', IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.repl r]) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C_R * instSize N G)
    {G K : SimpleGraph (Fin N)} {S S_cur : Finset (Fin N)} {D : List (Fin N)}
    {recs₀ recs : List (CrossRecord (Fin N))} {k j : ℕ} (hj : j < N) {s₀ s : State}
    (hK_le : K ≤ G) (hS_sub : (S_cur : Set (Fin N)) ⊆ (S : Set (Fin N)))
    (hinst : IsInstanceAt a K S_cur D s) (hD : HP25.IsCycleList K D)
    (hhist : IsHistoryFin G S D recs K S_cur D) (hlong : ContractionsLong recs)
    (hrepl : AllRepl recs)
    (hbuf : IsRecBufAt a_rec r_rec (recs₀ ++ recs) k s)
    (hpot : K.edgeSet.ncard + 3 * S_cur.card ≤ G.edgeSet.ncard + 3 * S.card)
    (hlen_rec : (s.arrs a_rec).length = (s₀.arrs a_rec).length)
    (hk_cap : 4 * C_R * instSize N G ≤ k)
    (hkeep : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s)
    (hrN : s.regs r_base = N) (hrv : s.regs (r_base + 1) = j)
    (hrch_cyc : s.arrs (a_base + 5) =
      List.ofFn (fun x : Fin N => if x ∈ ReachSet G (S : Set (Fin N)) D then 1 else 0))
    (hw_R : wordSize c_R (instSize N K + (s₀.arrs a_rec).length) ≤ w)
    (hw_4K : 4 * instSize N K + 4 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (K' : SimpleGraph (Fin N)) (S' : Finset (Fin N))
      (recs' : List (CrossRecord (Fin N))) (k' : ℕ),
      Exec w (phase1BodyProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 5)
        (a_base + 7) (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 2) (r_base + 3))
        s s' t ∧
      t ≤ (4 * C_R + 1500) * instSize N G ∧
      K' ≤ G ∧ (S' : Set (Fin N)) ⊆ (S : Set (Fin N)) ∧
      IsInstanceAt a K' S' D s' ∧ HP25.IsCycleList K' D ∧
      IsHistoryFin G S D recs' K' S' D ∧ ContractionsLong recs' ∧ AllRepl recs' ∧
      IsRecBufAt a_rec r_rec (recs₀ ++ recs') k' s' ∧
      K'.edgeSet.ncard + 3 * S'.card ≤ G.edgeSet.ncard + 3 * S.card ∧
      (s'.arrs a_rec).length = (s₀.arrs a_rec).length ∧
      k ≤ k' + 4 * C_R * instSize N G ∧
      KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s' ∧
      s'.regs r_base = N ∧ s'.regs (r_base + 1) = j ∧
      s'.arrs (a_base + 5) =
        List.ofFn (fun x : Fin N => if x ∈ ReachSet G (S : Set (Fin N)) D then 1 else 0) := by
  have hK_sz : instSize N K ≤ 4 * instSize N G := (instSize_le_four_mul_of_edge_pot hpot).2
  have hw1 : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by have := le_instSize_self N K; omega
  have hjw : j < 2 ^ w := by omega
  set v : Fin N := ⟨j, hj⟩
  set av : ℕ := if v ∈ S_cur then 1 else 0
  have hav_w : av < 2 ^ w := by simp only [av]; split_ifs <;> omega
  have hal_len : j < (s.arrs a.alive).length := by rw [hinst.length_alive]; exact hj
  have hal_val : (s.arrs a.alive)[j]'hal_len = av := by simp [hinst.2.1, av, v]
  have hrd_al : (Expr.read a.alive (.reg (r_base + 1))).eval w s = some av := by
    have := eval_read (a := a.alive) (eval_reg hrv hjw) hal_len (by rw [hal_val]; exact hav_w)
    rwa [hal_val] at this
  set s₁ := s.setReg (r_base + 2) av
  have hex₁ : Exec w (.assign (r_base + 2) (.read a.alive (.reg (r_base + 1)))) s s₁ 3 :=
    .assign hrd_al
  by_cases hvS : v ∈ S_cur
  · have hav1 : av = 1 := by simp [av, hvS]
    have hcond1 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₁ = some 1 := by
      have := eval_eq (s := s₁) (eval_reg (r := r_base + 2) (by simp [s₁, hav1]) hw1)
        (eval_const hw1) hw1
      simpa using this
    set cv : ℕ := if v ∈ ReachSet G (S : Set (Fin N)) D then 1 else 0
    have hcv_w : cv < 2 ^ w := by simp only [cv]; split_ifs <;> omega
    have hrc_len : j < (s₁.arrs (a_base + 5)).length := by simp [s₁, hrch_cyc, hj]
    have hrc_val : (s₁.arrs (a_base + 5))[j]'hrc_len = cv := by simp [s₁, hrch_cyc, cv, v]
    have hrd_rc : (Expr.read (a_base + 5) (.reg (r_base + 1))).eval w s₁ = some cv := by
      have hrv₁ : s₁.regs (r_base + 1) = j := by simp [s₁, hrv]
      have := eval_read (a := a_base + 5) (eval_reg hrv₁ hjw) hrc_len (by rw [hrc_val]; exact hcv_w)
      rwa [hrc_val] at this
    set s₂ := s₁.setReg (r_base + 2) cv
    have hex₂ : Exec w (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1)))) s₁ s₂ 3 :=
      .assign hrd_rc
    by_cases hvR : v ∈ ReachSet G (S : Set (Fin N)) D
    · have hcv1 : cv = 1 := by simp [cv, hvR]
      have hcond2 : (Expr.op .eq (.reg (r_base + 2)) (.const 0)).eval w s₂ = some 0 := by
        have := eval_eq (s := s₂) (eval_reg (r := r_base + 2) (by simp [s₂, hcv1]) hw1)
          (eval_const h0w) hw1
        simpa using this
      have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
          (phase1DiscardProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 7)
            (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 3)) .skip) s₂ s₂ 4 :=
        .ite_false hcond2 (.skip s₂)
      have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
          (.seq (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1))))
            (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
              (phase1DiscardProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 7)
                (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 3)) .skip)) .skip)
          s₁ s₂ 10 := .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
      have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
      have h_mul : (4 * C_R + 1500) * instSize N G =
          4 * C_R * instSize N G + 1500 * instSize N G := by ring
      refine ⟨s₂, 13, K, S_cur, recs, k, .seq hex₁ hex_ite1, by omega,
        hK_le, hS_sub, hinst.of_keeps_disjoint (fun _ _ => rfl), hD, hhist, hlong, hrepl,
        hbuf.of_arrs_regs_eq rfl (by simp [s₂, s₁, show r_rec ≠ r_base + 2 by omega]),
        hpot, hlen_rec, by omega,
        (hkeep.setReg_ge (by omega) _).setReg_ge (by omega) _,
        by simp [s₂, s₁, hrN], by simp [s₂, s₁, hrv], hrch_cyc⟩
    · have hcv0 : cv = 0 := by simp [cv, hvR]
      have hcond2 : (Expr.op .eq (.reg (r_base + 2)) (.const 0)).eval w s₂ = some 1 := by
        have := eval_eq (s := s₂) (eval_reg (r := r_base + 2) (by simp [s₂, hcv0]) h0w)
          (eval_const h0w) hw1
        simpa using this
      obtain ⟨s₃, t₃, hex₃, ht₃, hsrc₃, ha₃, hr₃⟩ :=
        singleSrcProg_exec_nat (w := w) (a_base + 7) (r_base + 1) v (s := s₂)
          (by simp [s₂, s₁, hrv, v]) hw1 hNw
      have hinst₃ : IsInstanceAt a K S_cur D s₃ :=
        hinst.of_keeps_disjoint (fun x hx => ha₃ x (fun e =>
          add_not_mem_instArrs_of_arrsOk harrs (e ▸ hx)))
      have hno_a : ∀ d, a_base + d ∉ a.list := fun d => add_not_mem_instArrs_of_arrsOk harrs
      have hal_ne : ∀ d, a_base + d ≠ a.alive :=
        fun d e => hno_a d (e ▸ by simp [InstArrs.list])
      obtain ⟨s₄, t₄, hex₄, ht₄, hr₄, ha₄, _, hdel₄⟩ :=
        reachSearchProg_exec a a.alive (a_base + 7) (a_base + 8) (a_base + 2) (a_base + 9)
          (r_base + 3) hinst₃ (alive_eq_ofFn_mem hinst₃) hsrc₃ (by simp)
          ⟨hno_a 8, hal_ne 8, by omega, by omega, by omega⟩
          ⟨hno_a 9, hal_ne 9, by omega, by omega⟩
          ⟨hno_a 2, hal_ne 2, by omega, by omega⟩ hw_4K
      have hinst₄ : IsInstanceAt a K S_cur D s₄ :=
        hinst₃.of_keeps_disjoint (fun x hx => ha₄ x
          (fun e => hno_a 8 (e ▸ hx)) (fun e => hno_a 2 (e ▸ hx)) (fun e => hno_a 9 (e ▸ hx)))
      have hsrc₄ : s₄.arrs (a_base + 7) = [v].map Fin.val := by
        rw [ha₄ (a_base + 7) (by omega) (by omega) (by omega)]; exact hsrc₃
      obtain ⟨s₅, t₅, hex₅, ht₅, hr₅, ha₅, _, hrep₅⟩ :=
        reachSearchProg_exec a a.alive (a_base + 7) (a_base + 8) (a_base + 4) (a_base + 9)
          (r_base + 3) hinst₄ (alive_eq_ofFn_mem hinst₄) hsrc₄ (by simp)
          ⟨hno_a 8, hal_ne 8, by omega, by omega, by omega⟩
          ⟨hno_a 9, hal_ne 9, by omega, by omega⟩
          ⟨hno_a 4, hal_ne 4, by omega, by omega⟩ hw_4K
      obtain ⟨hex₆, hbd₆⟩ := alloc_empty_isSetListAt (N := N) (a_base + 3) s₅ h0w
      set s₆ := s₅.setArr (a_base + 3) []
      have ha₆_below : ∀ x < a_base, s₆.arrs x = s.arrs x := by
        intro x hx
        simp only [s₆, State.setArr_arrs_ne _ _ (show x ≠ a_base + 3 by omega)]
        rw [ha₅ x (by omega) (by omega) (by omega),
            ha₄ x (by omega) (by omega) (by omega),
            ha₃ x (by omega)]
        rfl
      have hinst₆ : IsInstanceAt a K S_cur D s₆ :=
        hinst.of_keeps_disjoint (fun x hx => ha₆_below x (mem_instArrs_lt_of_arrsOk harrs hx))
      let A : Set (Fin N) := {y | ReachIn K (S_cur : Set (Fin N)) v y}
      have hA_eq : ReachSet K (S_cur : Set (Fin N)) [v] = A :=
        reachSet_singleton K (S_cur : Set (Fin N))
      have hdel₆ : IsSetListAt (a_base + 2) A s₆ := by
        rw [← hA_eq]
        apply hdel₄.of_arrs_eq
        simp only [s₆, State.setArr_arrs_ne _ _ (by omega : a_base + 2 ≠ a_base + 3)]
        exact ha₅ (a_base + 2) (by omega) (by omega) (by omega)
      have hrep₆ : IsSetListAt (a_base + 4) A s₆ := by
        rw [← hA_eq]
        apply hrep₅.of_arrs_eq
        simp [s₆]
      have hunreach : ∀ d ∈ D, ¬ ReachIn K (S_cur : Set (Fin N)) d v := by
        intro d hd hreach
        apply hvR
        exact ⟨hS_sub hvS, d, hd, ReachIn.mono_graph_set hK_le hS_sub hreach⟩
      let r : ReplRecord (Fin N) :=
        { graph := K, verts := (S_cur : Set (Fin N)), deleted := A, boundary := ∅, rep := A }
      have hval : r.IsValid D := replRecord_isValid_of_unreach hinst.1 hvS hunreach
      let S' : Finset (Fin N) := r.newVerts.toFinset
      have hS'_coe : (S' : Set (Fin N)) = r.newVerts := Set.coe_toFinset r.newVerts
      have hrec_lt : a_rec < a_base := harrs.2 a_rec (by simp)
      have hbuf₆ : IsRecBufAt a_rec r_rec (recs₀ ++ recs) k s₆ := by
        apply hbuf.of_arrs_regs_eq (ha₆_below a_rec hrec_lt)
        simp only [s₆, State.setArr_regs]
        rw [hr₅ r_rec (by omega), hr₄ r_rec (by omega), hr₃]
        simp [s₂, s₁, show r_rec ≠ r_base + 2 by omega]
      have hlen_rec₆ : (s₆.arrs a_rec).length = (s₀.arrs a_rec).length := by
        rw [ha₆_below a_rec hrec_lt, hlen_rec]
      have hk_R : C_R * instSize N K ≤ k := by
        calc C_R * instSize N K ≤ C_R * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
          _ = 4 * C_R * instSize N G := by ring
          _ ≤ k := hk_cap
      obtain ⟨s₇, t₇, hex₇, ht₇, hkeep₇, hinst₇, k', hbuf₇, hlen₇, hk₇⟩ :=
        hP_repl w N K S_cur D r (recs₀ ++ recs) S' k s₆
          (by rwa [hlen_rec₆]) hinst₆ hD rfl rfl hval hS'_coe hdel₆
          (by simpa [r] using hbd₆) hrep₆ hbuf₆ hk_R
      have hex_disc : Exec w
          (phase1DiscardProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 7)
            (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 3))
          s₂ s₇ (t₃ + (t₄ + (t₅ + (1 + t₇)))) :=
        .seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))
      have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
          (phase1DiscardProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 7)
            (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 3)) .skip)
          s₂ s₇ (3 + (t₃ + (t₄ + (t₅ + (1 + t₇))))) :=
        .ite_true hcond2 one_ne_zero hex_disc
      have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
          (.seq (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1))))
            (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
              (phase1DiscardProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 7)
                (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 3)) .skip)) .skip)
          s₁ s₇ (3 + (3 + (3 + (t₃ + (t₄ + (t₅ + (1 + t₇))))))) :=
        .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
      have hK'_le : r.newGraph ≤ G :=
        le_trans (by simpa [r, ReplRecord.newGraph] using replaceGraph_empty_le K A) hK_le
      have hS'_sub : (S' : Set (Fin N)) ⊆ (S : Set (Fin N)) := by
        rw [hS'_coe]
        exact Set.Subset.trans Set.sdiff_subset hS_sub
      have hD' : HP25.IsCycleList r.newGraph D := ReplRecord.isCycleList_newGraph hD hval
      have hhist' : IsHistoryFin G S D (recs ++ [CrossRecord.repl r]) r.newGraph S' D :=
        hhist.snoc_repl rfl rfl hval hS'_coe
      have hlong' : ContractionsLong (recs ++ [CrossRecord.repl r]) := hlong.append_repl
      have hrepl' : AllRepl (recs ++ [CrossRecord.repl r]) := hrepl.append_repl
      have hbuf₇' : IsRecBufAt a_rec r_rec (recs₀ ++ (recs ++ [CrossRecord.repl r])) k' s₇ := by
        rwa [← List.append_assoc]
      have hpot' : r.newGraph.edgeSet.ncard + 3 * S'.card ≤ G.edgeSet.ncard + 3 * S.card :=
        le_trans (edge_pot_step rfl rfl hval hS'_coe).2.2 hpot
      have hkeep_s₆ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₆ := by
        refine ⟨fun r₀ hr₀ hnr₀ => ?_, fun x hx hnx => ?_⟩
        · simp only [s₆, State.setArr_regs]
          rw [hr₅ r₀ (by omega), hr₄ r₀ (by omega), hr₃]
          simp only [s₂, s₁, State.setReg_regs_ne _ _ (show r₀ ≠ r_base + 2 by omega)]
          exact hkeep.1 r₀ hr₀ hnr₀
        · rw [ha₆_below x hx]
          exact hkeep.2 x hx hnx
      have hkeep_s₇ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₇ :=
        hkeep_s₆.trans (hkeep₇.le (by omega) (by omega))
          (fun _ hm _ => hm) (fun _ hm _ => hm)
      have hrN₇ : s₇.regs r_base = N := by
        rw [hkeep₇.1 r_base (by omega) (by simp; omega)]
        simp only [s₆, State.setArr_regs]
        rw [hr₅ r_base (by omega), hr₄ r_base (by omega), hr₃]
        simp [s₂, s₁, hrN]
      have hrv₇ : s₇.regs (r_base + 1) = j := by
        rw [hkeep₇.1 (r_base + 1) (by omega) (by simp; omega)]
        simp only [s₆, State.setArr_regs]
        rw [hr₅ (r_base + 1) (by omega), hr₄ (r_base + 1) (by omega), hr₃]
        simp [s₂, s₁, hrv]
      have hrch_cyc₇ : s₇.arrs (a_base + 5) =
          List.ofFn (fun x : Fin N => if x ∈ ReachSet G (S : Set (Fin N)) D then 1 else 0) := by
        rw [hkeep₇.2 (a_base + 5) (by omega) (by
          simp only [List.mem_append, List.mem_singleton, not_or]
          exact ⟨hno_a 5, by omega⟩)]
        simp only [s₆, State.setArr_arrs_ne _ _ (by omega : a_base + 5 ≠ a_base + 3)]
        rw [ha₅ (a_base + 5) (by omega) (by omega) (by omega),
            ha₄ (a_base + 5) (by omega) (by omega) (by omega),
            ha₃ (a_base + 5) (by omega)]
        exact hrch_cyc
      have ht_bound : 3 + (3 + (3 + (3 + (t₃ + (t₄ + (t₅ + (1 + t₇))))))) ≤
          (4 * C_R + 1500) * instSize N G := by
        have h1 : C_R * instSize N K ≤ 4 * C_R * instSize N G := by
          calc C_R * instSize N K ≤ C_R * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
            _ = 4 * C_R * instSize N G := by ring
        have h2 : (4 * C_R + 1500) * instSize N G =
            4 * C_R * instSize N G + 1500 * instSize N G := by ring
        have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
        omega
      have hk_bound : k ≤ k' + 4 * C_R * instSize N G := by
        have h1 : C_R * instSize N K ≤ 4 * C_R * instSize N G := by
          calc C_R * instSize N K ≤ C_R * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
            _ = 4 * C_R * instSize N G := by ring
        omega
      exact ⟨s₇, _, r.newGraph, S', recs ++ [CrossRecord.repl r], k',
        .seq hex₁ hex_ite1, ht_bound, hK'_le, hS'_sub, hinst₇, hD', hhist', hlong', hrepl',
        hbuf₇', hpot', hlen₇.trans hlen_rec₆, hk_bound, hkeep_s₇, hrN₇, hrv₇, hrch_cyc₇⟩
  · have hav0 : av = 0 := by simp [av, hvS]
    have hcond1 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₁ = some 0 := by
      have := eval_eq (s := s₁) (eval_reg (r := r_base + 2) (by simp [s₁, hav0]) h0w)
        (eval_const hw1) hw1
      simpa using this
    have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
        (.seq (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1))))
          (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
            (phase1DiscardProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 7)
              (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 3)) .skip)) .skip)
        s₁ s₁ 4 := .ite_false hcond1 (.skip s₁)
    have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
    have h_mul : (4 * C_R + 1500) * instSize N G =
        4 * C_R * instSize N G + 1500 * instSize N G := by ring
    refine ⟨s₁, 7, K, S_cur, recs, k, .seq hex₁ hex_ite1, by omega,
      hK_le, hS_sub, hinst.of_keeps_disjoint (fun _ _ => rfl), hD, hhist, hlong, hrepl,
      hbuf.of_arrs_regs_eq rfl (by simp [s₁, show r_rec ≠ r_base + 2 by omega]),
      hpot, hlen_rec, by omega,
      hkeep.setReg_ge (by omega) _,
      by simp [s₁, hrN], by simp [s₁, hrv], hrch_cyc⟩

open Classical in
/-- Execution of `phase1Prog`, tracking `AllRepl recs₁`. -/
theorem phase1Prog_exec_full {w N : ℕ} (a : InstArrs) (a_rec r_rec a_base r_base : ℕ)
    (harrs : ArrsOk (a.list ++ [a_rec]) a_base) (hr_rec : r_rec < r_base)
    {P_repl : Cmd} {C_R c_R c_F : ℕ}
    (hP_repl : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (r : ReplRecord (Fin N)) (recs : List (CrossRecord (Fin N)))
      (S' : Finset (Fin N)) (k : ℕ) (s : State),
      wordSize c_R (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → r.graph = G → r.verts = S → r.IsValid D →
      (S' : Set (Fin N)) = r.newVerts →
      IsSetListAt (a_base + 2) r.deleted s → IsSetListAt (a_base + 3) (r.boundary : Set (Fin N)) s →
      IsSetListAt (a_base + 4) r.rep s →
      IsRecBufAt a_rec r_rec recs k s → C_R * instSize N G ≤ k →
      ∃ s' t, Exec w P_repl s s' t ∧ t ≤ C_R * instSize N G ∧
        KeepsBelow (r_base + 3) (a_base + 10) [r_rec] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a r.newGraph S' D s' ∧
        ∃ k', IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.repl r]) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C_R * instSize N G)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {recs₀ : List (CrossRecord (Fin N))} {k : ℕ} {s : State}
    (hw : wordSize (3 * c_F + 3 * c_R + 5) ((N + 1) * instSize N G + (s.arrs a_rec).length) ≤ w)
    (hinst : IsInstanceAt a G S D s) (hD : HP25.IsCycleList G D)
    (hbuf : IsRecBufAt a_rec r_rec recs₀ k s)
    (hk : N * (4 * C_R * instSize N G) ≤ k) :
    ∃ (s' : State) (t : ℕ) (G₁ : SimpleGraph (Fin N)) (S₁ : Finset (Fin N))
      (recs₁ : List (CrossRecord (Fin N))) (k₁ : ℕ),
      Exec w (phase1Prog a a_base P_repl r_base) s s' t ∧
      t ≤ (4 * C_R + 1800) * (N + 1) * instSize N G ∧
      IsInstanceAt a G₁ S₁ D s' ∧ HP25.IsCycleList G₁ D ∧
      IsHistoryFin G S D recs₁ G₁ S₁ D ∧ ContractionsLong recs₁ ∧ AllRepl recs₁ ∧
      IsRecBufAt a_rec r_rec (recs₀ ++ recs₁) k₁ s' ∧
      G₁.edgeSet.ncard + 3 * S₁.card ≤ G.edgeSet.ncard + 3 * S.card ∧
      (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
      k ≤ k₁ + N * (4 * C_R * instSize N G) ∧
      KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' := by
  have hb0 := wordSize_subprog_bounds (K := G)
    (by have := instSize_pos N G; omega) hw
  have hw1 : 1 < 2 ^ w := hb0.2.2.2.2.1
  have h0w : 0 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := hb0.2.2.2.2.2
  have hno_a : ∀ d, a_base + d ∉ a.list := fun d => add_not_mem_instArrs_of_arrsOk harrs
  have hal_ne : ∀ d, a_base + d ≠ a.alive :=
    fun d e => hno_a d (e ▸ by simp [InstArrs.list])
  have hcyc_ne : ∀ d, a_base + d ≠ a.cyc :=
    fun d e => hno_a d (e ▸ by simp [InstArrs.list])
  have hD_len : D.length ≤ N + 1 := le_trans (isCycleList_length_le_fin hD) (by omega)
  obtain ⟨s₁, t₁, hex₁, ht₁, hr₁, ha₁, hrch_cyc₁, _⟩ :=
    reachSearchProg_exec a a.alive a.cyc (a_base + 5) (a_base + 2) (a_base + 9) (r_base + 3)
      hinst (alive_eq_ofFn_mem hinst) hinst.2.2.2.2 hD_len
      ⟨hno_a 5, hal_ne 5, hcyc_ne 5, by omega, by omega⟩
      ⟨hno_a 9, hal_ne 9, hcyc_ne 9, by omega⟩
      ⟨hno_a 2, hal_ne 2, hcyc_ne 2, by omega⟩ hb0.2.2.1
  have hinst₁ : IsInstanceAt a G S D s₁ :=
    hinst.of_keeps_disjoint (fun x hx => ha₁ x
      (fun e => hno_a 5 (e ▸ hx)) (fun e => hno_a 2 (e ▸ hx)) (fun e => hno_a 9 (e ▸ hx)))
  have hal_len₁ : (s₁.arrs a.alive).length = N := hinst₁.length_alive
  set s₂ := s₁.setReg r_base N
  have hex₂ : Exec w (.assign r_base (.len a.alive)) s₁ s₂ 2 :=
    .assign (by rw [← hal_len₁]; exact eval_len rfl (by rw [hal_len₁]; exact hNw))
  set s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 := .assign (eval_const h0w)
  let I₁ : ℕ → State → Prop := fun j st =>
    st.regs r_base = N ∧ st.regs (r_base + 1) = j ∧
    st.arrs (a_base + 5) =
      List.ofFn (fun x : Fin N => if x ∈ ReachSet G (S : Set (Fin N)) D then 1 else 0) ∧
    (st.arrs a_rec).length = (s.arrs a_rec).length ∧
    KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s st ∧
    ∃ (K : SimpleGraph (Fin N)) (S_cur : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
      (k_cur : ℕ),
      K ≤ G ∧ (S_cur : Set (Fin N)) ⊆ (S : Set (Fin N)) ∧
      IsInstanceAt a K S_cur D st ∧ HP25.IsCycleList K D ∧
      IsHistoryFin G S D recs K S_cur D ∧ ContractionsLong recs ∧ AllRepl recs ∧
      IsRecBufAt a_rec r_rec (recs₀ ++ recs) k_cur st ∧
      K.edgeSet.ncard + 3 * S_cur.card ≤ G.edgeSet.ncard + 3 * S.card ∧
      k ≤ k_cur + j * (4 * C_R * instSize N G)
  have hrec_lt : a_rec < a_base := harrs.2 a_rec (by simp)
  have hI0 : I₁ 0 s₃ := by
    refine ⟨by simp [s₃, s₂], by simp [s₃], hrch_cyc₁,
      by simp [s₃, s₂, ha₁ a_rec (by omega) (by omega) (by omega)],
      ⟨fun r₀ hr₀ _ => by
        simp [s₃, s₂, show r₀ ≠ r_base + 1 by omega, show r₀ ≠ r_base by omega,
          hr₁ r₀ (by omega)],
       fun x hx _ => by
        simp [s₃, s₂, ha₁ x (by omega) (by omega) (by omega)]⟩,
      G, S, [], k, le_rfl, Set.Subset.rfl, hinst₁, hD, IsHistoryFin.refl G S D,
      ContractionsLong.nil, AllRepl.nil, ?_, le_rfl, by omega⟩
    rw [List.append_nil]
    exact hbuf.of_arrs_regs_eq (ha₁ a_rec (by omega) (by omega) (by omega))
      (by simp [s₃, s₂, show r_rec ≠ r_base + 1 by omega, show r_rec ≠ r_base by omega,
        hr₁ r_rec (by omega)])
  let B₁ := (4 * C_R + 1500) * instSize N G
  obtain ⟨s₄, t₄, hex₄, ht₄, hIN⟩ := forUp_exec' I₁ N B₁
    (r_i := r_base + 1) (hi := .reg r_base)
    (body := phase1BodyProg a (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 5)
      (a_base + 7) (a_base + 8) (a_base + 9) P_repl (r_base + 1) (r_base + 2) (r_base + 3))
    hw1 hNw
    (fun j _ st hI => ⟨hI.2.1, eval_reg hI.1 hNw⟩)
    (fun j hj st hI => by
      obtain ⟨hrN, hrv, hrch, hlen, hkeep, K, S_cur, recs, k_cur,
        hK_le, hS_sub, hinst_K, hD_K, hhist, hlong, hrepl, hbuf_K, hpot, hk_j⟩ := hI
      have hK_sz := (instSize_le_four_mul_of_edge_pot hpot).2
      have hwb := wordSize_subprog_bounds hK_sz hw
      have hk_rem : 4 * C_R * instSize N G ≤ k_cur := by
        have : (j + 1) * (4 * C_R * instSize N G) ≤ N * (4 * C_R * instSize N G) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      obtain ⟨st', t', K', S', recs', k', hex_b, ht_b, hK'_le, hS'_sub,
        hinst', hD', hhist', hlong', hrepl', hbuf', hpot', hlen', hk', hkeep', hrN', hrv', hrch'⟩ :=
        phase1BodyProg_exec_full a a_rec r_rec a_base r_base harrs hr_rec hP_repl hj
          hK_le hS_sub hinst_K hD_K hhist hlong hrepl hbuf_K hpot hlen hk_rem hkeep hrN hrv hrch
          hwb.2.1 hwb.2.2.1
      refine ⟨st', t', hex_b, ht_b, ?_, hrv'⟩
      refine ⟨by simp [hrN'], by simp, hrch', hlen', hkeep'.setReg_ge (by omega) _,
        K', S', recs', k', hK'_le, hS'_sub,
        hinst'.of_keeps_disjoint (fun _ _ => rfl), hD', hhist', hlong', hrepl',
        hbuf'.of_arrs_regs_eq rfl (by simp [show r_rec ≠ r_base + 1 by omega]),
        hpot', ?_⟩
      rw [Nat.add_mul, Nat.one_mul]
      omega)
    s₃ hI0
  obtain ⟨_, _, _, hlen₄, hkeep₄, G₁, S₁, recs₁, k₁, _, _,
    hinst₄, hD₄, hhist₄, hlong₄, hrepl₄, hbuf₄, hpot₄, hk₄⟩ := hIN
  refine ⟨s₄, _, G₁, S₁, recs₁, k₁, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    hinst₄, hD₄, hhist₄, hlong₄, hrepl₄, hbuf₄, hpot₄, hlen₄, hk₄, hkeep₄⟩
  simp only [Expr.cost, B₁] at ht₄
  have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
  have hN_le : N ≤ N * instSize N G := by
    simpa using Nat.mul_le_mul_left N hsz_pos
  have hring : (4 * C_R + 1800) * (N + 1) * instSize N G + 7 * N =
      N * (1 + 6 + (4 * C_R + 1500) * instSize N G) + 300 * (N * instSize N G) +
      4 * C_R * instSize N G + 1800 * instSize N G := by ring
  omega

end GraphMinor.Compute.Crossing
