module

public import GraphMinor.Crossing.Statements
public import GraphMinor.Crossing.StatementsLift
public import GraphMinor.Crossing.LinkList
import GraphMinor.Crossing.CutSec3
import GraphMinor.Crossing.SparseLift

/-!
# Lifting crossings through the history (`docs/crossing/crossing_extractor.tex`, Section 11)

Section 11 of `docs/crossing/crossing_extractor.tex`:
"Thus every contraction lifts without a search. Reversing all accepted operations gives two
disjoint $C$-paths in the original graph, with alternating ends."

This file proves `LiftHistoryStatement` (`liftHistory_of`) from the single-step lift statements:
* `Lemma1ReverseStatement` (Section 3, replacement at a small separator);
* `Lift11OffOffStatement` (Section 11, contraction with both ends off the cycle);
* `Lift11OneOnStatement` (Section 11, contraction with one end on the cycle);
* `Lift11BothOnStatement` (Section 11, contraction with both ends on the cycle).
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph

universe u

variable {V : Type u}

/-! ### Forward invariants of accepted operations -/

/-- A valid replacement preserves `HP25.IsSupportedOn`. -/
theorem ReplRecord.isSupportedOn_newGraph {r : ReplRecord V} {D : List V}
    (hG : HP25.IsSupportedOn r.graph r.verts) (hval : r.IsValid D) :
    HP25.IsSupportedOn r.newGraph r.newVerts := by
  intro a b hadj
  rcases hadj with ⟨hab, ha, -⟩ | ⟨ha, -, -⟩
  · exact ⟨hG hab, ha⟩
  · exact hval.2.2.2.1 ha

/-- A valid replacement preserves `HP25.IsCycleList`. -/
theorem ReplRecord.isCycleList_newGraph {r : ReplRecord V} {D : List V}
    (hD : HP25.IsCycleList r.graph D) (hval : r.IsValid D) :
    HP25.IsCycleList r.newGraph D := by
  refine ⟨hD.1, hD.2.1, fun p hp => ?_⟩
  have hp1 : p.1 ∈ D := (List.of_mem_zip hp).1
  have hp2 : p.2 ∈ D := List.mem_rotate.mp (List.of_mem_zip hp).2
  exact Or.inl ⟨hD.2.2 p hp, fun h => hval.2.1 p.1 h hp1, fun h => hval.2.1 p.2 h hp2⟩

/-- A valid contraction preserves `HP25.IsSupportedOn`. -/
theorem ContractRecord.isSupportedOn_newGraph [DecidableEq V] {r : ContractRecord V}
    (hval : r.IsValid) : HP25.IsSupportedOn r.newGraph r.newVerts := by
  obtain ⟨hG, -, huv, -⟩ := hval
  have hv : r.v ∈ r.verts := hG huv.symm
  intro a b ⟨_, hau, _, h⟩
  refine ⟨?_, hau⟩
  rcases h with hab | ⟨rfl, -⟩ | ⟨-, hua⟩
  · exact hG hab
  · exact hv
  · exact hG hua.symm

/-- Erasing `u = D[i]` from a duplicate-free list `D` shifts indices at or above `i` by `1`. -/
private theorem erase_eq_take_append_drop [DecidableEq V] {D : List V} (hnd : D.Nodup)
    {i : ℕ} (hi : i < D.length) :
    D.erase (D[i]) = D.take i ++ D.drop (i + 1) := by
  have hsplit : D = D.take i ++ D[i] :: D.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hnd' : (D.take i ++ D[i] :: D.drop (i + 1)).Nodup := hsplit ▸ hnd
  have hu_not_take : D[i] ∉ D.take i := fun hmem =>
    (List.nodup_append.mp hnd').2.2 (D[i]) hmem (D[i]) List.mem_cons_self rfl
  have h1 : D.erase (D[i]) = (D.take i ++ D[i] :: D.drop (i + 1)).erase (D[i]) :=
    congrArg (fun L => L.erase (D[i])) hsplit
  rw [h1, List.erase_append_right _ hu_not_take, List.erase_cons_head]

/-- Element lookup in `D.erase (D[i])` for a duplicate-free list `D`. -/
private theorem getElem_erase_of_nodup [DecidableEq V] {D : List V} (hnd : D.Nodup)
    {i : ℕ} (hi : i < D.length) {k : ℕ} (hk : k < (D.erase (D[i])).length) :
    (D.erase (D[i]))[k] = D[if k < i then k else k + 1]'(by
      have hlen : (D.erase (D[i])).length = D.length - 1 :=
        List.length_erase_of_mem (List.getElem_mem hi)
      split_ifs <;> omega) := by
  have hlen : (D.erase (D[i])).length = D.length - 1 :=
    List.length_erase_of_mem (List.getElem_mem hi)
  have heq := erase_eq_take_append_drop hnd hi
  have hk' : k < (D.take i ++ D.drop (i + 1)).length := heq ▸ hk
  have hget : (D.erase (D[i]))[k] = (D.take i ++ D.drop (i + 1))[k] := by
    congr 1
  rw [hget]
  have htake_len : (D.take i).length = i := List.length_take_of_le (by omega)
  split_ifs with hki
  · rw [List.getElem_append_left (by omega), List.getElem_take]
  · rw [List.getElem_append_right (by omega), List.getElem_drop]
    congr 1
    omega

/-- In a cycle `D` of `G`, adjacent indices modulo `D.length` are adjacent in `G`. -/
private theorem adj_getElem_mod_of_isCycleList {G : SimpleGraph V} {D : List V}
    (hD : HP25.IsCycleList G D) {m : ℕ} (hm : m < D.length) :
    G.Adj (D[m]) (D[(m + 1) % D.length]'(Nat.mod_lt _ (by have := hD.1; omega))) := by
  have hlen1 : (D.rotate 1).length = D.length := List.length_rotate D 1
  have hp : (D[m], (D.rotate 1)[m]'(by omega)) ∈ D.zip (D.rotate 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨m, by simp [hm], by simp⟩
  have hadj := hD.2.2 _ hp
  rwa [List.getElem_rotate] at hadj

/-- Contracting a cycle edge of a cycle `D` of length `> 4` yields a cycle in `contractGraph G u v`. -/
theorem isCycleList_erase_of_isCycleEdge [DecidableEq V] {G : SimpleGraph V} {D : List V}
    {u v : V} (hD : HP25.IsCycleList G D) (huv : IsCycleEdge D u v) (hlen4 : 4 < D.length) :
    HP25.IsCycleList (contractGraph G u v) (D.erase u) := by
  have hnd : D.Nodup := hD.2.1
  obtain ⟨p₀, hp₀, hp₀eq⟩ := huv
  have huD : u ∈ D := by
    have h1 := List.of_mem_zip hp₀
    rcases hp₀eq with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact h1.1
    · exact List.mem_rotate.mp h1.2
  have hlen_erase : (D.erase u).length = D.length - 1 := List.length_erase_of_mem huD
  have hnd_erase : (D.erase u).Nodup := hnd.erase u
  refine ⟨by omega, hnd_erase, ?_⟩
  obtain ⟨i, hi, hDi⟩ := List.getElem_of_mem huD
  subst hDi
  -- Identify the index of `v` as `(i + 1) % D.length` or `(i + D.length - 1) % D.length`
  have hv_idx : v = D[(i + 1) % D.length]'(Nat.mod_lt _ (by omega)) ∨
      v = D[(i + D.length - 1) % D.length]'(Nat.mod_lt _ (by omega)) := by
    rw [List.mem_iff_getElem] at hp₀
    obtain ⟨m, hm, hpm⟩ := hp₀
    simp only [List.length_zip, List.length_rotate, min_self] at hm
    simp only [List.getElem_zip, List.getElem_rotate] at hpm
    rcases hp₀eq with rfl | rfl
    · have h1 : D[m] = D[i] := congrArg Prod.fst hpm
      have hmi : m = i := (hnd.getElem_inj_iff).mp h1
      subst hmi
      left
      exact (congrArg Prod.snd hpm).symm
    · have h2 : D[(m + 1) % D.length]'(Nat.mod_lt _ (by omega)) = D[i] := congrArg Prod.snd hpm
      have hmi : (m + 1) % D.length = i := (hnd.getElem_inj_iff).mp h2
      right
      have hm_eq : m = (i + D.length - 1) % D.length := by
        by_cases hlast : m + 1 = D.length
        · rw [hlast, Nat.mod_self] at hmi
          subst hmi
          rw [zero_add, Nat.mod_eq_of_lt (by omega)]
          omega
        · have hlt : m + 1 < D.length := by omega
          rw [Nat.mod_eq_of_lt hlt] at hmi
          subst hmi
          have : m + 1 + D.length - 1 = m + D.length := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt hm]
      have hv_eq : D[m] = v := congrArg Prod.fst hpm
      rw [← hv_eq]
      congr 1
  -- Now check every cyclic edge of `D.erase (D[i])`
  intro p hp
  rw [List.mem_iff_getElem] at hp
  obtain ⟨k, hk, hpk⟩ := hp
  simp only [List.length_zip, List.length_rotate, min_self] at hk
  simp only [List.getElem_zip, List.getElem_rotate] at hpk
  rw [← hpk]
  dsimp only
  let k' := (k + 1) % (D.erase (D[i])).length
  have hk' : k' < (D.erase (D[i])).length := Nat.mod_lt _ (by omega)
  have hkk' : k ≠ k' := by
    intro heq
    change k = (k + 1) % (D.erase (D[i])).length at heq
    by_cases hwrap : k + 1 = (D.erase (D[i])).length
    · rw [hwrap, Nat.mod_self] at heq
      omega
    · have hlt : k + 1 < (D.erase (D[i])).length := by omega
      rw [Nat.mod_eq_of_lt hlt] at heq
      omega
  have hne : (D.erase (D[i]))[k] ≠ (D.erase (D[i]))[k'] := fun h =>
    hkk' ((hnd_erase.getElem_inj_iff).mp h)
  have hku : (D.erase (D[i]))[k] ≠ D[i] := fun h =>
    (hnd.mem_erase_iff.mp (List.getElem_mem hk)).1 h
  have hk'u : (D.erase (D[i]))[k'] ≠ D[i] := fun h =>
    (hnd.mem_erase_iff.mp (List.getElem_mem hk')).1 h
  refine ⟨hne, hku, hk'u, ?_⟩
  rw [getElem_erase_of_nodup hnd hi hk, getElem_erase_of_nodup hnd hi hk']
  let a_idx := if k < i then k else k + 1
  let b_idx := if k' < i then k' else k' + 1
  have ha_lt : a_idx < D.length := by dsimp [a_idx]; split_ifs <;> omega
  have hb_lt : b_idx < D.length := by dsimp [b_idx]; split_ifs <;> omega
  -- Either `b_idx = (a_idx + 1) % D.length` or `a_idx` is the predecessor of `i` and `b_idx` the successor
  by_cases hstep : b_idx = (a_idx + 1) % D.length
  · left
    have hadj := adj_getElem_mod_of_isCycleList hD ha_lt
    convert hadj using 2
  · right
    -- Here `a_idx` must be the predecessor of `i` and `b_idx = (i + 1) % D.length`
    have h_pred_succ : (a_idx + 1) % D.length = i ∧ b_idx = (i + 1) % D.length ∧
        a_idx = (i + D.length - 1) % D.length := by
      dsimp only [a_idx, b_idx, k'] at hstep ⊢
      by_cases hwrap : k + 1 = (D.erase (D[i])).length
      · have hk_val : k = D.length - 2 := by omega
        have hk'_val : (k + 1) % (D.erase (D[i])).length = 0 := by rw [hwrap, Nat.mod_self]
        simp only [hk'_val] at hstep ⊢
        by_cases hi0 : i = 0
        · subst hi0
          have hk0 : ¬ (k < 0) := by omega
          have h00 : ¬ (0 < 0) := by omega
          simp only [hk0, h00, ↓reduceIte] at hstep ⊢
          have hmod1 : (k + 1 + 1) % D.length = 0 := by
            rw [show k + 1 + 1 = D.length by omega, Nat.mod_self]
          refine ⟨hmod1, ?_, ?_⟩
          · rw [Nat.mod_eq_of_lt (by omega)]
          · rw [zero_add, Nat.mod_eq_of_lt (by omega)]; omega
        · by_cases hi_last : i = D.length - 1
          · have hk_lt_i : k < i := by omega
            have h0_lt_i : 0 < i := by omega
            simp only [hk_lt_i, h0_lt_i, ↓reduceIte]
            refine ⟨?_, ?_, ?_⟩
            · rw [show k + 1 = i by omega, Nat.mod_eq_of_lt hi]
            · rw [show i + 1 = D.length by omega, Nat.mod_self]
            · rw [show i + D.length - 1 = k + D.length by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
          · exfalso; apply hstep
            have hk_not_lt : ¬ k < i := by omega
            have h0_lt_i : 0 < i := by omega
            simp only [hk_not_lt, h0_lt_i, ↓reduceIte]
            rw [show k + 1 + 1 = D.length by omega, Nat.mod_self]
      · have hk1_lt : k + 1 < (D.erase (D[i])).length := by omega
        have hk'_val : (k + 1) % (D.erase (D[i])).length = k + 1 := Nat.mod_eq_of_lt hk1_lt
        simp only [hk'_val] at hstep ⊢
        by_cases hki : k < i
        · by_cases hk1i : k + 1 < i
          · exfalso; apply hstep
            simp only [hki, hk1i, ↓reduceIte]
            rw [Nat.mod_eq_of_lt (by omega)]
          · have hki_eq : k + 1 = i := by omega
            have hnot : ¬ (k + 1 < i) := by omega
            simp only [hki, hnot, ↓reduceIte]
            refine ⟨by rw [hki_eq, Nat.mod_eq_of_lt hi], ?_, ?_⟩
            · rw [hki_eq, Nat.mod_eq_of_lt (by omega)]
            · rw [← hki_eq, show k + 1 + D.length - 1 = k + D.length by omega,
                Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        · exfalso; apply hstep
          have hnot1 : ¬ (k + 1 < i) := by omega
          simp only [hki, hnot1, ↓reduceIte]
          rw [Nat.mod_eq_of_lt (by omega)]
    obtain ⟨ha_mod, hb_mod, ha_eq⟩ := h_pred_succ
    rcases hv_idx with hv1 | hv2
    · right
      refine ⟨?_, ?_⟩
      · rw [hv1]; congr 1
      · have hadj := adj_getElem_mod_of_isCycleList hD ha_lt
        have h1 : D[(a_idx + 1) % D.length]'(Nat.mod_lt _ (by omega)) = D[i] := by
          congr 1
        rw [h1] at hadj
        exact hadj.symm
    · left
      refine ⟨?_, ?_⟩
      · rw [hv2]; congr 1
      · have hadj := adj_getElem_mod_of_isCycleList hD hi
        convert hadj using 2

/-- A valid contraction (with `4 < r.cycle.length` when `r.u ∈ r.cycle`) preserves
`HP25.IsCycleList`. -/
theorem ContractRecord.isCycleList_newGraph [DecidableEq V] {r : ContractRecord V}
    (hval : r.IsValid) (hlen : r.u ∈ r.cycle → 4 < r.cycle.length) :
    HP25.IsCycleList r.newGraph r.newCycle := by
  obtain ⟨-, hD, huv, hcase⟩ := hval
  unfold ContractRecord.newGraph ContractRecord.newCycle contractCycle
  split_ifs with hu
  · rcases hcase with hu' | hce
    · exact absurd hu hu'
    · exact isCycleList_erase_of_isCycleEdge hD hce (hlen hu)
  · refine ⟨hD.1, hD.2.1, fun p hp => ?_⟩
    have hp1 : p.1 ∈ r.cycle := (List.of_mem_zip hp).1
    have hp2 : p.2 ∈ r.cycle := List.mem_rotate.mp (List.of_mem_zip hp).2
    have hadj : r.graph.Adj p.1 p.2 := hD.2.2 p hp
    exact ⟨hadj.ne, fun h => hu (h ▸ hp1), fun h => hu (h ▸ hp2), Or.inl hadj⟩

/-! ### Single-record lift lemmas -/

/-- A subgraph relation `G' ≤ G` lifts `IsPathList`. -/
theorem IsPathList.mono {G G' : SimpleGraph V} {L : List V} (hle : G' ≤ G)
    (h : IsPathList G' L) : IsPathList G L :=
  ⟨h.1, h.2.1, h.2.2.imp fun _ _ hab => hle hab⟩

/-- A subgraph relation `G' ≤ G` lifts `IsDPathList`. -/
theorem IsDPathList.mono {G G' : SimpleGraph V} {D L : List V} (hle : G' ≤ G)
    (h : IsDPathList G' D L) : IsDPathList G D L :=
  ⟨h.1.mono hle, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A subgraph relation `G' ≤ G` lifts `IsCrossingPair`. -/
theorem IsCrossingPair.mono {G G' : SimpleGraph V} {D L₁ L₂ : List V} (hle : G' ≤ G)
    (h : IsCrossingPair G' D L₁ L₂) : IsCrossingPair G D L₁ L₂ :=
  ⟨h.1.mono hle, h.2.1.mono hle, h.2.2.1, h.2.2.2⟩

/-- Lifting a crossing pair across a valid replacement record using `Lemma1ReverseStatement`. -/
theorem isLiftOne_repl_of [DecidableEq V]
    {r : ReplRecord V} {D : List V} (hG : HP25.IsSupportedOn r.graph r.verts)
    (hD : HP25.IsCycleList r.graph D) (hval : r.IsValid D) {L₁ L₂ : List V}
    (hcross : IsCrossingPair r.newGraph D L₁ L₂) :
    (∃ P', IsLiftOne (CrossRecord.repl r) (L₁, L₂) P') ∧
      ∀ P', IsLiftOne (CrossRecord.repl r) (L₁, L₂) P' → IsCrossingPair r.graph D P'.1 P'.2 := by
  classical
  obtain ⟨hnotboth, hnone, huse₁⟩ := lemma1Reverse_proved.{u} r D L₁ L₂ hG hD hval hcross
  obtain ⟨-, -, huse₂⟩ := lemma1Reverse_proved.{u} r D L₂ L₁ hG hD hval hcross.swap
  constructor
  · by_cases hu₁ : usesNewEdge r.graph L₁
    · obtain ⟨⟨Y, hY⟩, -⟩ := huse₁ hu₁
      exact ⟨(spliceBetween r.boundary L₁ Y, L₂), Or.inr (Or.inl ⟨hu₁, Y, hY, rfl⟩)⟩
    · by_cases hu₂ : usesNewEdge r.graph L₂
      · obtain ⟨⟨Y, hY⟩, -⟩ := huse₂ hu₂
        exact ⟨(L₁, spliceBetween r.boundary L₂ Y), Or.inr (Or.inr ⟨hu₁, hu₂, Y, hY, rfl⟩)⟩
      · exact ⟨(L₁, L₂), Or.inl ⟨hu₁, hu₂, rfl⟩⟩
  · intro P' hP'
    rcases hP' with ⟨hu₁, hu₂, rfl⟩ | ⟨hu₁, Y, hY, rfl⟩ | ⟨hu₁, hu₂, Y, hY, rfl⟩
    · exact hnone hu₁ hu₂
    · exact (huse₁ hu₁).2 Y hY
    · exact ((huse₂ hu₂).2 Y hY).swap

/-- Lifting a crossing pair across a valid contraction record using the Section 11 statements. -/
theorem isLiftOne_contr_of [DecidableEq V]

     {r : ContractRecord V} (hval : r.IsValid)
    {L₁ L₂ : List V} (hcross : IsCrossingPair r.newGraph r.newCycle L₁ L₂) :
    (∃ P', IsLiftOne (CrossRecord.contr r) (L₁, L₂) P') ∧
      ∀ P', IsLiftOne (CrossRecord.contr r) (L₁, L₂) P' →
        IsCrossingPair r.graph r.cycle P'.1 P'.2 := by
  classical
  refine ⟨⟨(r.lift L₁, r.lift L₂), rfl⟩, ?_⟩
  rintro P' rfl
  obtain ⟨hG, hD, huv, hcase⟩ := hval
  unfold ContractRecord.lift
  unfold ContractRecord.newGraph ContractRecord.newCycle contractCycle at hcross
  split_ifs with hu hv
  · rcases hcase with hu' | hce
    · exact absurd hu hu'
    · simp only [hu, ↓reduceIte] at hcross
      exact lift11BothOn_proved.{u} r.graph r.verts r.cycle r.u r.v L₁ L₂ hG hD huv hce hcross
  · simp only [hu, ↓reduceIte] at hcross
    exact lift11OneOn_proved.{u} r.graph r.verts r.cycle r.u r.v L₁ L₂ hG hD huv hu hv hcross
  · simp only [hu, ↓reduceIte] at hcross
    exact lift11OffOff_proved.{u} r.graph r.verts r.cycle r.u r.v L₁ L₂ hG hD huv hu hv hcross

/-! ### Link (c): Lifting through the history -/

/-- **Lifting through the history** (`docs/crossing/crossing_extractor.tex`, Section 11):
"Thus every contraction lifts without a search. Reversing all accepted operations gives two
disjoint $C$-paths in the original graph, with alternating ends." -/
theorem liftHistory_of : LiftHistoryStatement.{u} := by
  intro V _ G S D recs G' S' D' L₁ L₂ hS hG hD hhist hlen hcross
  induction recs generalizing G S D with
  | nil =>
    cases hhist
    exact ⟨⟨(L₁, L₂), rfl⟩, fun P hP => by rw [show P = (L₁, L₂) from hP]; exact hcross⟩
  | cons rec rs ih =>
    cases rec with
    | repl r =>
      obtain ⟨rfl, rfl, hval, hhist'⟩ := hhist
      have hS_next : r.newVerts.Finite := hS.sdiff
      have hG_next : HP25.IsSupportedOn r.newGraph r.newVerts := r.isSupportedOn_newGraph hG hval
      have hD_next : HP25.IsCycleList r.newGraph D := r.isCycleList_newGraph hD hval
      have hlen_next : ∀ r', CrossRecord.contr r' ∈ rs → r'.u ∈ r'.cycle → 4 < r'.cycle.length :=
        fun r' hr' => hlen r' (List.mem_cons_of_mem _ hr')
      obtain ⟨⟨P', hP'⟩, hsound'⟩ := ih r.newGraph r.newVerts D hS_next hG_next hD_next hhist' hlen_next
      have hcross' : IsCrossingPair r.newGraph D P'.1 P'.2 := hsound' P' hP'
      obtain ⟨⟨P'', hP''⟩, _⟩ := isLiftOne_repl_of hG hD hval hcross'
      refine ⟨⟨P'', P', hP', hP''⟩, fun P ⟨Q, hQ, hQP⟩ => ?_⟩
      exact (isLiftOne_repl_of hG hD hval (hsound' Q hQ)).2 P hQP
    | contr r =>
      obtain ⟨rfl, rfl, rfl, hval, hhist'⟩ := hhist
      have hS_next : r.newVerts.Finite := hS.sdiff
      have hG_next : HP25.IsSupportedOn r.newGraph r.newVerts := r.isSupportedOn_newGraph hval
      have hD_next : HP25.IsCycleList r.newGraph r.newCycle :=
        r.isCycleList_newGraph hval (hlen r List.mem_cons_self)
      have hlen_next : ∀ r', CrossRecord.contr r' ∈ rs → r'.u ∈ r'.cycle → 4 < r'.cycle.length :=
        fun r' hr' => hlen r' (List.mem_cons_of_mem _ hr')
      obtain ⟨⟨P', hP'⟩, hsound'⟩ :=
        ih r.newGraph r.newVerts r.newCycle hS_next hG_next hD_next hhist' hlen_next
      have hcross' : IsCrossingPair r.newGraph r.newCycle P'.1 P'.2 := hsound' P' hP'
      obtain ⟨⟨P'', hP''⟩, _⟩ := isLiftOne_contr_of hval hcross'
      refine ⟨⟨P'', P', hP', hP''⟩, fun P ⟨Q, hQ, hQP⟩ => ?_⟩
      exact (isLiftOne_contr_of hval (hsound' Q hQ)).2 P hQP
    | del G₁ S₁ =>
      obtain ⟨hle, hsub, hG₁, _, hce, hhist'⟩ := hhist
      have hS_next : S₁.Finite := hS.subset hsub
      have hD_next : HP25.IsCycleList G₁ D :=
        ⟨hD.1, hD.2.1, fun p hp => hce p.1 p.2 ⟨p, hp, Or.inl rfl⟩⟩
      have hlen_next : ∀ r', CrossRecord.contr r' ∈ rs → r'.u ∈ r'.cycle → 4 < r'.cycle.length :=
        fun r' hr' => hlen r' (List.mem_cons_of_mem _ hr')
      obtain ⟨⟨P', hP'⟩, hsound'⟩ := ih G₁ S₁ D hS_next hG₁ hD_next hhist' hlen_next
      refine ⟨⟨P', P', hP', rfl⟩, fun P ⟨Q, hQ, hQP⟩ => ?_⟩
      rw [show P = Q from hQP]
      exact (hsound' Q hQ).mono hle

/-- Unconditional proof of `LiftHistoryStatement` by plugging in `lemma1Reverse_proved`,
`lift11OffOff_proved`, `lift11OneOn_proved`, and `lift11BothOn_proved`. -/
theorem liftHistory_proved : LiftHistoryStatement.{u} :=
  liftHistory_of

end GraphMinor.Crossing
