module

public import GraphMinor.Compute.GM06TerminalPhaseSteps
public import GraphMinor.Compute.GM06Reduction4PhaseExec
import GraphMinor.Compute.CrossingOpsBasic
import GraphMinor.Compute.GM06CutCSR
import GraphMinor.Compute.GM06RowPositions
import GraphMinor.Compute.GM06CutSplitRows
import GraphMinor.Compute.GM06CutFaceFacts
import GraphMinor.Compute.CrossingOpsCycleTest

/-!
# The whole terminal phase of VI (5.7)

When no reduction applies and the terminal valency test passes, the
loop of VI (5.7), page 133, builds the new linkage (Sections 15 and 16
of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)). The RAM program
`gm06TerminalPhaseProg` does this on the current arrays.

* It cuts the current drawing and saves the component records, as the
  Reduction 4 phase does.
* For each $i$ it reads the record of $K_i$, computes the face $F_i$,
  loads the two boundary rows, runs `TERMINAL_PATH`, finds the end
  vertex $u_i$ on the right copy of $P_{i+1}$, and splices: the new row
  is $Q_i$ projected, then $P_{i+1}$ after $u_i$. It appends the row to an
  output buffer.
* Finally it copies the buffer, which is the usual row encoding of the
  new linkage, into array 8 and sets the answer register 0 to 1.

The result is exactly `gm06TerminalPhase x m`. The time is cubic in
`gm06PhaseSize`.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-! ### The programs -/

/-- The reverse inner cuff dart `4 * (m + i) + 1` of component `i`. -/
def gm06TerminalCuffExpr : Expr :=
  .op .add (.op .mul (.const 4) (.op .add (.reg 684) (.reg 681))) (.const 1)

/-- The index of the next path, cyclically. -/
def gm06TerminalNextExpr : Expr := .op .mod (.op .add (.reg 681) (.const 1)) (.reg 685)

/-- The new row of component `i`, from its selected face in array 600.
The row is left in array 637. -/
def gm06TerminalRowProg : Cmd :=
  .seq gm06PhaseLoadBoundariesProg
    (.seq (.assign 648 (.reg 682))
      (.seq (.assign 667 gm06TerminalCuffExpr)
        (.seq gm06TerminalPathProg
          (.seq (gm06PhaseCopyProg 607 635)
            (.seq gm06TerminalEndProg
              (.seq (.assign 688 gm06TerminalNextExpr)
                (.seq (gm06PhaseSelectRowProg 642 610)
                  (.seq gm06TerminalIndexProg gm06Apply4RowProg))))))))

/-- One round: read the record of component `i`, select its face, build
its row (empty without a face) and append it to the output. -/
def gm06TerminalPhaseBody : Cmd :=
  .seq (.assign 661 (.reg 693))
    (.seq (gm06PhaseReadRecordProg 640 625)
      (.seq (.assign 693 (.reg 661))
        (.seq gm06PhaseComponentCountsProg
          (.seq gm06PhaseComponentFacesProg
            (.seq (.ite (.reg 668) gm06TerminalRowProg (.alloc 637 (.const 0)))
              gm06TerminalEmitProg)))))

/-- **The terminal phase of VI (5.7).** Cut, save the records, build
every new row, then install the new linkage in array 8 and answer 1. -/
def gm06TerminalPhaseProg : Cmd :=
  .seq gm06PhaseCutProg
    (.seq gm06Reduction4PhaseSaveProg
      (.seq gm06TerminalOutputInitProg
        (.seq (forUp 681 (.reg 685) gm06TerminalPhaseBody)
          (.seq (gm06PhaseCopyPrefixProg 643 8 (.reg 700)) (.assign 0 (.const 1))))))

/-- Registers the terminal phase may change: the answer register and
the reserved block `600..799`. -/
def gm06TerminalPhaseRegs : List ℕ := 0 :: List.range' 600 200

/-- Arrays the terminal phase may change: the linkage and the reserved
block `600..659`. -/
def gm06TerminalPhaseArrs : List ℕ := 8 :: List.range' 600 60

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem terminal_written_regs :
    gm06TerminalPhaseProg.writtenRegs ⊆ gm06TerminalPhaseRegs.toFinset := by decide

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem terminal_written_arrs :
    gm06TerminalPhaseProg.writtenArrs ⊆ gm06TerminalPhaseArrs.toFinset := by decide

/-- Every execution of the terminal phase changes only array 8, the
answer register 0 and the reserved scratch block. -/
theorem gm06TerminalPhaseProg_frame {w t : ℕ} {s sf : State}
    (he : Exec w gm06TerminalPhaseProg s sf t) :
    Keeps gm06TerminalPhaseRegs gm06TerminalPhaseArrs s sf := by
  constructor
  · intro r hr
    apply he.regs_eq_of_not_mem_writtenRegs
    intro hm
    exact hr (by simpa only [List.mem_toFinset] using terminal_written_regs hm)
  · intro a ha
    apply he.arrs_eq_of_not_mem_writtenArrs
    intro hm
    exact ha (by simpa only [List.mem_toFinset] using terminal_written_arrs hm)

/-! ### One terminal row -/

/-- A selected face contains its selecting dart. -/
theorem gm06CutFaceIncidence_target_mem {n m target : ℕ} (data : GM06CutData)
    (hnd : data.rotations.flatten.Nodup) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hactive : ∀ d ∈ data.activeDarts, d < 2 * m)
    (hcover : ∀ d, d ∈ data.activeDarts ↔ d ∈ data.rotations.flatten)
    (hpair : ∀ d ∈ data.activeDarts, gm06DartMate d ∈ data.activeDarts) {face incV incE : List ℕ}
    (h : gm06CutFaceIncidence n m data target = some (face, incV, incE)) : target ∈ face := by
  have ht : target ∈ data.activeDarts := by
    by_contra hnot
    unfold gm06CutFaceIncidence at h
    split at h
    · rename_i hlt
      have hfin := gm06CutFiniteRows_valid data hnd hkeys hactive hcover hpair
      have hnone := (gm06SelectedFace_none_iff _ _ ⟨target, hlt⟩ hfin.1 hfin.2.1 hfin.2.2).mpr
        (fun hmem => hnot ((gm06FinLabels_mem_iff data.activeDarts hactive _).mp hmem))
      simp [gm06SelectedFaceIncidence, hnone] at h
    · simp at h
  obtain ⟨row, hrow, hmem, _⟩ := gm06CutFaceIncidence_spec data hnd hkeys hactive hcover hpair ht
  rw [hrow] at h
  have hface : row.map Fin.val = face := congrArg Prod.fst (Option.some.inj h)
  rw [← hface]
  exact hmem

/-- The end vertex of a path is a value of the origin table, or `0`. -/
private theorem terminalPathEnd_lt {w : ℕ} (origins path : List ℕ) (cuff : ℕ)
    (hwords : ∀ v ∈ origins, v < 2 ^ w) : gm06TerminalPathEnd origins cuff path < 2 ^ w := by
  unfold gm06TerminalPathEnd gm06CutNeighbourHead
  cases h : origins[gm06DartMate (path.getLastD cuff)]? with
  | none => exact Nat.two_pow_pos w
  | some v => exact hwords v (List.mem_of_getElem? h)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- With the selected face of component `i` in array 600, the row
program leaves the new row of component `i` in array 637. -/
theorem gm06TerminalRowProg_exec {w m i : ℕ} (x : GM06SuccessorInput) (part : GM06CutData)
    (s : State) (face incV incE : List ℕ)
    (horig : x.endpoints.length = 2 * m) (hvalues : ∀ v ∈ x.endpoints, v < x.vertexCount)
    (hdarts : ∀ d ∈ x.linkage.flatten, d < 2 * m)
    (hinner : ∀ v ∈ x.innerCuff, v < x.vertexCount) (houter : ∀ v ∈ x.outerCuff, v < x.vertexCount)
    (hcount : x.linkage.length = x.innerCuff.length)
    (hrows : x.rotations.length = x.vertexCount) (hnd : x.rotations.flatten.Nodup)
    (hkeys : ∀ d ∈ x.rotations.flatten, d < 2 * (m + x.innerCuff.length + x.outerCuff.length))
    (hword : 10000 * gm06PhaseSize x m ^ 3 < 2 ^ w)
    (hi : i < x.innerCuff.length) (hp : part ∈ gm06PhaseComponents x m)
    (hface : gm06CutFaceIncidence (2 * x.vertexCount)
      (2 * (m + x.innerCuff.length + x.outerCuff.length)) part (4 * (m + i) + 1) =
        some (face, incV, incE))
    (h3 : s.arrs 3 = x.endpoints) (h6 : s.arrs 6 = x.innerCuff)
    (h642 : s.arrs 642 = gm06EncodeRows x.linkage) (h626 : s.arrs 626 = part.origins)
    (h600 : s.arrs 600 = face) (h681 : s.regs 681 = i) (h685 : s.regs 685 = x.innerCuff.length)
    (h682 : s.regs 682 = 2 * x.vertexCount) (h684 : s.regs 684 = m) :
    ∃ sf t, Exec w gm06TerminalRowProg s sf t ∧ t ≤ 10000 * gm06PhaseSize x m ∧
      sf.arrs 637 = gm06TerminalPhaseComponent x m i part := by
  obtain ⟨hnN, haugN, hpathN, _, _, hflatN, _, hN⟩ := gm06PhaseSize_facts x m
  have hw : 4 < 2 ^ w := gm06PhaseSize_fit x hword (by omega)
  have hw1 : 1 < 2 ^ w := by omega
  have hik : i < x.linkage.length := by omega
  have hk0 : 0 < x.innerCuff.length := by omega
  have hnext : gm06PhaseNext x i < x.innerCuff.length := Nat.mod_lt _ hk0
  have hnextPath : gm06PhaseNext x i < x.linkage.length := by omega
  have hcodeLen := gm06FaceCode_length x.linkage
  have hlinkWords := gm06PhaseLinkage_words x hdarts hword
  -- Facts about the component and its face.
  obtain ⟨_, _, _, hpnd, hcanon, hpair⟩ := gm06PhaseComponents_encoding x hnd part hp
  obtain ⟨_, hporigLen, hporigVals, hpkeys⟩ :=
    gm06PhaseComponents_sizes x hrows horig hvalues hinner houter hnd hkeys part hp
  have hcover : ∀ d, d ∈ part.activeDarts ↔ d ∈ part.rotations.flatten := by
    intro d
    rw [hcanon, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact and_iff_right_of_imp (hpkeys d)
  have hkeys' : ∀ d ∈ part.rotations.flatten,
      d < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) := by
    intro d hd; have := hpkeys d hd; omega
  have hactive' : ∀ d ∈ part.activeDarts,
      d < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) :=
    fun d hd => hkeys' d ((hcover d).mp hd)
  obtain ⟨_, _, hfnd, hflen, hfmem, _⟩ := gm06CutFaceIncidence_some_facts part hpnd hkeys' hactive'
    hcover hpair (by omega) hface
  have hcuffMem : 4 * (m + i) + 1 ∈ face :=
    gm06CutFaceIncidence_target_mem part hpnd hkeys' hactive' hcover hpair hface
  have hfaceDarts : ∀ d ∈ face, d < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) :=
    fun d hd => hkeys' d (hfmem d hd)
  have horiginWords : ∀ v ∈ part.origins, v < 2 ^ w :=
    fun v hv => (hporigVals v hv).trans (gm06PhaseSize_fit x hword (by omega))
  -- The two boundary rows.
  let left := gm06PhaseBoundaryVertices x i 0
  let upper := gm06PhaseBoundaryVertices x (gm06PhaseNext x i) 1
  let P := x.linkage[gm06PhaseNext x i]
  have hPlen : P.length ≤ x.linkage.flatten.length := gm06Row_length_le_flatten (List.getElem_mem _)
  have hLlen : x.linkage[i].length ≤ x.linkage.flatten.length := gm06Row_length_le_flatten (List.getElem_mem _)
  have hleftLen : left.length = x.linkage[i].length + 1 := by
    simp only [left, gm06PhaseBoundaryVertices, List.length_cons, List.length_map,
      List.getElem?_eq_getElem hik, Option.getD_some]
  have hupperLen : upper.length = P.length + 1 := by
    simp only [upper, P, gm06PhaseBoundaryVertices, List.length_cons, List.length_map,
      List.getElem?_eq_getElem hnextPath, Option.getD_some]
  have hleftB : ∀ v ∈ left, v < 2 * x.vertexCount := by
    have hv := hinner _ (List.getElem_mem hi)
    have hd : ∀ d ∈ x.linkage[i], d < 2 * m := fun d hd => hdarts d
      (List.mem_flatten.mpr ⟨_, List.getElem_mem hik, hd⟩)
    simpa only [left, gm06PhaseBoundaryVertices, gm06PhaseBoundaryRow, List.getElem?_eq_getElem hik,
      List.getElem?_eq_getElem hi, Option.getD_some] using
      gm06PhaseBoundaryRow_bounds x.endpoints x.linkage[i] horig hvalues hd hv (by decide : 0 ≤ 1)
  have hupperB : ∀ v ∈ upper, v < 2 * x.vertexCount := by
    have hv := hinner _ (List.getElem_mem hnext)
    have hd : ∀ d ∈ P, d < 2 * m := fun d hd => hdarts d
      (List.mem_flatten.mpr ⟨_, List.getElem_mem hnextPath, hd⟩)
    simpa only [upper, P, gm06PhaseBoundaryVertices, gm06PhaseBoundaryRow,
      List.getElem?_eq_getElem hnextPath, List.getElem?_eq_getElem hnext, Option.getD_some] using
      gm06PhaseBoundaryRow_bounds x.endpoints P horig hvalues hd hv (by decide : 1 ≤ 1)
  -- Step 1: load the boundary rows.
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hl₁, hu₁, _⟩ := gm06PhaseLoadBoundariesProg_exec x s (by omega)
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) horig hvalues hdarts
    hinner hcount hi (gm06PhaseSize_fit x hword (by omega)) hlinkWords h3 h6 h642 h681 h685
  -- Steps 2 and 3: the vertex count and the reverse inner cuff dart.
  let s₂ := s₁.setReg 648 (2 * x.vertexCount)
  have he₂ : Exec w (.assign 648 (.reg 682)) s₁ s₂ 2 :=
    .assign (Crossing.eval_reg ((hk₁.1 682 (by decide)).trans h682) (gm06PhaseSize_fit x hword (by omega)))
  let s₃ := s₂.setReg 667 (4 * (m + i) + 1)
  have he₃ : Exec w (.assign 667 gm06TerminalCuffExpr) s₂ s₃ 8 := by
    have h684₂ : s₂.regs 684 = m := by simp only [s₂, State.setReg_regs_ne _ _ (by decide : (684 : ℕ) ≠ 648)]; exact (hk₁.1 684 (by decide)).trans h684
    have h681₂ : s₂.regs 681 = i := by simp only [s₂, State.setReg_regs_ne _ _ (by decide : (681 : ℕ) ≠ 648)]; exact (hk₁.1 681 (by decide)).trans h681
    exact .assign (Crossing.eval_add (Crossing.eval_mul (Crossing.eval_const (c := 4) (by omega))
      (Crossing.eval_add (Crossing.eval_reg h684₂ (gm06PhaseSize_fit x hword (by omega)))
        (Crossing.eval_reg h681₂ (gm06PhaseSize_fit x hword (by omega))) (gm06PhaseSize_fit x hword (by omega)))
      (gm06PhaseSize_fit x hword (by omega))) (Crossing.eval_const (c := 1) (by omega))
      (gm06PhaseSize_fit x hword (by omega)))
  -- Step 4: TERMINAL_PATH.
  have hface₃ : s₃.arrs 600 = face := (hk₁.2 600 (by decide)).trans h600
  have horig₃ : s₃.arrs 626 = part.origins := (hk₁.2 626 (by decide)).trans h626
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hQ₄, _, _⟩ := gm06TerminalPathProg_exec
    (n := 2 * x.vertexCount) (m := 2 * (m + x.innerCuff.length + x.outerCuff.length))
    part.origins face left upper (4 * (m + i) + 1) s₃ (by omega) (gm06PhaseSize_fit x hword (by omega))
    (gm06PhaseSize_fit x hword (by omega)) (by rw [hporigLen]; ring) hporigVals
    (gm06PhaseSize_fit x hword (by omega)) (gm06PhaseSize_fit x hword (by omega)) hfnd hcuffMem
    hfaceDarts hleftB hupperB horig₃ hface₃ hl₁ hu₁ (by simp [s₃]) (by simp [s₃, s₂])
  let Q := gm06TerminalPath (2 * x.vertexCount) part.origins face left upper (4 * (m + i) + 1)
  obtain ⟨hQlen, hQmem⟩ := gm06TerminalPath_sublist_face (2 * x.vertexCount) part.origins face left upper
    (4 * (m + i) + 1) hcuffMem
  have hQlen' : Q.length + 1 ≤ face.length := hQlen
  have hQdarts : ∀ d ∈ Q, d < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) :=
    fun d hd => hfaceDarts d (hQmem d hd)
  have hQwords : ∀ d ∈ Q, d < 2 ^ w :=
    fun d hd => (hQdarts d hd).trans (gm06PhaseSize_fit x hword (by omega))
  -- Step 5: keep a copy of the path as the replacement row.
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, h635₅⟩ := gm06PhaseCopyProg_exec 607 635 (by decide) Q s₄ hw1
    (gm06PhaseSize_fit x hword (by omega)) hQwords hQ₄
  -- Step 6: the end vertex.
  have e₃₅ := Exec.seq he₄ he₅
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, hu₆⟩ := gm06TerminalEndProg_exec (M := 2 * (m + x.innerCuff.length + x.outerCuff.length))
    part.origins Q s₅ (by omega) (gm06PhaseSize_fit x hword (by omega)) (by rw [hporigLen]; ring) horiginWords
    hQdarts (show 4 * (m + i) + 1 < 2 * (2 * (m + x.innerCuff.length + x.outerCuff.length)) by omega)
    (gm06PhaseSize_fit x hword (by omega)) ((hk₅.2 607 (by decide)).trans hQ₄)
    ((e₃₅.arrs_eq_of_not_mem_writtenArrs (a := 626) (by decide)).trans horig₃)
    ((e₃₅.regs_eq_of_not_mem_writtenRegs (r := 667) (by decide)).trans (by simp [s₃]))
  let u := gm06TerminalPathEnd part.origins (4 * (m + i) + 1) Q
  -- Step 7: the next path index.
  have e₁₆ := Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆))))
  have h681₆ : s₆.regs 681 = i := (e₁₆.regs_eq_of_not_mem_writtenRegs (r := 681) (by decide)).trans h681
  have h685₆ : s₆.regs 685 = x.innerCuff.length :=
    (e₁₆.regs_eq_of_not_mem_writtenRegs (r := 685) (by decide)).trans h685
  let s₇ := s₆.setReg 688 (gm06PhaseNext x i)
  have he₇ : Exec w (.assign 688 gm06TerminalNextExpr) s₆ s₇ 6 :=
    .assign (Crossing.eval_mod (Crossing.eval_add (Crossing.eval_reg h681₆ (gm06PhaseSize_fit x hword (by omega)))
      (Crossing.eval_const (c := 1) (by omega)) (gm06PhaseSize_fit x hword (by omega)))
      (Crossing.eval_reg h685₆ (gm06PhaseSize_fit x hword (by omega))) hk0)
  -- Step 8: the next original path.
  have e₁₇ := Exec.seq e₁₆ he₇
  obtain ⟨s₈, t₈, he₈, ht₈, hk₈, hP₈⟩ := gm06PhaseSelectRowProg_exec (i := gm06PhaseNext x i) 642 610
    (by decide) (by decide) (by decide) (by decide) (by decide) x.linkage s₇ hw1 hnextPath
    ((e₁₇.arrs_eq_of_not_mem_writtenArrs (a := 642) (by decide)).trans h642)
    (gm06PhaseSize_fit x hword (by omega)) hlinkWords (by simp [s₇])
  -- Step 9: the position of the end vertex.
  have e₂₈ := Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ (Exec.seq he₆ (Exec.seq he₇ he₈)))))
  have hupperWords : ∀ v ∈ upper, v < 2 ^ w :=
    fun v hv => (hupperB v hv).trans (gm06PhaseSize_fit x hword (by omega))
  obtain ⟨s₉, t₉, he₉, ht₉, hk₉, hj₉⟩ := gm06TerminalIndexProg_exec (u := u) upper P s₈ hw1
    (by omega) (gm06PhaseSize_fit x hword (by omega)) hupperWords
    (terminalPathEnd_lt part.origins Q (4 * (m + i) + 1) horiginWords)
    ((e₂₈.arrs_eq_of_not_mem_writtenArrs (a := 608) (by decide)).trans hu₁) hP₈
    ((hk₈.1 702 (by decide)).trans (by
      simp only [s₇, State.setReg_regs_ne _ _ (by decide : (702 : ℕ) ≠ 688)]; exact hu₆))
  -- Step 10: the splice.
  have e₅₉ := Exec.seq he₆ (Exec.seq he₇ (Exec.seq he₈ he₉))
  have hjle : (upper.take P.length).idxOf u ≤ P.length := by
    have h := List.idxOf_le_length (a := u) (l := upper.take P.length)
    simp only [List.length_take] at h
    omega
  obtain ⟨sf, t₁₀, he₁₀, ht₁₀, _, hrow⟩ := gm06Apply4RowProg_exec
    (j := (upper.take P.length).idxOf u) Q P s₉ hw (gm06PhaseSize_fit x hword (by omega)) hjle hQwords
    (fun d hd => (hdarts d (List.mem_flatten.mpr ⟨_, List.getElem_mem hnextPath, hd⟩)).trans
      (gm06PhaseSize_fit x hword (by omega)))
    ((e₅₉.arrs_eq_of_not_mem_writtenArrs (a := 635) (by decide)).trans h635₅)
    ((hk₉.2 610 (by simp)).trans hP₈) hj₉
  refine ⟨sf, t₁ + (2 + (8 + (t₄ + (t₅ + (t₆ + (6 + (t₈ + (t₉ + t₁₀)))))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ (.seq he₈ (.seq he₉ he₁₀)))))))),
    ?_, ?_⟩
  · omega
  · rw [hrow, gm06TerminalPhaseComponent_of_some hface]
    simp only [gm06Apply4Row, List.getElem?_eq_getElem hnextPath, Option.getD_some]
    rw [gm06_drop_idxOf_take]

end GraphMinor.Compute
