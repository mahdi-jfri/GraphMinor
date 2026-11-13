module

public import GraphMinor.GM06.Alg57CurrentTerminalTargets
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5LinkageEnds
import all GraphMinor.GM06.Alg57TerminalPathLink

/-!
# Terminal tracing representation from actual current arrays

For VI (5.7), page 133, a terminal trace stops before a cuff edge:
the removed inner end is absent, and any remaining outer end has
a marked tail. Every unmarked-tail end is therefore an ordinary
current edge in the prescribed region closure. All vertices of
the complete rotated walk have face-incidence labels, which are
injective for at least two paths. These facts close the remaining
fields of the actual terminal tracing representation.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

local notation "currentCut" => gm06CutDataOfLinkage x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff x.rotations (List.range x.vertexCount)
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (GM06CutData.rotations currentCut)))
local notation "gap" i:arg => gm06CutDart (2 * (rep.tagged.length + Fin.val (i : Fin k)) + 1) 0
local notation "edgeCount" => 2 * (rep.tagged.length + (k + k))
local notation "heads" => gm06TerminalHeadWords edgeCount (GM06CutData.origins currentCut)
set_option quotPrecheck false in
local notation "lower" hn:arg i:arg => gm06CutPathLabels x.vertexCount hn x.endpoints
  (x.linkage[Fin.val (i : Fin k)]'(by rw [rep.linkage.1]; exact Fin.isLt (i : Fin k)))
  (Fin.val (rep.source (i : Fin k))) true
set_option quotPrecheck false in
local notation "upper" hn:arg i:arg => gm06CutPathLabels x.vertexCount hn x.endpoints
  (x.linkage[Fin.val (finSuccCycle (i : Fin k))]'(by rw [rep.linkage.1]; exact Fin.isLt (finSuccCycle (i : Fin k))))
  (Fin.val (rep.source (finSuccCycle (i : Fin k)))) false
local notation "targets" hn:arg i:arg => gm06TerminalTargetBits (2 * x.vertexCount)
  (gm06CutVertex (Fin.val (rep.source (i : Fin k))) true)
  (List.map Fin.val (lower hn i)) (List.map Fin.val (upper hn i))

omit rep in
private theorem terminal_row_mem {row : List ℕ} {c q : ℕ}
    (hq : q ∈ gm06TerminalFaceDarts c row) : q ∈ row := by
  exact List.mem_rotate.mp ((List.dropLast_sublist _).subset hq)

private theorem terminal_head_vertex (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    {q : ℕ} (hq : q ∈ row) :
    ∃ u : Fin (2 * x.vertexCount), (heads)[q]?.getD 0 = u.val ∧
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 := by
  obtain ⟨_, hk, _, hc, hm⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hq
  have hmate := hm q hactive
  let u : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[gm06DartMate q]?.getD 0,
    (rep.cut_origins_valid _ hmate).1⟩
  exact ⟨u, terminalHeadWords_get _ (hk q ((hc q).mp hactive)),
    rep.selected_face_head_inc hG i row horbit hq u rfl⟩

private theorem terminal_source_vertex (hn : 0 < x.vertexCount)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q) (hgap : (gap i) ∈ row) :
    ∃ u : Fin (2 * x.vertexCount), u.val = gm06CutVertex (rep.source i).val true ∧
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 := by
  let u := gm06CutVertexFin x.vertexCount hn (rep.source i).val true
  have hval : u.val = gm06CutVertex (rep.source i).val true := cutVertexFin_val hn (rep.source i).isLt true
  have hmate : gm06DartMate (gap i) = gm06CutDart (2 * (rep.tagged.length + i.val)) 0 := by
    rw [← gm06CutDart_mate]
    simp [gm06DartMate]
  have horg : (currentCut).origins[gm06DartMate (gap i)]?.getD 0 = u.val := by
    rw [hmate, (rep.inner_copied_origins hG i).1, hval]
  exact ⟨u, hval, rep.selected_face_head_inc hG i row horbit hgap u horg⟩

private theorem terminal_walk_vertices_inc (hn : 0 < x.vertexCount)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q) (hgap : (gap i) ∈ row)
    {v : ℕ} (hv : v ∈ gm06WalkVertices (fun q => (heads)[q]?.getD 0)
      (gm06CutVertex (rep.source i).val true) (gm06TerminalFaceDarts (gap i) row)) :
    ∃ u : Fin (2 * x.vertexCount), u.val = v ∧
      (gm06IncV (2 * x.vertexCount) (currentCut).origins row)[u.val]?.getD 0 ≠ 0 := by
  simp only [gm06WalkVertices, List.mem_cons, List.mem_map] at hv
  rcases hv with rfl | ⟨q, hq, hqv⟩
  · exact rep.terminal_source_vertex hn hG i row horbit hgap
  · obtain ⟨u, hu, hui⟩ := rep.terminal_head_vertex hG i row horbit (terminal_row_mem hq)
    exact ⟨u, hu.symm.trans hqv, hui⟩

private theorem terminal_unmarked_tail_ordinary (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (hnd : row.Nodup) (hgap : (gap i) ∈ row) {q : ℕ}
    (hq : q ∈ gm06TerminalFaceDarts (gap i) row)
    (htarget : (targets hn i)[(currentCut).origins[q]?.getD 0]?.getD 0 = 0) :
    gm06UncutDart q < 2 * rep.tagged.length := by
  have hqr := terminal_row_mem hq
  have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hqr
  by_contra hlarge
  rcases rep.selected_face_cuff_cases hG i row horbit hqr (by omega) with he | ⟨j, he⟩
  · exact (terminalFaceDarts_rotate hnd hgap).2.1 (he ▸ hq)
  let u : Fin (2 * x.vertexCount) := ⟨(currentCut).origins[q]?.getD 0,
    (rep.cut_origins_valid q hactive).1⟩
  have hui := (incV_getD_ne_zero_iff _ _ _ u).mpr ⟨q, hqr, rfl⟩
  have hu : u.val = gm06CutVertex (rep.target j).val true := by
    dsimp only [u]
    rw [he]
    exact rep.positive_outer_origin hG j
  have hpoint : rep.cutVertexPoint u = cylinderM2Point k j := by
    trans rep.vertex (rep.target j)
    · apply congrArg rep.vertex
      apply Fin.ext
      change u.val / 2 = (rep.target j).val
      rw [hu, gm06CutVertex_project]
    · exact rep.target_point j
  obtain ⟨j', hj'⟩ := L.curve_one_surjective (mem_range_self j : cylinderM2Point k j ∈ cylinderM2 k)
  have huP : rep.cutVertexPoint u ∈ (L.pathDrawing j').V := by
    rw [hpoint, ← hj']
    exact (isPathDrawing_end_vertices (L.isPath j')).2
  have hj'i : j' = i := by
    rcases rep.selected_face_path_side hG i row horbit u hui j' ((L.pathDrawing j').V_subset_U huP) with h | h
    · exact h.2
    · have hpar : u.val % 2 = 0 := by simp [hu, gm06CutVertex]
      omega
  have hne : rep.cutVertexPoint u ≠ cylinderM1Point k i := by
    rw [hpoint]
    intro heq
    have hh := congrArg (fun p : ClosedCylinder => p.val.1) heq
    norm_num [cylinderM1Point, cylinderM2Point, cylinderPoint] at hh
  have hT : rep.cutVertexPoint u ∈ terminalTargets L i := by
    apply Or.inl
    exact ⟨hj'i ▸ huP, hne⟩
  have hbit := (rep.selected_face_terminal_target_iff hn hk hG i row horbit u hui).mpr hT
  exact hbit htarget

private theorem terminal_rep_of_row (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (i : Fin k) (row : List ℕ)
    (horbit : ∀ q, q ∈ row ↔ ∃ n, cutNext^[n] (gap i) = q)
    (hnd : row.Nodup) (hgap : (gap i) ∈ row) (horder : ∀ q ∈ row, row.formPerm q = cutNext q) :
    TerminalRep L i heads (targets hn i) (gm06TerminalFaceDarts (gap i) row)
      (gm06CutVertex (rep.source i).val true) (fun q => (currentCut).origins[q]?.getD 0)
      rep.cutPoint (fun q => rep.cutEdgePoint (q / 2)) := by
  refine {
    start_lab := ?_
    start_tgt := rep.terminal_source_unmarked hn i
    walk := ⟨_, rep.current_terminal_walk hG i row horbit hnd hgap horder⟩
    contact := rep.current_terminal_contact hn hG i row horbit hnd hgap horder
    target_iff := ?_
    edge := ?_
    inj := ?_ }
  · have hval := cutVertexFin_val hn (rep.source i).isLt true
    rw [← hval, rep.cutPoint_fin]
    exact rep.sourceCopy_point hn i
  · intro q hq
    obtain ⟨u, hu, hui⟩ := rep.terminal_head_vertex hG i row horbit (terminal_row_mem hq)
    rw [hu, rep.cutPoint_fin]
    exact rep.selected_face_terminal_target_iff hn hk hG i row horbit u hui
  · intro q hq htail
    have hqr := terminal_row_mem hq
    have hd := rep.terminal_unmarked_tail_ordinary hn hk hG i row horbit hnd hgap hq htail
    have hactive := rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q hqr
    obtain ⟨u, w, hu, hw, hlink⟩ := rep.cut_ordinary_isLink hG hactive hd
    obtain ⟨_, hkeys, _, hc, _⟩ := rep.cut_data_face_encoding hG (List.range x.vertexCount)
    refine ⟨?_, rep.selected_face_edge_subset hk hG
      (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩) i row horbit hqr hd⟩
    rw [hu, rep.cutPoint_fin, terminalHeadWords_get _ (hkeys q ((hc q).mp hactive)), hw, rep.cutPoint_fin]
    exact hlink
  · intro v hv w hw heq
    obtain ⟨u, hu, hui⟩ := rep.terminal_walk_vertices_inc hn hG i row horbit hgap hv
    obtain ⟨z, hz, hzi⟩ := rep.terminal_walk_vertices_inc hn hG i row horbit hgap hw
    have hp : rep.cutVertexPoint u = rep.cutVertexPoint z := by
      rw [← rep.cutPoint_fin, ← rep.cutPoint_fin, hu, hz]
      exact heq
    have huz := rep.selected_face_vertex_inj hk hG i row horbit u z hui hzi hp
    exact hu.symm.trans ((congrArg Fin.val huz).trans hz)

/-- The actual component face query, rotated before terminal
tracing, supplies every field of `TerminalRep` from the current
input for at least two linkage paths. -/
theorem component_terminal_rep (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (i : Fin k) :
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot currentCut rep.tagged.length i.val ∧
      ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) edgeCount
        (gm06CutComponentData currentCut root) (4 * (rep.tagged.length + i.val) + 1) =
          some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row, gm06IncE edgeCount row) ∧
      TerminalRep L i heads
        (gm06TerminalTargetBits (2 * x.vertexCount) (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
          ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD [])
            (x.innerCuff[i.val]?.getD 0) true).map Fin.val)
          ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[(finSuccCycle i).val]?.getD [])
            (x.innerCuff[(finSuccCycle i).val]?.getD 0) false).map Fin.val))
        (gm06TerminalFaceDarts (gap i) row) (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
        (fun q => (currentCut).origins[q]?.getD 0) rep.cutPoint (fun q => rep.cutEdgePoint (q / 2)) := by
  obtain ⟨root, hroot, row, hout, horbit, hnd, hgap, horder⟩ := rep.component_cut_face_order hG i
  have hpath (j : Fin k) : x.linkage[j.val]?.getD [] =
      x.linkage[j.val]'(by rw [rep.linkage.1]; exact j.isLt) := by
    rw [List.getElem?_eq_getElem (show j.val < x.linkage.length by rw [rep.linkage.1]; exact j.isLt)]
    rfl
  have hsource (j : Fin k) : x.innerCuff[j.val]?.getD 0 = (rep.source j).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  refine ⟨root, hroot, row, hout, ?_⟩
  rw [hpath i, hpath (finSuccCycle i), hsource i, hsource (finSuccCycle i)]
  exact rep.terminal_rep_of_row hn hk hG hno i row horbit hnd hgap horder

/-- The data of `component_terminal_rep`, together with the facts on
the selected row used to read the terminal output: the selected cuff
end is in the row, the row has no repetition, its rotated darts are
active, and a rotated dart with unmarked tail is an ordinary dart. -/
theorem component_terminal_rep_facts (hn : 0 < x.vertexCount) (hk : 1 < k)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L)
    (i : Fin k) :
    ∃ root : Fin (2 * x.vertexCount),
      root.val = gm06CutInnerRoot currentCut rep.tagged.length i.val ∧
      ∃ row : List ℕ, gm06CutFaceIncidence (2 * x.vertexCount) edgeCount
        (gm06CutComponentData currentCut root) (4 * (rep.tagged.length + i.val) + 1) =
          some (row, gm06IncV (2 * x.vertexCount) (currentCut).origins row, gm06IncE edgeCount row) ∧
      (gap i) ∈ row ∧ row.Nodup ∧
      (∀ q ∈ gm06TerminalFaceDarts (gap i) row, q ∈ (currentCut).activeDarts) ∧
      (∀ q ∈ gm06TerminalFaceDarts (gap i) row,
        (gm06TerminalTargetBits (2 * x.vertexCount) (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
          ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD [])
            (x.innerCuff[i.val]?.getD 0) true).map Fin.val)
          ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[(finSuccCycle i).val]?.getD [])
            (x.innerCuff[(finSuccCycle i).val]?.getD 0) false).map Fin.val))[
              (currentCut).origins[q]?.getD 0]?.getD 0 = 0 →
        gm06UncutDart q < 2 * rep.tagged.length) ∧
      TerminalRep L i heads
        (gm06TerminalTargetBits (2 * x.vertexCount) (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
          ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[i.val]?.getD [])
            (x.innerCuff[i.val]?.getD 0) true).map Fin.val)
          ((gm06CutPathLabels x.vertexCount hn x.endpoints (x.linkage[(finSuccCycle i).val]?.getD [])
            (x.innerCuff[(finSuccCycle i).val]?.getD 0) false).map Fin.val))
        (gm06TerminalFaceDarts (gap i) row) (gm06CutVertex (x.innerCuff[i.val]?.getD 0) true)
        (fun q => (currentCut).origins[q]?.getD 0) rep.cutPoint (fun q => rep.cutEdgePoint (q / 2)) := by
  obtain ⟨root, hroot, row, hout, horbit, hnd, hgap, horder⟩ := rep.component_cut_face_order hG i
  have hpath (j : Fin k) : x.linkage[j.val]?.getD [] =
      x.linkage[j.val]'(by rw [rep.linkage.1]; exact j.isLt) := by
    rw [List.getElem?_eq_getElem (show j.val < x.linkage.length by rw [rep.linkage.1]; exact j.isLt)]
    rfl
  have hsource (j : Fin k) : x.innerCuff[j.val]?.getD 0 = (rep.source j).val := by
    rw [rep.inner]
    simp only [List.getElem?_ofFn, j.isLt, dite_true, Option.getD_some]
  refine ⟨root, hroot, row, hout, hgap, hnd,
    fun q hq => rep.cut_face_row_active hG (List.range x.vertexCount) i horbit q (terminal_row_mem hq), ?_⟩
  rw [hpath i, hpath (finSuccCycle i), hsource i, hsource (finSuccCycle i)]
  exact ⟨fun q hq htail => rep.terminal_unmarked_tail_ordinary hn hk hG i row horbit hnd hgap hq htail,
    rep.terminal_rep_of_row hn hk hG hno i row horbit hnd hgap horder⟩

end GM06CurrentDrawingRep
end GraphMinor.GM06
