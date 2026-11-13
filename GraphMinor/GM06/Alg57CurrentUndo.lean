module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.Compute.GM06UndoDrawing
import Mathlib.Data.Set.Card
import GraphMinor.Compute.GM06ApplyReduction3

/-!
# UNDO for a reached current drawing

Lemma 17 and Section 18 of the proof of VI (5.7), page 133,
recover an output linkage by processing the actual reduction
history backwards. The drawing-level recovery and its RAM program
are already proved in `GM06UndoDrawing`. Here the current relation
supplies the initial undo state and bounds the number of vertices
by the original slot count. Hence all recovery bounds use the
original finite input sizes. Chronological traces can be extended
by each actual reduction step of the forward loop.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The graph and ordinary labels remembered by an undo record. -/
@[expose] def GM06CurrentDrawingRep.undoState
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) : GM06UndoState x.vertexCount :=
  ⟨G, rep.tagged, rep.vertex, rep.edge⟩

/-- The current live slots are in bijection with the actual vertices.
Unused original slots therefore contribute nothing to this count. -/
theorem GM06CurrentDrawingRep.vertex_ncard_eq_live_card
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) : G.V.ncard = rep.live.card := by
  have hV : G.V = rep.vertex '' (rep.live : Set (Fin x.vertexCount)) := by
    ext v
    constructor
    · exact rep.vertex_cover v
    · rintro ⟨a, ha, rfl⟩
      exact rep.vertex_mem a ha
  rw [hV, rep.vertex_inj.ncard_image, Set.ncard_coe_finset]

/-- The number of actual vertices is at most the original slot count. -/
theorem GM06CurrentDrawingRep.vertex_ncard_le
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) : G.V.ncard ≤ x.vertexCount := by
  rw [rep.vertex_ncard_eq_live_card]
  exact (Finset.card_le_card (Finset.subset_univ rep.live)).trans_eq (by simp)

/-- Replacing the reference linkage changes only its ordinary path
rows in the current relation. All graph, cuff and positive rotation
data are retained literally. This is the current-state update for
a rerouting on the unchanged drawing. -/
@[expose] def GM06CurrentDrawingRep.withLinkage
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (M : CylinderLinkage k G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M rep.tagged rep.vertex rep.edge rows) :
    GM06CurrentDrawingRep {x with linkage := rows} G M :=
  { rep with linkage := hrows }

/-- A change of reference linkage has no inverse operation on an
arbitrary final linkage: its graph and ordinary labels are unchanged. -/
theorem GM06CurrentDrawingRep.withLinkage_undo
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    (M : CylinderLinkage k G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M rep.tagged rep.vertex rep.edge rows) :
    GM06UndoStep x.vertexCount k rep.undoState
      (rep.withLinkage M rows hrows).undoState none :=
  GM06UndoStep.unchanged rep.undoState

end GraphMinor.GM06
namespace GraphMinor.Compute
open Set Topology GraphMinor.Surface GraphMinor.GM06 TwoPaths

/-- Joining two chronological actual histories joins their lists
of optional contraction records in the same order. -/
theorem GM06UndoTrace.append {n k : ℕ} {X Y Z : GM06UndoState n}
    {rs ss : List (Option (ℕ × ℕ))} (hxy : GM06UndoTrace n k X Y rs)
    (hyz : GM06UndoTrace n k Y Z ss) : GM06UndoTrace n k X Z (rs ++ ss) := by
  induction hxy with
  | nil => exact hyz
  | cons step rest ih => exact .cons step (ih hyz)

/-- One actual forward reduction appends exactly its undo record
to the reached chronological history. -/
theorem GM06UndoTrace.snoc {n k : ℕ} {X Y Z : GM06UndoState n}
    {rs : List (Option (ℕ × ℕ))} {record : Option (ℕ × ℕ)}
    (hxy : GM06UndoTrace n k X Y rs) (step : GM06UndoStep n k Y Z record) :
    GM06UndoTrace n k X Z (rs ++ [record]) :=
  hxy.append (.cons step (.nil Z))

/-- Extending the actual chronological history agrees with the
literal pair writes to array 9. A deletion or rerouting consumes no
suffix words, while a contraction consumes exactly two. -/
theorem gm06UndoHistoryWords_snoc (records : List (Option (ℕ × ℕ)))
    (tail : List ℕ) (record : Option (ℕ × ℕ))
    (hroom : 2 * (records.filterMap id).length + 1 <
      (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length) :
    let hist := gm06ContractionHistoryWords (records.filterMap id) ++ tail
    let updated := match record with
      | none => hist
      | some (i, d) => (hist.set (2 * (records.filterMap id).length) i).set
          (2 * (records.filterMap id).length + 1) d
    ∃ tail', updated = gm06ContractionHistoryWords ((records ++ [record]).filterMap id) ++ tail' ∧
      tail'.length + 2 * record.isSome.toNat = tail.length := by
  have hlength (rs : List (ℕ × ℕ)) : (gm06ContractionHistoryWords rs).length = 2 * rs.length := by
    induction rs with
    | nil => rfl
    | cons p ps ih =>
      simp only [gm06ContractionHistoryWords, List.flatMap_cons, List.length_append,
        List.length_cons, List.length_nil] at *
      omega
  dsimp only
  cases record with
  | none => exact ⟨tail, by simp, by simp⟩
  | some p =>
    obtain ⟨i, d⟩ := p
    cases tail with
    | nil => simp only [List.length_append, List.length_nil, hlength] at hroom; omega
    | cons x tail =>
      cases tail with
      | nil => simp only [List.length_append, List.length_cons, List.length_nil, hlength] at hroom; omega
      | cons y rest =>
        refine ⟨rest, ?_, by simp⟩
        simpa only [List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
          id_eq, List.append_nil] using gm06ContractionHistoryWords_record (records.filterMap id) i d x y rest

/-- UNDO for a reached drawing, measured in the original input's
slot and edge counts. It returns an actual linkage in the original
graph, with exactly the computed path rows and the same winding.
All per-record and output-word bounds follow from the trace. -/
theorem gm06RecoverContractionsProg_current
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
    {Y : GM06UndoState x.vertexCount} {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k rep.undoState Y records) {θ : ℝ}
    (M : CylinderLinkage k Y.drawing) (hθ : M.HasTheta θ) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding M Y.tagged Y.vertex Y.edge rows)
    (tail : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hcap : 1 + k + 2 * rep.tagged.length + x.vertexCount < 2 ^ w)
    (hhist : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows)
    (h9 : s.arrs 9 = gm06ContractionHistoryWords (records.filterMap id) ++ tail)
    (h309 : s.regs 309 = (records.filterMap id).length) :
    ∃ sf t, Exec w gm06RecoverContractionsProg s sf t ∧
      t ≤ 3 + x.vertexCount *
        (400 + 300 * (1 + k + 2 * rep.tagged.length + x.vertexCount)) ∧
      Keeps [309, 295, 23, 31, 7, 8, 9, 11, 313, 4, 323, 324, 98] [24, 27, 25, 8, 28] s sf ∧
      sf.regs 309 = 0 ∧ sf.arrs 8 = gm06EncodeRows (gm06UndoTraceRows records rows) ∧
      (sf.arrs 8).length = (gm06EncodeRows rows).length + (records.filterMap id).length ∧
      ∃ N : CylinderLinkage k G, N.HasTheta θ ∧
        GM06LinkageRowsEncoding N rep.tagged rep.vertex rep.edge (gm06UndoTraceRows records rows) := by
  have hV := rep.vertex_ncard_le
  have hcap' : 1 + k + 2 * rep.tagged.length + G.V.ncard < 2 ^ w :=
    (Nat.add_le_add_left hV _).trans_lt hcap
  obtain ⟨sf, t, he, ht, hk, hzero, hout, hlen, N, hN, henc⟩ :=
    gm06RecoverContractionsProg_drawing_of_trace trace M hθ rows hrows tail s hw
      hcap' hhist h8 h9 h309
  refine ⟨sf, t, he, ?_, hk, hzero, hout, hlen, N, hN, henc⟩
  apply ht.trans
  apply Nat.add_le_add le_rfl
  apply Nat.mul_le_mul hV
  apply Nat.add_le_add le_rfl
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_left hV _

end GraphMinor.Compute
