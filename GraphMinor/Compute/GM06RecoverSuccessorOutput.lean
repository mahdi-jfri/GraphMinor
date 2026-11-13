module

public import GraphMinor.GM06.Alg57InputWordBounds
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# UNDO returns the original-label successor output

The terminal phase of VI (5.7), page 133, produces ordinary rows
in the reached drawing. The actual inverse history recovers them
in the input graph. Equal initial tag, vertex and edge data then
identify those recovered rows with the original input enumeration.
The answer bit survives UNDO, so the result has exactly the public
successor output format, with a quadratic original-size time bound.
-/

public section
namespace GraphMinor.Compute
open Set GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM11 TwoPaths

private theorem linkage_encoding_congr
    {n k : ℕ} {G : Drawing ClosedCylinder} {M : CylinderLinkage k G}
    {tagged tagged' : List ((Fin n × Fin n) × ℕ)}
    {vertex vertex' : Fin n → ClosedCylinder}
    {edge : Fin tagged.length → Set ClosedCylinder}
    {edge' : Fin tagged'.length → Set ClosedCylinder} {rows : List (List ℕ)}
    (h : GM06LinkageRowsEncoding M tagged vertex edge rows)
    (ht : tagged = tagged') (hv : vertex = vertex') (he : HEq edge edge') :
    GM06LinkageRowsEncoding M tagged' vertex' edge' rows := by
  cases ht
  cases hv
  cases eq_of_heq he
  exact h

private theorem recover_cost_le {n m k N : ℕ} (hn : n ≤ N) (hm : m ≤ N) (hk : k ≤ N) :
    3 + n * (400 + 300 * (1 + k + 2 * m + n)) ≤ 2000 * (N + 1) ^ 2 := by
  calc
    3 + n * (400 + 300 * (1 + k + 2 * m + n)) ≤
        3 + N * (400 + 300 * (1 + N + 2 * N + N)) := by gcongr
    _ ≤ 2000 * (N + 1) ^ 2 := by nlinarith

/-- Given an actual terminal witness and its chronological inverse
history, RAM UNDO returns the public positive successor output in
the original input labels. Initial edge equality is ordinary label
interpretation data, including the labels of parallel edges. -/
theorem gm06RecoverContractionsProg_output
    {w k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {θ : ℝ}
    {L : CylinderLinkage k G} (input : GM06SuccessorInputRep x G L)
    (initial : GM06CurrentDrawingRep x G L)
    (htag : initial.tagged = input.graph.initialTagged)
    (hvertex : initial.vertex = input.graph.vertexLabels)
    (hedge : HEq initial.edge input.graph.edgeLabels)
    {Y : GM06UndoState x.vertexCount} {records : List (Option (ℕ × ℕ))}
    (trace : GM06UndoTrace x.vertexCount k initial.undoState Y records)
    (M : CylinderLinkage k Y.drawing) (hM : M.HasTheta (θ + 1 / (k : ℝ)))
    (rows : List (List ℕ)) (hrows : GM06LinkageRowsEncoding M Y.tagged Y.vertex Y.edge rows)
    (tail : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hcap : 1 + k + 2 * initial.tagged.length + x.vertexCount < 2 ^ w)
    (hhist : (gm06ContractionHistoryWords (records.filterMap id) ++ tail).length < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows)
    (h9 : s.arrs 9 = gm06ContractionHistoryWords (records.filterMap id) ++ tail)
    (h309 : s.regs 309 = (records.filterMap id).length) (h0 : s.regs 0 = 1) :
    ∃ sf t, Exec w gm06RecoverContractionsProg s sf t ∧
      t ≤ 2000 * (gm06SuccessorInputSize x + 1) ^ 2 ∧
      Keeps [309, 295, 23, 31, 7, 8, 9, 11, 313, 4, 323, 324, 98] [24, 27, 25, 8, 28] s sf ∧
      sf.regs 0 = 1 ∧ sf.regs 309 = 0 ∧
      sf.arrs 8 = gm06EncodeRows (gm06UndoTraceRows records rows) ∧
      GM06SuccessorOutputRep input θ (sf.regs 0) (sf.arrs 8) := by
  obtain ⟨sf, t, he, ht, hframe, hzero, hout, _, N, hN, henc⟩ :=
    gm06RecoverContractionsProg_current initial trace M hM rows hrows tail s hw hcap hhist h8 h9 h309
  have hbit : sf.regs 0 = 1 := (hframe.1 0 (by decide)).trans h0
  have henc' : GM06LinkageRowsEncoding N input.graph.initialTagged input.graph.vertexLabels
      input.graph.edgeLabels (gm06UndoTraceRows records rows) :=
    linkage_encoding_congr henc htag hvertex hedge
  have htagLen : initial.tagged.length = G.E.ncard := by
    rw [htag, GM06SuccessorGraphRep.initialTagged, List.length_map]
    exact input.graph.pairCount_eq
  obtain ⟨hn, hm, hk, _, _, _⟩ := input.size_bounds
  have hm' : initial.tagged.length ≤ gm06SuccessorInputSize x := by rw [htagLen]; exact hm
  refine ⟨sf, t, he, ht.trans (recover_cost_le hn hm' hk), hframe, hbit, hzero, hout, ?_⟩
  exact Or.inr ⟨hbit, N, gm06UndoTraceRows records rows, hout, hN, henc'⟩

end GraphMinor.Compute
