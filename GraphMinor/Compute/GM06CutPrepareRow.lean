module

public import GraphMinor.Compute.GM06CutDecodePosition
public import GraphMinor.Compute.GM06CutRowIndices

/-!
# Preparing a cut row from computed linkage and cuff tables

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) determines
the local case from the incoming and outgoing linkage marks, then reads
the two interval bounds in the original rotation. This composition
performs both operations, including for an empty row. Its exact
register state connects the four table entries to the row-selection
program. The only inputs are those tables, the row and its vertex label.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Registers changed while preparing a row's local cut metadata. -/
def gm06CutPrepareRowRegs : List ℕ := [650, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677]

/-- Load and decode the vertex's four marks, then compute its interval positions. -/
def gm06CutPrepareRowProg : Cmd := .seq gm06CutPreparePositionProg gm06CutRowIndicesProg

/-- The preparation computes its case and interval indices from the
actual tables and row. The second frame states that index preparation
preserves every field installed by the decoder. -/
theorem gm06CutPrepareRowProg_exec {w n q v : ℕ}
    (marks : GM06CutTables) (row : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hq : q < 2 ^ w) (hl : row.length < 2 ^ w)
    (hv : v < n) (hnd : row.Nodup) (hkeys : ∀ d ∈ row, d < q)
    (hlens : marks.incoming.length = n ∧ marks.outgoing.length = n ∧
      marks.cuffPositive.length = n ∧ marks.cuffNegative.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing)
    (h623 : s.arrs 623 = marks.cuffPositive) (h624 : s.arrs 624 = marks.cuffNegative)
    (h611 : s.arrs 611 = row) (h647 : s.regs 647 = q) (h666 : s.regs 666 = v) :
    let p := gm06CutPositionAt marks v
    let prepared := gm06CutDecodedState (gm06CutLoadedState s marks v) p
    ∃ sf t, Exec w gm06CutPrepareRowProg s sf t ∧ t ≤ 53 + 13 * q + 37 * row.length ∧
      Keeps gm06CutPrepareRowRegs [614] s sf ∧ Keeps [650, 675, 676, 677] [614] prepared sf ∧
      sf.arrs 614 = gm06RowPositions q row ∧
      sf.regs 676 = row.idxOf (gm06CutPositionBounds p).1 ∧
      sf.regs 677 = row.idxOf (gm06CutPositionBounds p).2 := by
  dsimp only
  have hw1 : 1 < 2 ^ w := by omega
  let p := gm06CutPositionAt marks v
  let prepared := gm06CutDecodedState (gm06CutLoadedState s marks v) p
  obtain ⟨tp, hep, htp⟩ := gm06CutPreparePositionProg_exec marks s hw hn hv hlens hwords
    h620 h621 h623 h624 h666
  have hkLoaded := gm06CutLoadedState_keeps s marks v
  have hkDecoded := gm06CutDecodedState_keeps (gm06CutLoadedState s marks v) p
  have hkPrep : Keeps gm06CutPrepareRowRegs [614] s prepared :=
    (hkLoaded.mono (by simp [gm06CutPrepareRowRegs]) (by simp)).trans hkDecoded
      (by simp [gm06CutPrepareRowRegs]) (by simp)
  have hfields := gm06CutPositionAt_word_bounds marks v hw hwords
  have hfirst : (gm06CutPositionBounds p).1 < 2 ^ w := hfields _ (by simp [p])
  have hlast : (gm06CutPositionBounds p).2 < 2 ^ w := hfields _ (by simp [p])
  obtain ⟨sf, ti, hei, hti, hki, hdi, hfi, hli⟩ := gm06CutRowIndicesProg_exec row
    (gm06CutPositionBounds p).1 (gm06CutPositionBounds p).2 prepared hw1 hq hl
    hfirst hlast hnd hkeys ((hkPrep.2 611 (by decide)).trans h611)
    ((hkPrep.1 647 (by simp [gm06CutPrepareRowRegs])).trans h647)
    (by simp [prepared, gm06CutDecodedState]) (by simp [prepared, gm06CutDecodedState])
  refine ⟨sf, tp + ti, .seq hep hei, by omega,
    hkPrep.trans hki (by simp [gm06CutPrepareRowRegs]) (fun _ h => h), hki, hdi, hfi, hli⟩

end GraphMinor.Compute
