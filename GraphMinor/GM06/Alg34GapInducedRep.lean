module

public import GraphMinor.GM06.Alg34GapInducedCuffRep
public import GraphMinor.Compute.GM06Alg34GapInducedSlots

/-!
# The augmented input remains exact after vertex deletion

The computed base payload has its canonical induced-drawing labels.
For every cuff, the computed gap group is the retained/reindexed old
group and has the proved exact segment, order, and incidence
interpretation. Thus arbitrary induced deletions preserve the complete
augmented input relation used by the algorithm.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The finite augmented deletion payload represents the actual induced
drawing and restricted division for every proper disc input. -/
theorem inducedGapInput_rep (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (vs : List (Fin X.drawing.n)) :
    Nonempty (GM06GapInputRep (X.inducedGapInput vs)
      (induceDrawing G (h.drawing.vertexImage vs)) (h.drawing.inducedDivision vs)) := by
  classical
  have hc := X.inducedGapInput_gap_count vs h.gap_count
  have hg : ∀ c : Fin (X.inducedGapInput vs).drawing.cuffs.length,
      Nonempty (GM06CuffGapRep (h.drawing.inducedGapBaseRep vs) c
        ((X.inducedGapInput vs).gapRegions[c.val]'(by rw [hc]; exact c.isLt))) := by
    intro c
    rw [X.inducedGapInput_gap_get vs h.gap_count c]
    exact GM06CuffGapRep.inducedCuffGapRep hS hproper vs c
      (h.gap (Fin.cast (X.drawing.inducedData_cuffs_length vs) c))
  exact ⟨{
    drawing := h.drawing.inducedGapBaseRep vs
    gap_count := hc
    gap := fun c => Classical.choice (hg c) }⟩

end GraphMinor.Compute.GM06GapInputRep
