module

public import GraphMinor.GM06.Alg34GapInducedRep
public import GraphMinor.GM06.Alg34FiniteCounts
public import GraphMinor.GM06.Alg34RestrictionCrossFree
public import GraphMinor.Compute.GM06Alg34UniformSize

/-!
# Fixed bounds for induced deletion and component restriction

A represented induced drawing cannot gain vertices, edges or regions.
Its new region records have the fixed quadratic bound, while the cuff
and division sections cannot grow. These facts apply both to interior
component deletion and to every materialized component task.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- Every induced augmented input retains the fixed count and section bounds. -/
theorem inducedGapInput_loop_bounds (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (Q : ℕ) (hQ : X.drawing.cellCount ≤ Q)
    (hc : X.drawing.cuffWords.length ≤ gm06SectionCap Q)
    (hd : X.drawing.divisionWords.length ≤ gm06SectionCap Q) (vs : List (Fin X.drawing.n)) :
    let Y := X.inducedGapInput vs
    Y.drawing.n + Y.drawing.regions.length ≤ X.drawing.n + X.drawing.regions.length ∧
      Y.drawing.ends.length ≤ X.drawing.ends.length ∧ Y.drawing.cellCount ≤ X.drawing.cellCount ∧
      Y.drawing.regionWords.length ≤ gm06SectionCap Q ∧
      Y.drawing.cuffWords.length ≤ gm06SectionCap Q ∧ Y.drawing.divisionWords.length ≤ gm06SectionCap Q := by
  have hnr := h.drawing.inducedData_vertices_regions_le hS hp vs
  have he : (X.drawing.inducedData vs).ends.length ≤ X.drawing.ends.length := by
    rw [X.drawing.inducedData_ends_length]
    exact (List.length_filter_le _ _).trans_eq List.length_finRange
  refine ⟨hnr, he, ?_, gm06Induced_regionWords_le_cap Q X.drawing hQ vs,
    (gm06Induced_cuffWords_length_le X.drawing vs).trans hc,
    (gm06Induced_divisionWords_length_le X.drawing vs).trans hd⟩
  change (X.drawing.inducedData vs).cellCount ≤ X.drawing.cellCount
  unfold GM06DrawingData.cellCount
  omega

end GraphMinor.Compute.GM06GapInputRep
