module

public import GraphMinor.GM06.Alg34GapSingletonCorrect
public import GraphMinor.GM06.Alg34FiniteCounts
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Counts through complete singleton exhaustion

Each singleton deletion strictly loses a vertex, cannot gain edges and,
for represented proper disc drawings, cannot gain regions. Repeat these
three bounds along the finite recursion. The fixed vertex-plus-region
and total-cell bounds used by the queue driver therefore survive the
entire singleton phase.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The full singleton phase cannot increase vertices, edges or regions. -/
theorem reduceSingletons_counts_le (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hD : IsDivision Δ) :
    (gm06GapReduceSingletons X).drawing.n ≤ X.drawing.n ∧
      (gm06GapReduceSingletons X).drawing.ends.length ≤ X.drawing.ends.length ∧
      (gm06GapReduceSingletons X).drawing.regions.length ≤ X.drawing.regions.length := by
  induction X using gm06GapReduceSingletons.induct generalizing G Δ with
  | case1 X hnone =>
    rw [gm06GapReduceSingletons, hnone]
    exact ⟨le_rfl, le_rfl, le_rfl⟩
  | case2 X v hfind ih =>
    have hv := h.drawing.findSingleton_mem v hfind
    obtain ⟨hnew⟩ := h.singletonGapData_rep hS hp v hD hv
    have hD' : IsDivision (Δ \ {{(h.drawing.vertex v).val}}) :=
      ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1, hD.2.2.subset sdiff_subset⟩
    have hp' : (induceDrawing G (G.V \ {(h.drawing.vertex v).val})).IsProper :=
      induceDrawing_isProper G hp sdiff_subset
    obtain ⟨hn, he, hr⟩ := ih hnew hp' hD'
    have hn' := gm06SingletonData_n_lt X.drawing v
    have he' := gm06SingletonData_edges_le X.drawing v
    have hr' := h.drawing.inducedData_regions_le hS hp (X.drawing.singletonSurvivors v)
    rw [gm06GapReduceSingletons, hfind]
    exact ⟨hn.trans hn'.le, he.trans he', hr.trans hr'⟩

/-- The vertex-plus-region and total-cell bounds survive singleton exhaustion. -/
theorem reduceSingletons_cellCount_le (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hD : IsDivision Δ) :
    (gm06GapReduceSingletons X).drawing.cellCount ≤ X.drawing.cellCount ∧
      (gm06GapReduceSingletons X).drawing.n + (gm06GapReduceSingletons X).drawing.regions.length ≤
        X.drawing.n + X.drawing.regions.length := by
  obtain ⟨hn, he, hr⟩ := h.reduceSingletons_counts_le hS hp hD
  unfold GM06DrawingData.cellCount
  omega

end GraphMinor.Compute.GM06GapInputRep
