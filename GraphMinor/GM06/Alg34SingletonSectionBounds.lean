module

public import GraphMinor.GM06.Alg34SingletonCountBounds
public import GraphMinor.Compute.GM06Alg34UniformSize
import GraphMinor.GM06.Alg34SingletonExhaustCorrect

/-!
# Uniform section bounds through singleton exhaustion

A singleton deletion cannot enlarge the cuff or division sections.
Its newly computed region section is bounded by the fixed cell count.
The geometric region monotonicity retains that cell count at the next
step. Induction therefore retains all three fixed section bounds for
the complete singleton phase.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- Exhaustive singleton deletion retains fixed bounds on all three sections. -/
theorem reduceSingletons_sections_le (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hD : IsDivision Δ)
    (Q : ℕ) (hQ : X.drawing.cellCount ≤ Q)
    (hr : X.drawing.regionWords.length ≤ gm06SectionCap Q)
    (hc : X.drawing.cuffWords.length ≤ gm06SectionCap Q)
    (hd : X.drawing.divisionWords.length ≤ gm06SectionCap Q) :
    (gm06GapReduceSingletons X).drawing.regionWords.length ≤ gm06SectionCap Q ∧
      (gm06GapReduceSingletons X).drawing.cuffWords.length ≤ gm06SectionCap Q ∧
      (gm06GapReduceSingletons X).drawing.divisionWords.length ≤ gm06SectionCap Q := by
  induction X using gm06GapReduceSingletons.induct generalizing G Δ with
  | case1 X hnone =>
    rw [gm06GapReduceSingletons, hnone]
    exact ⟨hr, hc, hd⟩
  | case2 X v hfind ih =>
    have hv := h.drawing.findSingleton_mem v hfind
    obtain ⟨hnew⟩ := h.singletonGapData_rep hS hp v hD hv
    have hD' : IsDivision (Δ \ {{(h.drawing.vertex v).val}}) :=
      ⟨hD.1.subset sdiff_subset, fun δ hδ => hD.2.1 δ hδ.1, hD.2.2.subset sdiff_subset⟩
    have hp' : (induceDrawing G (G.V \ {(h.drawing.vertex v).val})).IsProper :=
      induceDrawing_isProper G hp sdiff_subset
    have hn := gm06SingletonData_n_lt X.drawing v
    have he := gm06SingletonData_edges_le X.drawing v
    have hr' := h.drawing.inducedData_regions_le hS hp (X.drawing.singletonSurvivors v)
    have hQ' : (X.singletonGapData v).drawing.cellCount ≤ Q := by
      unfold GM06DrawingData.cellCount at hQ ⊢
      change (X.drawing.singletonData v).n + ((X.drawing.singletonData v).ends.length +
        (X.drawing.inducedData (X.drawing.singletonSurvivors v)).regions.length) ≤ Q
      omega
    have hreg := gm06Induced_regionWords_le_cap Q X.drawing hQ (X.drawing.singletonSurvivors v)
    have hcuff := (gm06Induced_cuffWords_length_le X.drawing (X.drawing.singletonSurvivors v)).trans hc
    have hdiv := (gm06Induced_divisionWords_length_le X.drawing (X.drawing.singletonSurvivors v)).trans hd
    rw [gm06GapReduceSingletons, hfind]
    exact ih hnew hp' hD' hQ' hreg hcuff hdiv

end GraphMinor.Compute.GM06GapInputRep
