module

public import GraphMinor.GM06.Alg34DiscArrayBounds
public import GraphMinor.GM06.Alg34DualEdgeLoss
public import GraphMinor.GM06.Alg34DualSingletonExists
public import GraphMinor.GM06.Alg34StuckBounds
public import GraphMinor.Compute.GM06Alg34UniformSections
import GraphMinor.GM06.DualExists

/-!
# Bounds and search progress for the plain dual update

Use the canonical cuff identity to read the dual's counts and sections.
At a stuck connected state, the exhausted searches force a nonempty
boundary and an edge. VI (2.3) supplies a dual singleton, and deleting
any such singleton strictly lowers the fixed queue charge.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The plain dual swaps vertices and regions and preserves its edge count. -/
theorem discDualData_counts (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S)
    (hR : 0 < X.drawing.regions.length) :
    X.discDualData.drawing.n = X.drawing.regions.length ∧
      X.discDualData.drawing.regions.length = X.drawing.n ∧
      X.discDualData.drawing.ends.length = X.drawing.ends.length := by
  obtain ⟨c, heq⟩ := h.discDualData_eq_cuff hS hR
  rw [heq]
  exact ⟨rfl, X.drawing.dualData_regions_length _ _ _, X.drawing.dualData_edges_length _ _ _⟩

/-- The plain dual's three sections fit the fixed quadratic bounds. -/
theorem discDualData_sections_le (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S)
    (Q : ℕ) (hQ : X.drawing.cellCount ≤ Q) (hR : 0 < X.drawing.regions.length) :
    X.discDualData.drawing.regionWords.length ≤ gm06SectionCap Q ∧
      X.discDualData.drawing.cuffWords.length ≤ gm06SectionCap Q ∧
      X.discDualData.drawing.divisionWords.length ≤ gm06SectionCap Q := by
  obtain ⟨c, heq⟩ := h.discDualData_eq_cuff hS hR
  have hLN := h.drawing.cuff_nodup X.drawing.cuffs[c] (List.getElem_mem c.isLt)
  rw [heq]
  exact ⟨gm06Dual_regionWords_le_cap Q X.drawing hQ _ hR _,
    gm06Dual_cuffWords_le_cap Q X.drawing hQ _ hLN hR _,
    gm06Dual_divisionWords_le_cap Q X.drawing hQ _ hLN hR _⟩

/-- The plain dual search succeeds at a non-null connected state where
both deletion searches are exhausted. -/
theorem discDualData_findSingleton_exists (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hc : IsGraphConnected G.toGraph)
    (hD : IsDivision Δ) (hbd : divisionUnion Δ = G.V ∩ bd S) (hn : 0 < X.drawing.n)
    (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none) :
    ∃ v, gm06FindSingleton X.discDualData.drawing.division = some v := by
  have hR := h.drawing.regions_pos_of_vertices hS hp hn
  obtain ⟨c, heq⟩ := h.discDualData_eq_cuff hS hR
  obtain ⟨D, hd⟩ := exists_isDiscDualDrawing hS hp hc
  rw [heq]
  exact (h.gap c).dualData_findSingleton_exists hS hc hd hR hD hbd
    (h.drawing.boundary_nonempty_of_no_interior hn hI) hSing

/-- Every following dual singleton deletion strictly lowers the queue charge
at a stuck connected state, using only the fixed vertex-plus-region bound. -/
theorem discDualData_singleton_workWeight_lt (h : GM06GapInputRep X G Δ)
    (hS : IsClosedDiscSpace S) (hp : G.IsProper) (hc : IsGraphConnected G.toGraph)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hn : 0 < X.drawing.n)
    (hI : X.drawing.findInteriorComponent = none)
    (hSing : gm06FindSingleton X.drawing.division = none)
    (M : ℕ) (hM : X.drawing.n + X.drawing.regions.length ≤ M)
    (v : Fin X.discDualData.drawing.n) :
    (X.discDualData.singletonGapData v).drawing.workWeight (M + 1) < X.drawing.workWeight (M + 1) := by
  have hR := h.drawing.regions_pos_of_vertices hS hp hn
  have hE := h.drawing.edges_pos_of_stuck hc hbd hn hI hSing
  obtain ⟨c, heq⟩ := h.discDualData_eq_cuff hS hR
  obtain ⟨D, hd⟩ := exists_isDiscDualDrawing hS hp hc
  revert v
  rw [heq]
  intro v
  exact h.drawing.dualData_singleton_workWeight_lt hS hd M _ hR _ hn (by omega) hE v

end GraphMinor.Compute.GM06GapInputRep
