module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialEdgeCollapse
import GraphMinor.GM06.Section5ContractedDrawing
import GraphMinor.GM06.Section5ContractedLinkage
import GraphMinor.GM06.Section5ContractionBoundary

/-!
# Applying Reduction 3 at an interior neighbour

Graph Minors VI, page 129, contracts the sole edge at an initial
vertex when its other end is not on the outer cuff. The rectangular
collapse supplies the topological map and homotopy. Deleting the
start before taking the image supplies the new drawing, and mapping
the suffix supplies its linkage. Together these give the actual
reduction used in the first sentence of the proof of (5.1).
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Under the printed local hypotheses of Reduction 3, page 129,
there is a reduced Section 5 drawing and linkage satisfying every
condition of the reduction. -/
theorem exists_section5_reduction3_of_interior_neighbour
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ (G' : Drawing ClosedCylinder) (L' : CylinderLinkage k G'),
      IsCylinderSection5Drawing k G' ∧ Section5Reduction3Step k G L G' L' := by
  obtain ⟨π, H, hH0, hH1, hHbd, hfiber, hhomeo, hi, hsurj, hopen, hfix⟩ :=
    exists_collapse_of_initial_valency_one_edge L hG i hval hl hvs hvC
  have hbd : ∀ x ∈ bd ClosedCylinder, π x = x :=
    fun x hx => (hH1 x).symm.trans (hHbd x hx 1)
  have hπfix : ∀ j, j ≠ i → ∀ x ∈ (L.pathDrawing j).U, π x = x :=
    fun j hj x hx => (hH1 x).symm.trans (hfix j hj x hx 1)
  obtain ⟨G', hU, hV, hE⟩ := exists_contracted_initial_edge_drawing hval hl hvs π hfiber hi
  obtain ⟨L', hpaths, hothers⟩ := exists_linkage_of_initial_edge_collapse L i hval hl hvs hvC
    π hfiber hi hbd hπfix hV hE
  refine ⟨G', L', isCylinderSection5Drawing_of_initial_edge_collapse hG hl π hfiber hi hbd hU hV,
    i, a, v, π, H, hval, hl.1, hl.2.2.1, hvs, hvC, hl, hH0, hH1, hHbd,
    hfiber, hhomeo, ?_, hsurj, hopen, hU, hV, hE, hpaths, hothers⟩
  intro x hx y hy hxy
  exact hi hx hy hxy

/-- The first step in VI (5.1), page 129: without a reduction, the
neighbour of a valency-one initial vertex must lie on the outer cuff. -/
theorem neighbour_mem_cuff2_of_no_section5_reduction
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v)
    (hvs : v ≠ cylinderM1Point k i) : v ∈ cylinderCuff2 := by
  by_contra hvC
  obtain ⟨G', L', hG', hred⟩ :=
    exists_section5_reduction3_of_interior_neighbour L hG i hval hl hvs hvC
  exact hno ⟨G', L', hG', Or.inr (Or.inr (Or.inl hred))⟩

end GraphMinor.GM06
