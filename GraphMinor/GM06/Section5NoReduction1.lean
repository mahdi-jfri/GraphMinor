module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM11.Defs
import GraphMinor.GM06.Section5CoverEdgeLift
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5
import GraphMinor.GM06.Section4SubgraphDrawing
import GraphMinor.GM11.Forest
import GraphMinor.GM11.Section5

/-!
# Excluding the first reduction in VI (5.1)

An edge with a clockwise lift misses every linkage path. Deleting it
therefore preserves the linkage and all boundary vertices and realizes
the corrected Reduction 1. For at least two paths, the printed incidence
and preceding-strip conditions suffice, by the proved agreement lemma.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM11

/-- An edge in a linkage strip is not an edge of any linkage path. -/
theorem edge_not_mem_linkage_of_subset_strip
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    {e : Set ClosedCylinder} (he : e ∈ G.E) {i : Fin k}
    (hstrip : e ⊆ cylinderStrip L i) (j : Fin k) :
    e ∉ (L.pathDrawing j).E := by
  intro hej
  obtain ⟨x, hx⟩ := he.1
  have houtside : x ∉ ⋃ j : Fin k, (L.pathDrawing j).U :=
    (connectedComponentIn_subset _ _ (hstrip hx)).2
  exact houtside (mem_iUnion.mpr ⟨j, (hej.2.1 hx).1⟩)

/-- Deleting an edge with a clockwise initial lift realizes the corrected
Reduction 1, with an unchanged linkage, in VI Section 5, page 128. -/
theorem exists_reduction1_deleting_clockwise_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) {i : Fin k} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hside : IsClockwiseInitialEdge L i e) :
    ∃ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ ∧ Section5Reduction1Step k G L G₁ L₁ ∧
      G₁.V = G.V ∧ G₁.E = G.E \ {e} ∧ G₁.U = G.U \ e := by
  have hstrip := hside.incident_and_subset.2
  let G' := G.deleteEdge e
  have hV : G'.V = G.V := GM11.deleteEdge_V G e
  have hE : G'.E = G.E \ {e} := deleteEdge_E G e
  have hU : G'.U = G.U \ e := deleteEdge_U G he
  have hpaths (j : Fin k) : (L.pathDrawing j).IsSubdrawing G' := by
    constructor
    · rw [hV]
      exact (L.isSubdrawing j).1.1
    · rw [hE]
      intro e' he'
      refine ⟨(L.isSubdrawing j).1.2 he', ?_⟩
      intro heq
      have he'e : e' = e := heq
      exact edge_not_mem_linkage_of_subset_strip L he hstrip j (he'e ▸ he')
  let L' : CylinderLinkage k G' :=
    { pathDrawing := L.pathDrawing
      curve := L.curve
      isSubdrawing := fun j => ⟨hpaths j, (hpaths j).U_subset⟩
      isPath := L.isPath
      curve_parametrizes := L.curve_parametrizes
      curve_one_mem := L.curve_one_mem
      pairwise_disjoint := L.pairwise_disjoint }
  have hGp : G'.IsProper := isProper_of_isSubdrawing hG.2.1 (deleteEdge_isSubdrawing G e)
  have hG' : IsCylinderSection5Drawing k G' := ⟨hG.1, hGp, by rw [hV]; exact hG.2.2⟩
  exact ⟨G', L', hG', ⟨i, e, he, hside, hV, hE, hU, rfl, rfl⟩, hV, hE, hU⟩

/-- Clearing the chosen clockwise edge gives Reduction 1 on the
concrete deleted drawing, with unchanged path and curve data. -/
theorem exists_reduction1_on_deleted_drawing
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) {i : Fin k} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hside : IsClockwiseInitialEdge L i e) :
    ∃ M : CylinderLinkage k (G.deleteEdge e),
      IsCylinderSection5Drawing k (G.deleteEdge e) ∧
      Section5Reduction1Step k G L (G.deleteEdge e) M ∧
      M.pathDrawing = L.pathDrawing ∧ M.curve = L.curve := by
  obtain ⟨G₁, M, hG₁, hRed, hV, hE, _⟩ :=
    exists_reduction1_deleting_clockwise_edge L hG he hside
  have hEq : G₁ = G.deleteEdge e := Drawing.ext_of_V_E
    (hV.trans (GM11.deleteEdge_V G e).symm) (hE.trans (deleteEdge_E G e).symm)
  subst G₁
  have hdata := hRed
  obtain ⟨_, _, _, _, _, _, _, hpaths, hcurves⟩ := hdata
  exact ⟨M, hG₁, hRed, hpaths, hcurves⟩

/-- Deleting a clockwise initial edge realizes the corrected Reduction 1. -/
theorem exists_reduction1_of_clockwise_initial_edge
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) {i : Fin k} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hside : IsClockwiseInitialEdge L i e) :
    ∃ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ ∧ Section5Reduction1Step k G L G₁ L₁ := by
  obtain ⟨G₁, L₁, hG₁, hRed, _⟩ := exists_reduction1_deleting_clockwise_edge L hG he hside
  exact ⟨G₁, L₁, hG₁, hRed⟩

/-- For k ≥ 2, the printed edge condition constructs the corrected deletion.
The equivalence of the two incidence conditions supplies its actual lift. -/
theorem exists_reduction1_of_incident_edge_in_strip
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {i : Fin k} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hs : cylinderM1Point k i ∈ closure e)
    (hstrip : e ⊆ cylinderStrip L (finPredCycle i)) :
    ∃ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ ∧ Section5Reduction1Step k G L G₁ L₁ := by
  exact exists_reduction1_of_clockwise_initial_edge L hG he
    ((isClockwiseInitialEdge_iff_of_two_le L hG hk i he).mpr ⟨hs, hstrip⟩)

/-- The incident-edge deletion is an applicable Section 5 reduction. -/
theorem reduction1_applies_of_incident_edge_in_strip
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) {i : Fin k} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hs : cylinderM1Point k i ∈ closure e)
    (hstrip : e ⊆ cylinderStrip L (finPredCycle i)) :
    Section5AnyReductionApplies k G L := by
  obtain ⟨G₁, L₁, hG₁, hRed⟩ := exists_reduction1_of_incident_edge_in_strip L hk hG he hs hstrip
  exact ⟨G₁, L₁, hG₁, Or.inl hRed⟩

/-- If no Section 5 reduction applies, no incident edge lies in the
preceding strip. This is the Reduction 1 exclusion used in VI (5.1). -/
theorem not_subset_strip_of_no_reduction1
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction1Step k G L G₁ L₁) {i : Fin k} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hs : cylinderM1Point k i ∈ closure e) :
    ¬ e ⊆ cylinderStrip L (finPredCycle i) := by
  intro hstrip
  obtain ⟨G₁, L₁, hG₁, hRed⟩ := exists_reduction1_of_incident_edge_in_strip L hk hG he hs hstrip
  exact hno G₁ L₁ hG₁ hRed

/-- Excluding all reductions in particular excludes Reduction 1. -/
theorem not_subset_strip_of_no_section5_reduction
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) {i : Fin k} {e : Set ClosedCylinder}
    (he : e ∈ G.E) (hs : cylinderM1Point k i ∈ closure e) :
    ¬ e ⊆ cylinderStrip L (finPredCycle i) := by
  exact not_subset_strip_of_no_reduction1 L hk hG
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inl hRed⟩) he hs

end GraphMinor.GM06
