module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5LinkageEnds
import GraphMinor.GM06.Section3Basic

/-!
# Excluding the second reduction in VI (5.1)

A separation with overlap at most one initial vertex allows deletion
of the side not used by the linkage. Containment of the linkage keeps
all boundary vertices on the retained side. We construct the unchanged
linkage there, so absence of Reduction 2 rules out every proper retained
side of this form, as required in the region argument on page 129.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- A separation whose first side contains the linkage realizes
Reduction 2 of VI Section 5, page 129. -/
theorem exists_reduction2_of_linkage_separation
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hoverlap : G₁.V ∩ G₂.V ⊆ {cylinderM1Point k i})
    (hne : G₁.toGraph ≠ G.toGraph)
    (hpaths : ∀ j, (L.pathDrawing j).IsSubdrawing G₁) :
    ∃ L₁ : CylinderLinkage k G₁, IsCylinderSection5Drawing k G₁ ∧
      Section5Reduction2Step k G L G₁ L₁ := by
  have hsub₁ : G₁.IsSubdrawing G := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have hsub₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  let L₁ : CylinderLinkage k G₁ :=
    { pathDrawing := L.pathDrawing
      curve := L.curve
      isSubdrawing := fun j => ⟨hpaths j, (hpaths j).U_subset⟩
      isPath := L.isPath
      curve_parametrizes := L.curve_parametrizes
      curve_one_mem := L.curve_one_mem
      pairwise_disjoint := L.pairwise_disjoint }
  have hG₁ := isCylinderSection5Drawing_of_contains_linkage L hG hsub₁ hpaths
  exact ⟨L₁, hG₁, i, G₂, hsep, hsub₁.U_subset, hsub₂.U_subset, hoverlap, hne, rfl, rfl⟩

/-- The absence of all Section 5 reductions implies the corresponding
conclusion obtained by excluding Reduction 2 alone. -/
theorem reduction2_applies_of_linkage_separation
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hoverlap : G₁.V ∩ G₂.V ⊆ {cylinderM1Point k i})
    (hne : G₁.toGraph ≠ G.toGraph)
    (hpaths : ∀ j, (L.pathDrawing j).IsSubdrawing G₁) :
    Section5AnyReductionApplies k G L := by
  obtain ⟨L₁, hG₁, hRed⟩ := exists_reduction2_of_linkage_separation L hG i hsep hoverlap hne hpaths
  exact ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩

/-- If no Section 5 reduction applies, a side containing the linkage
cannot be a proper side of a separation attached at one initial vertex. -/
theorem eq_of_linkage_separation_of_no_section5_reduction
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hoverlap : G₁.V ∩ G₂.V ⊆ {cylinderM1Point k i})
    (hpaths : ∀ j, (L.pathDrawing j).IsSubdrawing G₁) :
    G₁.toGraph = G.toGraph := by
  by_contra hne
  exact hno (reduction2_applies_of_linkage_separation L hG i hsep hoverlap hne hpaths)

end GraphMinor.GM06
