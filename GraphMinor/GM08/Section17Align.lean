module

public import GraphMinor.GM08.Section17Defs
public import GraphMinor.GM08.Section15Defs
import GraphMinor.GM08.Section17Cylinder
import GraphMinor.GM08.Section18Align

/-!
# Aligning the fixed-cuff classes

Two grafts in the same class from VIII Section 17 have equal counts on
both cuffs. Move the target drawing by a cuff-preserving homeomorphism
to match the host's boundary vertices. This supplies the boundary
condition for VII (9.3) in the proof of VIII (17.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u v

/-- Draw two members of the same fixed-cuff class with their boundary
vertex sets aligned, as needed in VIII (17.2), page 284. -/
theorem exists_aligned_drawings_of_mem_classBCuffCounts {S : Type}
    [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} {Y X : Graft α β} {k₁ k₂ : ℕ}
    (hY : Y ∈ classBCuffCounts S C D k₁ k₂)
    (hX : X ∈ classBCuffCounts S C D k₁ k₂) :
    ∃ (DY : GraftDrawing Y.G Y.T S) (DX : GraftDrawing X.G X.T S),
      DY.drawing.V ∩ bd S = DX.drawing.V ∩ bd S ∧
      (DX.drawing.V ∩ C).ncard = k₁ ∧ (DX.drawing.V ∩ D).ncard = k₂ := by
  obtain ⟨DY, hYC, hYD⟩ := hY
  obtain ⟨DX, hXC, hXD⟩ := hX
  obtain ⟨cap, hcapC, hcapD⟩ := CylinderSphereCap.exists_with_cuffs hS hC hD hCD
  have hcuffs : cuffs S = {C, D} := by rw [cap.cuffs_eq, hcapC, hcapD]
  have hcounts : ∀ F ∈ cuffs S,
      (DY.drawing.V ∩ F).ncard = (DX.drawing.V ∩ F).ncard := by
    intro F hF
    rw [hcuffs] at hF
    rcases hF with rfl | rfl
    · exact hYC.trans hXC.symm
    · exact hYD.trans hXD.symm
  obtain ⟨DY', hbd⟩ := exists_graftDrawing_aligned_boundary hS.1 DY DX hcounts
  exact ⟨DY', DX, hbd, hXC, hXD⟩

end GraphMinor.GM08
