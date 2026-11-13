module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutComp

/-!
# Every component of a cut reaches the cut

For a connected original surface and a nonempty cutting set, no component
of the cut surface can avoid the cutting set. Otherwise the complement of
that component is a nonempty open and closed set containing every lift,
which the cut-map lemma forces to be the whole surface. Each component
therefore has a boundary point. This excludes closed components in the
cut analysis of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- Every component of a surface cut along a nonempty set meets a lift of
that set. This is a local fact used in the cases of VIII (18.2), page 286. -/
theorem component_meets_cut {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    [ConnectedSpace S] (hS : IsSurface S) (hT : IsSurface T)
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F) (hF : F.Nonempty)
    {C : Set T} (hC : C ∈ spaceComponents T) : (C ∩ ψ ⁻¹' F).Nonempty := by
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  have := hT.locallyConnected
  rw [spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  by_contra hnot
  have haway : ψ ⁻¹' F ⊆ (connectedComponent x)ᶜ := by
    intro y hy hx
    exact hnot ⟨y, hx, hy⟩
  obtain ⟨z, hz⟩ := hF
  obtain ⟨y, hy⟩ := hcut.2.1 z
  have hyF : y ∈ ψ ⁻¹' F := by change ψ y ∈ F; rw [hy]; exact hz
  have hfull := eq_univ_of_cut hcut
    (W := (connectedComponent x)ᶜ)
    ⟨isOpen_connectedComponent.isClosed_compl, isClosed_connectedComponent.isOpen_compl⟩
    ⟨y, haway hyF⟩ haway
  have hx : x ∈ (connectedComponent x)ᶜ := hfull.symm ▸ mem_univ x
  exact hx mem_connectedComponent

/-- Every component of a cut along a nonempty set has a boundary point. -/
theorem component_has_boundary_of_cut {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [ConnectedSpace S] (hS : IsSurface S) (hT : IsSurface T)
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F) (hF : F.Nonempty)
    {C : Set T} (hC : C ∈ spaceComponents T) : (bd C).Nonempty := by
  obtain ⟨y, hyC, hyF⟩ := component_meets_cut hS hT hcut hF hC
  have := hT.locallyConnected
  have hCopen : IsOpen C := by
    rw [spaceComponents_eq] at hC
    obtain ⟨x, rfl⟩ := hC
    exact isOpen_connectedComponent
  exact ⟨⟨y, hyC⟩, (mem_bd_sub hCopen).mpr (hcut.2.2.2.2 hyF)⟩

/-- A component of a nonempty cut cannot be homeomorphic to a closed
surface. In VIII (18.2) this excludes the unchanged closed-surface component
from the cylinder-copy outcome of an arc cut. -/
theorem not_homeomorph_closed_component_of_cut {S T R : Type w}
    [TopologicalSpace S] [TopologicalSpace T] [TopologicalSpace R]
    [ConnectedSpace S] (hS : IsSurface S) (hT : IsSurface T) (hR : IsClosedSurface R)
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F) (hF : F.Nonempty)
    {C : Set T} (hC : C ∈ spaceComponents T) : ¬ Nonempty (C ≃ₜ R) := by
  rintro ⟨e⟩
  obtain ⟨x, hx⟩ := component_has_boundary_of_cut hS hT hcut hF hC
  have hex : e x ∈ bd R := image_bd_homeomorph e ▸ mem_image_of_mem e hx
  exact hex (hR.2.2 (e x))

end GraphMinor.GM08
