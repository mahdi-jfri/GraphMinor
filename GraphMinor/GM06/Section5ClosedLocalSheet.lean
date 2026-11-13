module

public import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Compactness.Compact

/-!
# A closed local image of one chosen cover sheet

For the side test in VI (5.7), page 133, the closed lifted strip
is compact, but its full projection can identify the two ends of
one linkage path. Restrict it to a closed neighbourhood inside a
single inverse chart before projecting. Its image is closed, and
near the initial vertex membership is exactly membership in the
chosen sheet. The construction also works at a cuff point.
-/

public section
namespace GraphMinor.GM06
open Set Topology
universe u v w

/-- Localizing a compact set inside an inverse chart gives a closed
image whose membership, in a neighbourhood, remembers the chosen sheet. -/
theorem exists_closed_local_sheet_image
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [RegularSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [T2Space Z]
    (η : OpenPartialHomeomorph X Y) {j : Y → Z} (hj : IsEmbedding j)
    {p : X} (hp : p ∈ η.source) {K : Set X} (hK : IsCompact K) :
    ∃ B O : Set Z, IsClosed B ∧ IsOpen O ∧ j (η p) ∈ O ∧ B ⊆ range j ∧
      ∀ y : Y, j y ∈ O → y ∈ η.target ∧ (j y ∈ B ↔ η.symm y ∈ K) := by
  obtain ⟨C, hpC, hCc, hCη⟩ := exists_mem_nhds_isClosed_subset (η.open_source.mem_nhds hp)
  let V := interior C
  have hpV : p ∈ V := mem_interior_iff_mem_nhds.mpr hpC
  have hVη : V ⊆ η.source := interior_subset.trans hCη
  have hηVo : IsOpen (η '' V) := η.isOpen_image_of_subset_source isOpen_interior hVη
  obtain ⟨O, hOo, hO⟩ := hj.isInducing.isOpen_iff.mp hηVo
  let B := (j ∘ η) '' (K ∩ C)
  have hBc : IsClosed B :=
    ((hK.inter_right hCc).image_of_continuousOn
      (hj.continuous.comp_continuousOn (η.continuousOn.mono
        (inter_subset_right.trans hCη)))).isClosed
  have hpO : j (η p) ∈ O := by
    change η p ∈ j ⁻¹' O
    rw [hO]
    exact ⟨p, hpV, rfl⟩
  refine ⟨B, O, hBc, hOo, hpO, ?_, ?_⟩
  · rintro _ ⟨x, _, rfl⟩
    exact mem_range_self (η x)
  · intro y hyO
    have hyV : y ∈ η '' V := by
      change y ∈ j ⁻¹' O at hyO
      rwa [hO] at hyO
    obtain ⟨x, hxV, hxy⟩ := hyV
    have hxη : x ∈ η.source := hVη hxV
    have hyη : y ∈ η.target := hxy ▸ η.map_source hxη
    have hback : η.symm y = x := by rw [← hxy, η.left_inv hxη]
    refine ⟨hyη, ?_⟩
    constructor
    · rintro ⟨z, ⟨hzK, hzC⟩, hzj⟩
      have hzy : η z = y := hj.injective hzj
      have hyz : η.symm y = z := by rw [← hzy, η.left_inv (hCη hzC)]
      rwa [hyz]
    · intro hyK
      exact ⟨x, ⟨hback ▸ hyK, interior_subset hxV⟩, congrArg j hxy⟩

end GraphMinor.GM06
