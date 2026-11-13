module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5ContractionCoverMap
import GraphMinor.GM06.Section5ContractionCoverBound
import GraphMinor.GM06.Section5CutRegionPreimage

/-!
# Region preimages in the angular cover of a contraction

For VI (5.5), page 130, a lifted region avoids all lifts of the
contracted vertex. The lifted contraction is closed and bijective
above that region. Its preimage is therefore connected, and its
closure maps onto the chosen lifted region closure. This retains
the sheet of every contact point.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A connected lifted region pulls back to a connected open set,
with exactly the required closure image, in its specified sheet. -/
theorem preimage_connected_open_set_of_cover_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ s → ∃ y, π y = x)
    {Y : Set CylinderCover} (hYo : IsOpen Y) (hY : IsConnected Y)
    (hYs : ∀ p ∈ Y, cylinderCoverProjection p ≠ s) :
    IsOpen (Φ ⁻¹' Y) ∧ IsConnected (Φ ⁻¹' Y) ∧
      Φ '' closure (Φ ⁻¹' Y) = closure Y := by
  have hclosed := isClosedMap_cover_of_commutes_with_translation Φ htrans
  have honto : Y ⊆ range Φ := by
    intro p hp
    exact cover_contraction_surjective_away_from_value π Φ s hproj htrans hsurj p (hYs p hp)
  have huniq : ∀ p, Φ p ∈ Y → ∀ q, Φ q ∈ Y → Φ p = Φ q → p = q := by
    intro p hp q _ he
    exact cover_contraction_injective_away_from_value π Φ s hproj htrans hinj (hYs _ hp) he
  have hpre := preconnected_preimage_of_closed_map_unique_on hY.isPreconnected hclosed honto huniq
  refine ⟨hYo.preimage Φ.continuous, ⟨hY.nonempty.preimage' honto, hpre⟩, ?_⟩
  rw [← hclosed.closure_image_eq_of_continuous Φ.continuous,
    image_preimage_eq_of_subset honto]

/-- A closed map with singleton fibres off a drawing carries
complementary components back to complementary components. -/
theorem preimage_component_of_closed_map_unique_on_complement
    (Φ : C(CylinderCover, CylinderCover)) (hclosed : IsClosedMap Φ)
    {B B' Y : Set CylinderCover} (hB : Φ ⁻¹' B' = B)
    (hsurj : ∀ y, y ∉ B' → ∃ x, Φ x = y)
    (huniq : ∀ x y, Φ x ∉ B' → Φ y ∉ B' → Φ x = Φ y → x = y)
    (hY : Y ∈ componentsIn B'ᶜ) : Φ ⁻¹' Y ∈ componentsIn Bᶜ := by
  obtain ⟨y, hy, hYe⟩ := hY
  have hyY : y ∈ Y := hYe.symm ▸ mem_connectedComponentIn hy
  have hYoff : Y ⊆ B'ᶜ := hYe.symm ▸ connectedComponentIn_subset _ _
  have hYpre : IsPreconnected Y := hYe.symm ▸ isPreconnected_connectedComponentIn
  have honto : Y ⊆ range Φ := fun z hz => hsurj z (hYoff hz)
  have hi : ∀ x, Φ x ∈ Y → ∀ z, Φ z ∈ Y → Φ x = Φ z → x = z :=
    fun x hx z hz he => huniq x z (hYoff hx) (hYoff hz) he
  have hpre := preconnected_preimage_of_closed_map_unique_on hYpre hclosed honto hi
  obtain ⟨p, hp⟩ := hsurj y hy
  have hpY : p ∈ Φ ⁻¹' Y := by change Φ p ∈ Y; rw [hp]; exact hyY
  have hoff : ∀ x, Φ x ∉ B' ↔ x ∉ B := by
    intro x
    change x ∉ Φ ⁻¹' B' ↔ x ∉ B
    rw [hB]
  have hpB : p ∈ Bᶜ := (hoff p).1 (hp ▸ hy)
  let r := connectedComponentIn Bᶜ p
  have hsub : Φ ⁻¹' Y ⊆ r := hpre.subset_connectedComponentIn hpY
    (fun z hz => (hoff z).1 (hYoff hz))
  have hpR : p ∈ r := mem_connectedComponentIn hpB
  have himage : Φ '' r ⊆ Y := by
    rw [← hYe, ← hp]
    exact (isPreconnected_connectedComponentIn.image Φ Φ.continuous.continuousOn).subset_connectedComponentIn (mem_image_of_mem Φ hpR)
        (by rintro z ⟨x, hx, rfl⟩; exact (hoff x).2 (connectedComponentIn_subset _ _ hx))
  have heq : Φ ⁻¹' Y = r := subset_antisymm hsub (fun x hx => himage ⟨x, hx, rfl⟩)
  exact heq.symm ▸ ⟨p, hpB, rfl⟩

/-- Complementary components in a specified angular sheet pull back
under the actual lifted contraction. The sets may include the cuffs. -/
theorem preimage_lifted_component_of_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (Φ : C(CylinderCover, CylinderCover))
    (s : ClosedCylinder)
    (hproj : ∀ p, cylinderCoverProjection (Φ p) = π (cylinderCoverProjection p))
    (htrans : ∀ z p, Φ (cylinderCoverTranslation z p) = cylinderCoverTranslation z (Φ p))
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ x, x ≠ s → ∃ y, π y = x)
    {B B' : Set ClosedCylinder} (hB : B' = π '' B)
    (hfibre : π ⁻¹' {s} ⊆ B) (hs : s ∈ B')
    {Y : Set CylinderCover} (hY : Y ∈ componentsIn (cylinderCoverProjection ⁻¹' B'ᶜ)) :
    Φ ⁻¹' Y ∈ componentsIn (cylinderCoverProjection ⁻¹' Bᶜ) := by
  have hsets : Φ ⁻¹' (cylinderCoverProjection ⁻¹' B') = cylinderCoverProjection ⁻¹' B := by
    ext p
    change cylinderCoverProjection (Φ p) ∈ B' ↔ cylinderCoverProjection p ∈ B
    rw [hproj]
    constructor
    · intro hp
      by_cases he : π (cylinderCoverProjection p) = s
      · exact hfibre he
      · obtain ⟨x, hx, hxp⟩ := hB ▸ hp
        have hxs : π x ≠ s := hxp.symm ▸ he
        have hxe : x = cylinderCoverProjection p := hinj x _ hxs he hxp
        exact hxe ▸ hx
    · intro hp
      exact hB ▸ mem_image_of_mem π hp
  have honto : ∀ p, p ∉ cylinderCoverProjection ⁻¹' B' → ∃ q, Φ q = p := by
    intro p hp
    change cylinderCoverProjection p ∉ B' at hp
    have hps : cylinderCoverProjection p ≠ s := fun he => hp (he ▸ hs)
    exact cover_contraction_surjective_away_from_value π Φ s hproj htrans hsurj p hps
  have hi : ∀ p q, Φ p ∉ cylinderCoverProjection ⁻¹' B' →
      Φ q ∉ cylinderCoverProjection ⁻¹' B' → Φ p = Φ q → p = q := by
    intro p q hp _ he
    change cylinderCoverProjection (Φ p) ∉ B' at hp
    have hps : cylinderCoverProjection (Φ p) ≠ s := fun h => hp (h ▸ hs)
    exact cover_contraction_injective_away_from_value π Φ s hproj htrans hinj hps he
  have hc := preimage_component_of_closed_map_unique_on_complement Φ
    (isClosedMap_cover_of_commutes_with_translation Φ htrans) hsets honto hi
    (show Y ∈ componentsIn ((cylinderCoverProjection ⁻¹' B')ᶜ) from hY)
  exact hc

/-- The interior of a continuous curve lying in a set belongs to
one complementary component, and both ends lie in its closure. -/
theorem exists_component_containing_curve_interior
    (f : C(unitInterval, CylinderCover)) {B : Set CylinderCover}
    (hf : ∀ t, 0 < t → t < 1 → f t ∈ B) :
    ∃ Y : Set CylinderCover, Y ∈ componentsIn B ∧
      (∀ t, 0 < t → t < 1 → f t ∈ Y) ∧ f 0 ∈ closure Y ∧ f 1 ∈ closure Y := by
  let m : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hm : m ∈ Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  let Y := connectedComponentIn B (f m)
  have hsub : f '' Ioo 0 1 ⊆ Y :=
    (isPreconnected_Ioo.image f f.continuous.continuousOn).subset_connectedComponentIn
      (mem_image_of_mem f hm) (by rintro _ ⟨t, ht, rfl⟩; exact hf t ht.1 ht.2)
  have hcl : f '' Icc 0 1 ⊆ closure Y := by
    have hclI : Icc (0 : unitInterval) 1 = closure (Ioo 0 1) := (closure_Ioo zero_ne_one).symm
    rw [hclI]
    exact (image_closure_subset_closure_image f.continuous).trans (closure_mono hsub)
  exact ⟨Y, ⟨f m, hf m hm.1 hm.2, rfl⟩,
    fun t ht0 ht1 => hsub (mem_image_of_mem f ⟨ht0, ht1⟩),
    hcl (mem_image_of_mem f ⟨le_rfl, zero_le_one⟩),
    hcl (mem_image_of_mem f ⟨zero_le_one, le_rfl⟩)⟩

end GraphMinor.GM06
