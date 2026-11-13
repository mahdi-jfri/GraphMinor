module

public import GraphMinor.GM06.Alg57OnePathCollar
public import GraphMinor.GM06.Alg57CornerSide
public import GraphMinor.GM06.Section5AnnulusInterior

/-!
# The two sides of the one path, on the sphere

`side_dichotomy` says that near a point of `P₁` a connected set of the cylinder that misses `P₁`
is on one side of it. The corners of the drawing live on the sphere, so here we move this fact
to the sphere. A point `z` of the sphere is on side one (`sphereSideOne`) if it is the image of a
point of the cylinder on side `U₁`. Near an inner point of `P₁` the property `sphereSideOne` does
not change on connected sets that miss the image of `P₁` (`sphere_sideDich`). We use inner points
because they are off the cuffs (`curve_notMem_bd`), so the sphere looks like the cylinder near
them.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- A point of the sphere is on side `U` if it is the image of a point of the cylinder on side
`U`. -/
@[expose] def sphereSide (D : Set (ℝ × ℝ)) (U : Set CylinderCover)
    (z : OnePoint EuclideanPlane) : Prop :=
  ∃ x : ClosedCylinder, cylinderToSphere x = z ∧ OnSide D U x

section Setting

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ in
/-- The sphere form of `side_dichotomy`: if a set `N` of the cylinder has the property of
`side_dichotomy`, then its image off the cuffs has the property `SideDich` on the sphere. -/
theorem sideDich_image_sdiff {N : Set ClosedCylinder}
    (hdich : ∀ S ⊆ N, IsPreconnected S → Disjoint S (L.pathDrawing 0).U →
      (∀ x ∈ S, OnSide D U₁ x) ∨ (∀ x ∈ S, OnSide D U₂ x)) :
    SideDich (cylinderToSphere '' (L.pathDrawing 0).U) (sphereSide D U₁)
      (cylinderToSphere '' (N \ bd ClosedCylinder)) := by
  intro S hSN hS hSX
  have hrange : S ⊆ range cylinderToSphere := fun z hz => by
    obtain ⟨x, -, rfl⟩ := hSN hz
    exact mem_range_self x
  set T := cylinderToSphere ⁻¹' S
  have hTS : cylinderToSphere '' T = S := image_preimage_eq_of_subset hrange
  have hT : IsPreconnected T := by
    rw [← isClosedEmbedding_cylinderToSphere.isEmbedding.isInducing.isPreconnected_image, hTS]
    exact hS
  have hTN : T ⊆ N := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hSN hx
    rw [← injective_cylinderToSphere hyx]
    exact hy.1
  have hTP : Disjoint T (L.pathDrawing 0).U :=
    disjoint_left.mpr fun x hx hxP => disjoint_left.mp hSX hx ⟨x, hxP, rfl⟩
  rcases hdich T hTN hT hTP with h | h
  · left
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hTS ▸ hz
    exact ⟨x, rfl, h x hx⟩
  · right
    rintro z hz ⟨x, rfl, hx⟩
    exact not_onSide_two_of_onSide_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂
      (disjoint_left.mp hTP hz) hx (h x hz)

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ in
/-- **Near an inner point of `P₁` the side does not change on the sphere.** -/
theorem sphere_sideDich {t : unitInterval} (h0 : t ≠ 0) (h1 : t ≠ 1) :
    ∃ N : Set (OnePoint EuclideanPlane), IsOpen N ∧ cylinderToSphere (L.curve 0 t) ∈ N ∧
      SideDich (cylinderToSphere '' (L.pathDrawing 0).U) (sphereSide D U₁) N := by
  obtain ⟨N, hN, hxN, hdich⟩ := side_dichotomy L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ t
  exact ⟨cylinderToSphere '' (N \ bd ClosedCylinder),
    isOpen_image_cylinderToSphere_sdiff_boundary hN,
    ⟨_, ⟨hxN, curve_notMem_bd L hG h0 h1⟩, rfl⟩,
    sideDich_image_sdiff L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hdich⟩

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ in
/-- `sphere_sideDich`, together with: near an inner point of `P₁`, each point off `P₁` is on side
one or on side two. -/
theorem sphere_sideDich' {t : unitInterval} (h0 : t ≠ 0) (h1 : t ≠ 1) :
    ∃ N : Set (OnePoint EuclideanPlane), IsOpen N ∧ cylinderToSphere (L.curve 0 t) ∈ N ∧
      SideDich (cylinderToSphere '' (L.pathDrawing 0).U) (sphereSide D U₁) N ∧
      ∀ y ∈ N, y ∉ cylinderToSphere '' (L.pathDrawing 0).U →
        sphereSide D U₁ y ∨ sphereSide D U₂ y := by
  obtain ⟨N, hN, hxN, hdich⟩ := side_dichotomy L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ t
  refine ⟨cylinderToSphere '' (N \ bd ClosedCylinder),
    isOpen_image_cylinderToSphere_sdiff_boundary hN,
    ⟨_, ⟨hxN, curve_notMem_bd L hG h0 h1⟩, rfl⟩,
    sideDich_image_sdiff L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hdich, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ hxX
  have hxP : x ∉ (L.pathDrawing 0).U := fun h => hxX ⟨x, h, rfl⟩
  rcases hdich {x} (singleton_subset_iff.mpr hx.1) isPreconnected_singleton
    (disjoint_singleton_left.mpr hxP) with h | h
  · exact Or.inl ⟨x, rfl, h x rfl⟩
  · exact Or.inr ⟨x, rfl, h x rfl⟩

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ in
/-- **Near any point of `P₁` the side does not change off `P₁` and the cuffs.** This also holds
at the two ends of `P₁`, which lie on the cuffs. A connected set that misses the cuffs lies in
the open cylinder or off the cylinder; off the cylinder no point is on side one. -/
theorem sphere_sideDich_cuffs (t : unitInterval) :
    ∃ N : Set (OnePoint EuclideanPlane), IsOpen N ∧ cylinderToSphere (L.curve 0 t) ∈ N ∧
      SideDich (cylinderToSphere '' ((L.pathDrawing 0).U ∪ bd ClosedCylinder))
        (sphereSide D U₁) N := by
  obtain ⟨N, hN, hxN, hdich⟩ := side_dichotomy L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ t
  have hcl : IsClosed (cylinderToSphere '' Nᶜ) :=
    isClosedEmbedding_cylinderToSphere.isClosedMap _ hN.isClosed_compl
  refine ⟨(cylinderToSphere '' Nᶜ)ᶜ, hcl.isOpen_compl, ?_, ?_⟩
  · rintro ⟨y, hy, hyx⟩
    exact hy (injective_cylinderToSphere hyx ▸ hxN)
  intro S hSN hS hSX
  have hA := isOpen_image_cylinderToSphere_sdiff_boundary (isOpen_univ (X := ClosedCylinder))
  have hB : IsOpen (range cylinderToSphere)ᶜ :=
    isClosedEmbedding_cylinderToSphere.isClosed_range.isOpen_compl
  have hSAB : S ⊆ cylinderToSphere '' (univ \ bd ClosedCylinder) ∪ (range cylinderToSphere)ᶜ := by
    intro z hz
    by_cases hr : z ∈ range cylinderToSphere
    · obtain ⟨y, rfl⟩ := hr
      refine Or.inl ⟨y, ⟨mem_univ y, fun hy => ?_⟩, rfl⟩
      exact disjoint_left.mp hSX hz ⟨y, Or.inr hy, rfl⟩
    · exact Or.inr hr
  have hAB : Disjoint (cylinderToSphere '' (univ \ bd ClosedCylinder)) (range cylinderToSphere)ᶜ :=
    disjoint_left.mpr fun z ⟨y, _, hy⟩ hz => hz ⟨y, hy⟩
  rcases hS.subset_or_subset hA hB hAB hSAB with h | h
  · have hSN' : S ⊆ cylinderToSphere '' (N \ bd ClosedCylinder) := by
      intro z hz
      obtain ⟨y, hy, rfl⟩ := h hz
      refine ⟨y, ⟨?_, hy.2⟩, rfl⟩
      by_contra hyN
      exact hSN hz ⟨y, hyN, rfl⟩
    exact sideDich_image_sdiff L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hdich S hSN' hS
      (hSX.mono_right (image_mono subset_union_left))
  · right
    rintro z hz ⟨x, rfl, -⟩
    exact h hz (mem_range_self x)

end Setting

end GraphMinor.GM06
