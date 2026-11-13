module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocalAtTarget

/-!
# Curves avoiding a contracted vertex

In the Reduction 3 case of Graph Minors VI (5.5), page 130,
a curve missing the contracted vertex lifts through the contraction.
The inverse is continuous on its compact range because the contraction
is one-to-one away from its exceptional fibre.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Away from its exceptional value, a continuous cylinder contraction
is a homeomorphism via its actual map. Compactness supplies closedness. -/
theorem exists_homeomorph_away_from_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (s : ClosedCylinder)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z) :
    ∃ h : {x : ClosedCylinder // π x ≠ s} ≃ₜ {y : ClosedCylinder // y ≠ s},
      ∀ x, (h x).1 = π x.1 := by
  let φ : {x : ClosedCylinder // π x ≠ s} → {y : ClosedCylinder // y ≠ s} :=
    fun x => ⟨π x, x.2⟩
  have hi : Function.Injective φ := by
    intro x y hxy
    exact Subtype.ext (hinj x y x.2 y.2 (congrArg Subtype.val hxy))
  have hs : Function.Surjective φ := by
    intro z
    obtain ⟨x, hx⟩ := hsurj z z.2
    exact ⟨⟨x, by rw [hx]; exact z.2⟩, Subtype.ext hx⟩
  have hc : Continuous φ :=
    (π.continuous.comp continuous_subtype_val).subtype_mk _
  have hclosed : IsClosedMap φ :=
    π.continuous.isClosedMap.restrictPreimage {y : ClosedCylinder | y ≠ s}
  exact ⟨(Equiv.ofBijective φ ⟨hi, hs⟩).toHomeomorphOfContinuousClosed hc hclosed,
    fun _ => rfl⟩

/-- At a nonexceptional point, taking the preimage under a contraction
commutes with taking closure. This retains the chosen old contact point. -/
theorem mem_closure_preimage_of_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (s : ClosedCylinder)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z)
    {R : Set ClosedCylinder} (hRs : s ∉ R)
    {x : ClosedCylinder} (hx : π x ≠ s) :
    x ∈ closure (π ⁻¹' R) ↔ π x ∈ closure R := by
  constructor
  · intro h
    exact closure_mono (image_preimage_subset π R)
      (mem_closure_image π.continuous.continuousAt h)
  · intro h
    have honto : R ⊆ range π := by
      intro z hz
      exact hsurj z (fun he => hRs (he ▸ hz))
    have himage : π '' closure (π ⁻¹' R) = closure R := by
      rw [← π.continuous.isClosedMap.closure_image_eq_of_continuous π.continuous,
        image_preimage_eq_of_subset honto]
    obtain ⟨y, hy, he⟩ := himage ▸ h
    have hys : π y ≠ s := he.symm ▸ hx
    exact (hinj y x hys hx he) ▸ hy

/-- A curve avoiding the exceptional value of a cylinder contraction
lifts continuously through its actual contraction map. -/
theorem exists_curve_lift_avoiding_contraction
    (π : C(ClosedCylinder, ClosedCylinder)) (s : ClosedCylinder)
    (hinj : ∀ x y, π x ≠ s → π y ≠ s → π x = π y → x = y)
    (hsurj : ∀ z, z ≠ s → ∃ x, π x = z)
    (f : Curve ClosedCylinder) (hf : ∀ t, f t ≠ s) :
    ∃ g : Curve ClosedCylinder, ∀ t, π (g t) = f t := by
  let K : Set ClosedCylinder := range f
  let D : Set ClosedCylinder := π ⁻¹' K
  have hK : IsClosed K := (isCompact_range f.continuous).isClosed
  let : CompactSpace D := isCompact_iff_compactSpace.mp
    ((hK.preimage π.continuous).isCompact)
  let φ : D → K := fun x => ⟨π x, x.2⟩
  have hφc : Continuous φ :=
    (π.continuous.comp continuous_subtype_val).subtype_mk _
  have hφi : Function.Injective φ := by
    intro x y hxy
    obtain ⟨t, ht⟩ := x.2
    obtain ⟨u, hu⟩ := y.2
    apply Subtype.ext
    exact hinj x y (ht ▸ hf t) (hu ▸ hf u) (congrArg Subtype.val hxy)
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨t, ht⟩ := z.2
    obtain ⟨x, hx⟩ := hsurj z (ht ▸ hf t)
    have hxD : x ∈ D := by
      change π x ∈ K
      rw [hx]
      exact z.2
    exact ⟨⟨x, hxD⟩, Subtype.ext hx⟩
  let e : D ≃ₜ K := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective φ ⟨hφi, hφs⟩) hφc
  let g : Curve ClosedCylinder :=
    ⟨fun t => (e.symm ⟨f t, mem_range_self t⟩).1,
      continuous_subtype_val.comp (e.symm.continuous.comp f.continuous.rangeFactorization)⟩
  refine ⟨g, fun t => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨f t, mem_range_self t⟩)

end GraphMinor.GM06
