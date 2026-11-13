module

public import GraphMinor.GM06.Section5CoverSides
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Translating one-path cover strips

Adding an integral full turn changes the angular sheet but preserves
projection to the cylinder. For one linkage path it carries the strip
with index m to the strip with index m + z. In particular, shifting
back one turn takes the following strip to the preceding strip.
This makes incidence at the right initial copy a clockwise-side
condition at the canonical initial lift in VI Section 5.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Translation by an integral full turn in the angular cover. -/
@[expose] noncomputable def cylinderCoverTranslation (z : ℤ) : CylinderCover ≃ₜ CylinderCover :=
  (Homeomorph.refl (Icc (1 : ℝ) 2)).prodCongr (Homeomorph.addRight ((z : ℝ) * (2 * π)))

/-- An integral full-turn translation preserves projection. -/
theorem cylinderCoverProjection_translation (z : ℤ) (p : CylinderCover) :
    cylinderCoverProjection (cylinderCoverTranslation z p) = cylinderCoverProjection p := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Circle.exp (p.2 + (z : ℝ) * (2 * π)) = Circle.exp p.2
    rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]

/-- For one linkage path, integral full-turn translation changes the
strip index by the same integer. -/
theorem image_cylinderCoverStrip_translation
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G) (m z : ℤ) :
    cylinderCoverTranslation z '' cylinderCoverStrip L m = cylinderCoverStrip L (m + z) := by
  let E := cylinderCoverTranslation z
  let S := cylinderCoverProjection ⁻¹' (univ \ ⋃ j, (L.pathDrawing j).U)
  let b : CylinderCover := (⟨1, by norm_num⟩, (2 * (m : ℝ) + 1) * π / (1 : ℕ))
  let c : CylinderCover := (⟨1, by norm_num⟩, (2 * ((m + z : ℤ) : ℝ) + 1) * π / (1 : ℕ))
  have hseed : E b = c := by
    apply Prod.ext
    · rfl
    · change (2 * (m : ℝ) + 1) * π / (1 : ℕ) + (z : ℝ) * (2 * π) =
        (2 * ((m + z : ℤ) : ℝ) + 1) * π / (1 : ℕ)
      norm_num only [Nat.cast_one, div_one, Int.cast_add]
      ring
  have hS : E '' S = S := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change cylinderCoverProjection (E q) ∈ univ \ ⋃ j, (L.pathDrawing j).U
      rw [cylinderCoverProjection_translation]
      exact hq
    · intro hp
      refine ⟨E.symm p, ?_, E.apply_symm_apply p⟩
      have hproj := cylinderCoverProjection_translation z (E.symm p)
      change cylinderCoverProjection (E (E.symm p)) = cylinderCoverProjection (E.symm p) at hproj
      rw [E.apply_symm_apply] at hproj
      change cylinderCoverProjection (E.symm p) ∈ univ \ ⋃ j, (L.pathDrawing j).U
      rw [← hproj]
      exact hp
  change E '' connectedComponentIn S b = connectedComponentIn S c
  by_cases hb : b ∈ S
  · rw [E.image_connectedComponentIn hb, hS, hseed]
  · have hc : c ∉ S := by
      intro hc
      have hEb : E b ∈ E '' S := hS.symm ▸ (hseed.symm ▸ hc)
      obtain ⟨q, hq, hqb⟩ := hEb
      exact hb (E.injective hqb ▸ hq)
    rw [connectedComponentIn_eq_empty hb, connectedComponentIn_eq_empty hc, image_empty]

end GraphMinor.GM06
