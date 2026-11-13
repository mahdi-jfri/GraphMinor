module

public import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5OpenIndexedSheet
import GraphMinor.GM06.Section5IndexedStripImage
import GraphMinor.GM06.Section5CutSheetComponent
import GraphMinor.GM06.Section5CoverTranslation
import GraphMinor.GM06.Section5StripInjective
import GraphMinor.Surface.PlaneDisc

/-!
# A closed disc for every sheet of the angular cover

For the side test in VI (5.7), page 133, each chosen cover strip
is a closed lifted disc with the linkage removed. For two or more
paths the injective strip projection gives this description. For
one path translate the cut disc by an integral angular period.
This keeps the side information at the two copies of its endpoint.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- Every indexed strip in the angular cover has a compact closed-disc
sheet, also when the linkage consists of a single path. -/
theorem exists_cover_strip_disc_sheet
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (m : ℤ) :
    ∃ D : Set (ℝ × ℝ), IsClosedDisc D ∧ discBd D = liftedStripBoundary hG.1 L m ∧
      D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} ∧
      cylinderCoverStrip L m = (planeToCylinderCover '' D) ∩
        cylinderCoverProjection ⁻¹' (univ \ ⋃ j, (L.pathDrawing j).U) := by
  by_cases hk : k = 1
  · subst k
    obtain ⟨D, hD, hBd, hstrip, _⟩ := exists_indexed_stripDisc_with_image L hG hθ 1
    let z : ℤ := m - 1
    let τ : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) := Homeomorph.addRight (0, (z : ℝ) * (2 * π))
    let T := cylinderCoverTranslation z
    have hτ (p : ℝ × ℝ) : τ p = (p.1, p.2 + (z : ℝ) * (2 * π)) :=
      Prod.ext (add_zero p.1) rfl
    have hcomm (p : ℝ × ℝ) : planeToCylinderCover (τ p) = T (planeToCylinderCover p) := by
      rw [hτ]
      rfl
    have htrans := hD.image τ.continuous.continuousOn τ.symm.continuous.continuousOn
      (fun p _ => τ.symm_apply_apply p)
    have hBd' : discBd (τ '' D) = liftedStripBoundary hG.1 L m := by
      rw [htrans.2, hBd]
      have hh := image_liftedStripBoundary_add_mul hG.1 L 1 z
      have hτfun : (τ : (ℝ × ℝ) → (ℝ × ℝ)) =
          fun p => (p.1, p.2 + (z : ℝ) * (2 * π)) := funext hτ
      rw [hτfun]
      simpa only [Nat.cast_one, one_mul, z, add_sub_cancel] using hh
    have hstrip' : τ '' D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} := by
      rintro _ ⟨p, hp, rfl⟩
      simpa only [hτ, mem_ofPred_eq] using hstrip hp
    let S := cylinderCoverProjection ⁻¹' (univ \ ⋃ j, (L.pathDrawing j).U)
    have hTS : T '' S = S := by
      ext p
      constructor
      · rintro ⟨q, hq, rfl⟩
        change cylinderCoverProjection (T q) ∈ (univ \ ⋃ j, (L.pathDrawing j).U)
        rw [cylinderCoverProjection_translation]
        exact hq
      · intro hp
        refine ⟨T.symm p, ?_, T.apply_symm_apply p⟩
        have hh := cylinderCoverProjection_translation z (T.symm p)
        change cylinderCoverProjection (T (T.symm p)) = _ at hh
        rw [T.apply_symm_apply] at hh
        change cylinderCoverProjection (T.symm p) ∈ (univ \ ⋃ j, (L.pathDrawing j).U)
        rw [← hh]
        exact hp
    have hTK : T '' (planeToCylinderCover '' D) = planeToCylinderCover '' (τ '' D) := by
      rw [image_image, image_image]
      congr 1
      funext p
      exact (hcomm p).symm
    have hR := cylinderCoverStrip_eq_single_strip_sheet L hG hθ hD hBd hstrip
    have hSole : (univ \ ⋃ j : Fin 1, (L.pathDrawing j).U) = (L.pathDrawing 0).Uᶜ := by
      ext p
      simp only [mem_sdiff, mem_univ, mem_iUnion, Fin.exists_fin_one,
        true_and, mem_compl_iff]
    have hR' : cylinderCoverStrip L 1 = (planeToCylinderCover '' D) ∩ S := by
      simpa only [S, hSole] using hR
    have hTstrip : T '' cylinderCoverStrip L 1 = cylinderCoverStrip L m := by
      have hh := image_cylinderCoverStrip_translation L 1 z
      simpa only [z, add_sub_cancel] using hh
    refine ⟨τ '' D, htrans.1, hBd', hstrip', ?_⟩
    rw [← hTstrip, hR', image_inter T.injective, hTK, hTS]
  · have hk' : 1 < k := by have hpos := hG.1; omega
    obtain ⟨D, hD, hBd, hstrip, himage⟩ := exists_indexed_stripDisc_with_image L hG hθ m
    exact ⟨D, hD, hBd, hstrip,
      cylinderCoverStrip_eq_indexed_disc_sheet_of_two_le L hG hk' hθ m hD hBd hstrip himage⟩

end GraphMinor.GM06
