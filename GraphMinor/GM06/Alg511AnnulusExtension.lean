module

public import GraphMinor.GM06.Alg511AnnulusCuffs
import Mathlib.Tactic

/-!
# Extending the cylinder's annular map over the plane

The orientation change in VI (5.11), page 134, is made on the
cylinder and then used in its sphere drawing. Extend a map of the
planar annulus to the inner and outer caps. On each cap use the
radial extension of its boundary-circle map. The three formulas
agree on their common circles, so pasting on closed sets proves
continuity. Pasting the inverse formulas proves that the resulting
plane map is a homeomorphism.
-/

public section
namespace GraphMinor.GM06
open Set Topology

open Classical in
private noncomputable def pasteAnnulus (H : alg511Annulus ≃ₜ alg511Annulus)
    (A B : ℂ ≃ₜ ℂ) (z : ℂ) : ℂ :=
  if hi : ‖z‖ ≤ (1 / 2 : ℝ) then A z
  else if ho : ‖z‖ ≤ (1 : ℝ) then (H ⟨z, ⟨le_of_lt (lt_of_not_ge hi), ho⟩⟩).val
  else B z

private theorem pasteAnnulus_inner (H : alg511Annulus ≃ₜ alg511Annulus)
    (A B : ℂ ≃ₜ ℂ) (z : ℂ) (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    pasteAnnulus H A B z = A z := by
  simp only [pasteAnnulus, dite_eq_left hz]

private theorem pasteAnnulus_middle (H : alg511Annulus ≃ₜ alg511Annulus)
    (A B : ℂ ≃ₜ ℂ)
    (hA : ∀ z : alg511Annulus, ‖z.val‖ = (1 / 2 : ℝ) → A z.val = (H z).val)
    (z : alg511Annulus) : pasteAnnulus H A B z.val = (H z).val := by
  by_cases hi : ‖z.val‖ ≤ (1 / 2 : ℝ)
  · rw [pasteAnnulus_inner H A B _ hi]
    exact hA z (le_antisymm hi z.property.1)
  · simp only [pasteAnnulus, dite_eq_right hi, dite_eq_left z.property.2]

private theorem pasteAnnulus_outer (H : alg511Annulus ≃ₜ alg511Annulus)
    (A B : ℂ ≃ₜ ℂ)
    (hB : ∀ z : alg511Annulus, ‖z.val‖ = (1 : ℝ) → B z.val = (H z).val)
    (z : ℂ) (hz : (1 : ℝ) ≤ ‖z‖) : pasteAnnulus H A B z = B z := by
  have hi : ¬ ‖z‖ ≤ (1 / 2 : ℝ) := by linarith
  by_cases ho : ‖z‖ ≤ (1 : ℝ)
  · have heq : ‖z‖ = (1 : ℝ) := le_antisymm ho hz
    simp only [pasteAnnulus, dite_eq_right hi, dite_eq_left ho]
    exact (hB ⟨z, ⟨by linarith, ho⟩⟩ heq).symm
  · simp only [pasteAnnulus, dite_eq_right hi, dite_eq_right ho]

private theorem pasteAnnulus_norm (H : alg511Annulus ≃ₜ alg511Annulus)
    (hH : ∀ z, ‖(H z).val‖ = ‖z.val‖) (A B : ℂ ≃ₜ ℂ)
    (hA : ∀ z, ‖A z‖ = ‖z‖) (hB : ∀ z, ‖B z‖ = ‖z‖) (z : ℂ) :
    ‖pasteAnnulus H A B z‖ = ‖z‖ := by
  unfold pasteAnnulus
  split_ifs with hi ho
  · exact hA z
  · exact hH _
  · exact hB z

private theorem pasteAnnulus_continuous (H : alg511Annulus ≃ₜ alg511Annulus)
    (A B : ℂ ≃ₜ ℂ)
    (hA : ∀ z : alg511Annulus, ‖z.val‖ = (1 / 2 : ℝ) → A z.val = (H z).val)
    (hB : ∀ z : alg511Annulus, ‖z.val‖ = (1 : ℝ) → B z.val = (H z).val) :
    Continuous (pasteAnnulus H A B) := by
  have hi : ContinuousOn (pasteAnnulus H A B) {z | ‖z‖ ≤ (1 / 2 : ℝ)} :=
    A.continuous.continuousOn.congr (fun z hz => pasteAnnulus_inner H A B z hz)
  have hm : ContinuousOn (pasteAnnulus H A B) alg511Annulus := by
    rw [continuousOn_iff_continuous_domRestrict]
    have heq : alg511Annulus.domRestrict (pasteAnnulus H A B) = fun z => (H z).val :=
      funext (pasteAnnulus_middle H A B hA)
    rw [heq]
    exact continuous_subtype_val.comp H.continuous
  have ho : ContinuousOn (pasteAnnulus H A B) {z | (1 : ℝ) ≤ ‖z‖} :=
    B.continuous.continuousOn.congr (fun z hz => pasteAnnulus_outer H A B hB z hz)
  have hci : IsClosed {z : ℂ | ‖z‖ ≤ (1 / 2 : ℝ)} := isClosed_le continuous_norm continuous_const
  have hcm : IsClosed alg511Annulus :=
    (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
  have hco : IsClosed {z : ℂ | (1 : ℝ) ≤ ‖z‖} := isClosed_le continuous_const continuous_norm
  apply continuousOn_univ.mp
  apply ((hi.union_of_isClosed hm hci hcm).union_of_isClosed ho (hci.union hcm) hco).mono
  intro z _
  by_cases hi : ‖z‖ ≤ (1 / 2 : ℝ)
  · exact Or.inl (Or.inl hi)
  · by_cases ho : ‖z‖ ≤ (1 : ℝ)
    · exact Or.inl (Or.inr ⟨le_of_lt (lt_of_not_ge hi), ho⟩)
    · exact Or.inr (le_of_lt (lt_of_not_ge ho))

private theorem homeomorph_norm_symm (A : ℂ ≃ₜ ℂ) (hA : ∀ z, ‖A z‖ = ‖z‖) (z : ℂ) :
    ‖A.symm z‖ = ‖z‖ := by
  have h := hA (A.symm z)
  rw [A.apply_symm_apply] at h
  exact h.symm

private theorem pasteAnnulus_left_inv (H : alg511Annulus ≃ₜ alg511Annulus)
    (hH : ∀ z, ‖(H z).val‖ = ‖z.val‖) (A B : ℂ ≃ₜ ℂ)
    (hAn : ∀ z, ‖A z‖ = ‖z‖) (hBn : ∀ z, ‖B z‖ = ‖z‖)
    (hA : ∀ z : alg511Annulus, ‖z.val‖ = (1 / 2 : ℝ) → A z.val = (H z).val)
    (hB : ∀ z : alg511Annulus, ‖z.val‖ = (1 : ℝ) → B z.val = (H z).val)
    (z : ℂ) : pasteAnnulus H.symm A.symm B.symm (pasteAnnulus H A B z) = z := by
  have hAi := alg511_annulus_cuff_extension_symm H hH (1 / 2) A hA
  by_cases hi : ‖z‖ ≤ (1 / 2 : ℝ)
  · rw [pasteAnnulus_inner H A B z hi,
      pasteAnnulus_inner H.symm A.symm B.symm _ (by rw [hAn]; exact hi), A.symm_apply_apply]
  · by_cases ho : ‖z‖ ≤ (1 : ℝ)
    · let p : alg511Annulus := ⟨z, ⟨le_of_lt (lt_of_not_ge hi), ho⟩⟩
      have hp : pasteAnnulus H A B z = (H p).val := pasteAnnulus_middle H A B hA p
      rw [hp, pasteAnnulus_middle H.symm A.symm B.symm hAi, H.symm_apply_apply]
    · have hz : (1 : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge ho)
      have hBi := alg511_annulus_cuff_extension_symm H hH 1 B hB
      rw [pasteAnnulus_outer H A B hB z hz,
        pasteAnnulus_outer H.symm A.symm B.symm hBi _ (by rw [hBn]; exact hz), B.symm_apply_apply]

/-- A norm-preserving map of the closed annulus extends to a
norm-preserving homeomorphism of the plane, agreeing on every
annular point. This supplies the cap extension in VI (5.11). -/
theorem alg511_exists_annulus_extension (H : alg511Annulus ≃ₜ alg511Annulus)
    (hH : ∀ z, ‖(H z).val‖ = ‖z.val‖) :
    ∃ E : ℂ ≃ₜ ℂ, (∀ z, ‖E z‖ = ‖z‖) ∧
      ∀ z : alg511Annulus, E z.val = (H z).val := by
  obtain ⟨A, _, hAn, hA⟩ := alg511_exists_annulus_cuff_extension H hH (1 / 2) (by constructor <;> norm_num)
  obtain ⟨B, _, hBn, hB⟩ := alg511_exists_annulus_cuff_extension H hH 1 (by constructor <;> norm_num)
  have hAi := alg511_annulus_cuff_extension_symm H hH (1 / 2) A hA
  have hBi := alg511_annulus_cuff_extension_symm H hH 1 B hB
  let E : ℂ ≃ₜ ℂ :=
    { toFun := pasteAnnulus H A B
      invFun := pasteAnnulus H.symm A.symm B.symm
      left_inv := pasteAnnulus_left_inv H hH A B hAn hBn hA hB
      right_inv := by
        intro z
        exact pasteAnnulus_left_inv H.symm (alg511Annulus_norm_symm H hH)
          A.symm B.symm (homeomorph_norm_symm A hAn) (homeomorph_norm_symm B hBn) hAi hBi z
      continuous_toFun := pasteAnnulus_continuous H A B hA hB
      continuous_invFun := pasteAnnulus_continuous H.symm A.symm B.symm hAi hBi }
  exact ⟨E, pasteAnnulus_norm H hH A B hAn hBn, pasteAnnulus_middle H A B hA⟩

end GraphMinor.GM06
