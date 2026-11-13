module

public import GraphMinor.Surface.CircleMove
import GraphMinor.GM08.Section9BoundaryMatch
import GraphMinor.GM07.CuffFrame
import GraphMinor.GM07.Section3
import GraphMinor.Surface.DiscTwist

/-!
# Matching the root positions on the circle in VIII (9.3)

Cut the circle at an unmarked point and list the marks by their parameters
in one turn. Increasing interpolation matches two lists of equal length.
Rotating each cut point to one lets the interval construction apply to
arbitrary finite sets of boundary marks.
-/

public section

namespace GraphMinor.GM08

open Set Surface

private theorem exists_circle_parameters {Z : Set Circle} (hZ : Z.Finite) (h1 : (1 : Circle) ∉ Z) :
    ∃ A : Set ℝ, A.Finite ∧ A ⊆ Ioo 0 1 ∧ ee '' A = Z ∧ A.ncard = Z.ncard := by
  classical
  have : Finite Z := hZ.to_subtype
  have hex : ∀ z : Z, ∃ a ∈ Ioo (0 : ℝ) 1, ee a = z.1 := by
    intro z
    obtain ⟨a, ha, he⟩ := GM07.exists_Ico_param_of_mem_cuff
      (Homeomorph.Set.univ Circle).symm (mem_univ z.1)
    change ee a = z.1 at he
    refine ⟨a, ⟨lt_of_le_of_ne ha.1 ?_, ha.2⟩, he⟩
    intro he0
    have : z.1 = 1 := by rw [← he, ← he0]; simp [ee]
    exact h1 (this ▸ z.2)
  choose a ha he using hex
  have hinj : Function.Injective a := by
    intro x y hxy
    apply Subtype.ext
    rw [← he x, ← he y, hxy]
  refine ⟨range a, finite_range a, range_subset_iff.mpr ha, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact he x ▸ x.2
    · intro hz
      exact ⟨a ⟨z, hz⟩, mem_range_self _, he _⟩
  · rw [ncard_range_of_injective hinj, Nat.card_coe_set_eq]

/-- Finite sets of circle marks of the same size can be carried to one
another when neither contains the cut point. This is used to align the
boundary roots before VII (9.4) is applied in VIII (9.3), page 270. -/
theorem exists_circle_match_of_not_mem_one {Z W : Set Circle}
    (hZ : Z.Finite) (hW : W.Finite) (hZ1 : (1 : Circle) ∉ Z) (hW1 : (1 : Circle) ∉ W)
    (hcard : Z.ncard = W.ncard) : ∃ σ : Circle ≃ₜ Circle, PreservesCircleOrientation σ ∧ σ '' Z = W := by
  obtain ⟨A, hA, hAI, hAZ, hAc⟩ := exists_circle_parameters hZ hZ1
  obtain ⟨B, hB, hBI, hBW, hBc⟩ := exists_circle_parameters hW hW1
  obtain ⟨τ, hc, hm, h0, h1, hAB⟩ := exists_increasing_parameter_match hA hB hAI hBI
    (hAc.trans (hcard.trans hBc.symm))
  obtain ⟨σ, hσo, hσ⟩ := exists_circle_homeo hc.continuousOn (hm.strictMonoOn _) (by rw [h0, h1]; norm_num)
  refine ⟨σ, hσo, ?_⟩
  rw [← hAZ, ← hBW]
  have heq : σ '' (ee '' A) = ee '' (τ '' A) := by
    ext z
    constructor
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨τ a, mem_image_of_mem τ ha, (hσ a ⟨(hAI ha).1.le, (hAI ha).2.le⟩).symm⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨ee a, mem_image_of_mem ee ha, hσ a ⟨(hAI ha).1.le, (hAI ha).2.le⟩⟩
  rw [heq, hAB]

/-- Two finite sets of circle marks of the same size are matched by an
orientation preserving homeomorphism. No order of graft roots needs to
be prescribed in VIII (9.3), page 270. -/
theorem exists_circle_match {Z W : Set Circle} (hZ : Z.Finite) (hW : W.Finite)
    (hcard : Z.ncard = W.ncard) :
    ∃ σ : Circle ≃ₜ Circle, PreservesCircleOrientation σ ∧ σ '' Z = W := by
  classical
  have hinf : (univ : Set Circle).Infinite :=
    GM07.isOArc_infinite_any ⟨(Homeomorph.Set.univ Circle).symm⟩
  obtain ⟨z, -, hz⟩ := (hinf.sdiff hZ).nonempty
  obtain ⟨w, -, hw⟩ := (hinf.sdiff hW).nonempty
  let a := Homeomorph.mulLeft z⁻¹
  let b := Homeomorph.mulLeft w⁻¹
  have ha1 : (1 : Circle) ∉ a '' Z := by
    rintro ⟨x, hx, heq⟩
    change z⁻¹ * x = 1 at heq
    have h : x = z := (inv_mul_eq_one.mp heq).symm
    exact hz (h ▸ hx)
  have hb1 : (1 : Circle) ∉ b '' W := by
    rintro ⟨x, hx, heq⟩
    change w⁻¹ * x = 1 at heq
    have h : x = w := (inv_mul_eq_one.mp heq).symm
    exact hw (h ▸ hx)
  obtain ⟨τ, hτo, hτ⟩ := exists_circle_match_of_not_mem_one (hZ.image a) (hW.image b)
    ha1 hb1 (by rw [ncard_image_of_injective _ a.injective,
      ncard_image_of_injective _ b.injective]; exact hcard)
  refine ⟨(a.trans τ).trans b.symm, ?_, ?_⟩
  · have hb : b.symm = Homeomorph.mulLeft w := by
      dsimp [b]
      rw [Homeomorph.mulLeft_symm, inv_inv]
    rw [hb]
    exact (preservesCircleOrientation_mul w).comp (hτo.comp (preservesCircleOrientation_mul z⁻¹))
  · calc
      ((a.trans τ).trans b.symm) '' Z = b.symm '' (τ '' (a '' Z)) := by
        rw [image_image, image_image]
        rfl
      _ = W := by rw [hτ]; simp only [image_image, b.symm_apply_apply, image_id']

end GraphMinor.GM08
