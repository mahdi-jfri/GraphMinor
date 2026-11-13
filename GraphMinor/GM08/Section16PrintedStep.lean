module

public import GraphMinor.GM08.Section16PrintedWidth
import GraphMinor.GM08.Section16LengthExtension
import GraphMinor.GM08.Section15

/-!
# Preserving printed width after an inward step

If the moved boundary still gives enough width, use it. Otherwise a hoop
witnessing the width failure must have exactly the old first boundary's
vertex set: the other exception and the lower bound are ruled out by the
witness. Use that hoop instead. Its boundary vertex set preserves the
printed width, and the normal-line extension estimate loses at most one
unit of length. The positive cut bound is supplied by the closest-hoop
argument in Case 2 of VIII (16.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- The width step in Case 2 of VIII (16.2), page 283, with precisely the
printed exceptions. If the inward hoop loses width, an offending hoop with
the old boundary vertex set replaces it. The original two-unit length
allowance covers the possible one-unit loss for that replacement. -/
theorem Tube.exists_printed_wide_hoop_after_step {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r s : ℕ} (hw : (r : ℕ∞) ≤ τ.printedWidth) (hl : s + 2 ≤ τ.length)
    {K : Set S} (hK : IsHoop K) (hNK : τ.Γ.IsNormal K)
    (hKsub : K ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hlenK : s ≤ (τ.subTube
      (areLaminarHoops_of_subset_cylinderBetween τ.laminar hK hKsub).2 hNK τ.isNormal_F₂).length)
    (hpos : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween K τ.F₂ →
      0 < (H ∩ τ.Γ.V).ncard) :
    ∃ (H : Set S) (hHB : AreLaminarHoops H τ.F₂) (hNH : τ.Γ.IsNormal H),
      H ⊆ cylinderBetween K τ.F₂ ∧
      (r : ℕ∞) ≤ (τ.subTube hHB hNH τ.isNormal_F₂).printedWidth ∧
      s ≤ (τ.subTube hHB hNH τ.isNormal_F₂).length := by
  classical
  have : T2Space S := τ.t2Space
  let hKB := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hK hKsub).2
  let κ := τ.subTube hKB hNK τ.isNormal_F₂
  by_cases hwK : (r : ℕ∞) ≤ κ.printedWidth
  · exact ⟨K, hKB, hNK, subset_cylinderBetween_left hKB, hwK, hlenK⟩
  have hbad : ¬ ∀ H : Set S, IsHoop H → κ.Γ.IsNormal H → H ⊆ cylinderBetween K τ.F₂ →
      H ∩ κ.Γ.V = K ∩ κ.Γ.V ∨ H ∩ κ.Γ.V = τ.F₂ ∩ κ.Γ.V ∨
        (r : ℕ∞) ≤ ((H ∩ κ.Γ.V).ncard : ℕ∞) := fun h => hwK (κ.le_printedWidth_iff.mpr h)
  push Not at hbad
  obtain ⟨H, hH, hNHκ, hHsub, _, hneqB, hsmall⟩ := hbad
  have hV : κ.Γ.V = τ.Γ.V ∩ cylinderBetween K τ.F₂ :=
    interSet_V_of_isClosed τ.Γ (isClosed_cylinderBetween hKB)
  have hverts : ∀ J : Set S, J ⊆ cylinderBetween K τ.F₂ → J ∩ κ.Γ.V = J ∩ τ.Γ.V := by
    intro J hJ
    rw [hV]
    ext x
    exact ⟨fun ⟨hxJ, hxV, _⟩ => ⟨hxJ, hxV⟩,
      fun ⟨hxJ, hxV⟩ => ⟨hxJ, hxV, hJ hxJ⟩⟩
  have hneqB' : H ∩ τ.Γ.V ≠ τ.F₂ ∩ τ.Γ.V := by
    simpa only [hverts H hHsub, hverts τ.F₂ (subset_cylinderBetween_right hKB)] using hneqB
  have hsmall' : ((H ∩ τ.Γ.V).ncard : ℕ∞) < (r : ℕ∞) := by
    simpa only [hverts H hHsub] using hsmall
  have hNH : τ.Γ.IsNormal H := (τ.subTube_isNormal_iff hKB hNK τ.isNormal_F₂ hHsub).mp hNHκ
  have hHall : H ⊆ cylinderBetween τ.F₁ τ.F₂ := hHsub.trans
    (cylinderBetween_subset_cylinderBetween τ.laminar hKB hKsub
      (subset_cylinderBetween_right τ.laminar))
  have hAeq : H ∩ τ.Γ.V = τ.F₁ ∩ τ.Γ.V := by
    rcases (τ.le_printedWidth_iff.mp hw) H hH hNH hHall with heq | heq | hbound
    · exact heq
    · exact (hneqB' heq).elim
    · exact (not_lt_of_ge hbound hsmall').elim
  let hHB := (areLaminarHoops_of_subset_cylinderBetween hKB hH hHsub).2
  have hwidth : (r : ℕ∞) ≤ (τ.subTube hHB hNH τ.isNormal_F₂).printedWidth := hw.trans
    (τ.printedWidth_le_subTube_of_boundary_vertices_eq hHB hNH τ.isNormal_F₂
      hHall (subset_cylinderBetween_right τ.laminar) hAeq rfl)
  have hHV : (H ∩ τ.Γ.V).Nonempty := nonempty_of_ncard_ne_zero (Nat.ne_of_gt (hpos H hH hNH hHsub))
  have hHA : H ∩ τ.Γ.V ⊆ τ.F₁ := hAeq ▸ inter_subset_left
  have hlen := τ.length_le_subTube_add_one_of_vertices_on_boundary hH hNH hHall hHV hHA
    (by omega : 2 ≤ τ.length)
  have hlen' : s ≤ (τ.subTube hHB hNH τ.isNormal_F₂).length := by
    change τ.length ≤ (τ.subTube hHB hNH τ.isNormal_F₂).length + 1 at hlen
    omega
  exact ⟨H, hHB, hNH, hHsub, hwidth, hlen'⟩

end GraphMinor.GM08
