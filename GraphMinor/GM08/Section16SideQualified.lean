module

public import GraphMinor.GM08.Section16Defs
import GraphMinor.GM08.Section16CaseOne
import GraphMinor.GM08.Section16Index
import GraphMinor.GM08.Section16CaseTwoGraft
import GraphMinor.GM08.Section16Symm

/-!
# The three cases with side-qualified width

Choose a normal hoop with minimum vertex count. If both boundaries attain
that count, Menger gives the first alternative. If just the smaller boundary
attains it, use the closest small hoop. Otherwise, the minimum hoop cuts the
graft into two pieces of smaller index.

The width used here is the side-qualified width of `Section15Tube`, whose
exceptions are stronger than the printed definition on page 280. Thus the
class inclusion below concerns that definition; it does not settle the
comparison with the printed definition.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

private theorem inclusion_of_ordered_boundary_counts {S : Type w} [TopologicalSpace S]
    {τ : Tube S} {α : Type u} {β : Type v} [Infinite α] {X : Graft α β}
    (fr : τ.Framing X) {k r s : ℕ} (hk : X.index ≤ k)
    (hnot : ¬ τ.IsBoundaryLinked r s)
    (horder : (τ.Γ.V ∩ τ.F₂).ncard ≤ (τ.Γ.V ∩ τ.F₁).ncard) :
    X ∈ classA k r s ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classA (2 * k) r (s + 2))) ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classB ((k : ℤ) - 1))) := by
  obtain ⟨F, hF, hNF, hFsub, hmin⟩ := τ.exists_minimum_hoop
  have hmin₁ := hmin τ.F₁ τ.isHoop_F₁ τ.isNormal_F₁ (subset_cylinderBetween_left τ.laminar)
  have hmin₂ := hmin τ.F₂ τ.isHoop_F₂ τ.isNormal_F₂ (subset_cylinderBetween_right τ.laminar)
  by_cases heq₁ : (τ.Γ.V ∩ τ.F₁).ncard = (τ.Γ.V ∩ F).ncard
  · have heq₂ : (τ.Γ.V ∩ τ.F₂).ncard = (τ.Γ.V ∩ F).ncard := by omega
    exact Or.inl (Or.inl (mem_classA_of_framing hk ⟨fr⟩
      (τ.hasNoSubTubeOf_of_minimum_boundaries heq₁ heq₂ hmin hnot)))
  · by_cases heq₂ : (τ.Γ.V ∩ τ.F₂).ncard = (τ.Γ.V ∩ F).ncard
    · have hglobal : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H →
          H ⊆ cylinderBetween τ.F₁ τ.F₂ →
          (τ.Γ.V ∩ τ.F₂).ncard ≤ (τ.Γ.V ∩ H).ncard := by
        rw [heq₂]
        exact hmin
      exact Or.inl (Or.inr (fr.mem_WGraftClass_of_minimum_second_boundary hk hglobal
        (by omega) hnot))
    · exact Or.inr (fr.mem_WGraftClass_of_smaller_hoop hk hF hNF hFsub (by omega) (by omega))

/-- Graph Minors VIII (16.2), pages 282–284, for the side-qualified width
of `Section15Tube`. The proof follows the three cases of the paper. The
comparison of this width with the printed definition remains separate. -/
theorem theorem_16_2_sideQualified {α : Type u} {β : Type v} [Infinite α] (k r s : ℕ) :
    classBUnlinked (α := α) (β := β) k r s ⊆ classA k r s ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classA (2 * k) r (s + 2))) ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classB ((k : ℤ) - 1))) := by
  rintro X ⟨hk, S, ts, τ, ⟨fr⟩, hnot⟩
  by_cases horder : (τ.Γ.V ∩ τ.F₂).ncard ≤ (τ.Γ.V ∩ τ.F₁).ncard
  · exact inclusion_of_ordered_boundary_counts fr hk hnot horder
  · have hnot' : ¬ τ.symm.IsBoundaryLinked r s := by
      intro h
      have h' := h.symm
      rw [Tube.symm_symm] at h'
      exact hnot h'
    exact inclusion_of_ordered_boundary_counts fr.symm hk hnot' (Nat.le_of_lt (Nat.lt_of_not_ge horder))

end GraphMinor.GM08
