module

public import GraphMinor.GM08.Section16Defs
public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section16PrintedCaseOne
import GraphMinor.GM08.Section16Index
import GraphMinor.GM08.Section16PrintedCaseTwoGraft
import GraphMinor.GM08.Section16Symm
import GraphMinor.GM08.Section16PrintedSymm

/-!
# The three cases of Graph Minors VIII (16.2)

Choose a normal hoop with minimum vertex count. If both boundaries attain
that count, Menger gives the first alternative. If just the smaller boundary
attains it, use the closest small hoop. Otherwise, the minimum hoop cuts the
graft into two pieces of smaller index.

The width is precisely the printed width. In Case 2, if the moved hoop
loses width, an offending hoop with the old boundary vertex set replaces
it. The proved one-unit length estimate fits within the two-unit allowance.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v

private theorem inclusion_of_ordered_boundary_counts {S : Type} [TopologicalSpace S]
    {τ : Tube S} {α : Type u} {β : Type v} [Infinite α] {X : Graft α β}
    (fr : τ.Framing X) {k r s : ℕ} (hk : X.index ≤ k)
    (hnot : ¬ τ.IsPrintedBoundaryLinked r s)
    (horder : (τ.Γ.V ∩ τ.F₂).ncard ≤ (τ.Γ.V ∩ τ.F₁).ncard) :
    X ∈ printedClassA k r s ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (printedClassA (2 * k) r (s + 2))) ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classB ((k : ℤ) - 1))) := by
  obtain ⟨F, hF, hNF, hFsub, hmin⟩ := τ.exists_minimum_hoop
  have hmin₁ := hmin τ.F₁ τ.isHoop_F₁ τ.isNormal_F₁ (subset_cylinderBetween_left τ.laminar)
  have hmin₂ := hmin τ.F₂ τ.isHoop_F₂ τ.isNormal_F₂ (subset_cylinderBetween_right τ.laminar)
  by_cases heq₁ : (τ.Γ.V ∩ τ.F₁).ncard = (τ.Γ.V ∩ F).ncard
  · have heq₂ : (τ.Γ.V ∩ τ.F₂).ncard = (τ.Γ.V ∩ F).ncard := by omega
    exact Or.inl (Or.inl (mem_printedClassA_of_framing hk ⟨fr⟩
      (τ.hasNoPrintedSubTubeOf_of_minimum_boundaries heq₁ heq₂ hmin hnot)))
  · by_cases heq₂ : (τ.Γ.V ∩ τ.F₂).ncard = (τ.Γ.V ∩ F).ncard
    · have hglobal : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H →
          H ⊆ cylinderBetween τ.F₁ τ.F₂ →
          (τ.Γ.V ∩ τ.F₂).ncard ≤ (τ.Γ.V ∩ H).ncard := by
        rw [heq₂]
        exact hmin
      exact Or.inl (Or.inr (fr.mem_WGraftClass_of_minimum_second_boundary_printed hk hglobal
        (by omega) hnot))
    · exact Or.inr (fr.mem_WGraftClass_of_smaller_hoop hk hF hNF hFsub (by omega) (by omega))

/-- Graph Minors VIII (16.2), pages 282–284. The three minimum-hoop cases
use exactly the printed width exceptions. In Case 2 the exceptional-hoop
replacement supplies the width step and its required length estimate. -/
theorem theorem_16_2_proof {α : Type u} {β : Type v} [Infinite α] (k r s : ℕ) :
    printedClassBUnlinked (α := α) (β := β) k r s ⊆ printedClassA k r s ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (printedClassA (2 * k) r (s + 2))) ∪
      WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (classB ((k : ℤ) - 1))) := by
  rintro X ⟨hk, S, ts, τ, ⟨fr⟩, hnot⟩
  by_cases horder : (τ.Γ.V ∩ τ.F₂).ncard ≤ (τ.Γ.V ∩ τ.F₁).ncard
  · exact inclusion_of_ordered_boundary_counts fr hk hnot horder
  · have hnot' : ¬ τ.symm.IsPrintedBoundaryLinked r s := by
      intro h
      have h' := h.symm
      rw [Tube.symm_symm] at h'
      exact hnot h'
    exact inclusion_of_ordered_boundary_counts fr.symm hk hnot' (Nat.le_of_lt (Nat.lt_of_not_ge horder))

end GraphMinor.GM08
