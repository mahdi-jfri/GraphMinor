module

public import GraphMinor.GM08.Section16Defs
public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section16PrintedCaseTwo
import GraphMinor.GM08.Section16Index
import GraphMinor.GM08.Section16Split
import GraphMinor.GM08.Section14

/-!
# The graft conclusion of Case 2 with the printed width

The closest small hoop separates a lower-index tubular graft from a graft in
`printedClassA`. Gluing these two pieces proves the middle alternative of VIII (16.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v

private theorem twoPieceGluing_symm {α : Type u} {β : Type v} {X A B : Graft α β}
    (h : IsTwoPieceGluing X A B) : IsTwoPieceGluing X B A where
  le_A := h.le_B
  le_B := h.le_A
  vertexSet_union := (union_comm _ _).trans h.vertexSet_union
  edgeSet_union := (union_comm _ _).trans h.edgeSet_union
  edge_disjoint := h.edge_disjoint.symm
  inter_sub_TA := by rw [inter_comm]; exact h.inter_sub_TB
  inter_sub_TB := by rw [inter_comm]; exact h.inter_sub_TA
  T_sub_union := by rw [union_comm]; exact h.T_sub_union
  union_diff_sub_T := by rw [union_comm B.T A.T, inter_comm]; exact h.union_diff_sub_T

/-- Case 2 of Graph Minors VIII (16.2), page 283. The second boundary has
minimum cut size, and the first boundary is larger. -/
theorem Tube.Framing.mem_WGraftClass_of_minimum_second_boundary_printed {S : Type}
    [TopologicalSpace S] {τ : Tube S} {α : Type u} {β : Type v} [Infinite α]
    {X : Graft α β} (fr : τ.Framing X) {k r s : ℕ} (hk : X.index ≤ k)
    (hglobal : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H → H ⊆ cylinderBetween τ.F₁ τ.F₂ →
      (τ.Γ.V ∩ τ.F₂).ncard ≤ (τ.Γ.V ∩ H).ncard)
    (hlt : (τ.Γ.V ∩ τ.F₂).ncard < (τ.Γ.V ∩ τ.F₁).ncard)
    (hnot : ¬ τ.IsPrintedBoundaryLinked r s) :
    X ∈ WGraftClass (graftDirectSumClass (classB ((k : ℤ) - 1)) (printedClassA (2 * k) r (s + 2))) := by
  have hex : ∃ H : Set S, IsHoop H ∧ τ.Γ.IsNormal H ∧
      H ⊆ cylinderBetween τ.F₁ τ.F₂ ∧ (τ.Γ.V ∩ H).ncard < (τ.Γ.V ∩ τ.F₁).ncard :=
    ⟨τ.F₂, τ.isHoop_F₂, τ.isNormal_F₂, subset_cylinderBetween_right τ.laminar, hlt⟩
  obtain ⟨F, hF, hNF, hFsub, hFlt, hmin⟩ := τ.exists_closest_small_hoop hex
  let hlam := areLaminarHoops_of_subset_cylinderBetween τ.laminar hF hFsub
  have hno := τ.hasNoPrintedSubTubeOf_left_of_closest hF hNF hFsub
    (lt_of_le_of_lt (Nat.zero_le _) hlt) rfl hglobal hmin hnot
  have hA : fr.subGraft hlam.1 ∈ printedClassA (2 * k) r (s + 2) := by
    apply mem_printedClassA_of_framing (τ := τ.subTube hlam.1 τ.isNormal_F₁ hNF)
      (hfr := fr.isFraming_subTube hlam.1 τ.isNormal_F₁ hNF) (hno := hno)
    have hroot₁ : (fr.vertsIn τ.F₁).ncard ≤ X.index := by
      change (fr.vertsIn τ.F₁).ncard ≤ X.T.ncard
      apply ncard_le_ncard _ (X.finite_G.1.subset X.T_subset)
      rw [← fr.vertsIn_F_union]
      exact subset_union_left
    have hrootF : (fr.vertsIn F).ncard < (fr.vertsIn τ.F₁).ncard := by
      rw [fr.ncard_vertsIn, fr.ncard_vertsIn, inter_comm F, inter_comm τ.F₁]
      exact hFlt
    have hsum := ncard_union_le (fr.vertsIn τ.F₁) (fr.vertsIn F)
    change (fr.vertsIn τ.F₁ ∪ fr.vertsIn F).ncard ≤ 2 * k
    omega
  have hB : fr.subGraft hlam.2 ∈ classB ((k : ℤ) - 1) := by
    refine ⟨IsTubularGraft.of_framing (fr.isFraming_subTube hlam.2 hNF τ.isNormal_F₂), ?_⟩
    have hidx := fr.index_right_lt_of_hoop hF hFsub hFlt
    change ((fr.subGraft hlam.2).index : ℤ) ≤ (k : ℤ) - 1
    omega
  have h := mem_WGraftClass_of_isTwoPieceGluing
    (twoPieceGluing_symm (fr.isTwoPieceGluing_of_hoop hF hNF hFsub)) hB hA
  rwa [isoGraftClass_classB_eq, isoGraftClass_printedClassA_eq] at h

end GraphMinor.GM08
