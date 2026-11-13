module

public import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.Fan
import GraphMinor.Surface.PlaneDisc
import GraphMinor.GM16.TangentDisc
import GraphMinor.GM07.CuffFrame

/-!
# Disjoint loop petals in the disc induction

Inside an empty disc touching a drawing vertex, place finitely many
smaller discs that meet only at that vertex. Split the disc by a chord,
put one petal tangent in one half, and repeat in the other half. Their
boundaries give loops whose bounded interiors stay empty. This is used
to choose the cellular drawings for VIII, Section 12, page 274.
-/

public section

namespace GraphMinor.GM08

open Set Surface Metric

universe u

private theorem exists_petal_discs_zero {S : Type} [TopologicalSpace S] [T2Space S]
    (n : ℕ) {D : Set S} (hD : IsClosedDisc D) {v : S} (hv : v ∈ discBd D) :
    ∃ E : Fin n → Set S,
      (∀ i, IsClosedDisc (E i) ∧ E i ⊆ D ∧ v ∈ discBd (E i)) ∧
      Pairwise (fun i j => E i ∩ E j = {v}) := by
  classical
  induction n generalizing D with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨w, hw, hwv⟩ := ((GM07.isOArc_infinite_any hD.isOArc_discBd).sdiff (finite_singleton v)).nonempty
    have hvw : v ≠ w := Ne.symm hwv
    obtain ⟨L, hL, hLD, hLbd⟩ := exists_chord hD hv hw hvw
    obtain ⟨A₁, A₂, D₁, D₂, _, _, hD₁, hD₂, hcover, hmeet, hbd₁, hbd₂, _⟩ :=
      disc_iArc D L v w hD hLD hvw hL hLbd
    have hvL : v ∈ L := hL.left_mem
    have hv₁ : v ∈ discBd D₁ := hbd₁.symm ▸ Or.inr hvL
    have hv₂ : v ∈ discBd D₂ := hbd₂.symm ▸ Or.inr hvL
    obtain ⟨E₀, hE₀, hE₀D, _, hvE₀, hE₀bd⟩ :=
      GM16.exists_tangent_disc hD₁ isOpen_univ hv₁ (mem_univ v)
    obtain ⟨E, hE, hEE⟩ := ih hD₂ hv₂
    have hsub₁ : D₁ ⊆ D := hcover ▸ subset_union_left
    have hsub₂ : D₂ ⊆ D := hcover ▸ subset_union_right
    have hcross : ∀ i, E₀ ∩ E i = {v} := by
      intro i
      apply Subset.antisymm
      · rintro x ⟨hx₀, hxi⟩
        have hxL : x ∈ L := hmeet ▸ And.intro (hE₀D hx₀) ((hE i).2.1 hxi)
        have hxbd : x ∈ discBd D₁ := hbd₁.symm ▸ Or.inr hxL
        exact hE₀bd ▸ And.intro hx₀ hxbd
      · rintro x rfl
        exact ⟨discBd_subset E₀ hvE₀, discBd_subset (E i) (hE i).2.2⟩
    refine ⟨Fin.cons E₀ E, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hE₀, hE₀D.trans hsub₁, hvE₀⟩
      · exact ⟨(hE j).1, (hE j).2.1.trans hsub₂, (hE j).2.2⟩
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j _ => hcross j) j
        exact fun h => False.elim (h rfl)
      · refine Fin.cases ?_ (fun j hij => hEE (fun h => hij (congrArg Fin.succ h))) j
        intro _
        rw [inter_comm]
        exact hcross i

/-- Finitely many petal discs inside a closed disc, meeting only at one
boundary vertex. Their boundaries are the cellular loops used before
deriving portraits in VIII, Section 12, page 274. -/
theorem exists_petal_discs {S : Type u} [TopologicalSpace S] [T2Space S]
    (n : ℕ) {D : Set S} (hD : IsClosedDisc D) {v : S} (hv : v ∈ discBd D) :
    ∃ E : Fin n → Set S,
      (∀ i, IsClosedDisc (E i) ∧ E i ⊆ D ∧ v ∈ discBd (E i)) ∧
      Pairwise (fun i j => E i ∩ E j = {v}) := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hp : h v ∈ discBd (closedBall (0 : ℂ) 1) := by
    rw [isClosedDisc_closedBall.2, ← c.bd]
    exact mem_image_of_mem h hv
  obtain ⟨E, hE, hEE⟩ := exists_petal_discs_zero n isClosedDisc_closedBall.1 hp
  have hgv : g (h v) = v := c.gh (discBd_subset D hv)
  refine ⟨fun i => g '' E i, ?_, ?_⟩
  · intro i
    have hd := c.disc_g (hE i).2.1 (hE i).1
    refine ⟨hd.1, c.g_subset (hE i).2.1, ?_⟩
    rw [hd.2]
    exact hgv ▸ mem_image_of_mem g (hE i).2.2
  · intro i j hij
    rw [← c.g_inter (hE i).2.1 (hE j).2.1, hEE hij, image_singleton, hgv]

end GraphMinor.GM08
