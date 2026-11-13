module

public import GraphMinor.GM08.Section11Side
import GraphMinor.GM08.Section12LoopDiscs
import GraphMinor.GM08.Section12CellularFaces
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.Surface.DiscMerge

/-!
# Loop discs outside the foundation

For each remaining loop use the closed disc bounded by its empty
region. The loop-disc separation lemmas show that these discs meet
the foundation and one another only on their edge boundaries. This
assembles the loop part of the thickening on VIII, page 272.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The remaining cellular loops have the thickened discs required
by the derived portrait construction used in VIII, Section 12. -/
theorem exists_loop_disc_family {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S)
    (hp : D.IsProper) (hc : IsCellularDrawing D)
    {t : ℕ} {F : Fin t → Set S} (hF : IsFoundation D univ F) :
    ∃ B : {e : Set S // e ∈ ringEdges D F ∧ D.IsLoop e} → Set S,
      (∀ i, IsClosedDisc (B i) ∧ discBd (B i) = closure i.1 ∧
        B i ∩ D.U = closure i.1 ∧
        (∀ j, B i ∩ (F j ∪ insideSet (F j)) ⊆ closure i.1) ∧
        B i ∩ bd S ⊆ D.V) ∧
      ∀ i j, i ≠ j → B i ∩ B j ⊆ closure i.1 ∩ closure j.1 := by
  classical
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  have hman := (isSurface_of_closedDisc_univ hS).2.2
  let L := {e : Set S // e ∈ ringEdges D F ∧ D.IsLoop e}
  have hex : ∀ i : L, ∃ B, IsInsideDisc univ (closure i.1) B ∧ discInt B ∈ D.R :=
    fun i => hc i.1 i.2.2
  choose B hB hr using hex
  have hFB : ∀ j, IsInsideDisc univ (F j) (F j ∪ insideSet (F j)) := by
    intro j
    obtain ⟨K, hK, hBd, -, hEq⟩ := exists_ring_disc hS (hF.isOArc j)
    have hKi := isInsideDisc_of_closedDisc_univ hS hK
    rw [hBd] at hKi
    exact hEq.symm ▸ hKi
  refine ⟨B, ?_, ?_⟩
  · intro i
    refine ⟨(hB i).2.1, (hB i).2.2.1,
      loop_disc_inter_drawing i.2.1.1 (hB i) (hr i), ?_, ?_⟩
    · intro j
      obtain ⟨C, hC, -, -, hmin, -⟩ := hF
      obtain ⟨v, hv⟩ := i.2.2.2
      exact loop_disc_inter_ring_disc_subset hS i.2.1.1 hv (hB i) (hr i)
        (hC j) (hmin j).1 (hFB j) (i.2.1.2 j)
    · intro x hx
      have hxBd : x ∈ discBd (B i) := by
        by_contra hn
        have hi : x ∈ discInt (univ : Set S) := discInt_mono hman (hB i).2.1
          (subset_univ _) ⟨hx.1, hn⟩
        exact hi.2 (GM06.discBd_univ S ▸ hx.2)
      have hxU := D.closure_subset_U i.2.1.1 ((hB i).2.2.1 ▸ hxBd)
      exact hp ⟨hx.2, hxU⟩
  · intro i j hij
    exact loop_discs_inter_subset_edges i.2.1.1 j.2.1.1
      (fun h => hij (Subtype.ext h)) (hB i) (hB j) (hr i) (hr j)

end GraphMinor.GM08
