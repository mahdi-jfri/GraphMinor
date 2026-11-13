module

public import GraphMinor.GM08.Section11Side
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.Surface.DiscMerge

/-!
# Intersections of the closed foundation discs

The closed ring discs meet only at the nodes left outside all ring
interiors. Their intersections with the ambient boundary are nodes as
well. These checks let the foundation discs form cells of the painting
constructed on VIII, page 272, for Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

variable {S : Type u} [TopologicalSpace S] {D : Drawing S}
  {t : ℕ} {F : Fin t → Set S}

/-- A foundation ring bounds a closed disc, as used in Section 12. -/
theorem IsFoundation.ring_disc (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation D univ F) (i : Fin t) :
    IsClosedDisc (F i ∪ insideSet (F i)) ∧
      discBd (F i ∪ insideSet (F i)) = F i := by
  obtain ⟨B, hB, hBd, -, hEq⟩ := exists_ring_disc hS (hF.isOArc i)
  exact hEq.symm ▸ And.intro hB hBd

/-- Ambient boundary points cannot lie inside a foundation ring. -/
theorem IsFoundation.not_inside_of_bd (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation D univ F) {x : S} (hx : x ∈ bd S) (i : Fin t) :
    x ∉ insideSet (F i) := by
  obtain ⟨B, hB, -, hInt, -⟩ := exists_ring_disc hS (hF.isOArc i)
  intro hi
  have hxi := discInt_mono (isSurface_of_closedDisc_univ hS).2.2 hB
    (subset_univ B) (hInt ▸ hi)
  exact hxi.2 (GM06.discBd_univ S ▸ hx)

/-- Closed foundation discs intersect only at nodes of the painting. -/
theorem IsFoundation.ring_discs_inter_nodes (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation D univ F) {i j : Fin t} (hij : i ≠ j) :
    (F i ∪ insideSet (F i)) ∩ (F j ∪ insideSet (F j)) ⊆ ringNodes D F := by
  rintro x ⟨hxi, hxj⟩
  have hxiF : x ∈ F i := by
    rcases hxi with h | h
    · exact h
    · rcases hxj with hj | hj
      · exact False.elim (disjoint_left.mp (hF.disjoint_ring_inside hS hij.symm) hj h)
      · exact False.elim (disjoint_left.mp (hF.disjoint_inside hij) h hj)
  have hxjF : x ∈ F j := hxj.resolve_right
    (disjoint_left.mp (hF.disjoint_ring_inside hS hij) hxiF)
  have hxV : x ∈ D.V := by
    obtain ⟨-, -, -, -, -, -, hFF, -⟩ := hF
    exact hFF hij ⟨hxiF, hxjF⟩
  exact ⟨hxV, fun l => hF.not_inside_of_mem hS hxiF l⟩

/-- A closed foundation disc meets the ambient boundary only at nodes. -/
theorem IsFoundation.ring_disc_inter_bd_nodes (hS : IsClosedDisc (univ : Set S))
    (hF : IsFoundation D univ F) (i : Fin t) :
    (F i ∪ insideSet (F i)) ∩ bd S ⊆ ringNodes D F := by
  rintro x ⟨hx, hxbd⟩
  have hxF : x ∈ F i := hx.resolve_right (hF.not_inside_of_bd hS hxbd i)
  have hxV : x ∈ D.V := by
    obtain ⟨-, -, -, -, -, -, -, hbd⟩ := hF
    exact hbd i ⟨hxF, GM06.discBd_univ S ▸ hxbd⟩
  exact ⟨hxV, fun l => hF.not_inside_of_mem hS hxF l⟩

end GraphMinor.GM08
