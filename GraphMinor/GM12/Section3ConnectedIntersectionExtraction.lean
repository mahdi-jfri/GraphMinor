module

public import GraphMinor.GM12.Section3LineIntersectionExtraction
import GraphMinor.GM12.Section3ConnectedSubcircle

/-!
# The connected-intersection case of schismatic extraction

The extraction used by XII (3.1), page 245, is already proved for
circles meeting once. If their intersection is connected and has more
than one point, it is a proper compact connected part of either circle,
hence a line. The common-line theta argument then supplies a schismatic
subset. Thus only disconnected intersections remain after this step.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Two near-planar circles with a nontrivial connected intersection
and non-near-planar union contain a schismatic subset. -/
theorem exists_schismatic_subset_of_connected_circle_intersection
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {F A : Set S} (hF : IsOArc F) (hA : IsOArc A)
    (hnF : GM07.IsNearPlanar F) (hnA : GM07.IsNearPlanar A)
    (hnot : ¬ GM07.IsNearPlanar (F ∪ A))
    (hmeet : (F ∩ A).Nonempty) (hpre : IsPreconnected (F ∩ A))
    (hnonsingle : ∀ x, F ∩ A ≠ {x}) :
    ∃ Y, Y ⊆ F ∪ A ∧ GM07.IsSchismatic Y := by
  classical
  obtain ⟨x, hx⟩ := hmeet
  have hex : ∃ y ∈ F ∩ A, y ≠ x := by
    by_contra hn
    apply hnonsingle x
    apply Subset.antisymm
    · intro y hy
      have heq : y = x := by
        by_contra hne
        exact hn ⟨y, hy, hne⟩
      exact mem_singleton_iff.mpr heq
    · exact singleton_subset_iff.mpr hx
  obtain ⟨y, hy, hyx⟩ := hex
  have hproper : F ∩ A ≠ F := by
    intro heq
    have hFA : F ⊆ A := heq.symm ▸ inter_subset_right
    have hEq : F = A := oArc_eq_of_subset hF hA hFA
    exact hnot (by simpa only [hEq, union_self] using hnA)
  have hcompact : IsCompact (F ∩ A) := hF.isCompact.inter_right hA.isCompact.isClosed
  obtain ⟨u, v, _, hL⟩ := isLineWithEnds_of_compact_preconnected_subset_oArc
    hF inter_subset_left hproper hcompact hpre hx hy hyx.symm
  exact exists_schismatic_subset_of_line_intersection hF hA hL rfl hnF hnA hnot

end GraphMinor.GM12
