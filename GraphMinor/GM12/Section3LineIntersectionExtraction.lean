module

public import GraphMinor.GM12.Section3ThetaSchismatic
public import GraphMinor.GM12.Section3CircleSchismatic
import GraphMinor.Surface.PushOff
import GraphMinor.GM11.RadialChord

/-!
# Extracting a schismatic set when the intersection is a line

In the finite circle-intersection reduction used by XII (3.1),
page 245, two circles with a common line form three branches between
the ends of that line. If the third pair is not near-planar, it is
already a schismatic circle. Otherwise all three pairs are near-planar
and the non-near-planar union is the third schismatic shape.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The common-line case of schismatic extraction: the union is a
theta graph, and either its third circle or the whole union is
schismatic. -/
theorem exists_schismatic_subset_of_line_intersection
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {F A L : Set S} {u v : S} (hF : IsOArc F) (hA : IsOArc A)
    (hL : IsLineWithEnds L u v) (hinter : F ∩ A = L)
    (hnF : GM07.IsNearPlanar F) (hnA : GM07.IsNearPlanar A)
    (hnot : ¬ GM07.IsNearPlanar (F ∪ A)) :
    ∃ Y, Y ⊆ F ∪ A ∧ GM07.IsSchismatic Y := by
  classical
  have hLF : L ⊆ F := hinter ▸ inter_subset_left
  have hLA : L ⊆ A := hinter ▸ inter_subset_right
  obtain ⟨p, q, hpq, hpL, hp0, hp1, hpqF⟩ := exists_arcs_of_line hF hL hLF
  obtain ⟨r, s, hrs, hrL, hr0, hr1, hrsA⟩ := exists_arcs_of_line hA hL hLA
  have huv : u ≠ v := by
    intro heq
    have he : p 0 = p 1 := hp0.trans (heq.trans hp1.symm)
    exact zero_ne_one (hpq.arc_left.2 he)
  have hQ : IsLineWithEnds (range q) u v := by
    have h := isLine_range hpq.arc_right.1 hpq.arc_right.2
    rwa [hpq.zero, hpq.one, hp0, hp1] at h
  have hR : IsLineWithEnds (range s) u v := by
    have h := isLine_range hrs.arc_right.1 hrs.arc_right.2
    rwa [hrs.zero, hrs.one, hr0, hr1] at h
  have hPQ : L ∩ range q = {u, v} := by
    have h := hpq.inter
    rwa [hpL, hp0, hp1] at h
  have hPR : L ∩ range s = {u, v} := by
    have h := hrs.inter
    rwa [hrL, hr0, hr1] at h
  have hF' : L ∪ range q = F := hpL ▸ hpqF
  have hA' : L ∪ range s = A := hrL ▸ hrsA
  have hQF : range q ⊆ F := hF' ▸ subset_union_right
  have hRA : range s ⊆ A := hA' ▸ subset_union_right
  have hQR : range q ∩ range s = {u, v} := by
    apply Subset.antisymm
    · intro x hx
      have hxL : x ∈ L := hinter ▸ (show x ∈ F ∩ A from ⟨hQF hx.1, hRA hx.2⟩)
      exact hPQ ▸ (show x ∈ L ∩ range q from ⟨hxL, hx.1⟩)
    · rintro x (rfl | rfl)
      · exact ⟨hQ.left_mem, hR.left_mem⟩
      · exact ⟨hQ.right_mem, hR.right_mem⟩
  have hunion : L ∪ range q ∪ range s = F ∪ A := by
    rw [← hF', ← hA']
    ext x
    simp only [mem_union]
    tauto
  by_cases hnQR : GM07.IsNearPlanar (range q ∪ range s)
  · refine ⟨F ∪ A, subset_rfl, ?_⟩
    rw [← hunion]
    apply isSchismatic_x3_of_nearPlanar_pairs huv hL hQ hR hPQ hPR hQR
    · exact hF'.symm ▸ hnF
    · exact hA'.symm ▸ hnA
    · exact hnQR
    · exact hunion.symm ▸ hnot
  · refine ⟨range q ∪ range s, union_subset (hQF.trans subset_union_left)
      (hRA.trans subset_union_right), ?_⟩
    exact isSchismatic_oArc (isOArc_union_of_lines_inter_eq_ends hQ hR hQR) hnQR

end GraphMinor.GM12
