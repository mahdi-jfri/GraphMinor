module

public import GraphMinor.GM08.Section9
import GraphMinor.GM08.Section9Foundation
import GraphMinor.GM08.Section9Reduction
import GraphMinor.GM08.Section11Inside
import GraphMinor.Surface.Disc
import GraphMinor.GM06.DiscRegions

/-!
# Graph Minors VIII (9.1): nests in a truncation are boundary-linked

A nest which is not boundary-linked starts with a boss. Minimum-ring
uniqueness and foundation coverage put that boss inside a selected ring.
The sleeve count then gives a contradiction. For the count we retain
`k / 2 + 1` enclosed circuits, including possible ring contacts. This covers
the small even-boundary case of the printed proof (see the correction to the
proof of (9.1) in `corrections/GM08.md`).
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

universe u

/-- A truncation is a subdrawing, by its defining induced foundation. -/
theorem IsTruncation.isSubdrawing {S : Type u} [TopologicalSpace S]
    {D Dstar : Drawing S} {Δ : Set S} (h : IsTruncation D Δ Dstar) : Dstar.IsSubdrawing D := by
  obtain ⟨t, F, hF⟩ := h
  exact hF.2.1

/-- Graph Minors VIII, (9.1), pages 269–270: every `(r,s)`-nest of a
truncation is boundary-linked in the original drawing when `r,s ≥ k`.
Properness is part of the paper's drawing definition, Section 5(iii), page 262.
The sleeve contradiction uses a corrected count of enclosed circuits. -/
theorem theorem_9_1_proof {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) {D Dstar : Drawing S} (hprop : D.IsProper)
    (htrunc : IsTruncation D univ Dstar) {r s : ℕ}
    (hr : (D.V ∩ discBd (univ : Set S)).ncard ≤ r)
    (hs : (D.V ∩ discBd (univ : Set S)).ncard ≤ s) (N : DrawingNest Dstar univ r s) :
    IsBoundaryLinkedNest D univ (N.ofSubdrawing htrunc.isSubdrawing) := by
  have hS' := hS
  obtain ⟨e⟩ := hS'
  have : T2Space S := (e.trans (Homeomorph.Set.univ S)).t2Space
  have : ConnectedSpace S := connectedSpace_iff_univ.mpr hS.isPathConnected.isConnected
  have hbd : D.IsNormal (discBd (univ : Set S)) := by
    rw [GM06.discBd_univ]
    exact hprop
  obtain ⟨t, F, hF⟩ := htrunc
  change IsBoundaryLinkedNest D univ (N.ofSubdrawing hF.2.1)
  by_contra hnot
  obtain ⟨hpos, hboss⟩ := isBoss_of_not_isBoundaryLinkedNest hS (subset_univ _) hbd
    (N.ofSubdrawing hF.2.1) hr hs hnot
  obtain ⟨i, henc⟩ := hF.1.encloses_boss hS (subset_univ _) hbd hboss
  exact hF.not_encloses_first_disc hS N hpos hr hs i henc

end GraphMinor.GM08
