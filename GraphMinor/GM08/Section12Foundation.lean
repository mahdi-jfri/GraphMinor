module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section12Bosses
import GraphMinor.GM08.Section12RingFamily
import GraphMinor.GM08.Section12Rings
import GraphMinor.GM08.Section12NormalShrink
import GraphMinor.GM08.Section9Foundation
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM08.Section6
import GraphMinor.GM06.DiscRegions
import GraphMinor.Surface.Disc

/-!
# Existence of the foundation used in VIII, Section 12

Choose maximal boss edge sets, uncross their minimal rings, and shrink
the discs slightly. The shrinking preserves the drawing contacts and
enclosed edges, so minimality is retained. Disjoint interiors then make
distinct rings meet only in drawing vertices. The same adjustment makes
each ring meet the ambient boundary only in drawing vertices. This is
the foundation construction on page 267 used in the disc conclusion.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- The final shrinking of a minimal boss ring in VIII, page 267.
The new minimal ring lies inside the old one except at drawing vertices. -/
theorem exists_clean_minimal_ring {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S}
    (hS : IsClosedDisc (univ : Set S))
    {C : DiscCircuit D univ} {F : Set S}
    (hC : IsBoss D univ C) (hF : IsMinimalCRing C F) :
    ∃ F' : Set S, IsMinimalCRing C F' ∧ OArcEncloses univ F F' ∧
      ∀ x ∈ F', InsideOArc univ F x ∨ x ∈ D.V := by
  obtain ⟨B, hB, -⟩ := disc_oArc univ F hS (subset_univ _) hF.1.2.1
  have hCU : C.U ⊆ C.ins := C.isInside.2.2.1 ▸ discBd_subset C.ins
  have hCB := insideDisc_subset_of_oArcEncloses hS hB C.isInside hF.1.2.2.2.1
  have hCint := hC.inside_cRing hS (subset_univ _) hF.1
  have hKB : C.ins ⊆ discInt B := by
    intro x hx
    by_cases hxBd : x ∈ discBd C.ins
    · exact (insideOArc_iff_mem_discInt hS hB).mp
        (hCint x (C.isInside.2.2.1 ▸ hxBd))
    · exact hCB.2 ⟨hx, hxBd⟩
  have hnB : D.IsNormal (discBd B) := hB.2.2.1.symm ▸ hF.1.2.2.1
  obtain ⟨B', hB', hK', hsub, hn', hV', hclean, -⟩ :=
    exists_shrunk_normal_disc_in_disc hS D hB.2.1 C.isInside.2.1 hKB hnB
  obtain ⟨E, hE, huniq⟩ := disc_oArc univ (discBd B') hS (subset_univ _) hB'.isOArc_discBd
  have heq : E = B' := (huniq B' (subset_univ _) hB' rfl).symm
  have hB'inside : IsInsideDisc univ (discBd B') B' := heq ▸ hE
  have henc : OArcEncloses univ F (discBd B') :=
    (oArcEncloses_iff_subset hS hB).mpr ((discBd_subset _).trans hsub)
  have hCR : IsCRing C (discBd B') := by
    refine ⟨subset_univ _, hB'.isOArc_discBd, hn', ?_, ?_⟩
    · exact (oArcEncloses_iff_subset hS hB'inside).mpr
        (hCU.trans (hK'.trans (discInt_subset _)))
    · rw [hV', hB.2.2.1]
      exact hF.1.2.2.2.2
  refine ⟨discBd B', hF.of_enclosed hS hCR henc, henc, ?_⟩
  intro x hx
  rcases hclean hx with hin | hv
  · exact .inl ((insideOArc_iff_mem_discInt hS hB).mpr hin)
  · exact .inr hv

/-- The foundation existence construction on VIII, page 267, used in
Section 12, page 274. It follows the maximal-boss choice, repeated
uncrossing by (6.5), and the final shrinking of the ring discs. -/
theorem exists_foundation {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S) (hprop : D.IsProper) :
    ∃ (t : ℕ) (F : Fin t → Set S), IsFoundation D univ F := by
  classical
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  have : ConnectedSpace S := connectedSpace_iff_univ.mpr hS.isPathConnected.isConnected
  have hbd : D.IsNormal (discBd (univ : Set S)) := by rw [GM06.discBd_univ]; exact hprop
  obtain ⟨t, C, hC, hdis, hcover⟩ := exists_maximal_boss_family (D := D) hS
  obtain ⟨F, hF, hFdis⟩ := exists_disjoint_minimal_ring_family hS (subset_univ _) hbd C hC hdis
  choose G hG heG hclean using fun i => exists_clean_minimal_ring hS (hC i) (hF i)
  refine ⟨t, G, C, hC, hdis, hcover, hG, ?_, ?_, ?_⟩
  · intro i j hij
    exact boundDisjointOpenDiscs_of_enclosed hS
      (hF i).1.1 (hF j).1.1 (hG i).1.1 (hG j).1.1
      (hF i).1.2.1 (hF j).1.2.1 (hG i).1.2.1 (hG j).1.2.1
      (heG i) (heG j) (hFdis hij)
  · intro i j hij x hx
    by_contra hxV
    exact disjoint_left.mp (hFdis hij)
      ((hclean i x hx.1).resolve_right hxV) ((hclean j x hx.2).resolve_right hxV)
  · intro i x hx
    by_contra hxV
    obtain ⟨B, hB, hxB⟩ := (hclean i x hx.1).resolve_right hxV
    have hxF : x ∈ B \ F i := ⟨hxB.1, hB.2.2.1 ▸ hxB.2⟩
    exact disjoint_left.mp hB.2.2.2.2.1 hxF hx.2

end GraphMinor.GM08
