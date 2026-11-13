module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM08.Section18CutSide
import GraphMinor.GM08.Section18DiscComplement
import GraphMinor.GM08.Section18BoundaryDisc
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.DiscMerge
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section5a

/-!
# The disc side of a proper arc cut

The image of a disc side is a disc whose boundary consists of the cutting
arc and a complementary line. The complementary line maps into the old
boundary, hence into the cuff containing an end of the cutting arc.
Interior points of a disc are interior points of the surface, so the disc
meets that cuff precisely in this complementary line. Capping the cuff
therefore makes the cutting arc together with the cuff planar. This
excludes the disc side for schisms of type (iii) in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- A disc side of a proper arc cut makes the cutting arc together with
its end cuff near-planar. This is the disc-side exclusion for type (iii)
in VIII (18.2), page 286. -/
theorem isNearPlanar_union_cuff_of_arc_disc_side {S T : Type w}
    [TopologicalSpace S] [TopologicalSpace T] (hS : IsSurface S) (hT : IsSurface T)
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F) {u v : S}
    (hF : IsLineWithEnds F u v) (hbd : F ∩ bd S = {u, v})
    {C : Set S} (hC : C ∈ cuffs S) (hu : u ∈ C)
    {W A B : Set T} (hW : IsClopen W) (hdisc : IsClosedDisc W)
    (hlifts : A ∪ B = ψ ⁻¹' F) (hBW : Disjoint B W)
    (hAW : A ⊆ W) (hbA : BijOn ψ A F) : GM07.IsNearPlanar (F ∪ C) := by
  have : T2Space S := hS.2.1
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  obtain ⟨hΔ, hΔbd⟩ := isClosedDisc_image_cut_side hcut hdisc hlifts hBW hbA.injOn
  let Δ := ψ '' W
  have hFΔbd : F ⊆ discBd Δ := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hbA.surjOn hz
    have hyW : y ∈ W := hAW hy
    have hybd : y ∈ bd T := hcut.2.2.2.2 (hlifts ▸ Or.inl hy)
    rw [hΔbd]
    exact ⟨y, ⟨⟨y, hyW⟩, (mem_bd_sub hW.2).mpr hybd, rfl⟩, rfl⟩
  obtain ⟨L, hL, hcover, hinter⟩ := exists_complementary_boundary_line hΔ hF hFΔbd
  have hFΔ : F ⊆ Δ := hFΔbd.trans (Surface.discBd_subset Δ)
  have hLΔbd : L ⊆ discBd Δ := subset_union_right.trans hcover.subset
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hendsL : ({u, v} : Set S) ⊆ L := by
    rintro x (rfl | rfl)
    · exact hL.left_mem
    · exact hL.right_mem
  have hLbd : L ⊆ bd S := by
    intro x hxL
    by_cases hxF : x ∈ F
    · exact (hbd.symm ▸ hinter.subset ⟨hxF, hxL⟩ : x ∈ F ∩ bd S).2
    · obtain ⟨y, hybd, hyx⟩ := hΔbd.subset (hLΔbd hxL)
      have hyT : y ∈ bd T := by
        obtain ⟨z, hz, hzy⟩ := hybd
        exact hzy ▸ (mem_bd_sub hW.2).mp hz
      have hxold := bd_of_bd hcut (GM07.IsLineWithEnds.isSolid hF).2 hyT
        (fun hyF => hxF (hyx ▸ hyF))
      exact hyx ▸ hxold
  have hcomponent : connectedComponentIn (bd S) u = C := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact (connectedComponentIn_eq hu).symm
  have hLC : L ⊆ C := by
    rw [← hcomponent]
    exact (GM07.IsLineWithEnds.isConnected hL).2.subset_connectedComponentIn hL.left_mem hLbd
  have hΔC : Δ ∩ C = L := by
    apply Subset.antisymm
    · rintro x ⟨hxΔ, hxC⟩
      have hxbd : x ∈ discBd Δ := by
        by_contra hn
        exact hCbd hxC (isInteriorPoint_of_mem_discInt hS.2.2 hΔ ⟨hxΔ, hn⟩)
      rcases hcover.symm ▸ hxbd with hxF | hxL
      · exact hendsL (hbd.subset ⟨hxF, hCbd hxC⟩)
      · exact hxL
    · exact fun x hx => ⟨Surface.discBd_subset Δ (hLΔbd hx), hLC hx⟩
  have hp := isPlanarInCappedCuff_disc_union_cuff hS hC hΔ hL hΔC hLΔbd
  exact Or.inr ⟨C, hC, hp.mono (union_subset_union_left C hFΔ)⟩

end GraphMinor.GM08
