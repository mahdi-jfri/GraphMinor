module

public import GraphMinor.GM06.Section5CoverDisc
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5LiftCover
import GraphMinor.GM06.Section5CoverLocalHomeomorph
import GraphMinor.GM06.Section5IndexedStripImage
import GraphMinor.GM06.Section5StripInjective
import GraphMinor.GM06.Section5InitialExtraEdgeStrip
import GraphMinor.GM06.Section5RegionInterior

/-!
# Open sheets over indexed cylinder strips

The side interpretation for VI (5.7), page 133, uses the closed
disc between consecutive linkage lifts. With at least two paths
its cylinder projection is injective. Invert this projection on
the open cylinder strip. The resulting section of the angular
cover has open image, exactly the disc with its linkage points
removed. Connectedness identifies it with the selected cover strip.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- For at least two paths, an indexed lifted strip is the corresponding
closed disc with all linkage points removed. -/
theorem cylinderCoverStrip_eq_indexed_disc_sheet_of_two_le
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ) (m : ℤ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L m)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (himage : radialCylinderProjection '' D = closure (cylinderStrip L (modIdx k hG.1 m))) :
    cylinderCoverStrip L m = (planeToCylinderCover '' D) ∩
      cylinderCoverProjection ⁻¹' (univ \ ⋃ j, (L.pathDrawing j).U) := by
  classical
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  let : CompactSpace D := isCompact_iff_compactSpace.mp hD.isCompact
  let S := cylinderStrip L (modIdx k hG.1 m)
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hfc : Continuous f := continuous_radialCylinderProjection.comp continuous_subtype_val
  have hfi : Function.Injective f := by
    intro p q hpq
    exact Subtype.ext (injOn_radialCylinderProjection_stripDisc L hG hk hθ m hD hBd hstrip
      p.2 q.2 hpq)
  have hfrange : range f = closure S := by
    rw [← himage]
    ext x
    simp only [f, mem_range, mem_image, Subtype.exists, exists_prop]
  let E : D ≃ₜ range f := (hfc.isClosedEmbedding hfi).isEmbedding.toHomeomorph
  let H : D ≃ₜ closure S := E.trans (Homeomorph.setCongr hfrange)
  have hH (p : D) : (H p).1 = f p := rfl
  let s : C(S, CylinderCover) :=
    ⟨fun x => planeToCylinderCover (H.symm ⟨x.1, subset_closure x.2⟩).1,
      continuous_planeToCylinderCover.comp (continuous_subtype_val.comp
        (H.symm.continuous.comp (continuous_subtype_val.subtype_mk _)))⟩
  have hproj (x : S) : cylinderCoverProjection (s x) = x.1 := by
    have hh := congrArg Subtype.val (H.apply_symm_apply ⟨x.1, subset_closure x.2⟩)
    rw [hH] at hh
    exact hh
  have hUclosed : IsClosed (⋃ j : Fin k, (L.pathDrawing j).U) :=
    isClosed_iUnion_of_finite fun j => (L.pathDrawing j).isClosed_U
  have hSo : IsOpen S := by
    change IsOpen (connectedComponentIn (univ \ ⋃ j : Fin k, (L.pathDrawing j).U) _)
    have hcomp : IsOpen (univ \ ⋃ j : Fin k, (L.pathDrawing j).U) := by
      simpa only [compl_eq_univ_sdiff] using hUclosed.isOpen_compl
    exact hcomp.connectedComponentIn
  have hsopen : IsOpenEmbedding s :=
    IsLocalHomeomorph.isOpenEmbedding_of_comp isLocalHomeomorph_cylinderCoverProjection
      (show IsOpenEmbedding (cylinderCoverProjection ∘ s) from
        (show cylinderCoverProjection ∘ s = Subtype.val from funext hproj).symm ▸
          hSo.isOpenEmbedding_subtypeVal) s.continuous
  let K := planeToCylinderCover '' D
  let I := K ∩ cylinderCoverProjection ⁻¹' (univ \ ⋃ j, (L.pathDrawing j).U)
  have hIrange : range s = I := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨⟨_, (H.symm ⟨x.1, subset_closure x.2⟩).2, rfl⟩, mem_univ _, ?_⟩
      rw [hproj]
      exact (connectedComponentIn_subset _ _ x.2).2
    · rintro ⟨⟨q, hq, rfl⟩, _, hoff⟩
      have hqS : radialCylinderProjection q ∈ S := by
        have hh := closure_cylinderStrip_subset_strip_union_linkage L hG (modIdx k hG.1 m)
          (himage ▸ mem_image_of_mem radialCylinderProjection hq)
        exact hh.resolve_right hoff
      let x : S := ⟨radialCylinderProjection q, hqS⟩
      refine ⟨x, ?_⟩
      have hHx : H ⟨q, hq⟩ = ⟨x.1, subset_closure x.2⟩ := Subtype.ext (hH ⟨q, hq⟩)
      change planeToCylinderCover (H.symm ⟨x.1, subset_closure x.2⟩).1 = _
      rw [← hHx, H.symm_apply_apply]
  have hIo : IsOpen I := hIrange ▸ hsopen.isOpen_range
  have hKc : IsClosed K := (hD.isCompact.image continuous_planeToCylinderCover).isClosed
  have hIR : I ⊆ cylinderCoverStrip L m := by
    rintro _ ⟨⟨q, hq, rfl⟩, _, hoff⟩
    apply mem_cylinderCoverStrip_of_mem_disc L hG hθ m hD hBd hstrip _ hoff
    change (max 1 (min 2 q.1), q.2) ∈ D
    rw [min_eq_right (hstrip hq).2, max_eq_right (hstrip hq).1]
    exact hq
  have hcover : cylinderCoverStrip L m ⊆ I ∪ Kᶜ := by
    intro p hp
    by_cases hpK : p ∈ K
    · exact Or.inl ⟨hpK, connectedComponentIn_subset _ _ hp⟩
    · exact Or.inr hpK
  have hchoice : cylinderCoverStrip L m ⊆ I ∨ cylinderCoverStrip L m ⊆ Kᶜ :=
    isPreconnected_connectedComponentIn.subset_or_subset hIo hKc.isOpen_compl
      (disjoint_compl_right.mono_left inter_subset_left) hcover
  have hIne : I.Nonempty := by
    obtain ⟨p, hp⟩ := hD.nonempty_discInt
    refine ⟨planeToCylinderCover p, ⟨p, hp.1, rfl⟩, mem_univ _, ?_⟩
    apply stripDiscInterior_projection_not_mem_linkage L hG hθ m hD hBd hstrip hp
    · change max 1 (min 2 p.1) = p.1
      rw [min_eq_right (hstrip hp.1).2, max_eq_right (hstrip hp.1).1]
    · rfl
  apply subset_antisymm _ hIR
  rcases hchoice with hh | hh
  · exact hh
  · obtain ⟨p, hp⟩ := hIne
    exact False.elim (hh (hIR hp) hp.1)

end GraphMinor.GM06
