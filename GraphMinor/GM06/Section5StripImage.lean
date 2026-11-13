module

public import GraphMinor.GM06.Section5StripProjection
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM07.Section11f
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.DiscUnion

/-!
# The projected strip disc fills the strip closure

For VI (5.1), page 129, the disc between consecutive lifted paths
projects onto the closure of Σᵢ. Its interior image is open. Its
boundary projects onto linkage paths and cuffs, so, away from those
sets, its closed image equals its interior image. The part of Σᵢ
off the cuffs is connected. It therefore lies wholly in that image.
Density of points off the cuffs gives the full closure.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- Angular projection sends an indexed linkage lift back to the
path with the corresponding residue index. -/
theorem radialCylinderProjection_liftedLinkageCurve
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (n : ℤ) (t : unitInterval) :
    radialCylinderProjection (liftedLinkageCurve hk L n t) = L.curve (modIdx k hk n) t := by
  have hn := liftedLinkageCurve_props_raw hk L n
  apply Subtype.ext
  apply Prod.ext
  · rw [radialCylinderProjection_fst (hn.1 t), liftedLinkageCurve_fst]
  · exact hn.2.2.2.2.2 t

/-- The boundary of a lifted strip disc projects only onto linkage
paths or cylinder cuffs. -/
theorem image_liftedStripBoundary_subset_linkage_union_boundary
    {k : ℕ} {G : Drawing ClosedCylinder} (hk : 0 < k)
    (L : CylinderLinkage k G) (m : ℤ) :
    radialCylinderProjection '' liftedStripBoundary hk L m ⊆
      (⋃ i, (L.pathDrawing i).U) ∪ bd ClosedCylinder := by
  rintro x ⟨p, hp, rfl⟩
  rcases hp with ((hp | hp) | hp) | hp
  · obtain ⟨t, rfl⟩ := hp
    apply Or.inl
    rw [radialCylinderProjection_liftedLinkageCurve]
    exact mem_iUnion.mpr ⟨_, (L.curve_parametrizes _).2.1 ▸ mem_range_self t⟩
  · obtain ⟨t, rfl⟩ := hp
    apply Or.inl
    rw [radialCylinderProjection_liftedLinkageCurve]
    exact mem_iUnion.mpr ⟨_, (L.curve_parametrizes _).2.1 ▸ mem_range_self t⟩
  · apply Or.inr
    rw [bd_closedCylinder]
    apply Or.inl
    change max 1 (min 2 p.1) = 1
    rw [mem_singleton_iff.mp hp.1]
    norm_num
  · apply Or.inr
    rw [bd_closedCylinder]
    apply Or.inr
    change max 1 (min 2 p.1) = 2
    rw [mem_singleton_iff.mp hp.1]
    norm_num

/-- The compact image of the lifted strip disc is exactly the
closure of the cylinder strip it bounds. -/
theorem image_stripDisc_eq_closure_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hθ : L.HasTheta θ) (i : Fin k)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L ((i.val : ℤ) + 1))
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    radialCylinderProjection '' D = closure (cylinderStrip L i) := by
  let H := radialCylinderProjection '' D
  let U := radialCylinderProjection '' discInt D
  let S := cylinderStrip L i \ bd ClosedCylinder
  have hH : IsClosed H := (hD.isCompact.image continuous_radialCylinderProjection).isClosed
  have hU : IsOpen U := isOpen_image_radialCylinderProjection
    (hD.isOpen_discInt (fun p => by
      let e : ℂ ≃ₜ ℝ × ℝ := Complex.equivRealProdCLM.toHomeomorph
      have hh := isManifoldPoint_of_isOpenEmbedding e.isOpenEmbedding
        (isManifoldPoint_complex (e.symm p))
      simpa only [e.apply_symm_apply] using hh))
    (discInt_subset_open_radial_strip hD hstrip)
  have hUS : U ⊆ S := by
    rintro x ⟨p, hp, rfl⟩
    refine ⟨stripDiscInterior_projection_mem_strip L hG hθ i hD hBd hstrip hp
      (radialCylinderProjection_fst (hstrip hp.1)) rfl, ?_⟩
    intro hbd
    rw [bd_closedCylinder] at hbd
    have hrad := discInt_subset_open_radial_strip hD hstrip hp
    change 1 < p.1 ∧ p.1 < 2 at hrad
    rw [← radialCylinderProjection_fst (hstrip hp.1)] at hrad
    rcases hbd with h1 | h2
    · exact (ne_of_gt hrad.1) h1
    · exact (ne_of_lt hrad.2) h2
  have hUH : U ⊆ H := image_mono (discInt_subset D)
  have hSHU : S ∩ H ⊆ U := by
    rintro x ⟨hx, p, hp, rfl⟩
    refine ⟨p, ⟨hp, ?_⟩, rfl⟩
    intro hpb
    have hb := image_liftedStripBoundary_subset_linkage_union_boundary hG.1 L
      ((i.val : ℤ) + 1) ⟨p, hBd ▸ hpb, rfl⟩
    rcases hb with hlink | hbd
    · exact (connectedComponentIn_subset _ _ hx.1).2 hlink
    · exact hx.2 hbd
  have hpaths : IsClosed (⋃ j, (L.pathDrawing j).U) := by
    apply isClosed_iUnion_of_finite
    intro j
    rw [← (L.curve_parametrizes j).2.1]
    exact (isCompact_range (L.curve j).continuous).isClosed
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  have hstripOpen : IsOpen (cylinderStrip L i) :=
    (isOpen_univ.sdiff hpaths).connectedComponentIn
  have hS : IsPreconnected S := GM07.isPreconnected_diff_bd isSurface_closedCylinder
    hstripOpen isPreconnected_connectedComponentIn
  have hcover : S ⊆ U ∪ Hᶜ := by
    intro x hx
    by_cases hxh : x ∈ H
    · exact Or.inl (hSHU ⟨hx, hxh⟩)
    · exact Or.inr hxh
  have hdis : Disjoint U Hᶜ := disjoint_left.mpr (fun _ hu hc => hc (hUH hu))
  have hSinH : S ⊆ H := by
    rcases hS.subset_or_subset hU hH.isOpen_compl hdis hcover with hin | hout
    · exact hin.trans hUH
    · obtain ⟨p, hp⟩ := hD.nonempty_discInt
      have hu : radialCylinderProjection p ∈ U := ⟨p, hp, rfl⟩
      exact False.elim (hout (hUS hu) (hUH hu))
  apply Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact stripDisc_projection_mem_closure_strip L hG hθ i hD hBd hstrip hp
      (radialCylinderProjection_fst (hstrip hp)) rfl
  · rw [← closure_sdiff_boundary_of_isOpen isSurface_closedCylinder hstripOpen]
    exact closure_minimal hSinH hH

end GraphMinor.GM06
