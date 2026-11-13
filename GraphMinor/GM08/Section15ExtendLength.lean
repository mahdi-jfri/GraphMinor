module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15Menger
import GraphMinor.GM08.Section15RegionDistance
import GraphMinor.GM08.Section15EmptySides
import GraphMinor.GM08.Section15TrimArc
import GraphMinor.GM08.Section15CuffLength
import GraphMinor.GM07.CylinderCap
import GraphMinor.GM07.CylinderGrid

/-!
# Extending a short tube witness to the cylinder cuffs

Cap the cylinder by two discs. Extend a short normal witness through
the empty interiors on the two sides of the framing. Its vertex count
bounds the region distance between the caps. The normal line for that
distance joins the actual cuffs with no greater count. Shorten it to a
proper arc. This opens even an interior or touching framing in (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- A tube of length below `s` has a normal proper arc joining the
ambient cylinder cuffs and meeting fewer than `s` drawing vertices.
This supplies the disc cut for interior and touching framings in
Graph Minors VIII (15.4), page 282. -/
theorem Tube.exists_cuff_arc_of_length_lt {S : Type} [TopologicalSpace S]
    (τ : Tube S) {s : ℕ} (hs : τ.length < s) :
    ∃ (C D J : Set S) (u v : S), C ∈ cuffs S ∧ D ∈ cuffs S ∧ C ≠ D ∧
      IsLineWithEnds J u v ∧ u ∈ C ∧ v ∈ D ∧ J ∩ bd S = {u, v} ∧
      τ.Γ.IsNormal J ∧ (J ∩ τ.Γ.V).ncard < s := by
  classical
  have : T2Space S := τ.t2Space
  have : CompactSpace S := τ.isCylinder.compactSpace
  have : Nonempty S := τ.isCylinder.nonempty
  obtain ⟨I, u, v, hI, hu, hv, hNI, _, hIs⟩ := τ.length_lt_iff.mp hs
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have : T2Space cap.Z := cap.t2Space_Z
  have : ConnectedSpace cap.Z := cap.connectedSpace
  obtain ⟨G, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
  have hGU : G.U = cap.j '' τ.Γ.U := by simpa using hm.image_U.symm
  have hGV : G.V = cap.j '' τ.Γ.V := by simpa using hm.image_V.symm
  let E₁ := cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁
  let E₂ := cap.disc₂ τ.isCylinder.1 τ.isHoop_F₁
  let D₁ := cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂
  let D₂ := cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂
  obtain ⟨hE₁, _, hbE₁, _, _, hEcap, hcap₁, _⟩ :=
    cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₁
  obtain ⟨_, hD₂, _, hbD₂, _, hDcap, _, hcap₂⟩ :=
    cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₂
  have hGUsub : G.U ⊆ D₁ ∩ E₂ := by
    rw [hGU]
    rintro _ ⟨x, hx, rfl⟩
    have h := τ.U_subset hx
    rwa [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hle] at h
  have hEoff : Disjoint (discInt E₁) G.U := by
    refine disjoint_left.mpr ?_
    intro x hx hxG
    exact hx.2 (hbE₁.symm ▸ (hEcap ▸ ⟨hx.1, (hGUsub hxG).2⟩))
  have hDoff : Disjoint (discInt D₂) G.U := by
    refine disjoint_left.mpr ?_
    intro x hx hxG
    exact hx.2 (hbD₂.symm ▸ (hDcap ▸ ⟨(hGUsub hxG).1, hx.1⟩))
  have hNI' : G.IsNormal (cap.j '' I) := by
    rintro x ⟨⟨y, hy, rfl⟩, hxG⟩
    rw [hGU] at hxG
    obtain ⟨z, hz, heq⟩ := hxG
    have hyU : y ∈ τ.Γ.U := cap.inj heq ▸ hz
    rw [hGV]
    exact mem_image_of_mem cap.j (hNI ⟨hy, hyU⟩)
  have hju : cap.j u ∈ E₁ := Surface.discBd_subset _ (hbE₁ ▸ mem_image_of_mem _ hu)
  have hjv : cap.j v ∈ D₂ := Surface.discBd_subset _ (hbD₂ ▸ mem_image_of_mem _ hv)
  obtain ⟨A, hAc, hNA, _, hEA, hDA, hAV⟩ :=
    exists_normal_connector_with_empty_sides (GM07.image_line cap.isClosedEmbedding.isEmbedding hI)
      hE₁ hD₂ hju hjv hEoff hDoff hNI'
  have hAs : (A ∩ G.V).ncard < s := by
    rw [hAV, hGV, ← image_inter cap.inj, ncard_image_of_injective _ cap.inj]
    exact hIs
  obtain ⟨p, hp⟩ := cap.isClosedDisc_D₁.nonempty_discInt
  obtain ⟨q, hq⟩ := cap.isClosedDisc_D₂.nonempty_discInt
  have hpA : p ∈ A := hEA (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₁ hcap₁ hp)
  have hqA : q ∈ A := hDA (discInt_mono cap.isManifoldPoint_Z cap.isClosedDisc_D₂ hcap₂ hq)
  have hpU : p ∈ univ \ G.U := ⟨mem_univ _, fun hx =>
    disjoint_left.mp cap.disjoint_range_discInt_D₁
      (image_subset_range _ _ (hGU ▸ hx)) hp⟩
  have hqU : q ∈ univ \ G.U := ⟨mem_univ _, fun hx =>
    disjoint_left.mp cap.disjoint_range_discInt_D₂
      (image_subset_range _ _ (hGU ▸ hx)) hq⟩
  let r₀ := connectedComponentIn (univ \ G.U) p
  let r₂ := connectedComponentIn (univ \ G.U) q
  have hr₀ : r₀ ∈ G.R := ⟨p, hpU, rfl⟩
  have hr₂ : r₂ ∈ G.R := ⟨q, hqU, rfl⟩
  have hdist := mem_regLayer_of_normal_preconnected cap.isClosedSurface cap.isSphere hAc hNA
    hr₀ hr₂ hpA hqA (mem_connectedComponentIn hpU) (mem_connectedComponentIn hqU)
  obtain ⟨L, a, b, hL, ha, hb, hNL, hdis₁, hdis₂, hcount⟩ :=
    GM07.exists_cross_line cap.isClosedSurface cap.isClosedDisc_D₁ cap.isClosedDisc_D₂
      cap.disjoint_D hr₀ (mem_connectedComponentIn hpU) hp.1
      (mem_connectedComponentIn hqU) hq.1 hdist
  obtain ⟨a', ha', hea⟩ := cap.discBd_D₁.symm ▸ ha
  obtain ⟨b', hb', heb⟩ := cap.discBd_D₂.symm ▸ hb
  have hLrange : L ⊆ range cap.j := cap.subset_range_of_disjoint_discInts hdis₁ hdis₂
  have hline : IsLineWithEnds (cap.j ⁻¹' L) a' b' := by
    rw [← hea, ← heb] at hL
    exact GM07.pull_line cap.isClosedEmbedding.isEmbedding hL hLrange
  have hnorm : τ.Γ.IsNormal (cap.j ⁻¹' L) := by
    intro x hx
    have hjV := hNL ⟨hx.1, hGU.symm ▸ mem_image_of_mem cap.j hx.2⟩
    rw [hGV] at hjV
    obtain ⟨y, hy, heq⟩ := hjV
    exact cap.inj heq ▸ hy
  have hsmall : (cap.j ⁻¹' L ∩ τ.Γ.V).ncard < s := by
    have himg := image_preimage_inter cap.j τ.Γ.V L
    have hcard := ncard_image_of_injective (cap.j ⁻¹' L ∩ τ.Γ.V) cap.inj
    rw [himg, ← hGV] at hcard
    exact hcard.symm ▸ hcount.trans_lt hAs
  obtain ⟨J, a'', b'', hJL, ha'', hb'', hJ, hbd⟩ := exists_subarc_between_closed_sets hline
    (GM11.isCompact_of_isOArc ((cuff_statement S τ.isCylinder.1).2.2 _ cap.C₁_mem_cuffs)).isClosed
    (GM11.isCompact_of_isOArc ((cuff_statement S τ.isCylinder.1).2.2 _ cap.C₂_mem_cuffs)).isClosed
    cap.disjoint_cuffs ha' hb'
  refine ⟨cap.C₁, cap.C₂, J, a'', b'', cap.C₁_mem_cuffs, cap.C₂_mem_cuffs,
    cap.C₁_ne_C₂, hJ, ha'', hb'', ?_, ?_, ?_⟩
  · rwa [cap.bd_eq]
  · exact fun x hx => hnorm ⟨hJL hx.1, hx.2⟩
  · exact (ncard_le_ncard (inter_subset_inter_left _ hJL)
      (τ.Γ.finite_V.subset inter_subset_right)).trans_lt hsmall

end GraphMinor.GM08
