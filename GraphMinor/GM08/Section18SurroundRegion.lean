module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM08.Section18SurroundDisc
import GraphMinor.GM07.CuffFinger
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.LoopSides
import GraphMinor.GM07.Section3
import GraphMinor.GM07.Section5a
import GraphMinor.GM19.FeatureOrient
import GraphMinor.GM19.FragmentRegion
import GraphMinor.Surface.ArcDisc
import GraphMinor.Surface.Classification
import GraphMinor.Surface.Cuffs
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.Surface.ModelCriterion

/-!
# The region between a surrounding circle and its cuff

Let the circle `A` surround the cuff `C` and miss the boundary. Suppose a
connected surface `K` lies in `Σ` (by a one to one map), contains `C` in its
interior, and has its frontier inside `A`. Then `K` is a cylinder
(`nonempty_cylinder_of_surround_region`).

The reason: cap `C` with a disc `D`. Since `A` surrounds `C`, it bounds a closed
disc `Δ` of `Σ + Ĉ` around `D`. The interior of `K` is connected and misses
`A`, so it lies inside `Δ`, and thus `K ∪ D ⊆ Δ`. Conversely, the interior of
`Δ` is connected, and it splits into the open part of `K ∪ D` and the points off
`K ∪ D`. So `Δ = K ∪ D`. Thus `Δ` is `K` with the cuff `C` capped. A disc is
`Σ(0, 0, 1)`, so `K` is `Σ(0, 0, 2)`.

We use this in the cut of (18.2) for types (iv) and (v), page 286, to show that
a copy of `Σ` cannot lie between a schism circle and its cuff.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- The image of an open set `U` together with everything off the range is
open, for a one to one map of a compact space. -/
theorem isOpen_image_union_compl_range {S S' : Type w} [TopologicalSpace S]
    [TopologicalSpace S'] [CompactSpace S] [T2Space S'] {j : S → S'} (hj : Continuous j)
    (hinj : Function.Injective j) {U : Set S} (hU : IsOpen U) :
    IsOpen (j '' U ∪ (range j)ᶜ) := by
  have h : (j '' U ∪ (range j)ᶜ)ᶜ = j '' Uᶜ := by
    ext y
    constructor
    · intro hy
      simp only [mem_compl_iff, mem_union, not_or, not_not] at hy
      obtain ⟨⟨x, rfl⟩, hx⟩ := hy.2, hy.1
      exact ⟨x, fun hxU => hx ⟨x, hxU, rfl⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩ (⟨x', hx', he⟩ | hr)
      · exact hx (hinj he ▸ hx')
      · exact hr ⟨x, rfl⟩
  rw [← isClosed_compl_iff, h]
  exact (hU.isClosed_compl.isCompact.image hj).isClosed

/-- A closed disc inside a set `Δ` is a closed disc of the subspace `Δ`, with
the same boundary circle. -/
theorem isClosedDisc_subtype {S : Type w} [TopologicalSpace S] {Δ D : Set S} (hD : IsClosedDisc D)
    (hDΔ : D ⊆ Δ) :
    IsClosedDisc (Subtype.val ⁻¹' D : Set Δ) ∧
      discBd (Subtype.val ⁻¹' D : Set Δ) = Subtype.val ⁻¹' discBd D := by
  have himg : Subtype.val '' (Subtype.val ⁻¹' D : Set Δ) = D := by
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hDΔ]
  let e : (Subtype.val ⁻¹' D : Set Δ) ≃ₜ D :=
    (IsEmbedding.subtypeVal.homeomorphImage (Subtype.val ⁻¹' D : Set Δ)).trans
      (Homeomorph.setCongr himg)
  have he : ∀ y, (e y : S) = (y : Δ).1 := fun y => rfl
  obtain ⟨d⟩ := hD
  refine ⟨⟨d.trans e.symm⟩, ?_⟩
  apply (preimage_image_eq _ Subtype.val_injective).symm.trans
  congr 1
  unfold discBd
  rw [image_image, ← image_bd_homeomorph e, image_image]
  rfl

/-- **The region around a cuff inside a surrounding circle is a cylinder.** -/
theorem nonempty_cylinder_of_surround_region {S K : Type w} [TopologicalSpace S]
    [TopologicalSpace K] (hS : IsSurface S) {A C : Set S} (hA : IsOArc A)
    (hoff : Disjoint A (bd S)) (hsur : GM07.SurroundsCuff A C) (hK : IsSurface K)
    [ConnectedSpace K] {φ : K → S} (hφ : Continuous φ) (hinj : Function.Injective φ)
    (hbdK : bd K = φ ⁻¹' (A ∪ bd S)) (hCint : C ⊆ interior (range φ))
    (hfr : frontier (range φ) ⊆ A) : Nonempty (K ≃ₜ SurfaceModel 0 0 2) := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have : CompactSpace K := hK.1
  have : T2Space K := hK.2.1
  have hC : C ∈ cuffs S := hsur.1
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hCA : Disjoint C A := disjoint_left.mpr fun x hx hxA =>
    disjoint_left.mp hoff hxA (hCbd hx)
  obtain ⟨S', tS', j, D, hcap, -⟩ := GM07.exists_cappedCuff hS hC
  let := tS'
  have hS' := hcap.isSurface
  have : T2Space S' := hS'.2.1
  have hman := hS'.2.2
  have hj := hcap.isEmbedding
  obtain ⟨Δ, hΔ, hbΔ, hDΔ⟩ := exists_surrounding_disc hS hA hsur hcap
  set R : Set S := range φ with hRdef
  have hRc : IsCompact R := isCompact_range hφ
  have hfrΔ : frontier Δ ⊆ j '' A := hbΔ ▸ GM07.frontier_disc_subset hman hΔ
  have hDc : IsClosed D := hcap.isClosedDisc.isClosed
  -- the points of `j '' C` lie in the interior of `Δ`
  have hjC : ∀ c ∈ C, j c ∈ discInt Δ := by
    intro c hc
    refine ⟨hDΔ ?_, ?_⟩
    · have : j c ∈ discBd D := hcap.discBd_eq ▸ mem_image_of_mem j hc
      exact discBd_subset D this
    · rw [hbΔ]
      rintro ⟨a, ha, he⟩
      exact disjoint_left.mp hCA (hj.injective he ▸ hc) ha
  obtain ⟨c₀, hc₀⟩ : C.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact ⟨x, mem_connectedComponentIn hx⟩
  -- `j '' R ⊆ Δ`
  have hsub : j '' R ⊆ Δ := by
    set Z : Set S' := j '' (φ '' (bd K)ᶜ) with hZ
    have hZp : IsPreconnected Z :=
      ((GM19.isPreconnected_compl_bd hK).image _ hφ.continuousOn).image _ hj.continuous.continuousOn
    have hZf : Disjoint Z (frontier Δ) := by
      rw [disjoint_left]
      rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩ hf
      obtain ⟨a, ha, he⟩ := hfrΔ hf
      apply hk
      rw [hbdK]
      exact Or.inl (hj.injective he ▸ ha)
    have hRZ : j '' R ⊆ closure Z := by
      rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
      have hdense : Dense (bd K)ᶜ := by
        obtain ⟨a, b, c, ⟨eK⟩⟩ := classification K hK inferInstance
        have hM := (modelCriterion.1 a b c).1
        have : T2Space (SurfaceModel a b c) := hM.2.1
        have hd := GM19.dense_interior' hM
        have h1 := eK.symm.surjective.denseRange.dense_image eK.symm.continuous hd
        rwa [image_compl_eq eK.symm.bijective, image_bd_homeomorph] at h1
      have hk : k ∈ closure (bd K)ᶜ := hdense.closure_eq ▸ mem_univ k
      have h1 : φ k ∈ closure (φ '' (bd K)ᶜ) := image_closure_subset_closure_image hφ ⟨k, hk, rfl⟩
      exact image_closure_subset_closure_image hj.continuous ⟨φ k, h1, rfl⟩
    rcases GM07.inside_or_off hZp hΔ.isClosed hZf with hin | hout
    · exact hRZ.trans (closure_minimal (hin.trans interior_subset) hΔ.isClosed)
    · exfalso
      have h1 : j c₀ ∈ closure Δᶜ :=
        closure_mono hout (hRZ ⟨c₀, (interior_subset (hCint hc₀)), rfl⟩)
      have hint : j c₀ ∈ interior Δ := by
        by_contra hni
        have hfr' : j c₀ ∈ frontier Δ :=
          ⟨subset_closure (hjC c₀ hc₀).1, hni⟩
        exact (hjC c₀ hc₀).2 (hbΔ ▸ hfrΔ hfr')
      have h2 : interior Δ ∩ Δᶜ = ∅ := by
        ext y
        simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and,
          not_not]
        exact fun hy => interior_subset hy
      exact (mem_closure_iff.mp h1 _ isOpen_interior hint).ne_empty h2
  -- `Δ ⊆ j '' R ∪ D`
  have hsup : Δ ⊆ j '' R ∪ D := by
    set V : Set S' := j '' interior R ∪ (range j)ᶜ with hV
    have hVo : IsOpen V :=
      isOpen_image_union_compl_range hj.continuous hj.injective isOpen_interior
    have hO₂ : IsOpen (j '' R ∪ D)ᶜ :=
      ((hRc.image hj.continuous).isClosed.union hDc).isOpen_compl
    have hVsub : V ⊆ j '' R ∪ D := by
      rintro y (⟨x, hx, rfl⟩ | hy)
      · exact Or.inl ⟨x, interior_subset hx, rfl⟩
      · have : y ∈ range j ∪ D := hcap.union_eq ▸ mem_univ y
        exact Or.inr (this.resolve_left hy)
    have hcov : discInt Δ ⊆ V ∪ (j '' R ∪ D)ᶜ := by
      intro y hy
      by_cases hyRD : y ∈ j '' R ∪ D
      · left
        by_cases hyr : y ∈ range j
        · obtain ⟨s, rfl⟩ := hyr
          by_cases hs : s ∈ interior R
          · exact Or.inl ⟨s, hs, rfl⟩
          · exfalso
            rcases hyRD with ⟨s', hs', he⟩ | hD
            · have hsR : s ∈ R := hj.injective he ▸ hs'
              have hfs : s ∈ frontier R := ⟨subset_closure hsR, hs⟩
              apply hy.2
              rw [hbΔ]
              exact mem_image_of_mem j (hfr hfs)
            · have : j s ∈ j '' C := hcap.inter_eq ▸ ⟨mem_range_self s, hD⟩
              obtain ⟨c, hc, he⟩ := this
              exact hs (hj.injective he ▸ hCint hc)
        · exact Or.inr hyr
      · exact Or.inr hyRD
    have hne : (discInt Δ ∩ V).Nonempty :=
      ⟨j c₀, hjC c₀ hc₀, Or.inl ⟨c₀, hCint hc₀, rfl⟩⟩
    have hdisj : Disjoint V (j '' R ∪ D)ᶜ := disjoint_left.mpr fun y hy hy' => hy' (hVsub hy)
    have hin := hΔ.isPreconnected_discInt.subset_left_of_subset_union hVo hO₂ hdisj hcov hne
    calc Δ ⊆ closure (discInt Δ) := hΔ.subset_closure_discInt
      _ ⊆ j '' R ∪ D := closure_minimal (hin.trans hVsub)
          ((hRc.image hj.continuous).isClosed.union hDc)
  -- the capped surface `K + Ĉ` is `Δ`
  have hφemb : IsEmbedding φ := (hφ.isClosedEmbedding hinj).isEmbedding
  have hjφ : IsEmbedding (j ∘ φ) := hj.comp hφemb
  have hmemΔ : ∀ k, (j ∘ φ) k ∈ Δ := fun k => hsub ⟨φ k, mem_range_self k, rfl⟩
  let j' : K → Δ := Set.codRestrict (j ∘ φ) Δ hmemΔ
  have hj' : IsEmbedding j' := hjφ.codRestrict Δ hmemΔ
  let CK : Set K := φ ⁻¹' C
  have hCR : C ⊆ R := fun c hc => interior_subset (hCint hc)
  have hCK : IsOArc CK := by
    obtain ⟨eC⟩ := (cuff_statement S hS).2.2 C hC
    have himg : φ '' CK = C := image_preimage_eq_of_subset hCR
    exact ⟨eC.trans ((hφemb.homeomorphImage CK).trans (Homeomorph.setCongr himg)).symm⟩
  have hCKbd : CK ⊆ bd K := fun k hk => hbdK ▸ Or.inr (hCbd hk)
  have hCKc : CK ∈ cuffs K := GM07.isCuff_of_isOArc_subset_bd hK hCK hCKbd
  obtain ⟨hD', hbD'⟩ := isClosedDisc_subtype hcap.isClosedDisc hDΔ
  obtain ⟨dΔ⟩ := hΔ
  obtain ⟨d01⟩ := nonempty_disc_homeo
  have hSΔ : IsSurface Δ :=
    GM07.isSurface_of_homeo (d01.trans dΔ) ((modelCriterion.1 0 0 1).1)
  have hcapK : GM07.IsCappedCuff CK Δ j' (Subtype.val ⁻¹' D) := by
    refine ⟨hCKc, hSΔ, hj', hD', ?_, ?_, ?_⟩
    · rw [hbD', hcap.discBd_eq]
      ext y
      constructor
      · rintro ⟨c, hc, he⟩
        obtain ⟨k, rfl⟩ := hCR hc
        exact ⟨k, hc, Subtype.ext he⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨φ k, hk, rfl⟩
    · ext y
      simp only [mem_union, mem_range, mem_preimage, mem_univ, iff_true]
      rcases hsup y.2 with ⟨s, ⟨k, rfl⟩, he⟩ | hD
      · exact Or.inl ⟨k, Subtype.ext he⟩
      · exact Or.inr hD
    · ext y
      constructor
      · rintro ⟨⟨k, rfl⟩, hD⟩
        have : j (φ k) ∈ j '' C := hcap.inter_eq ▸ ⟨mem_range_self _, hD⟩
        obtain ⟨c, hc, he⟩ := this
        exact ⟨k, show φ k ∈ C from hj.injective he ▸ hc, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        refine ⟨mem_range_self k, ?_⟩
        have : j (φ k) ∈ discBd D := hcap.discBd_eq ▸ mem_image_of_mem j hk
        exact discBd_subset D this
  obtain ⟨a, b, c, ⟨eK⟩⟩ := classification K hK inferInstance
  obtain ⟨-, ⟨eΔ⟩⟩ := GM07.cappedCuff_homeo_model hK ⟨eK⟩ hCKc hcapK
  obtain ⟨hc1, hab, -⟩ :=
    ((modelCriterion.2 a b (c - 1) 0 0 1).mp ⟨eΔ.symm.trans (d01.trans dΔ).symm⟩)
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  have hc2 : c = 2 := by
    obtain ⟨-, ⟨-⟩⟩ := GM07.cappedCuff_homeo_model hK ⟨eK⟩ hCKc hcapK
    have h1 := (GM07.cappedCuff_homeo_model hK ⟨eK⟩ hCKc hcapK).1
    omega
  subst ha hb hc2
  exact ⟨eK⟩

end GraphMinor.GM08
