module

public import GraphMinor.GM08.Section18CutCount
import GraphMinor.GM08.Section18PinchedCut
import GraphMinor.GM08.Section18X2Tools
import GraphMinor.GM08.Section18X2Disc
import GraphMinor.GM08.Section18SurroundSides
import GraphMinor.GM08.Section18X3Cut
import GraphMinor.GM08.Section18CutSum
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM08.Section18Theorem182
import GraphMinor.GM08.Section18Invariance
import GraphMinor.GM08.Section6
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.Surface.CutIArc

/-!
# The cut along two circles that meet at one point

This proves `X2CutCountStatement`. Let `A₁, A₂` be circles that meet only at
`u`, miss the boundary, and surround different cuffs `C₁, C₂`.

1. Cut along `A₁` (`exists_surround_sides`). One side `W` is a cylinder around
   `C₁`. The far side `V = Wᶜ` holds the lift of `A₂ \ {u}`, since `A₂` is not
   planar in `Σ + Ĉ₁` (`preimage_subset_compl_of_planar`). In `V` the lift of
   `A₂` is a circle that meets the boundary only at the lift `p` of `u`.
2. Cut `V` along this circle (`exists_pinched_cut`), and keep `W`
   (`isCutMap_sum_compl`).

Each point of `A₁ ∪ A₂` other than `u` has two lifts, and `u` has four. The
measure drops: `W` is a cylinder, and the pinched cut either lowers the measure
of `V`, which is at most `g(Σ)`, or splits `V` into a disc and a piece that is
a cylinder (`nonempty_cylinder_of_x2_disc`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- A cut map has one point over each point off the cut set. -/
theorem ncard_preimage_eq_one_of_isCutMap {X Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} {F : Set Y} (hf : GM19.IsCutMap f F) {x : Y} (hx : x ∉ F) :
    (f ⁻¹' {x}).ncard = 1 := by
  obtain ⟨y, rfl⟩ := hf.2.1 x
  refine ncard_eq_one.mpr ⟨y, ?_⟩
  ext z
  simp only [mem_preimage, mem_singleton_iff]
  exact ⟨fun hz => hf.2.2.1 (show f z ∉ F by rw [hz]; exact hx) hx hz, fun h => h ▸ rfl⟩

/-- A compact set that a continuous map sends one to one onto a circle is a
circle. -/
theorem isOArc_of_injOn_image {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {f : X → Y} (hf : Continuous f) {Z : Set X} (hZ : IsCompact Z) (hinj : InjOn f Z)
    {A : Set Y} (hA : IsOArc A) (himg : f '' Z = A) : IsOArc Z := by
  have : CompactSpace Z := isCompact_iff_compactSpace.mp hZ
  let g : Z → Y := fun x => f x.1
  have hg : Continuous g := hf.comp continuous_subtype_val
  have hgi : Function.Injective g := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hrange : range g = A := by
    rw [← himg]
    ext y
    exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, h⟩ => ⟨⟨x, hx⟩, h⟩⟩
  obtain ⟨e⟩ := hA
  exact ⟨e.trans ((hg.isClosedEmbedding hgi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)).symm⟩

variable {S : Type w} [TopologicalSpace S]

/-- **(18.2) with lift counts for two circles that meet at one point.** -/
theorem hasCountedCut_X2 [ConnectedSpace S] (hS : IsSurface S)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (h3 : 3 ≤ surfaceComplexity S)
    {A₁ A₂ C₁ C₂ : Set S} {u : S} (hA₁ : IsOArc A₁) (hA₂ : IsOArc A₂) (h12 : A₁ ∩ A₂ = {u})
    (hoff : Disjoint (A₁ ∪ A₂) (bd S)) (hsur₁ : GM07.SurroundsCuff A₁ C₁)
    (hsur₂ : GM07.SurroundsCuff A₂ C₂) (hC : C₁ ≠ C₂) : HasCountedCut S (A₁ ∪ A₂) := by
  classical
  have : T2Space S := hS.2.1
  have hoff₁ : Disjoint A₁ (bd S) := hoff.mono_left subset_union_left
  have hoff₂ : Disjoint A₂ (bd S) := hoff.mono_left subset_union_right
  have huu : u ∈ A₁ ∩ A₂ := by rw [h12]; rfl
  have hA₁c : IsClosed A₁ := hA₁.isCompact.isClosed
  have hA₂c : IsClosed A₂ := hA₂.isCompact.isClosed
  have hFc : IsClosed (A₁ ∪ A₂) := hA₁c.union hA₂c
  have hmeet : ∀ x ∈ A₁, x ∈ A₂ → x = u := fun x h1 h2 => by
    have h : x ∈ A₁ ∩ A₂ := ⟨h1, h2⟩
    rw [h12] at h
    exact h
  -- step 1: the cut along `A₁`
  obtain ⟨T₁, t₁, ψ₁, W, hT₁, hcut₁, hs, hgR⟩ := exists_surround_sides hS hncyl h3 hA₁ hoff₁ hsur₁
  let := t₁
  have : CompactSpace T₁ := hT₁.1
  have : T2Space T₁ := hT₁.2.1
  have hbd₁ : ψ₁ ⁻¹' (bd S ∪ A₁) = bd T₁ :=
    (isCutAlongSet_of_isCutting hS hT₁ hA₁c hcut₁).preimage_bd
  set V : Set T₁ := Wᶜ with hVdef
  have hVo : IsClopen V := hs.isClopen.compl
  have : ConnectedSpace V := hs.connected_compl
  have hVs : IsSurface V := isSurface_sub hT₁ hVo
  have hinjV : InjOn ψ₁ V := hs.injOn_compl
  have hfar : ψ₁ ⁻¹' (A₂ \ {u}) ⊆ V :=
    preimage_subset_compl_of_planar hS hT₁ hncyl hcut₁ hs hsur₁.1 hA₂ hsur₂ hC
      (isPreconnected_oArc_sdiff_singleton hA₂ u)
      (disjoint_left.mpr fun z hz hzA => hz.2 (hmeet z hzA hz.1))
      (fun z hz => by
        by_cases hzu : z = u
        · exact Or.inl (hzu ▸ huu.1)
        · exact Or.inr (subset_closure ⟨hz, hzu⟩))
  -- the lift `p₀` of `u` in `V`
  obtain ⟨-, Y₁, -, -, hY₁V, -, hbY₁⟩ := hs.lifts
  obtain ⟨p₀, hp₀Y, hp₀⟩ := hbY₁.surjOn huu.1
  have hp₀V : p₀ ∈ V := hY₁V hp₀Y
  -- the lift of `A₂` in `V` is a circle that meets the boundary only at `p₀`
  set Z₀ : Set T₁ := V ∩ ψ₁ ⁻¹' A₂ with hZ₀def
  have hZ₀c : IsClosed Z₀ := hVo.isClosed.inter (hA₂c.preimage hcut₁.1)
  have hZ₀img : ψ₁ '' Z₀ = A₂ := by
    apply subset_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hz.2
    · intro z hz
      by_cases hzu : z = u
      · refine ⟨p₀, ⟨hp₀V, ?_⟩, hp₀.trans hzu.symm⟩
        change ψ₁ p₀ ∈ A₂
        rw [hp₀]
        exact huu.2
      · obtain ⟨t, rfl⟩ := hcut₁.2.1 z
        exact ⟨t, ⟨hfar ⟨hz, hzu⟩, hz⟩, rfl⟩
  have hZ₀ : IsOArc Z₀ := isOArc_of_injOn_image hcut₁.1 hZ₀c.isCompact
    (hinjV.mono inter_subset_left) hA₂ hZ₀img
  have hZs : IsOArc ((Subtype.val : V → T₁) ⁻¹' Z₀) :=
    GM12.isOArc_subtype_preimage inter_subset_left hZ₀
  have hZsp : (Subtype.val : V → T₁) ⁻¹' Z₀ ∩ bd V = {⟨p₀, hp₀V⟩} := by
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_bd_sub hVo.isOpen]
    constructor
    · rintro ⟨hzZ, hzb⟩
      have hzb' : z.1 ∈ ψ₁ ⁻¹' (bd S ∪ A₁) := by rw [hbd₁]; exact hzb
      rcases hzb' with h | h
      · exact absurd h (disjoint_left.mp hoff₂ hzZ.2)
      · exact Subtype.ext (hinjV z.2 hp₀V ((hmeet _ h hzZ.2).trans hp₀.symm))
    · rintro rfl
      refine ⟨⟨hp₀V, ?_⟩, hcut₁.2.2.2.2 ?_⟩
      · change ψ₁ p₀ ∈ A₂
        rw [hp₀]
        exact huu.2
      · change ψ₁ p₀ ∈ A₁
        rw [hp₀]
        exact huu.1
  -- step 2: the pinched cut of `V`, next to `W`
  obtain ⟨Y, tY, ρ, hY, hρ, hρp, hρ2, hcase⟩ := exists_pinched_cut hVs hZs hZsp
  let := tY
  set ξ : Y ⊕ (Vᶜ : Set T₁) → T₁ := Sum.elim (Subtype.val ∘ ρ) Subtype.val with hξdef
  have hξ : GM19.IsCutMap ξ Z₀ := isCutMap_sum_compl inter_subset_left hρ
  have hWs : IsSurface (Vᶜ : Set T₁) := isSurface_sub hT₁ hVo.compl
  have hTf : IsSurface (Y ⊕ (Vᶜ : Set T₁)) := GM07.isSurface_sum hY hWs
  have : CompactSpace (Y ⊕ (Vᶜ : Set T₁)) := hTf.1
  have hcovA₂ : ψ₁ ⁻¹' A₂ ⊆ Z₀ ∪ bd T₁ := by
    intro t ht
    by_cases htV : t ∈ V
    · exact Or.inl ⟨htV, ht⟩
    · right
      have htu : ψ₁ t = u := by
        by_contra h
        exact htV (hfar ⟨ht, h⟩)
      exact hcut₁.2.2.2.2 (show ψ₁ t ∈ A₁ by rw [htu]; exact huu.1)
  have hθ : GM19.IsCutMap (ψ₁ ∘ ξ) (A₁ ∪ A₂) :=
    IsCutMap.comp (GM19.IsCutting.isCutMap hcut₁) hξ hZ₀c (fun z hz => hz.2) hcovA₂
  have hcutF : GM07.IsCutAlongSet (A₁ ∪ A₂) (ψ₁ ∘ ξ) := isCutAlongSet_of_cutMap hS hTf hFc hθ
  -- the number of lifts
  have hξZ : ∀ t ∈ Z₀, t ≠ p₀ → (ξ ⁻¹' {t}).ncard = 2 := fun t ht htp => by
    rw [hξdef, ncard_preimage_sum_compl ht.1]
    exact hρ2 ⟨t, ht.1⟩ ht fun h => htp (congrArg Subtype.val h)
  have hξp : (ξ ⁻¹' {p₀}).ncard = 3 := by
    rw [hξdef, ncard_preimage_sum_compl hp₀V]
    exact hρp
  have hξ1 : ∀ t ∉ Z₀, (ξ ⁻¹' {t}).ncard = 1 := fun t ht => by
    by_cases htV : t ∈ V
    · rw [hξdef, ncard_preimage_sum_compl htV]
      exact ncard_preimage_eq_one_of_isCutMap hρ ht
    · exact ncard_preimage_sum_compl_of_notMem htV
  have hfib : ∀ x ∈ A₁ ∪ A₂, 2 ≤ ((ψ₁ ∘ ξ) ⁻¹' {x}).ncard ∧
      ((ψ₁ ∘ ξ) ⁻¹' {x}).ncard ≤ 2 + if x = u then 2 else 0 := by
    intro x hx
    change 2 ≤ (ξ ⁻¹' (ψ₁ ⁻¹' {x})).ncard ∧ (ξ ⁻¹' (ψ₁ ⁻¹' {x})).ncard ≤ _
    by_cases hxA₁ : x ∈ A₁
    · obtain ⟨s, t, hst, hpair⟩ := ncard_eq_two.mp (hcut₁.2.2.2.1 x hxA₁)
      have hs' : ψ₁ s = x := (show s ∈ ψ₁ ⁻¹' {x} from hpair ▸ Or.inl rfl)
      have ht' : ψ₁ t = x := (show t ∈ ψ₁ ⁻¹' {x} from hpair ▸ Or.inr rfl)
      have hun : ξ ⁻¹' {s, t} = ξ ⁻¹' {s} ∪ ξ ⁻¹' {t} := by
        rw [← preimage_union]
        rfl
      rw [hpair, hun]
      have hfin := (hξ.2.2.2.1 s).union (hξ.2.2.2.1 t)
      refine ⟨?_, (ncard_union_le _ _).trans ?_⟩
      · obtain ⟨ys, hys⟩ := hξ.2.1 s
        obtain ⟨yt, hyt⟩ := hξ.2.1 t
        have hne : ys ≠ yt := fun h => hst (hys ▸ hyt ▸ congrArg ξ h)
        calc 2 = ({ys, yt} : Set _).ncard := (ncard_pair hne).symm
          _ ≤ _ := ncard_le_ncard (by
              rintro y (rfl | rfl)
              exacts [Or.inl hys, Or.inr hyt]) hfin
      · have hb : ∀ r, ψ₁ r = x → (ξ ⁻¹' {r}).ncard ≤ if r = p₀ then 3 else 1 := by
          intro r hr
          split_ifs with hrp
          · rw [hrp, hξp]
          · have hrZ : r ∉ Z₀ := by
              rintro ⟨hrV, hrA⟩
              exact hrp (hinjV hrV hp₀V (hr.trans
                ((hmeet x hxA₁ (hr ▸ hrA)).trans hp₀.symm)))
            rw [hξ1 r hrZ]
        have h1 := hb s hs'
        have h2 := hb t ht'
        by_cases hsp : s = p₀
        · have htp : t ≠ p₀ := fun h => hst (hsp.trans h.symm)
          have hxu : x = u := hs' ▸ hsp ▸ hp₀
          simp only [hsp, htp, hxu, ↓reduceIte] at h1 h2 ⊢
          omega
        · by_cases htp : t = p₀
          · have hxu : x = u := ht' ▸ htp ▸ hp₀
            simp only [hsp, htp, hxu, ↓reduceIte] at h1 h2 ⊢
            omega
          · simp only [hsp, htp, ↓reduceIte] at h1 h2
            split_ifs <;> omega
    · have hxA₂ : x ∈ A₂ := hx.resolve_left hxA₁
      have hxu : x ≠ u := fun h => hxA₁ (h ▸ huu.1)
      obtain ⟨t, ht⟩ := ncard_eq_one.mp
        (ncard_preimage_eq_one_of_isCutMap (GM19.IsCutting.isCutMap hcut₁) hxA₁)
      have ht' : ψ₁ t = x := (show t ∈ ψ₁ ⁻¹' {x} from ht ▸ rfl)
      have htA : ψ₁ t ∈ A₂ := by rw [ht']; exact hxA₂
      have htu : ψ₁ t ≠ u := by rw [ht']; exact hxu
      have htZ : t ∈ Z₀ := ⟨hfar ⟨htA, htu⟩, htA⟩
      have htp : t ≠ p₀ := fun h => hxu (ht' ▸ h ▸ hp₀)
      rw [ht, hξZ t htZ htp]
      simp only [hxu, ↓reduceIte]
      omega
  -- the measure of the cylinder side
  have hg2 : surfaceComplexity (Vᶜ : Set T₁) = 2 := by
    obtain ⟨e⟩ := hs.cylinder
    have e' : (Vᶜ : Set T₁) ≃ₜ SurfaceModel 0 0 2 :=
      (Homeomorph.setCongr (compl_compl W)).trans e
    have := (modelCriterion.1 0 0 2).2
    rw [surfaceComplexity_congr e', surfaceComplexity_eq_connected,
      connectedSurfaceComplexity_eq ⟨Homeomorph.refl _⟩]
  have hgY : surfaceComplexity Y < surfaceComplexity S := by
    rcases hcase with hlt | ⟨D, hD, hDdisc, hDc, hDu, hDcu, -⟩
    · exact lt_of_lt_of_le hlt hgR
    · -- the disc case: the pieces `W`, `D` and `K = Dᶜ` of the cut surface
      have hWVc : ∀ w : (Vᶜ : Set T₁), w.1 ∈ W := fun w => by simpa [hVdef] using w.2
      have hDcon : ConnectedSpace D := by
        obtain ⟨e⟩ := hDdisc
        obtain ⟨e₀⟩ := nonempty_disc_homeo
        have := (modelCriterion.1 0 0 1).2
        exact (e₀.trans e).surjective.connectedSpace (e₀.trans e).continuous
      have hWcon : ConnectedSpace (Vᶜ : Set T₁) := by
        obtain ⟨e⟩ := hs.cylinder
        have := (modelCriterion.1 0 0 2).2
        let e' : (Vᶜ : Set T₁) ≃ₜ SurfaceModel 0 0 2 :=
          (Homeomorph.setCongr (compl_compl W)).trans e
        exact e'.symm.surjective.connectedSpace e'.symm.continuous
      have hclopen_inl : ∀ P : Set Y, IsClopen P →
          IsClopen (Sum.inl '' P : Set (Y ⊕ (Vᶜ : Set T₁))) :=
        fun P hP => ⟨isClosedMap_inl _ hP.isClosed, isOpenMap_inl _ hP.isOpen⟩
      have hconn_inl : ∀ P : Set Y, ConnectedSpace P →
          ConnectedSpace (Sum.inl '' P : Set (Y ⊕ (Vᶜ : Set T₁))) := fun P hP =>
        isConnected_iff_connectedSpace.mp
          ((isConnected_iff_connectedSpace.mpr hP).image _ continuous_inl.continuousOn)
      have hWf : IsClopen (range (Sum.inr : (Vᶜ : Set T₁) → Y ⊕ (Vᶜ : Set T₁))) :=
        ⟨isClosed_range_inr, isOpen_range_inr⟩
      have : ConnectedSpace (range (Sum.inr : (Vᶜ : Set T₁) → Y ⊕ (Vᶜ : Set T₁))) :=
        isConnected_iff_connectedSpace.mp (isConnected_range continuous_inr)
      have := hconn_inl D hDcon
      have := hconn_inl Dᶜ hDc
      have hDKf : Disjoint (Sum.inl '' D : Set (Y ⊕ (Vᶜ : Set T₁))) (Sum.inl '' Dᶜ) :=
        disjoint_left.mpr fun _ ⟨a, ha, hae⟩ ⟨b, hb, hbe⟩ =>
          hb (Sum.inl_injective (hbe.trans hae.symm) ▸ ha)
      have hDKW : (Sum.inl '' D : Set (Y ⊕ (Vᶜ : Set T₁))) ∪ Sum.inl '' Dᶜ =
          (range Sum.inr)ᶜ := by
        ext (y | z)
        · simp only [mem_union, mem_image, Sum.inl.injEq, exists_eq_right, mem_compl_iff,
            mem_range, reduceCtorEq, exists_false, not_false_eq_true, iff_true]
          exact em (y ∈ D)
        · simp
      have hDdiscf : IsClosedDisc (Sum.inl '' D : Set (Y ⊕ (Vᶜ : Set T₁))) := by
        obtain ⟨e⟩ := hDdisc
        exact ⟨e.trans (IsEmbedding.inl.homeomorphImage D)⟩
      have hWA₂ : ∀ z ∈ range (Sum.inr : (Vᶜ : Set T₁) → Y ⊕ (Vᶜ : Set T₁)),
          (ψ₁ ∘ ξ) z ∈ A₂ → (ψ₁ ∘ ξ) z = u := by
        rintro _ ⟨w, rfl⟩ h
        change ψ₁ w.1 ∈ A₂ at h
        change ψ₁ w.1 = u
        by_contra hne
        exact w.2 (hfar ⟨h, hne⟩)
      have hWC₁ : ∃ z ∈ range (Sum.inr : (Vᶜ : Set T₁) → Y ⊕ (Vᶜ : Set T₁)),
          (ψ₁ ∘ ξ) z ∈ C₁ := by
        obtain ⟨c, hc⟩ :=
          (GM07.IsOArc.isConnected ((cuff_statement S hS).2.2 C₁ hsur₁.1)).nonempty
        obtain ⟨t, rfl⟩ := hcut₁.2.1 c
        have htW : t ∈ (Vᶜ : Set T₁) := by simpa [hVdef] using hs.cuff_sub hc
        exact ⟨Sum.inr ⟨t, htW⟩, ⟨_, rfl⟩, hc⟩
      have hWbd : ∀ z ∈ range (Sum.inr : (Vᶜ : Set T₁) → Y ⊕ (Vᶜ : Set T₁)),
          (ψ₁ ∘ ξ) z ∈ bd S → (ψ₁ ∘ ξ) z ∈ C₁ := by
        rintro _ ⟨w, rfl⟩ h
        exact hs.bd_sub w.1 (hWVc w) h
      have hWA₁ : ∀ a ∈ A₁, ∃ z ∈ range (Sum.inr : (Vᶜ : Set T₁) → Y ⊕ (Vᶜ : Set T₁)),
          (ψ₁ ∘ ξ) z = a := by
        intro a ha
        obtain ⟨s, t, hst, hpair⟩ := ncard_eq_two.mp (hcut₁.2.2.2.1 a ha)
        have hs' : ψ₁ s = a := (show s ∈ ψ₁ ⁻¹' {a} from hpair ▸ Or.inl rfl)
        have ht' : ψ₁ t = a := (show t ∈ ψ₁ ⁻¹' {a} from hpair ▸ Or.inr rfl)
        by_cases hsV : s ∈ V
        · have htV : t ∉ V := fun htV => hst (hinjV hsV htV (hs'.trans ht'.symm))
          exact ⟨Sum.inr ⟨t, htV⟩, ⟨_, rfl⟩, ht'⟩
        · exact ⟨Sum.inr ⟨s, hsV⟩, ⟨_, rfl⟩, hs'⟩
      have hc₂ : ∀ z ∈ A₁ ∪ A₂, z ≠ u → ((ψ₁ ∘ ξ) ⁻¹' {z}).ncard = 2 := by
        intro z hz hzu
        have h := hfib z hz
        simp only [hzu, ↓reduceIte] at h
        omega
      have hpre : (ψ₁ ∘ ξ) ⁻¹' {u} ∩ (range Sum.inr)ᶜ =
          Sum.inl '' (ρ ⁻¹' {⟨p₀, hp₀V⟩}) := by
        ext (y | z)
        · simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_compl_iff, mem_range,
            reduceCtorEq, exists_false, not_false_eq_true, and_true, mem_image, Sum.inl.injEq,
            exists_eq_right]
          change ψ₁ (ρ y).1 = u ↔ _
          constructor
          · intro h
            exact Subtype.ext (hinjV (ρ y).2 hp₀V (h.trans hp₀.symm))
          · intro h
            rw [h]
            exact hp₀
        · simp
      have hu₃ : ((ψ₁ ∘ ξ) ⁻¹' {u} ∩ (range Sum.inr)ᶜ).ncard = 3 := by
        rw [hpre, ncard_image_of_injective _ Sum.inl_injective]
        exact hρp
      have hlu : ∀ y, ρ y = ⟨p₀, hp₀V⟩ → (ψ₁ ∘ ξ) (Sum.inl y) = u := fun y hy => by
        change ψ₁ (ρ y).1 = u
        rw [hy]
        exact hp₀
      obtain ⟨yD, hyD, hyDp⟩ := hDu
      obtain ⟨yK, hyK, hyKp⟩ := hDcu
      obtain ⟨eK⟩ := nonempty_cylinder_of_x2_disc hS hncyl h3 hA₁ hA₂ h12 hoff hsur₁ hsur₂ hC
        hTf hθ hcutF hWf (hclopen_inl D hD) (hclopen_inl Dᶜ hD.compl) hDKf hDKW hDdiscf hWA₂
        hWC₁ hWbd hWA₁ hc₂ hu₃ ⟨Sum.inl yD, ⟨yD, hyD, rfl⟩, hlu yD hyDp⟩
        ⟨Sum.inl yK, ⟨yK, hyK, rfl⟩, hlu yK hyKp⟩
      have hgD : surfaceComplexity D = 1 := by
        obtain ⟨e⟩ := hDdisc
        obtain ⟨e₀⟩ := nonempty_disc_homeo
        have := (modelCriterion.1 0 0 1).2
        rw [surfaceComplexity_congr (e₀.trans e).symm, surfaceComplexity_eq_connected,
          connectedSurfaceComplexity_eq ⟨Homeomorph.refl _⟩]
      have hgK : surfaceComplexity (Dᶜ : Set Y) = 2 := by
        have := (modelCriterion.1 0 0 2).2
        rw [surfaceComplexity_congr ((IsEmbedding.inl.homeomorphImage Dᶜ).trans eK),
          surfaceComplexity_eq_connected, connectedSurfaceComplexity_eq ⟨Homeomorph.refl _⟩]
      have := surfaceComplexity_le_max_of_isClopen hY hD
      rw [hgD, hgK] at this
      omega
  refine ⟨Y ⊕ (Vᶜ : Set T₁), inferInstance, ψ₁ ∘ ξ, hcutF, hθ, ?_, fun x hx => (hfib x hx).1,
    fun B hB hfin => ncard_preimage_le_of_fiber hfin hθ.2.2.2.1 fun y hy => (hfib y (hB hy)).2⟩
  have := surfaceComplexity_sum_le hY hWs
  rw [hg2] at this
  exact lt_of_le_of_lt this (max_lt hgY (by omega))

/-- **The `X₂` case of the cut counts.** -/
theorem x2CutCountStatement : X2CutCountStatement.{w} :=
  fun _ _ _ hS hncyl h3 _ _ _ _ _ hA₁ hA₂ hcap hoff hs₁ hs₂ hC =>
    hasCountedCut_X2 hS hncyl h3 hA₁ hA₂ hcap hoff hs₁ hs₂ hC

end GraphMinor.GM08
