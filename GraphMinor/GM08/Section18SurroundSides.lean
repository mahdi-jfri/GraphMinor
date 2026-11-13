module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM07.CutStages
import GraphMinor.GM08.Section18SurroundRegion
import GraphMinor.GM08.Section18SurroundDisc
import GraphMinor.GM08.Section18CylinderCutSide
import GraphMinor.GM08.Section18CutDisc
import GraphMinor.GM08.Section18CutSide
import GraphMinor.GM08.Section18ClopenComplexity
import GraphMinor.GM08.Section18Invariance
import GraphMinor.GM07.CuffFinger
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.Section5a
import GraphMinor.GM19.FeatureOrient
import GraphMinor.GM19.FragmentRegion
import GraphMinor.Surface.CutOArc
import GraphMinor.Surface.CutCyl
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.Classification
import GraphMinor.Surface.InvarianceOfDomain
import GraphMinor.Surface.ModelCriterion

/-!
# The two sides of a circle that surrounds a cuff

Let the circle `A` surround the cuff `C` and miss the boundary. We cut along
`A` (VIII (18.2), page 286, types (iv) and (v)). The circle bounds a disc of
`Σ + Ĉ` around the cap, so `Σ - A` is not connected, and the cut has two
pieces, one on each side of `A` (`exists_surround_sides`). The cut map is one
to one on each piece. The piece `W` that holds `C` lies between `A` and `C`,
so it is a cylinder by `nonempty_cylinder_of_surround_region`, and capping `C`
makes all of it planar. The other piece has measure at most `g(Σ)`.

The region lemma is first put in the form we use for pieces of cuts
(`nonempty_cylinder_of_cut_piece`).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- A one to one continuous map of a compact set onto a circle off the cut
set: the preimage of a circle that misses the cut set is a circle. -/
theorem isOArc_preimage_of_isCutting {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [CompactSpace T] [T2Space S] {ψ : T → S} {G B : Set S}
    (hc : IsCutting ψ G) (hB : IsOArc B) (hBG : Disjoint B G) :
    IsOArc (ψ ⁻¹' B) ∧ BijOn ψ (ψ ⁻¹' B) B := by
  have hBc : IsClosed B := hB.isCompact.isClosed
  have hinj : InjOn ψ (ψ ⁻¹' B) := fun x hx y hy hxy =>
    hc.2.2.1 (show ψ x ∈ Gᶜ from fun h => disjoint_left.mp hBG hx h)
      (show ψ y ∈ Gᶜ from fun h => disjoint_left.mp hBG hy h) hxy
  have himg : ψ '' (ψ ⁻¹' B) = B := image_preimage_eq _ hc.2.1
  refine ⟨?_, ⟨fun x hx => hx, hinj, fun y hy => by rw [himg]; exact hy⟩⟩
  have : CompactSpace (ψ ⁻¹' B) :=
    isCompact_iff_compactSpace.mp (hBc.preimage hc.1).isCompact
  let f : (ψ ⁻¹' B) → S := fun x => ψ x.1
  have hf : Continuous f := hc.1.comp continuous_subtype_val
  have hfi : Function.Injective f := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hrange : range f = B := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hz
      obtain ⟨x, hx, he⟩ := (himg.symm ▸ hz : z ∈ ψ '' (ψ ⁻¹' B))
      exact ⟨⟨x, hx⟩, he⟩
  obtain ⟨e⟩ := hB
  exact ⟨e.trans ((hf.isClosedEmbedding hfi).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr hrange)).symm⟩

/-- **A piece of a cut between a surrounding circle and its cuff is a
cylinder.** The piece `Q` maps one to one into `Σ`, holds every lift of `C`,
and meets the cut set only over `A`. -/
theorem nonempty_cylinder_of_cut_piece {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    (hS : IsSurface S) {A C F : Set S} (hA : IsOArc A) (hoff : Disjoint A (bd S))
    (hsur : GM07.SurroundsCuff A C) (hAF : A ⊆ F) {θ : T → S} (hθ : GM07.IsCutAlongSet F θ)
    (hinjF : InjOn θ (θ ⁻¹' Fᶜ)) {Q : Set T} (hQ : IsClopen Q) [ConnectedSpace Q]
    (hinjQ : InjOn θ Q) (hQF : θ '' Q ∩ F ⊆ A) (hCQ : θ ⁻¹' C ⊆ Q) :
    Nonempty (Q ≃ₜ SurfaceModel 0 0 2) := by
  have hT := hθ.isSurface
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  have hsurj : Function.Surjective θ := hθ.quotientMap.surjective
  have hθc : Continuous θ := hθ.quotientMap.continuous
  let φ : Q → S := fun x => θ x.1
  have hφ : Continuous φ := hθc.comp continuous_subtype_val
  have hφi : Function.Injective φ := fun x y h => Subtype.ext (hinjQ x.2 y.2 h)
  have hrange : range φ = θ '' Q := by
    ext z
    exact ⟨fun ⟨x, hx⟩ => ⟨x.1, x.2, hx⟩, fun ⟨x, hx, he⟩ => ⟨⟨x, hx⟩, he⟩⟩
  set O : Set S := (θ '' Qᶜ)ᶜ with hO
  have hOo : IsOpen O := (hQ.compl.isClosed.isCompact.image hθc).isClosed.isOpen_compl
  have hOQ : O ⊆ θ '' Q := by
    intro x hx
    obtain ⟨z, rfl⟩ := hsurj x
    by_cases hz : z ∈ Q
    · exact ⟨z, hz, rfl⟩
    · exact absurd ⟨z, hz, rfl⟩ hx
  refine nonempty_cylinder_of_surround_region hS hA hoff hsur (isSurface_sub hT hQ) hφ hφi
    ?_ ?_ ?_
  · ext x
    rw [mem_bd_sub hQ.2, ← hθ.preimage_bd]
    simp only [mem_preimage, mem_union]
    constructor
    · rintro (h | h)
      · exact Or.inr h
      · exact Or.inl (hQF ⟨⟨x.1, x.2, rfl⟩, h⟩)
    · rintro (h | h)
      · exact Or.inr (hAF h)
      · exact Or.inl h
  · intro c hc
    rw [hrange]
    refine interior_maximal hOQ hOo ?_
    rintro ⟨z, hz, hzc⟩
    exact hz (hCQ (show θ z ∈ C from hzc ▸ hc))
  · intro x hx
    rw [hrange] at hx
    have hxQ : x ∈ θ '' Q := (hQ.isClosed.isCompact.image hθc).isClosed.frontier_subset hx
    by_contra hxA
    have hxF : x ∉ F := fun hxF => hxA (hQF ⟨hxQ, hxF⟩)
    have hxO : x ∈ O := by
      rintro ⟨z', hz', rfl⟩
      obtain ⟨z, hz, he⟩ := hxQ
      have : z = z' := hinjF (show θ z ∈ Fᶜ from he ▸ hxF) (show θ z' ∈ Fᶜ from hxF) he
      exact hz' (this ▸ hz)
    exact hx.2 (interior_maximal hOQ hOo hxO)

/-- The inside of a surface is dense. -/
theorem dense_compl_bd {K : Type w} [TopologicalSpace K] (hK : IsSurface K) [ConnectedSpace K] :
    Dense (bd K)ᶜ := by
  obtain ⟨a, b, c, ⟨eK⟩⟩ := classification K hK inferInstance
  have hM := (modelCriterion.1 a b c).1
  have : T2Space (SurfaceModel a b c) := hM.2.1
  have hd := GM19.dense_interior' hM
  have h1 := eK.symm.surjective.denseRange.dense_image eK.symm.continuous hd
  rwa [image_compl_eq eK.symm.bijective, image_bd_homeomorph] at h1

/-- **A circle that surrounds a cuff separates the surface.** -/
theorem not_isPreconnected_compl_of_surrounds {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {A C : Set S} (hA : IsOArc A) (hoff : Disjoint A (bd S))
    (hsur : GM07.SurroundsCuff A C) : ¬ IsPreconnected Aᶜ := by
  intro hpre
  have : T2Space S := hS.2.1
  have hC : C ∈ cuffs S := hsur.1
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  obtain ⟨S', tS', j, D, hcap, hbdS'⟩ := GM07.exists_cappedCuff hS hC
  let := tS'
  have hS' := hcap.isSurface
  have : T2Space S' := hS'.2.1
  have hman := hS'.2.2
  have hj := hcap.isEmbedding
  obtain ⟨Δ, hΔ, hbΔ, hDΔ⟩ := exists_surrounding_disc hS hA hsur hcap
  have hfrΔ : frontier Δ ⊆ j '' A := hbΔ ▸ GM07.frontier_disc_subset hman hΔ
  obtain ⟨c₀, hc₀⟩ : C.Nonempty := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact ⟨x, mem_connectedComponentIn hx⟩
  have hc₀A : c₀ ∉ A := fun h => disjoint_left.mp hoff h (hCbd hc₀)
  have hjc : j c₀ ∈ interior Δ := by
    have hmem : j c₀ ∈ Δ := hDΔ (Surface.discBd_subset D (hcap.discBd_eq ▸ mem_image_of_mem j hc₀))
    by_contra hni
    obtain ⟨a, ha, he⟩ := hfrΔ ⟨subset_closure hmem, hni⟩
    exact hc₀A (hj.injective he ▸ ha)
  obtain ⟨s₁, hs₁⟩ : ∃ s, j s ∉ Δ := by
    by_contra hall
    push_neg at hall
    have huniv : Δ = univ := eq_univ_of_forall fun y => by
      have : y ∈ range j ∪ D := hcap.union_eq ▸ mem_univ y
      rcases this with ⟨s, rfl⟩ | hy
      · exact hall s
      · exact hDΔ hy
    have hb : discBd Δ = bd S' := by
      subst huniv
      unfold discBd
      rw [← image_bd_homeomorph (Homeomorph.Set.univ S')]
      rfl
    obtain ⟨a, ha⟩ := (GM07.IsOArc.isConnected hA).nonempty
    have hja : j a ∈ bd S' := hb ▸ hbΔ.symm ▸ mem_image_of_mem j ha
    rw [hbdS'] at hja
    obtain ⟨s, hs, he⟩ := hja
    exact disjoint_left.mp hoff ha (hj.injective he ▸ hs.1)
  have hs₁A : s₁ ∉ A := fun h =>
    hs₁ (Surface.discBd_subset Δ (hbΔ ▸ mem_image_of_mem j h))
  have hU₁ : IsOpen (j ⁻¹' interior Δ) := isOpen_interior.preimage hj.continuous
  have hU₂ : IsOpen (j ⁻¹' Δᶜ) := hΔ.isClosed.isOpen_compl.preimage hj.continuous
  have hcov : Aᶜ ⊆ j ⁻¹' interior Δ ∪ j ⁻¹' Δᶜ := fun x hx => by
    by_cases h : j x ∈ Δ
    · left
      by_contra hni
      obtain ⟨a, ha, he⟩ := hfrΔ ⟨subset_closure h, hni⟩
      exact hx (hj.injective he ▸ ha)
    · exact Or.inr h
  obtain ⟨x, -, hx1, hx2⟩ := hpre _ _ hU₁ hU₂ hcov ⟨c₀, hc₀A, hjc⟩ ⟨s₁, hs₁A, hs₁⟩
  exact hx2 (interior_subset hx1)

/-- The two sides of a cut along a circle that surrounds the cuff `C`. The
side `W` holds the lifts of `C`; it is a cylinder whose image is planar after
capping `C`, and it meets the boundary only over `C`. The cut map is one to
one on each side. -/
structure SurroundSides {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    (ψ : T → S) (A C : Set S) (W : Set T) : Prop where
  isClopen : IsClopen W
  connected : ConnectedSpace W
  connected_compl : ConnectedSpace (Wᶜ : Set T)
  injOn : InjOn ψ W
  injOn_compl : InjOn ψ Wᶜ
  cylinder : Nonempty (W ≃ₜ SurfaceModel 0 0 2)
  lifts : ∃ X Y : Set T, X ∪ Y = ψ ⁻¹' A ∧ X ⊆ W ∧ Y ⊆ Wᶜ ∧ IsOArc Y ∧ BijOn ψ Y A
  cuff_sub : ψ ⁻¹' C ⊆ W
  planar : ∀ Z ⊆ W, GM07.IsPlanarInCappedCuff C (ψ '' Z)
  bd_sub : ∀ z ∈ W, ψ z ∈ bd S → ψ z ∈ C

private theorem surroundSides_of {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    [ConnectedSpace S] (hS : IsSurface S) (hT : IsSurface T)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {A C : Set S} (hA : IsOArc A) (hoff : Disjoint A (bd S)) (hsur : GM07.SurroundsCuff A C)
    {ψ : T → S} (hcut : IsCutting ψ A) {X Y W W' : Set T}
    (hun : X ∪ Y = ψ ⁻¹' A) (hX : IsOArc X) (hY : IsOArc Y)
    (hbX : BijOn ψ X A) (hbY : BijOn ψ Y A) (hXW : X ⊆ W) (hYW : Y ⊆ W')
    (hW : IsClopen W) (hUW : W ∪ W' = univ) (hdis : Disjoint W W')
    (hc : ConnectedSpace W) (hc' : ConnectedSpace W') (hCW : ψ ⁻¹' C ⊆ W) :
    SurroundSides ψ A C W ∧ Wᶜ = W' := by
  have : T2Space S := hS.2.1
  have hAc : IsClosed A := (GM07.IsOArc.isSolid hA).2
  have hWc : Wᶜ = W' := by
    ext z
    constructor
    · intro hz
      exact (hUW.symm ▸ mem_univ z : z ∈ W ∪ W').resolve_left hz
    · intro hz hzW
      exact disjoint_left.mp hdis hzW hz
  have hYX : Disjoint Y W := disjoint_left.mpr fun z hz hzW =>
    disjoint_left.mp hdis hzW (hYW hz)
  have hXW' : Disjoint X W' := disjoint_left.mpr fun z hz hzW' =>
    disjoint_left.mp hdis (hXW hz) hzW'
  have hinjW : InjOn ψ W := injOn_cut_side hcut hun hYX hbX.injOn
  have hcyl : Nonempty (W ≃ₜ SurfaceModel 0 0 2) :=
    nonempty_cylinder_of_cut_piece hS hA hoff hsur subset_rfl
      (GM07.IsCutAlongSet.of_isCutting hT hS hAc hcut) (fun x hx y hy h => hcut.2.2.1 hx hy h)
      hW hinjW (fun _ h => h.2) hCW
  obtain ⟨D, hD, hp, hbdD⟩ :=
    exists_cuff_planar_of_cylinder_cut_side hS hT hcut hAc hW hcyl hun hYX hXW hX hbX
  have hDC : D = C := by
    by_contra hne
    have hpA : GM07.IsPlanarInCappedCuff D A := hbX.image_eq ▸ hp X hXW
    exact hncyl (GM07.surroundsCuff_and_planarInCappedCuff_imp_cylinder hS hsur.1 hD
      (Ne.symm hne) hA hsur hpA)
  subst hDC
  refine ⟨⟨hW, hc, hWc ▸ hc', hinjW, ?_, hcyl, ⟨X, Y, hun, hXW, hWc ▸ hYW, hY, hbY⟩, hCW, hp,
    fun z hz hzb => hbdD z hz hzb fun hzA => disjoint_left.mp hoff hzA hzb⟩, hWc⟩
  rw [hWc]
  exact injOn_cut_side hcut (union_comm X Y ▸ hun) hXW' hbY.injOn

/-- **The two sides of a surrounding circle.** Cutting along a circle `A`
that surrounds the cuff `C` and misses the boundary gives two sides: a
cylinder `W` around `C`, and a side whose measure is at most `g(Σ)`. -/
theorem exists_surround_sides {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (h3 : 3 ≤ surfaceComplexity S)
    {A C : Set S} (hA : IsOArc A) (hoff : Disjoint A (bd S)) (hsur : GM07.SurroundsCuff A C) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S) (W : Set T), IsSurface T ∧
      IsCutting ψ A ∧ SurroundSides ψ A C W ∧
      surfaceComplexity (Wᶜ : Set T) ≤ surfaceComplexity S := by
  have : T2Space S := hS.2.1
  obtain ⟨T, tT, ψ, hT, hcut, hcase, hlifts⟩ := cutOArc S A hS inferInstance hA hoff
  let := tT
  have : CompactSpace T := hT.1
  have : T2Space T := hT.2.1
  have hnc : ¬ ConnectedSpace T := by
    intro hconn
    have hpre : IsPreconnected (ψ ⁻¹' Aᶜ) :=
      (GM19.isPreconnected_compl_bd hT).subset_closure
        (fun z hz hzA => hz (hcut.2.2.2.2 hzA))
        (fun z _ => (dense_compl_bd hT).closure_eq ▸ mem_univ z)
    have himg : ψ '' (ψ ⁻¹' Aᶜ) = Aᶜ := image_preimage_eq _ hcut.2.1
    exact not_isPreconnected_compl_of_surrounds hS hA hoff hsur
      (himg ▸ hpre.image _ hcut.1.continuousOn)
  rcases hlifts with ⟨X, Y, -, hun, hX, hY, hbX, hbY⟩ | hpre
  swap
  · exact absurd (connected_of_cut hcut hT hpre.isPreconnected rfl
      (GM07.IsOArc.isConnected hpre).nonempty) hnc
  obtain ⟨x, hx⟩ := (GM07.IsOArc.isConnected hX).nonempty
  obtain ⟨y, hy⟩ := (GM07.IsOArc.isConnected hY).nonempty
  rcases cut_comps hcut hT hX.isPreconnected hY.isPreconnected hun hx hy with hconn |
    ⟨W₁, W₂, -, hW, hXW, hYW, hW₁, hW₂, hU, hdis, hc₁, hc₂⟩
  · exact absurd hconn hnc
  have hC : C ∈ cuffs S := hsur.1
  have hCbd : C ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC
    exact connectedComponentIn_subset _ _
  have hCA : Disjoint C A := disjoint_left.mpr fun x hx hxA =>
    disjoint_left.mp hoff hxA (hCbd hx)
  obtain ⟨hCO, -⟩ := isOArc_preimage_of_isCutting hcut ((cuff_statement S hS).2.2 C hC) hCA
  have hcov : ψ ⁻¹' C ⊆ W₁ ∪ W₂ := fun z _ => hU ▸ mem_univ z
  -- the measure of a component is at most `g(Σ)`
  have hg : ∀ K ∈ spaceComponents T, IsClopen K →
      surfaceComplexity (K : Set T) ≤ surfaceComplexity S := by
    intro K hK hKc
    rcases hcase with hsimp | ⟨K₁, K₂, -, hcomps, ⟨e₁⟩, ⟨e₂⟩⟩ | hdisc
    · obtain ⟨z⟩ := (inferInstance : Nonempty S)
      obtain ⟨t, _⟩ := hcut.2.1 z
      have : Nonempty T := ⟨t⟩
      exact (surfaceComplexity_le_of_isClopen hT hKc).trans
        (surfaceComplexity_lt_of_cutIsSimpler hsimp).le
    · rw [hcomps] at hK
      rcases hK with rfl | rfl
      · obtain ⟨ecyl⟩ := nonempty_cyl_homeo
        rw [surfaceComplexity_congr (e₁.trans ecyl.symm)]
        have := (modelCriterion.1 0 0 2).2
        rw [surfaceComplexity_eq_connected,
          connectedSurfaceComplexity_eq ⟨Homeomorph.refl (SurfaceModel 0 0 2)⟩]
        omega
      · rw [surfaceComplexity_congr e₂]
    · exact absurd hdisc (not_cutHasDisc_of_circle_lifts hS hT hcut hsur.2.2
        (Or.inl ⟨X, Y, disjoint_left.mpr fun z hzX hzY =>
          disjoint_left.mp hdis (hXW hzX) (hYW hzY), hun, hX, hY, hbX, hbY⟩))
  have hW₁m : W₁ ∈ spaceComponents T := hW ▸ (Or.inl rfl : W₁ ∈ ({W₁, W₂} : Set (Set T)))
  have hW₂m : W₂ ∈ spaceComponents T := hW ▸ (Or.inr rfl : W₂ ∈ ({W₁, W₂} : Set (Set T)))
  rcases (GM07.IsOArc.isConnected hCO).isPreconnected.subset_or_subset hW₁.isOpen hW₂.isOpen
      hdis hcov with h1 | h2
  · obtain ⟨hs, hWc⟩ := surroundSides_of hS hT hncyl hA hoff hsur hcut hun hX hY hbX hbY hXW hYW
      hW₁ hU hdis hc₁ hc₂ h1
    exact ⟨T, tT, ψ, W₁, hT, hcut, hs, hWc ▸ hg W₂ hW₂m hW₂⟩
  · obtain ⟨hs, hWc⟩ := surroundSides_of hS hT hncyl hA hoff hsur hcut (union_comm X Y ▸ hun)
      hY hX hbY hbX hYW hXW hW₂ (union_comm W₁ W₂ ▸ hU) hdis.symm hc₂ hc₁ h2
    exact ⟨T, tT, ψ, W₂, hT, hcut, hs, hWc ▸ hg W₁ hW₁m hW₁⟩

end GraphMinor.GM08
