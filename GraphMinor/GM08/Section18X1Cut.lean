module

public import GraphMinor.GM08.Section18X3Cut
import GraphMinor.GM08.Section18SurroundFarSide
import GraphMinor.GM08.Section18DiscPiece
import GraphMinor.GM08.Section18LineLift
import GraphMinor.GM08.Section18CutDisc
import GraphMinor.GM08.Section18CutSide
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM08.Section18Theorem182
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM12.Section3BarbellCircles
import GraphMinor.GM07.CuffStep
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section3
import GraphMinor.Surface.CutOArc
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.CutCyl
import GraphMinor.Surface.CutLoop
import GraphMinor.Surface.Cuffs
import GraphMinor.Surface.ChartCells

/-!
# The cut along an `X₁`-arc

A schism of type (iv) (VIII (18.2), page 286) may be an `X₁`-arc: two
disjoint circles `A₁, A₂` that surround different cuffs `C₁, C₂`, and a line
`P` from `u ∈ A₁` to `v ∈ A₂`. We cut in three steps.

1. Cut along `A₁` (`exists_surround_sides`). One side is a cylinder `W`
   around `C₁`; the far side `R = Wᶜ` holds the lifts of `A₂` and of the
   inside of `P`.
2. Cut `R` along the lift of `A₂` (`exists_second_cut`). Every piece has a
   smaller measure than `Σ`, except perhaps the piece `Q` that holds the
   `R`-side lift of `A₁`, whose measure is at most `g(Σ)`. The only hard case
   is a cylinder piece `K₁` and a copy `K₂` of `R`, with `Q = K₁`. Then `K₁`
   has two cuffs, over `A₁` and over `A₂`, so it holds no point over `C₂`
   (`three_le_ncard_cuffs`). So `K₂` lies between `A₂` and `C₂`, and it is a
   cylinder by the region lemma (`nonempty_cylinder_of_cut_piece`).
3. The lift of `P` is a line in `Q` from the cuff over `A₁` to the cuff over
   `A₂`. Cutting `Q` along it lowers `g(Q)` by one
   (`exists_line_cut_of_distinct`).

The lift counts are those of `lifts_comp`, since `A₁ ∪ A₂` and `P` share only
`u` and `v`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- **Three cuffs.** If the boundary of a surface maps into three disjoint
closed sets, and each set holds the image of a boundary point, then the
surface has at least three cuffs. -/
theorem three_le_ncard_cuffs {K S : Type w} [TopologicalSpace K] [TopologicalSpace S]
    (hK : IsSurface K) {θ : K → S} (hθ : Continuous θ) {G₁ G₂ G₃ : Set S}
    (hG₁ : IsClosed G₁) (hG₂ : IsClosed G₂) (hG₃ : IsClosed G₃) (h12 : Disjoint G₁ G₂)
    (h13 : Disjoint G₁ G₃) (h23 : Disjoint G₂ G₃) (hbd : ∀ z ∈ bd K, θ z ∈ G₁ ∪ G₂ ∪ G₃)
    {p₁ p₂ p₃ : K} (hp₁ : p₁ ∈ bd K) (hp₂ : p₂ ∈ bd K) (hp₃ : p₃ ∈ bd K)
    (hθ₁ : θ p₁ ∈ G₁) (hθ₂ : θ p₂ ∈ G₂) (hθ₃ : θ p₃ ∈ G₃) : 3 ≤ (cuffs K).ncard := by
  have hb1 : ∀ z ∈ bd K, θ z ∈ G₁ ∪ (G₂ ∪ G₃) := fun z hz => by
    rw [← union_assoc]; exact hbd z hz
  have hb2 : ∀ z ∈ bd K, θ z ∈ G₂ ∪ (G₁ ∪ G₃) := fun z hz => by
    rcases hbd z hz with (h | h) | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have c12 := connectedComponentIn_bd_ne_of_map hθ hG₁ (hG₂.union hG₃)
    (disjoint_union_right.mpr ⟨h12, h13⟩) hb1 hp₁ hp₂ hθ₁ (Or.inl hθ₂)
  have c13 := connectedComponentIn_bd_ne_of_map hθ hG₁ (hG₂.union hG₃)
    (disjoint_union_right.mpr ⟨h12, h13⟩) hb1 hp₁ hp₃ hθ₁ (Or.inr hθ₃)
  have c23 := connectedComponentIn_bd_ne_of_map hθ hG₂ (hG₁.union hG₃)
    (disjoint_union_right.mpr ⟨h12.symm, h23⟩) hb2 hp₂ hp₃ hθ₂ (Or.inr hθ₃)
  have hsub : ({connectedComponentIn (bd K) p₁, connectedComponentIn (bd K) p₂,
      connectedComponentIn (bd K) p₃} : Set (Set K)) ⊆ cuffs K := by
    rintro c (rfl | rfl | rfl)
    · exact ⟨p₁, hp₁, rfl⟩
    · exact ⟨p₂, hp₂, rfl⟩
    · exact ⟨p₃, hp₃, rfl⟩
  have h3 := ncard_le_ncard hsub (cuff_statement K hK).2.1
  rwa [ncard_eq_three.mpr ⟨_, _, _, c12, c13, c23, rfl⟩] at h3

/-- Distinct cuffs are disjoint. -/
theorem disjoint_of_mem_cuffs {S : Type w} [TopologicalSpace S] {C C' : Set S}
    (hC : C ∈ cuffs S) (hC' : C' ∈ cuffs S) (hne : C ≠ C') : Disjoint C C' := by
  obtain ⟨a, -, rfl⟩ := hC
  obtain ⟨b, -, rfl⟩ := hC'
  refine disjoint_left.mpr fun z hza hzb => hne ?_
  rw [connectedComponentIn_eq hza, connectedComponentIn_eq hzb]

section copy

variable {S T₁ : Type w} [TopologicalSpace S] [TopologicalSpace T₁] [ConnectedSpace S]
  {A₁ C₁ A₂ C₂ : Set S} {ψ₁ : T₁ → S} {W : Set T₁}

/-- **The copy case of the second cut.** After the cut along `A₁`, cut the far
side `R = Wᶜ` along the lift of `A₂`, and suppose this gives a cylinder piece
`W₁` and another piece `W₂`. If `W₁` holds a point over `A₁`, then `W₂` is a
cylinder too. -/
theorem nonempty_cylinder_of_copy (hS : IsSurface S) (hT₁ : IsSurface T₁)
    (hA₁ : IsOArc A₁) (hA₂ : IsOArc A₂) (hdis : Disjoint A₁ A₂) (hoff₁ : Disjoint A₁ (bd S))
    (hoff₂ : Disjoint A₂ (bd S))
    (hsur₂ : GM07.SurroundsCuff A₂ C₂) (hC₁ : C₁ ∈ cuffs S) (hC : C₁ ≠ C₂)
    (hcut₁ : IsCutting ψ₁ A₁) (hs : SurroundSides ψ₁ A₁ C₁ W)
    (hA₂W : ψ₁ ⁻¹' A₂ ⊆ Wᶜ)
    {T₂ : Type w} [TopologicalSpace T₂] (hT₂ : IsSurface T₂) {ψ₂ : T₂ → (Wᶜ : Set T₁)}
    (hcut : IsCutting ψ₂ (Subtype.val ⁻¹' (ψ₁ ⁻¹' A₂)))
    {X Y W₁ W₂ : Set T₂} (hun : X ∪ Y = ψ₂ ⁻¹' (Subtype.val ⁻¹' (ψ₁ ⁻¹' A₂)))
    (hX : IsOArc X) (hbY : BijOn ψ₂ Y (Subtype.val ⁻¹' (ψ₁ ⁻¹' A₂)))
    (hXW : X ⊆ W₁) (hW₁ : IsClopen W₁) (hW₂ : IsClopen W₂) (hU : W₁ ∪ W₂ = univ)
    (hdisW : Disjoint W₁ W₂) (hc₂ : ConnectedSpace W₂)
    (hcyl : Nonempty (W₁ ≃ₜ SurfaceModel 0 0 2)) {z₀ : T₂} (hz₀ : z₀ ∈ W₁)
    (hz₀A : ψ₁ (ψ₂ z₀) ∈ A₁) : Nonempty (W₂ ≃ₜ SurfaceModel 0 0 2) := by
  have : T2Space S := hS.2.1
  have : CompactSpace T₁ := hT₁.1
  have : T2Space T₁ := hT₁.2.1
  have : CompactSpace T₂ := hT₂.1
  have hRo : IsClopen (Wᶜ : Set T₁) := hs.isClopen.compl
  have hR : IsSurface (Wᶜ : Set T₁) := isSurface_sub hT₁ hRo
  have : T2Space (Wᶜ : Set T₁) := hR.2.1
  have hA₁c : IsClosed A₁ := hA₁.isCompact.isClosed
  have hA₂c : IsClosed A₂ := hA₂.isCompact.isClosed
  set F₂ : Set (Wᶜ : Set T₁) := Subtype.val ⁻¹' (ψ₁ ⁻¹' A₂) with hF₂def
  have hF₂c : IsClosed F₂ := (hA₂c.preimage hcut₁.1).preimage continuous_subtype_val
  have hbdT₁ : ψ₁ ⁻¹' (bd S ∪ A₁) = bd T₁ :=
    (isCutAlongSet_of_isCutting hS hT₁ hA₁c hcut₁).preimage_bd
  have hbd' : ψ₂ ⁻¹' (bd (Wᶜ : Set T₁) ∪ F₂) = bd T₂ :=
    (isCutAlongSet_of_isCutting hR hT₂ hF₂c hcut).preimage_bd
  have hbdlift : ∀ z : T₂, ψ₁ (ψ₂ z) ∈ bd S ∪ A₁ → z ∈ bd T₂ := fun z hz => by
    rw [← hbd']
    left
    rw [mem_bd_sub hRo.isOpen, ← hbdT₁]
    exact hz
  have hbdmap : ∀ z ∈ bd T₂, ψ₁ (ψ₂ z) ∈ A₁ ∪ A₂ ∪ bd S := fun z hz => by
    rw [← hbd'] at hz
    rcases hz with h | h
    · have h' : (ψ₂ z : T₁) ∈ ψ₁ ⁻¹' (bd S ∪ A₁) := by
        rw [hbdT₁]
        exact (mem_bd_sub hRo.isOpen).mp h
      rcases h' with h' | h'
      · exact Or.inr h'
      · exact Or.inl (Or.inl h')
    · exact Or.inl (Or.inr h)
  -- the points over `A₁` lie in `W₁`
  obtain ⟨X₁, Y₁, hun₁, hX₁W, hY₁W, hY₁, -⟩ := hs.lifts
  have hY₁eq : (Subtype.val ⁻¹' (ψ₁ ⁻¹' A₁) : Set (Wᶜ : Set T₁)) = Subtype.val ⁻¹' Y₁ := by
    ext z
    constructor
    · intro h
      have : z.1 ∈ X₁ ∪ Y₁ := hun₁ ▸ h
      exact this.resolve_left fun hx => z.2 (hX₁W hx)
    · intro h
      exact (hun₁ ▸ Or.inr h : z.1 ∈ ψ₁ ⁻¹' A₁)
  have hpreA₁ : IsPreconnected (ψ₂ ⁻¹' (Subtype.val ⁻¹' (ψ₁ ⁻¹' A₁))) := by
    refine isPreconnected_preimage_of_isCutMap (GM19.IsCutting.isCutMap hcut) ?_ ?_
    · rw [hY₁eq]
      exact (GM07.IsOArc.isConnected (GM12.isOArc_subtype_preimage hY₁W hY₁)).isPreconnected
    · exact disjoint_left.mpr fun z h1 h2 => disjoint_left.mp hdis h1 h2
  have hA₁W₁ : ψ₂ ⁻¹' (Subtype.val ⁻¹' (ψ₁ ⁻¹' A₁)) ⊆ W₁ :=
    hpreA₁.subset_isClopen hW₁ ⟨z₀, hz₀A, hz₀⟩
  -- no point of `W₁` lies over `C₂`, since `W₁` has only two cuffs
  have hC₂bd : C₂ ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hsur₂.1
    exact connectedComponentIn_subset _ _
  have hW₁C₂ : ∀ p ∈ W₁, ψ₁ (ψ₂ p) ∉ C₂ := by
    intro p hp hpC
    have hW₁s : IsSurface W₁ := isSurface_sub hT₂ hW₁
    have hn := GM07.ncard_cuffs_of_homeomorph_surfaceModel hcyl
    obtain ⟨e⟩ := hX
    have hxX : ((e 1) : T₂) ∈ X := (e 1).2
    have hxF : (e 1 : T₂) ∈ ψ₂ ⁻¹' F₂ := hun ▸ Or.inl hxX
    have h3 := three_le_ncard_cuffs hW₁s (θ := fun q : W₁ => ψ₁ (ψ₂ q.1))
      (hcut₁.1.comp (continuous_subtype_val.comp (hcut.1.comp continuous_subtype_val)))
      hA₁c hA₂c (cuff_statement S hS).1 hdis hoff₁ hoff₂
      (fun q hq => hbdmap q.1 ((mem_bd_sub hW₁.isOpen).mp hq))
      (p₁ := ⟨z₀, hz₀⟩) (p₂ := ⟨_, hXW hxX⟩) (p₃ := ⟨p, hp⟩)
      ((mem_bd_sub hW₁.isOpen).mpr (hbdlift z₀ (Or.inr hz₀A)))
      ((mem_bd_sub hW₁.isOpen).mpr (hcut.2.2.2.2 hxF))
      ((mem_bd_sub hW₁.isOpen).mpr (hbdlift p (Or.inl (hC₂bd hpC))))
      hz₀A hxF (hC₂bd hpC)
    omega
  -- the glued cut along `A₁ ∪ A₂`, and the region lemma for the piece over `W₂`
  have hcut₂ := isCutting_sum_compl hA₂W hcut
  have hTs : IsSurface (T₂ ⊕ ((Wᶜ)ᶜ : Set T₁)) :=
    GM07.isSurface_sum hT₂ (isSurface_sub hT₁ hRo.compl)
  have : CompactSpace (T₂ ⊕ ((Wᶜ)ᶜ : Set T₁)) := hTs.1
  have hθ := IsCutting.comp_of_disjoint hcut₁ hcut₂ hA₂c hdis
  have hθA := isCutAlongSet_of_isCutting hS hTs (hA₁c.union hA₂c) hθ
  have hQ : IsClopen (Sum.inl '' W₂ : Set (T₂ ⊕ ((Wᶜ)ᶜ : Set T₁))) :=
    ⟨IsClosedEmbedding.inl.isClosedMap _ hW₂.1, isOpenMap_inl _ hW₂.2⟩
  have : ConnectedSpace (Sum.inl '' W₂ : Set (T₂ ⊕ ((Wᶜ)ᶜ : Set T₁))) :=
    isConnected_iff_connectedSpace.mp
      ((isConnected_iff_connectedSpace.mpr hc₂).image _ continuous_inl.continuousOn)
  have hinj₂ : InjOn ψ₂ W₂ :=
    injOn_cut_side hcut (union_comm X Y ▸ hun) (hdisW.mono_left hXW) hbY.injOn
  have hQinj : InjOn (ψ₁ ∘ Sum.elim (Subtype.val ∘ ψ₂) (Subtype.val : ((Wᶜ)ᶜ : Set T₁) → T₁))
      (Sum.inl '' W₂) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    exact congrArg Sum.inl (hinj₂ ha hb (Subtype.ext (hs.injOn_compl (ψ₂ a).2 (ψ₂ b).2 hab)))
  have hQF : (ψ₁ ∘ Sum.elim (Subtype.val ∘ ψ₂) (Subtype.val : ((Wᶜ)ᶜ : Set T₁) → T₁)) ''
      (Sum.inl '' W₂) ∩ (A₁ ∪ A₂) ⊆ A₂ := by
    rintro _ ⟨⟨_, ⟨a, ha, rfl⟩, rfl⟩, h⟩
    rcases h with h | h
    · exact absurd (hA₁W₁ h) (disjoint_right.mp hdisW ha)
    · exact h
  have hCQ : (ψ₁ ∘ Sum.elim (Subtype.val ∘ ψ₂) (Subtype.val : ((Wᶜ)ᶜ : Set T₁) → T₁)) ⁻¹' C₂ ⊆
      Sum.inl '' W₂ := by
    rintro (a | w) h
    · refine ⟨a, ?_, rfl⟩
      have : a ∈ W₁ ∪ W₂ := hU ▸ mem_univ a
      exact this.resolve_left fun ha => hW₁C₂ a ha h
    · exfalso
      have hw : (w : T₁) ∈ W := not_not.mp w.2
      exact disjoint_left.mp (disjoint_of_mem_cuffs hC₁ hsur₂.1 hC) (hs.bd_sub w hw (hC₂bd h)) h
  obtain ⟨e⟩ := nonempty_cylinder_of_cut_piece hS hA₂ hoff₂ hsur₂ subset_union_right hθA
    hθ.2.2.1 hQ hQinj hQF hCQ
  exact ⟨(IsEmbedding.inl.homeomorphImage W₂).trans e⟩

/-- **The second cut of an `X₁`-arc.** After the cut along `A₁`, cut the far
side along the lift of `A₂`. A piece that holds a point over `A₁` on the far
side has measure at most `g(Σ)`, and every other piece has a smaller measure. -/
theorem exists_second_cut (hS : IsSurface S) (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (h3 : 3 ≤ surfaceComplexity S) (hT₁ : IsSurface T₁)
    (hA₁ : IsOArc A₁) (hA₂ : IsOArc A₂) (hdis : Disjoint A₁ A₂) (hoff₁ : Disjoint A₁ (bd S))
    (hoff₂ : Disjoint A₂ (bd S)) (hsur₁ : GM07.SurroundsCuff A₁ C₁)
    (hsur₂ : GM07.SurroundsCuff A₂ C₂) (hC : C₁ ≠ C₂)
    (hcut₁ : IsCutting ψ₁ A₁) (hs : SurroundSides ψ₁ A₁ C₁ W)
    (hgR : surfaceComplexity (Wᶜ : Set T₁) ≤ surfaceComplexity S) :
    ∃ (T₂ : Type w) (_ : TopologicalSpace T₂) (ψ₂ : T₂ → T₁), IsSurface T₂ ∧
      IsCutting ψ₂ (ψ₁ ⁻¹' A₂) ∧
      ∀ z : T₂, ψ₂ z ∈ Wᶜ → ψ₁ (ψ₂ z) ∈ A₁ →
        connectedSurfaceComplexity (connectedComponent z) ≤ surfaceComplexity S ∧
        ∀ z' ∉ connectedComponent z,
          connectedSurfaceComplexity (connectedComponent z') < surfaceComplexity S := by
  have : T2Space S := hS.2.1
  have : CompactSpace T₁ := hT₁.1
  have : T2Space T₁ := hT₁.2.1
  have hA₂W := preimage_subset_compl_of_surrounds hS hT₁ hncyl hcut₁ hs hA₂ hdis hsur₂ hsur₁.1 hC
  obtain ⟨hO₂, hbij₂⟩ := isOArc_preimage_of_isCutting hcut₁ hA₂ hdis.symm
  have hRo : IsClopen (Wᶜ : Set T₁) := hs.isClopen.compl
  have hR : IsSurface (Wᶜ : Set T₁) := isSurface_sub hT₁ hRo
  have := hs.connected_compl
  have : T2Space (Wᶜ : Set T₁) := hR.2.1
  have hA₁c : IsClosed A₁ := hA₁.isCompact.isClosed
  have hbdT₁ : ψ₁ ⁻¹' (bd S ∪ A₁) = bd T₁ :=
    (isCutAlongSet_of_isCutting hS hT₁ hA₁c hcut₁).preimage_bd
  set F₂ : Set (Wᶜ : Set T₁) := Subtype.val ⁻¹' (ψ₁ ⁻¹' A₂) with hF₂def
  have hF₂ : IsOArc F₂ := GM12.isOArc_subtype_preimage hA₂W hO₂
  have hF₂bd : Disjoint F₂ (bd (Wᶜ : Set T₁)) := disjoint_left.mpr fun z hz hzb => by
    have : (z : T₁) ∈ ψ₁ ⁻¹' (bd S ∪ A₁) := hbdT₁ ▸ (mem_bd_sub hRo.isOpen).mp hzb
    rcases this with h | h
    · exact disjoint_left.mp hoff₂ hz h
    · exact disjoint_left.mp hdis h hz
  obtain ⟨T₂, t₂, ψ₂, hT₂, hcut, hcase, hlifts⟩ :=
    cutOArc (Wᶜ : Set T₁) F₂ hR inferInstance hF₂ hF₂bd
  let := t₂
  have : CompactSpace T₂ := hT₂.1
  have hRc : IsSurface ((Wᶜ)ᶜ : Set T₁) := isSurface_sub hT₁ hRo.compl
  refine ⟨T₂ ⊕ ((Wᶜ)ᶜ : Set T₁), inferInstance, _, GM07.isSurface_sum hT₂ hRc,
    isCutting_sum_compl hA₂W hcut, ?_⟩
  have hinr : ∀ w : ((Wᶜ)ᶜ : Set T₁), connectedSurfaceComplexity
      (connectedComponent (Sum.inr w : T₂ ⊕ ((Wᶜ)ᶜ : Set T₁))) < surfaceComplexity S := by
    intro w
    rw [connectedSurfaceComplexity_component_inr,
      connectedSurfaceComplexity_component_subtype hRo.compl,
      connectedSurfaceComplexity_component_of_mem_cylinder hs (not_not.mp w.2)]
    omega
  suffices hmain : ∀ z₀ : T₂, ψ₁ (ψ₂ z₀) ∈ A₁ →
      connectedSurfaceComplexity (connectedComponent z₀) ≤ surfaceComplexity S ∧
      ∀ z₀' ∉ connectedComponent z₀,
        connectedSurfaceComplexity (connectedComponent z₀') < surfaceComplexity S by
    rintro (z₀ | w) hzR hzA
    · obtain ⟨h1, h2⟩ := hmain z₀ hzA
      refine ⟨by rw [connectedSurfaceComplexity_component_inl]; exact h1, ?_⟩
      rintro (z₀' | w') hz'
      · rw [connectedSurfaceComplexity_component_inl]
        refine h2 z₀' fun h => hz' ?_
        exact (isPreconnected_connectedComponent.image _ continuous_inl.continuousOn
          ).subset_connectedComponent ⟨z₀, mem_connectedComponent, rfl⟩ ⟨z₀', h, rfl⟩
      · exact hinr w'
    · exact absurd hzR w.2
  have hgR' : connectedSurfaceComplexity (Wᶜ : Set T₁) ≤ surfaceComplexity S := by
    rw [← surfaceComplexity_eq_connected]
    exact hgR
  intro z₀ hz₀
  rcases hcase with hsimp | ⟨K₁, K₂, hK, hcomps, ⟨e₁⟩, ⟨e₂⟩⟩ | hdisc
  · have hlt : ∀ z : T₂, connectedSurfaceComplexity (connectedComponent z) <
        surfaceComplexity S := fun z => by
      have := connectedSurfaceComplexity_lt_of_isSimplerThan
        (hsimp.2 _ (by rw [Surface.spaceComponents_eq]; exact ⟨z, rfl⟩))
      omega
    exact ⟨(hlt z₀).le, fun z _ => hlt z⟩
  · have hne2 : ¬ ConnectedSpace T₂ := by
      intro hconn
      have h1 : K₁ ∈ spaceComponents T₂ := hcomps ▸ (Or.inl rfl)
      have h2 : K₂ ∈ spaceComponents T₂ := hcomps ▸ (Or.inr rfl)
      rw [Surface.spaceComponents_eq] at h1 h2
      obtain ⟨a, rfl⟩ := h1
      obtain ⟨b, rfl⟩ := h2
      exact hK ((PreconnectedSpace.connectedComponent_eq_univ a).trans
        (PreconnectedSpace.connectedComponent_eq_univ b).symm)
    rcases hlifts with ⟨X, Y, -, hun, hX, hY, hbX, hbY⟩ | hone
    swap
    · exact absurd (connected_of_cut hcut hT₂ hone.isPreconnected rfl
        (GM07.IsOArc.isConnected hone).nonempty) hne2
    obtain ⟨x, hx⟩ := (GM07.IsOArc.isConnected hX).nonempty
    obtain ⟨y, hy⟩ := (GM07.IsOArc.isConnected hY).nonempty
    rcases cut_comps hcut hT₂ hX.isPreconnected hY.isPreconnected hun hx hy with hconn |
      ⟨W₁, W₂, -, hW, hXW, hYW, hW₁, hW₂, hU, hdisW, hc₁, hc₂⟩
    · exact absurd hconn hne2
    have hcomp : ∀ z : T₂, connectedComponent z = K₁ ∨ connectedComponent z = K₂ := by
      intro z
      have : connectedComponent z ∈ spaceComponents T₂ := by
        rw [Surface.spaceComponents_eq]
        exact ⟨z, rfl⟩
      rwa [hcomps] at this
    have hK₁ : K₁ = W₁ ∨ K₁ = W₂ := by
      have : K₁ ∈ spaceComponents T₂ := hcomps ▸ (Or.inl rfl)
      rwa [hW] at this
    have hK₂ : K₂ = W₁ ∨ K₂ = W₂ := by
      have : K₂ ∈ spaceComponents T₂ := hcomps ▸ (Or.inr rfl)
      rwa [hW] at this
    have hdata : ∃ X' Y' : Set T₂, X' ∪ Y' = ψ₂ ⁻¹' F₂ ∧ IsOArc X' ∧ BijOn ψ₂ Y' F₂ ∧
        X' ⊆ K₁ ∧ IsClopen K₁ ∧ IsClopen K₂ ∧ K₁ ∪ K₂ = univ ∧ Disjoint K₁ K₂ ∧
        ConnectedSpace K₂ := by
      rcases hK₁ with rfl | rfl <;> rcases hK₂ with rfl | rfl
      · exact absurd rfl hK
      · exact ⟨X, Y, hun, hX, hbY, hXW, hW₁, hW₂, hU, hdisW, hc₂⟩
      · exact ⟨Y, X, union_comm X Y ▸ hun, hY, hbX, hYW, hW₂, hW₁, (union_comm _ _).trans hU,
          hdisW.symm, hc₁⟩
      · exact absurd rfl hK
    obtain ⟨X', Y', hun', hX', hbY', hXK, hK₁c, hK₂c, hUK, hdisK, hcK₂⟩ := hdata
    have hcylK₁ : Nonempty (K₁ ≃ₜ SurfaceModel 0 0 2) := by
      obtain ⟨c⟩ := nonempty_cyl_homeo
      exact ⟨e₁.trans c.symm⟩
    have hg₁ : connectedSurfaceComplexity K₁ = 2 := connectedSurfaceComplexity_eq hcylK₁
    have hg₂ : connectedSurfaceComplexity K₂ ≤ surfaceComplexity S := by
      rw [connectedSurfaceComplexity_congr e₂]
      exact hgR'
    have hother : ∀ z', z' ∉ connectedComponent z₀ →
        connectedComponent z' ≠ connectedComponent z₀ := fun z' hz' h =>
      hz' (h ▸ mem_connectedComponent)
    rcases hcomp z₀ with h₀ | h₀
    · have hz₀K : z₀ ∈ K₁ := h₀ ▸ mem_connectedComponent
      have hcyl₂ := nonempty_cylinder_of_copy hS hT₁ hA₁ hA₂ hdis hoff₁ hoff₂ hsur₂ hsur₁.1 hC
        hcut₁ hs hA₂W hT₂ hcut hun' hX' hbY' hXK hK₁c hK₂c hUK hdisK hcK₂ hcylK₁ hz₀K hz₀
      refine ⟨by rw [h₀, hg₁]; omega, fun z' hz' => ?_⟩
      rcases hcomp z' with h' | h'
      · exact absurd (h'.trans h₀.symm) (hother z' hz')
      · rw [h', connectedSurfaceComplexity_eq hcyl₂]
        omega
    · refine ⟨by rw [h₀]; exact hg₂, fun z' hz' => ?_⟩
      rcases hcomp z' with h' | h'
      · rw [h', hg₁]
        omega
      · exact absurd (h'.trans h₀.symm) (hother z' hz')
  · exfalso
    refine not_cutHasDisc_of_circle_lifts hR hT₂ hcut ?_ hlifts hdisc
    rintro ⟨Δ, hΔ, hFΔ⟩
    have hf : Continuous fun z : (Wᶜ : Set T₁) => ψ₁ z.1 := hcut₁.1.comp continuous_subtype_val
    have hinj : InjOn (fun z : (Wᶜ : Set T₁) => ψ₁ z.1) Δ := fun a _ b _ h =>
      Subtype.ext (hs.injOn_compl a.2 b.2 h)
    refine hsur₂.2.2 ⟨_, (isClosedDisc_image_of_injOn hf hΔ hinj).1, fun a ha => ?_⟩
    obtain ⟨z, hz, rfl⟩ := hbij₂.surjOn ha
    exact ⟨⟨z, hA₂W hz⟩, hFΔ hz, rfl⟩

end copy

/-- **(18.2) with lift counts for an `X₁`-arc.** -/
theorem hasCountedCut_X1 {S : Type w} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (h3 : 3 ≤ surfaceComplexity S)
    {A₁ A₂ P C₁ C₂ : Set S} {u v : S} (hA₁ : IsOArc A₁) (hA₂ : IsOArc A₂)
    (hdis : Disjoint A₁ A₂) (hP : IsLineWithEnds P u v) (hu : u ∈ A₁) (hv : v ∈ A₂)
    (hPA₁ : P ∩ A₁ = {u}) (hPA₂ : P ∩ A₂ = {v}) (hoff : Disjoint (A₁ ∪ A₂ ∪ P) (bd S))
    (hsur₁ : GM07.SurroundsCuff A₁ C₁) (hsur₂ : GM07.SurroundsCuff A₂ C₂) (hC : C₁ ≠ C₂) :
    HasCountedCut S (A₁ ∪ A₂ ∪ P) := by
  have : T2Space S := hS.2.1
  have hoff₁ : Disjoint A₁ (bd S) := hoff.mono_left (subset_union_left.trans subset_union_left)
  have hoff₂ : Disjoint A₂ (bd S) := hoff.mono_left (subset_union_right.trans subset_union_left)
  have hA₁c : IsClosed A₁ := hA₁.isCompact.isClosed
  have hA₂c : IsClosed A₂ := hA₂.isCompact.isClosed
  have hGc : IsClosed (A₁ ∪ A₂) := hA₁c.union hA₂c
  obtain ⟨T₁, t₁, ψ₁, W, hT₁, hcut₁, hs, hgR⟩ := exists_surround_sides hS hncyl h3 hA₁ hoff₁ hsur₁
  have : CompactSpace T₁ := hT₁.1
  have : T2Space T₁ := hT₁.2.1
  have hA₂W := preimage_subset_compl_of_surrounds hS hT₁ hncyl hcut₁ hs hA₂ hdis hsur₂ hsur₁.1 hC
  obtain ⟨T₂, t₂, ψ₂, hT₂, hcut₂, hmeas⟩ := exists_second_cut hS hncyl h3 hT₁ hA₁ hA₂ hdis hoff₁
    hoff₂ hsur₁ hsur₂ hC hcut₁ hs hgR
  have : CompactSpace T₂ := hT₂.1
  have : T2Space T₂ := hT₂.2.1
  have := hT₂.locallyConnected
  have hθ : IsCutting (ψ₁ ∘ ψ₂) (A₁ ∪ A₂) := IsCutting.comp_of_disjoint hcut₁ hcut₂ hA₂c hdis
  have hθc : Continuous (ψ₁ ∘ ψ₂) := hθ.1
  have huv : u ≠ v := fun h => disjoint_left.mp hdis hu (h ▸ hv)
  have hPo : Disjoint (P \ {u, v}) (A₁ ∪ A₂) := by
    refine disjoint_left.mpr fun z hz hzA => hz.2 ?_
    rcases hzA with h | h
    · exact Or.inl (hPA₁ ▸ ⟨hz.1, h⟩ : z ∈ ({u} : Set S))
    · exact Or.inr (hPA₂ ▸ ⟨hz.1, h⟩ : z ∈ ({v} : Set S))
  obtain ⟨x, y, hx, hy, hL, hbij, hdiff⟩ :=
    exists_line_closure_lift_of_cutMap (GM19.IsCutting.isCutMap hθ) hGc hP hPo
  set L := closure ((ψ₁ ∘ ψ₂) ⁻¹' (P \ {u, v}))
  have hfar₁ : ψ₁ ⁻¹' (P \ {u, v}) ⊆ Wᶜ :=
    preimage_subset_compl_of_closure hS hT₁ hcut₁ hs hA₂W
      (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hP)
      (hPo.mono_right subset_union_left)
      ⟨v, hP.subset_closure_diff hP.right_mem, hv⟩
  have hLR : L ⊆ ψ₂ ⁻¹' Wᶜ :=
    closure_minimal (fun z hz => hfar₁ hz) (hs.isClopen.compl.isClosed.preimage hcut₂.1)
  have hxR : ψ₂ x ∈ Wᶜ := hLR hL.left_mem
  obtain ⟨hgQ, hgother⟩ := hmeas x hxR (show ψ₁ (ψ₂ x) ∈ A₁ from by rw [← Function.comp_apply (f := ψ₁), hx]; exact hu)
  set Q := connectedComponent x
  have hQ : IsClopen Q := ⟨isClosed_connectedComponent, isOpen_connectedComponent⟩
  have : ConnectedSpace Q := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hLQ : L ⊆ Q := by
    obtain ⟨f, hf0, -⟩ := hL
    refine (isPreconnected_of_isLine ⟨f⟩).subset_connectedComponent ?_
    rw [← hf0]
    exact (f 0).2
  have hxy : x ≠ y := fun h => huv (hx ▸ hy ▸ congrArg (ψ₁ ∘ ψ₂) h)
  have hbdT : (ψ₁ ∘ ψ₂) ⁻¹' (bd S ∪ (A₁ ∪ A₂)) = bd T₂ :=
    (isCutAlongSet_of_isCutting hS hT₂ hGc hθ).preimage_bd
  have huG : u ∈ A₁ ∪ A₂ := Or.inl hu
  have hvG : v ∈ A₁ ∪ A₂ := Or.inr hv
  have hxb : x ∈ bd T₂ := hθ.2.2.2.2 (show (ψ₁ ∘ ψ₂) x ∈ A₁ ∪ A₂ by rw [hx]; exact huG)
  have hyb : y ∈ bd T₂ := hθ.2.2.2.2 (show (ψ₁ ∘ ψ₂) y ∈ A₁ ∪ A₂ by rw [hy]; exact hvG)
  have hLbd : L ∩ bd T₂ = {x, y} := by
    ext z
    constructor
    · rintro ⟨hzL, hzb⟩
      by_contra hz
      have hz' : z ∈ (ψ₁ ∘ ψ₂) ⁻¹' (P \ {u, v}) := hdiff ▸ ⟨hzL, hz⟩
      rcases (hbdT ▸ hzb : z ∈ (ψ₁ ∘ ψ₂) ⁻¹' (bd S ∪ (A₁ ∪ A₂))) with h | h
      · exact disjoint_left.mp hoff (Or.inr hz'.1) h
      · exact disjoint_left.mp hPo hz' h
    · rintro (rfl | rfl)
      · exact ⟨hL.left_mem, hxb⟩
      · exact ⟨hL.right_mem, hyb⟩
  have hcuffs : connectedComponentIn (bd T₂) x ≠ connectedComponentIn (bd T₂) y :=
    connectedComponentIn_bd_ne_of_map hθc hA₁c (hA₂c.union (cuff_statement S hS).1)
      (disjoint_union_right.mpr ⟨hdis, hoff₁⟩)
      (fun z hz => by
        rcases (hbdT ▸ hz : z ∈ (ψ₁ ∘ ψ₂) ⁻¹' (bd S ∪ (A₁ ∪ A₂))) with h | h | h
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h))
      hxb hyb (show (ψ₁ ∘ ψ₂) x ∈ A₁ by rw [hx]; exact hu)
      (show (ψ₁ ∘ ψ₂) y ∈ A₂ ∪ bd S by rw [hy]; exact Or.inl hv)
  have hQn : surfaceComplexity Q ≤ surfaceComplexity S - 1 + 1 := by
    rw [surfaceComplexity_eq_connected]
    omega
  obtain ⟨T₃, t₃, ψ₃, hT₃, hcut₃, hg₃⟩ := exists_line_cut_of_distinct hT₂ hQ hLQ hL hxy hLbd
    hcuffs hQn fun z hz => by have := hgother z hz; omega
  have hLc : IsClosed L := isClosed_closure
  have hG₂H : L ⊆ (ψ₁ ∘ ψ₂) ⁻¹' P := fun z hz => hbij.mapsTo hz
  have hH : (ψ₁ ∘ ψ₂) ⁻¹' P ⊆ L ∪ bd T₂ := by
    intro z hz
    by_cases huvz : (ψ₁ ∘ ψ₂) z ∈ ({u, v} : Set S)
    · refine Or.inr (hθ.2.2.2.2 ?_)
      rcases huvz with h | h
      · rw [mem_preimage, h]
        exact huG
      · rw [mem_preimage, mem_singleton_iff.mp h]
        exact hvG
    · exact Or.inl (subset_closure ⟨hz, huvz⟩)
  have hHG₂ : (ψ₁ ∘ ψ₂) ⁻¹' (P \ (A₁ ∪ A₂)) ⊆ L := by
    intro z hz
    refine subset_closure ⟨hz.1, fun h => hz.2 ?_⟩
    rcases h with h | h
    · rw [h]; exact huG
    · rw [mem_singleton_iff.mp h]; exact hvG
  have hFc : IsClosed (A₁ ∪ A₂ ∪ P) := hGc.union hP.isCompact.isClosed
  have hcutF := isCutAlongSet_comp hS hT₂ hT₃ hθ hGc hcut₃ hLc hG₂H hH
  have hmapF := isCutMap_comp hT₂ hT₃ hθ hcut₃ hLc hG₂H hH
  obtain ⟨hlift, hcount⟩ := lifts_comp hθ hcut₃ hbij.injOn hG₂H hHG₂
  have hAP : (A₁ ∪ A₂) ∩ P = {u, v} := by
    rw [union_inter_distrib_right, inter_comm, hPA₁, inter_comm, hPA₂]
    rfl
  refine ⟨T₃, t₃, (ψ₁ ∘ ψ₂) ∘ ψ₃, hcutF, hmapF, by omega, hlift, fun B _ hB =>
    (hcount B hB).trans (ncard_bound_of_inter hB (hAP ▸ toFinite _) ?_)⟩
  rw [hAP]
  exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])

end GraphMinor.GM08
