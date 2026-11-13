module

public import GraphMinor.GM08.Section18Subgraft
public import GraphMinor.GM07.Defs
import GraphMinor.GM07.CuffStep
import GraphMinor.GM07.CollarPush
import GraphMinor.GM07.CuffArc
import GraphMinor.GM07.CuffFinger
import GraphMinor.Surface.Collar
import GraphMinor.Surface.DiscMerge
import GraphMinor.Surface.DiscGrow

/-!
# The outer piece of the split step

Let `Γ` draw a graft in `Σ`, and let `F` be a `Γ`-normal `O`-arc that bounds
a disc `Δ` of `Σ + Ĉ` around the pasted disc of the cuff `C`. The edges of
`Γ` miss `F`, so each lies inside `Δ` or outside it
(`edge_subset_or_disjoint`). The part of `Γ` outside the interior of `Δ`
is a drawing in a copy of `Σ`: VII's push `h` (`GM07.exists_capped_push`)
maps `Σ` onto the outside of the interior of `Δ`, and maps `C` onto `F`.
Read in `Σ` by `h`, this part is a drawing of a subgraft whose roots are the
old roots off `C` and the vertices on `F` (`exists_outer_graft`). This is
the graft in `𝒞(Σ, k - 1)` in case (ii) of the proof of (18.3), page 287.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u v w

/-- The part of a drawing off an open set `Z` whose edges each meet `Z` only if
they lie in `Z`; its edges are the edges that miss `Z`. -/
theorem exists_outside_drawing_edges {S : Type w} [TopologicalSpace S] [T1Space S]
    {G : Drawing S} {Z : Set S} (hZ : IsOpen Z)
    (hedge : ∀ e ∈ G.E, (∃ y ∈ e, y ∉ Z) → Disjoint e Z) :
    ∃ G₁ : Drawing S, G₁.IsSubdrawing G ∧ G₁.U = G.U ∩ Zᶜ ∧ G₁.V = G.V ∩ Zᶜ ∧
      G₁.E = {e ∈ G.E | Disjoint e Z} := by
  classical
  let G₁ := G.span Zᶜ {e | Disjoint e Z}
  have hsub : G₁.IsSubdrawing G := Drawing.span_isSubdrawing G _ _
  have hE : ∀ e ∈ ({e | Disjoint e Z} ∩ G.E : Set (Set S)), closure e ⊆ Zᶜ :=
    fun e he => (Disjoint.closure_left he.1 hZ).le_compl_right
  have hV : G₁.V ⊆ Zᶜ := by
    rintro x (hx | hx)
    · exact hx.1
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact hE e he hxe.1
  refine ⟨G₁, hsub, subset_antisymm (subset_inter hsub.U_subset ?_) ?_,
    subset_antisymm (subset_inter hsub.1 hV) ?_, ?_⟩
  · rintro x (hx | hx)
    · exact hV hx
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact hE e he hxe
  · rintro x ⟨hxU, hxZ⟩
    by_cases hxV : x ∈ G.V
    · exact .inl (.inl ⟨hxZ, hxV⟩)
    · obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem hxU hxV
      exact .inr (mem_iUnion₂.mpr ⟨e, ⟨hedge e he ⟨x, hxe, hxZ⟩, he⟩, subset_closure hxe⟩)
  · rintro x ⟨hxV, hxZ⟩
    exact .inl ⟨hxZ, hxV⟩
  · rw [Drawing.span_E]
    ext e
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- An edge of a drawing that misses `j⁻¹(bd Δ)` lies in `j⁻¹(int Δ)` or misses
`j⁻¹(Δ)`. -/
theorem edge_subset_or_disjoint {S T : Type*} [TopologicalSpace S] [TopologicalSpace T] [T2Space T]
    (hman : ∀ x : T, IsManifoldPoint x) {j : S → T} (hj : Continuous j) {Δ : Set T}
    (hΔ : IsClosedDisc Δ) {G : Drawing S} (hn : G.IsNormal (j ⁻¹' discBd Δ)) {e : Set S}
    (he : e ∈ G.E) : e ⊆ j ⁻¹' discInt Δ ∨ Disjoint e (j ⁻¹' Δ) := by
  have hpc : IsPreconnected (j '' e) :=
    he.2.2.1.isConnected.isPreconnected.image _ hj.continuousOn
  have hdb : Disjoint (j '' e) (discBd Δ) := by
    rw [disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ hzb
    have hzU := he.2.1 hz
    exact hzU.2 (hn ⟨hzb, hzU.1⟩)
  rcases GM07.inside_or_off hpc hΔ.isClosed (hdb.mono_right (GM07.frontier_disc_subset hman hΔ))
    with h1 | h1
  · left
    intro y hy
    exact ⟨interior_subset (h1 (mem_image_of_mem j hy)),
      disjoint_left.mp hdb (mem_image_of_mem j hy)⟩
  · right
    rw [disjoint_left]
    intro y hy hyΔ
    exact h1 (mem_image_of_mem j hy) hyΔ

/-- **The outer piece.** The vertices and edges of `X` drawn outside the
interior of `Δ` form a graft whose roots are the old roots off `C` and the
vertices on `F`, and it embeds in `Σ`. -/
theorem exists_outer_graft {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    [Nonempty S] (hS : IsSurface S) {X : Graft α β} (gd : GraftDrawing X.G X.T S)
    {C F : Set S} (hC : C ∈ cuffs S) (hF : IsOArc F) (hFb : F ∩ bd S ⊆ C) (hn : gd.drawing.IsNormal F)
    {T : Type w} [TopologicalSpace T] {j : S → T} {D Δ : Set T}
    (hcap : GM07.IsCappedCuff C T j D) (hbT : bd T = j '' (bd S \ C))
    (hΔ : IsClosedDisc Δ) (hbΔ : discBd Δ = j '' F) (hDΔ : D ⊆ Δ) :
    ∃ A : Graft α β, A.G ≤ X.G ∧
      V(A.G) = {v ∈ V(X.G) | gd.iso.fv v ∉ j ⁻¹' discInt Δ} ∧
      E(A.G) = {e ∈ E(X.G) | Disjoint (gd.iso.fe e) (j ⁻¹' discInt Δ)} ∧
      A.T = {v ∈ V(X.G) | gd.iso.fv v ∈ (bd S \ C) ∪ F} ∧ EmbedsGraft S A := by
  classical
  have hT := hcap.isSurface
  have : T2Space T := hT.2.1
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hman := hT.2.2
  have hj := hcap.isEmbedding
  obtain ⟨x₀, hx₀⟩ : C.Nonempty := by
    obtain ⟨φ⟩ := (cuff_statement S hS).2.2 C hC
    exact ⟨(φ 1).1, (φ 1).2⟩
  obtain ⟨a₁, ha₁⟩ : F.Nonempty := by
    obtain ⟨φ⟩ := hF
    exact ⟨(φ 1).1, (φ 1).2⟩
  have hFpre : j ⁻¹' discBd Δ = F := by rw [hbΔ]; exact preimage_image_eq _ hj.injective
  have hbdT : ∀ x ∈ bd S \ C, j x ∈ bd T := fun x hx => hbT ▸ mem_image_of_mem j hx
  have hoffInt : ∀ {Y : Set T}, IsClosedDisc Y → ∀ x ∈ bd S \ C, j x ∉ discInt Y :=
    fun hY x hx hi => hbdT x hx (isInteriorPoint_of_mem_discInt hman hY hi)
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := by
    intro x hx
    by_contra hb
    have hxb : x ∈ bd T := hb
    rw [hbT] at hxb
    obtain ⟨y, hy, rfl⟩ := hxb
    have hyF : y ∈ F := by rw [← hFpre]; exact hx
    exact hy.2 (hFb ⟨hyF, hy.1⟩)
  obtain ⟨Y, hY, hΔY, -⟩ := exists_disc_around hman hΔ hint isOpen_univ (subset_univ _)
  have ha : j a₁ ∈ discBd Δ := hbΔ ▸ mem_image_of_mem j ha₁
  obtain ⟨Q, hQ⟩ := GM07.exists_path_in_collar hcap hΔ hDΔ hY hΔY hx₀ ha
  obtain ⟨h, Φ, hhc, -, hhi, hfix, -, -, hrange, himC, -⟩ :=
    GM07.exists_capped_push hcap hΔ hDΔ hY hΔY (GM07.discBd_subset_range hcap hDΔ) hx₀ ha Q hQ
  have hcl : IsClosedEmbedding h := hhc.isClosedEmbedding hhi
  set Z : Set S := j ⁻¹' discInt Δ with hZdef
  have hZo : IsOpen Z := (hΔ.isOpen_discInt hman).preimage hj.continuous
  have hnF : gd.drawing.IsNormal (j ⁻¹' discBd Δ) := hFpre ▸ hn
  have hedge : ∀ e ∈ gd.drawing.E, (∃ y ∈ e, y ∉ Z) → Disjoint e Z := by
    rintro e he ⟨y, hye, hyZ⟩
    rcases edge_subset_or_disjoint hman hj.continuous hΔ hnF he with h1 | h1
    · exact absurd (h1 hye) hyZ
    · exact h1.mono_right (preimage_mono (discInt_subset Δ))
  obtain ⟨J, hJ, hJU, hJV, hJE⟩ := exists_outside_drawing_edges hZo hedge
  have hhZ : ∀ x, h x ∉ Z := fun x hx => by
    have : h x ∈ j ⁻¹' (discInt Δ)ᶜ := hrange ▸ mem_range_self x
    exact this hx
  have hhC : ∀ x ∈ C, h x ∈ F := fun x hx => by
    rw [← hFpre, ← himC]
    exact mem_image_of_mem h hx
  have hhfix : ∀ x ∈ bd S \ C, h x = x := fun x hx => (hfix x (hoffInt hY x hx)).1
  have himbd : h '' bd S = (bd S \ C) ∪ F := by
    apply subset_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      by_cases hxC : x ∈ C
      · exact .inr (hhC x hxC)
      · rw [hhfix x ⟨hx, hxC⟩]
        exact .inl ⟨hx, hxC⟩
    · rintro y (hy | hy)
      · exact ⟨y, hy.1, hhfix y hy⟩
      · have hy' : y ∈ h '' C := by rw [himC, hFpre]; exact hy
        obtain ⟨x, hx, rfl⟩ := hy'
        exact ⟨x, GM07.connectedComponentIn_subset_of_cuff hC hx, rfl⟩
  have hoffZ : ∀ y ∈ (bd S \ C) ∪ F, y ∉ Z := by
    rintro y (hy | hy) hyZ
    · exact hoffInt hΔ y hy hyZ
    · exact hyZ.2 (hbΔ ▸ mem_image_of_mem j hy)
  obtain ⟨A, hAX, hAV, hAE, hAT, hAemb⟩ := exists_subgraft_embedsGraft gd hJ hcl
    (fun y hy => by rw [hrange]; rw [hJU] at hy; exact hy.2)
    (fun y hyU hyb => by
      rw [hJU] at hyU
      rw [hJV]
      refine ⟨?_, hyU.2⟩
      by_cases hyC : y ∈ C
      · exact hn ⟨hhC y hyC, hyU.1⟩
      · have h1 := hhfix y ⟨hyb, hyC⟩
        rw [h1] at hyU ⊢
        exact gd.isProper ⟨hyb, hyU.1⟩)
    {v ∈ V(X.G) | gd.iso.fv v ∈ (bd S \ C) ∪ F}
    (fun v hv => ⟨hv.1, by rw [hJV]; exact ⟨(show gd.iso.fv v ∈ gd.drawing.V from Iso.fv_mem (a := gd.iso) hv.1), hoffZ _ hv.2⟩⟩)
    (fun v hv _ => by rw [himbd]; exact ⟨fun h => ⟨hv, h⟩, fun h => h.2⟩)
  refine ⟨A, hAX, ?_, ?_, hAT, hAemb⟩
  · rw [hAV, hJV]
    ext v
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (show gd.iso.fv v ∈ gd.drawing.V from Iso.fv_mem (a := gd.iso) h.1), h.2⟩⟩
  · rw [hAE, hJE]
    ext e
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, (show gd.iso.fe e ∈ gd.drawing.E from Iso.fe_mem (a := gd.iso) h.1), h.2⟩⟩

end GraphMinor.GM08
