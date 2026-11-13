module

public import GraphMinor.GM08.Section18SplitOuter
public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section18Push
import GraphMinor.GM08.Section18NestedCap
import GraphMinor.GM08.Section12Pullback
import GraphMinor.GM08.Section12Subspace
import GraphMinor.GM07.CollarPush
import GraphMinor.GM07.Section9DiscSphere
import GraphMinor.GM11.GlueDiscs
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM12.Section3SubspaceArcs
import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM16.DrawingGraphPaths
import GraphMinor.GM19.FeatureOrient
import GraphMinor.GM19.FragmentCollapse
import GraphMinor.GM19.RadialExists
import GraphMinor.Surface.Collar
import GraphMinor.Surface.DiscMerge

/-!
# The inner piece of the split step

Let `F` be a `Γ`-normal `O`-arc that bounds a disc `Δ` of `Σ + Ĉ` around the
pasted disc `D` of the cuff `C`. The part of `Γ` in `Δ` lies between `C` and
`F`, and it is a tubular graft whose roots are its vertices on `C ∪ F`
(`exists_inner_graft`).

To frame it, take a closed disc `Y` with `Δ` in its interior. The interior of
`Y` is an open disc, so adding one point makes it a sphere `Z`. In `Z` remove
the interior of a small disc `P₁` inside `D`, and the interior of the disc
`P₂` on the other side of `F`. What is left is a cylinder `Q`
(`exists_nestedCap`), and the images of `C` and `F` are nested hoops of `Q`
(`CylinderSphereCap.isHoop_of_discs`). The part of `Γ` in `Δ` moves into `Q`
(`exists_push_drawing`) and lies between these hoops. This is the graft in
`ℬ(2k - 1)` in case (ii) of the proof of (18.3), page 287.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u v w

/-- **The inner piece.** The vertices and edges of `X` drawn in `Δ` form a
tubular graft whose roots are the vertices on `C ∪ F`. -/
theorem exists_inner_graft {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    [Nonempty S] (hS : IsSurface S) {X : Graft α β} (gd : GraftDrawing X.G X.T S)
    {C F : Set S} (hC : C ∈ cuffs S) (hFb : F ∩ bd S ⊆ C) (hn : gd.drawing.IsNormal F)
    {T : Type w} [TopologicalSpace T] {j : S → T} {D Δ : Set T}
    (hcap : GM07.IsCappedCuff C T j D) (hbT : bd T = j '' (bd S \ C))
    (hΔ : IsClosedDisc Δ) (hbΔ : discBd Δ = j '' F) (hDΔ : D ⊆ Δ)
    (hne : (gd.drawing.V ∩ C).Nonempty) :
    ∃ B : Graft α β, B.G ≤ X.G ∧
      V(B.G) = {v ∈ V(X.G) | gd.iso.fv v ∈ j ⁻¹' Δ} ∧
      E(B.G) = {e ∈ E(X.G) | Disjoint (gd.iso.fe e) (j ⁻¹' Δ)ᶜ} ∧
      B.T = {v ∈ V(X.G) | gd.iso.fv v ∈ C ∪ F} ∧ IsTubularGraft B := by
  classical
  have hT := hcap.isSurface
  have : T2Space T := hT.2.1
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hman := hT.2.2
  have hj := hcap.isEmbedding
  have hD := hcap.isClosedDisc
  have hFpre : j ⁻¹' discBd Δ = F := by rw [hbΔ]; exact preimage_image_eq _ hj.injective
  have hCpre : j ⁻¹' discBd D = C := by
    rw [hcap.discBd_eq]; exact preimage_image_eq _ hj.injective
  have hjD : ∀ x, j x ∈ D → j x ∈ discBd D := fun x hx => by
    rw [hcap.discBd_eq, ← hcap.inter_eq]; exact ⟨mem_range_self x, hx⟩
  have hCR : ∀ x ∈ C, j x ∈ Δ := fun x hx =>
    hDΔ (discBd_subset D (hcap.discBd_eq ▸ mem_image_of_mem j hx))
  have hFR : ∀ x ∈ F, j x ∈ Δ := fun x hx => discBd_subset Δ (hbΔ ▸ mem_image_of_mem j hx)
  -- the part of the drawing in `Δ`
  set R : Set S := j ⁻¹' Δ with hRdef
  have hRc : IsClosed R := hΔ.isClosed.preimage hj.continuous
  have hnF : gd.drawing.IsNormal (j ⁻¹' discBd Δ) := hFpre ▸ hn
  have hedge : ∀ e ∈ gd.drawing.E, (∃ y ∈ e, y ∉ Rᶜ) → Disjoint e Rᶜ := by
    rintro e he ⟨y, hye, hyR⟩
    rcases edge_subset_or_disjoint hman hj.continuous hΔ hnF he with h1 | h1
    · rw [disjoint_compl_right_iff_subset]
      exact h1.trans (preimage_mono (discInt_subset Δ))
    · exact absurd (not_not.mp hyR) (disjoint_left.mp h1 hye)
  obtain ⟨J, hJ, hJU, hJV, hJE⟩ := exists_outside_drawing_edges hRc.isOpen_compl hedge
  rw [compl_compl] at hJU hJV
  obtain ⟨G', hG'X, hG'V₀, hG'E₀, hbij⟩ :=
    exists_subgraph_of_iso gd.iso (GM16.toGraph_le_of_isSubdrawing hJ)
  have hG'V : V(G') = {v ∈ V(X.G) | gd.iso.fv v ∈ J.V} := hG'V₀
  have hG'E : E(G') = {e ∈ E(X.G) | gd.iso.fe e ∈ J.E} := hG'E₀
  -- a sphere around `Δ`
  have hint : ∀ x ∈ discBd Δ, IsInteriorPoint x := by
    intro x hx
    by_contra hb
    have hxb : x ∈ bd T := hb
    rw [hbT] at hxb
    obtain ⟨y, hy, rfl⟩ := hxb
    have hyF : y ∈ F := by rw [← hFpre]; exact hx
    exact hy.2 (hFb ⟨hyF, hy.1⟩)
  obtain ⟨Y, hY, hΔY, -⟩ := exists_disc_around hman hΔ hint isOpen_univ (subset_univ _)
  set A := discInt Y with hAdef
  have hAo : IsOpen A := hY.isOpen_discInt hman
  have hΔA : Δ ⊆ A := hΔY
  have hsph : IsSphere (OnePoint A) := GM11.isSphere_onePoint (GM19.isOpenDisc_discInt hman hY)
  obtain ⟨hZs, hZc⟩ := GM11.IsSphere.isClosedSurface hsph
  have : T2Space (OnePoint A) := hZs.2.1
  have : ConnectedSpace (OnePoint A) := hZc
  have hmanZ : ∀ x : OnePoint A, IsManifoldPoint x := fun x => (hZs.2.2 x).isManifoldPoint
  set κ := GM11.collapse A with hκdef
  have hκc : Continuous κ := GM11.continuous_collapse hAo
  have hκi : InjOn κ A := fun x hx y hy he => by
    rw [hκdef, GM11.collapse_of_mem hx, GM11.collapse_of_mem hy] at he
    exact congrArg Subtype.val (OnePoint.coe_injective he)
  have hκΔ : InjOn κ Δ := hκi.mono hΔA
  -- the discs of the sphere
  have hκdisc : ∀ {K : Set T}, IsClosedDisc K → K ⊆ Δ →
      IsClosedDisc (κ '' K) ∧ discBd (κ '' K) = κ '' discBd K ∧
        discInt (κ '' K) = κ '' discInt K := by
    intro K hK hKΔ
    obtain ⟨h1, h2⟩ := GM19.isClosedDisc_image_injOn hK hκc.continuousOn (hκΔ.mono hKΔ)
    refine ⟨h1, h2, ?_⟩
    change κ '' K \ discBd (κ '' K) = κ '' (K \ discBd K)
    rw [h2, (hκΔ.mono hKΔ).image_sdiff_subset (discBd_subset K)]
  obtain ⟨x₀, hx₀⟩ := hD.nonempty_discInt
  obtain ⟨D₀, hD₀, hD₀D, -⟩ := GM19.exists_disc_around_interior
    (isInteriorPoint_of_mem_discInt hman hD hx₀) (hD.isOpen_discInt hman) hx₀
  have hD₀Δ : D₀ ⊆ Δ := hD₀D.trans ((discInt_subset D).trans hDΔ)
  obtain ⟨hP₁, -, -⟩ := hκdisc hD₀ hD₀Δ
  obtain ⟨hΔ', hbΔ', hiΔ'⟩ := hκdisc hΔ subset_rfl
  obtain ⟨hD', hbD', hiD'⟩ := hκdisc hD hDΔ
  obtain ⟨P₂, hP₂, hbP₂, hP₂eq, hiP₂⟩ := GM07.exists_compl_disc_in_sphere hsph hΔ'
  obtain ⟨E₂, hE₂, hbE₂, hE₂eq, -⟩ := GM07.exists_compl_disc_in_sphere hsph hD'
  have hiDΔ : discInt D ⊆ discInt Δ := discInt_mono hman hD hDΔ
  have hP₁int : κ '' D₀ ⊆ discInt (κ '' Δ) := by
    rw [hiΔ']; exact image_mono (hD₀D.trans hiDΔ)
  have hdisj : Disjoint (κ '' D₀) P₂ := by
    rw [hP₂eq, disjoint_compl_right_iff_subset]; exact hP₁int
  set Q := GM12.discComplement ![κ '' D₀, P₂] with hQdef
  obtain ⟨hcyl, cap, e, hje, hcD₁, hcD₂⟩ := exists_nestedCap hZs hsph hP₁ hP₂ hdisj
  have hmemQ := GM07.mem_discComplement_iff hZs (![κ '' D₀, P₂] : Fin 2 → Set (OnePoint A))
    (by intro i; fin_cases i <;> assumption)
    (by
      intro i k hik
      fin_cases i <;> fin_cases k
      · exact (hik rfl).elim
      · exact hdisj
      · exact hdisj.symm
      · exact (hik rfl).elim)
  -- the image of the part of `Δ` in `S`
  set φ : S → OnePoint A := fun x => κ (j x) with hφdef
  have hφc : Continuous φ := hκc.comp hj.continuous
  have hφi : InjOn φ R := fun x hx y hy h => hj.injective (hκΔ hx hy h)
  have hφin : ∀ x ∈ R, φ x ∈ κ '' Δ ∧ φ x ∉ κ '' discInt D := by
    intro x hx
    refine ⟨mem_image_of_mem κ hx, ?_⟩
    rintro ⟨y, hy, hyx⟩
    have hyΔ : y ∈ Δ := hDΔ (discInt_subset D hy)
    have : y = j x := hκΔ hyΔ hx hyx
    subst this
    exact hy.2 (hjD x hy.1)
  have hφQ : ∀ x ∈ R, φ x ∈ Q := by
    intro x hx
    refine (hmemQ _).mpr fun i hi => ?_
    fin_cases i
    · have h := (hκdisc hD₀ hD₀Δ).2.2
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hi
      rw [h] at hi
      exact (hφin x hx).2 (image_mono ((discInt_subset D₀).trans hD₀D) hi)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hi
      rw [hiP₂] at hi
      exact hi (hφin x hx).1
  -- push the part in `Δ` into the sphere, and read it in the cylinder `Q`
  have hJUR : J.U ⊆ R := fun x hx => by rw [hJU] at hx; exact hx.2
  have hJne : J.U.Nonempty := by
    obtain ⟨x, hxV, hxC⟩ := hne
    exact ⟨x, by rw [hJU]; exact ⟨gd.drawing.V_subset_U hxV, hCR x hxC⟩⟩
  obtain ⟨D', hD'U, hD'V, i, hi⟩ := exists_push_drawing J hJne hφc (hφi.mono hJUR)
  have hD'Q : D'.U ⊆ Q := by
    rw [hD'U]
    rintro _ ⟨x, hx, rfl⟩
    exact hφQ x (hJUR hx)
  have hQc : IsClosed Q := isClosed_closure
  set D'' := GM12.drawingInSubspace D' Q hD'Q with hD''def
  let i₃ := (isGraphBij_drawingInSubspace D' hQc hD'Q).toIso
  -- the images of `C` and `F` are nested hoops of `Q`
  have hCsub : C ⊆ R := fun x hx => hCR x hx
  have hFsub : F ⊆ R := fun x hx => hFR x hx
  have hbDC : discBd (κ '' D) = φ '' C := by
    rw [hbD', hcap.discBd_eq, image_image]
  have hbΔF : discBd (κ '' Δ) = φ '' F := by
    rw [hbΔ', hbΔ, image_image]
  have hφmem : ∀ x ∈ R, ∀ P ⊆ R, φ x ∈ φ '' P ↔ x ∈ P := fun x hx P hP =>
    (hφi.mono subset_rfl).mem_image_iff hP hx
  have hsubQ : ∀ P ⊆ R, φ '' P ⊆ Q := by
    rintro P hP _ ⟨x, hx, rfl⟩
    exact hφQ x (hP hx)
  have hcupK : ∀ K : Set (OnePoint A), K ∪ (discInt K)ᶜ = univ := fun K =>
    eq_univ_of_forall fun z => by
      by_cases hz : z ∈ K
      · exact .inl hz
      · exact .inr fun h => hz h.1
  have hcapK : ∀ K : Set (OnePoint A), K ∩ (discInt K)ᶜ = discBd K := fun K => by
    ext z
    constructor
    · rintro ⟨hz, hz'⟩
      by_contra hb
      exact hz' ⟨hz, hb⟩
    · intro hz
      exact ⟨discBd_subset K hz, fun h => h.2 hz⟩
  set H₁ : Set Q := Subtype.val ⁻¹' discBd (κ '' D) with hH₁def
  set H₂ : Set Q := Subtype.val ⁻¹' discBd (κ '' Δ) with hH₂def
  have hsub₁ : discBd (κ '' D) ⊆ Q := hbDC ▸ hsubQ C hCsub
  have hsub₂ : discBd (κ '' Δ) ⊆ Q := hbΔF ▸ hsubQ F hFsub
  have him₁ : (Subtype.val : Q → OnePoint A) '' H₁ = discBd (κ '' D) :=
    image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub₁)
  have him₂ : (Subtype.val : Q → OnePoint A) '' H₂ = discBd (κ '' Δ) :=
    image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hsub₂)
  have hiDΔ' : discInt (κ '' D) ⊆ discInt (κ '' Δ) := by
    rw [hiD', hiΔ']; exact image_mono hiDΔ
  obtain ⟨hH₁, hd₁₁, hd₂₁⟩ := cap.isHoop_of_discs hcyl.1 e hje hcD₁ hcD₂
    (GM12.isOArc_subtype_preimage hsub₁ hD'.isOArc_discBd) hD' hE₂ him₁.symm
    (by rw [hbE₂]; exact him₁.symm) (by rw [hE₂eq]; exact hcupK _) (by rw [hE₂eq, hcapK]; exact him₁.symm)
    (image_mono (hD₀D.trans (discInt_subset D)))
    (by rw [hP₂eq, hE₂eq]; exact compl_subset_compl.mpr hiDΔ')
  obtain ⟨hH₂, hd₁₂, hd₂₂⟩ := cap.isHoop_of_discs hcyl.1 e hje hcD₁ hcD₂
    (GM12.isOArc_subtype_preimage hsub₂ hΔ'.isOArc_discBd) hΔ' hP₂ him₂.symm
    (by rw [hbP₂]; exact him₂.symm) (by rw [hP₂eq]; exact hcupK _) (by have h := hcapK (κ '' Δ); rw [← hP₂eq] at h; rw [h]; exact him₂.symm)
    (image_mono hD₀Δ) subset_rfl
  have hle : cap.disc₁ hcyl.1 hH₁ ⊆ cap.disc₁ hcyl.1 hH₂ := by
    rw [hd₁₁, hd₁₂]; exact image_mono (image_mono hDΔ)
  have hlam : AreLaminarHoops H₁ H₂ := (cap.areLaminarHoops_iff hcyl hH₁ hH₂).mpr (.inl hle)
  have hbetween := cap.cylinderBetween_eq_of_disc₁_subset hcyl hH₁ hH₂ hle
  -- points of the drawing in `Q`
  have hD''U : ∀ q : Q, q ∈ D''.U → ∃ x ∈ J.U, φ x = q.1 := fun q hq => by
    rw [hD''def, GM12.drawingInSubspace_U, mem_preimage, hD'U] at hq
    exact hq
  have hnormal : ∀ P ⊆ R, gd.drawing.IsNormal P → ∀ q : Q, q.1 ∈ φ '' P → q ∈ D''.U →
      q ∈ D''.V := by
    intro P hP hnP q hqP hqU
    obtain ⟨x, hxU, hxq⟩ := hD''U q hqU
    have hxP : x ∈ P := (hφmem x (hJUR hxU) P hP).mp (hxq ▸ hqP)
    have hxU' : x ∈ gd.drawing.U := by rw [hJU] at hxU; exact hxU.1
    have hxV : x ∈ J.V := by rw [hJV]; exact ⟨hnP ⟨hxP, hxU'⟩, hJUR hxU⟩
    rw [hD''def, GM12.drawingInSubspace_V, mem_preimage, hD'V, ← hxq]
    exact mem_image_of_mem φ hxV
  have hCnormal : gd.drawing.IsNormal C := fun x hx =>
    gd.isProper ⟨GM07.connectedComponentIn_subset_of_cuff hC hx.1, hx.2⟩
  let τ : Tube Q := {
    Γ := D''
    F₁ := H₁
    F₂ := H₂
    isCylinder := hcyl
    laminar := hlam
    isNormal_F₁ := fun q hq => hnormal C hCsub hCnormal q (hbDC ▸ hq.1) hq.2
    isNormal_F₂ := fun q hq => hnormal F hFsub hn q (hbΔF ▸ hq.1) hq.2
    U_subset := by
      rw [hbetween, hd₁₂, hd₂₁, hE₂eq]
      intro q hq
      obtain ⟨x, hxU, hxq⟩ := hD''U q hq
      rw [mem_preimage, hje]
      refine ⟨mem_image_of_mem e ?_, mem_image_of_mem e ?_⟩
      · rw [← hxq]; exact (hφin x (hJUR hxU)).1
      · rw [← hxq, hiD']; exact (hφin x (hJUR hxU)).2 }
  -- the graft and its framing
  have hTV : {v ∈ V(X.G) | gd.iso.fv v ∈ C ∪ F} ⊆ V(G') := by
    intro v hv
    rw [hG'V, hJV]
    refine ⟨hv.1, (show gd.iso.fv v ∈ gd.drawing.V from Iso.fv_mem (a := gd.iso) hv.1), ?_⟩
    rcases hv.2 with h | h
    · exact hCsub h
    · exact hFsub h
  let B : Graft α β := ⟨G', {v ∈ V(X.G) | gd.iso.fv v ∈ C ∪ F}, hTV,
    ⟨X.finite_G.1.subset hG'X.vertexSet_mono, X.finite_G.2.subset hG'X.edgeSet_mono⟩⟩
  have hinv : ∀ (g : E(D'.toGraph)) (y z : V(D'.toGraph)),
      D'.toGraph.IsLink g.1 y.1 z.1 ↔
        D''.toGraph.IsLink (i₃.edgeEquiv.symm g).1 (i₃.vertexEquiv.symm y).1
          (i₃.vertexEquiv.symm z).1 := by
    intro g y z
    have h := i₃.isLink_iff (i₃.edgeEquiv.symm g) (i₃.vertexEquiv.symm y) (i₃.vertexEquiv.symm z)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  let a : GraphMinor.Iso B.G τ.Γ.toGraph := {
    vertexEquiv := hbij.toIso.vertexEquiv.trans (i.vertexEquiv.trans i₃.vertexEquiv.symm)
    edgeEquiv := hbij.toIso.edgeEquiv.trans (i.edgeEquiv.trans i₃.edgeEquiv.symm)
    isLink_iff := fun g y z => (hbij.toIso.isLink_iff g y z).trans
      ((i.isLink_iff _ _ _).trans (hinv _ _ _)) }
  have ha : ∀ v : V(B.G), ((a.vertexEquiv v).1 : OnePoint A) = φ (gd.iso.fv v.1) := by
    intro v
    have h1 : ((i₃.vertexEquiv (i₃.vertexEquiv.symm (i.vertexEquiv
        (hbij.toIso.vertexEquiv v)))).1 : OnePoint A) =
        (i.vertexEquiv (hbij.toIso.vertexEquiv v)).1 := by rw [Equiv.apply_symm_apply]
    change ((i₃.vertexEquiv.symm (i.vertexEquiv (hbij.toIso.vertexEquiv v))).1 : OnePoint A) = _
    refine Eq.trans h1 ?_
    rw [hi]
    rfl
  refine ⟨B, hG'X, ?_, ?_, rfl, IsTubularGraft.of_framing (τ := τ) ⟨⟨a, fun v => ?_⟩⟩⟩
  · rw [hG'V, hJV]
    ext v
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, (show gd.iso.fv v ∈ gd.drawing.V from Iso.fv_mem (a := gd.iso) h.1), h.2⟩⟩
  · rw [hG'E, hJE]
    ext g
    exact ⟨fun h => ⟨h.1, h.2.2⟩,
      fun h => ⟨h.1, (show gd.iso.fe g ∈ gd.drawing.E from Iso.fe_mem (a := gd.iso) h.1), h.2⟩⟩
  · have hvB : v.1 ∈ V(X.G) := hG'X.vertexSet_mono v.2
    have hvR : gd.iso.fv v.1 ∈ R := by
      have h : v.1 ∈ {v ∈ V(X.G) | gd.iso.fv v ∈ J.V} := hG'V ▸ v.2
      rw [hJV] at h
      exact h.2.2
    have e1 : (a.vertexEquiv v).1 ∈ H₁ ↔ gd.iso.fv v.1 ∈ C := by
      change ((a.vertexEquiv v).1 : OnePoint A) ∈ discBd (κ '' D) ↔ _
      rw [ha, hbDC]
      exact hφmem _ hvR C hCsub
    have e2 : (a.vertexEquiv v).1 ∈ H₂ ↔ gd.iso.fv v.1 ∈ F := by
      change ((a.vertexEquiv v).1 : OnePoint A) ∈ discBd (κ '' Δ) ↔ _
      rw [ha, hbΔF]
      exact hφmem _ hvR F hFsub
    change (a.vertexEquiv v).1 ∈ H₁ ∪ H₂ ↔ v.1 ∈ {v ∈ V(X.G) | gd.iso.fv v ∈ C ∪ F}
    rw [mem_union, e1, e2]
    exact ⟨fun h => ⟨hvB, h⟩, fun h => h.2⟩

end GraphMinor.GM08
