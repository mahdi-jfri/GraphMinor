module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Cited
public import GraphMinor.GM07.Section9
public import GraphMinor.GM07.Bridge
public import GraphMinor.GM07.CuffSlide
public import GraphMinor.GM09.DiscDrawing
public import GraphMinor.GM19.Section6a
public import GraphMinor.GM19.FragmentCut
public import GraphMinor.GM21.Section4Tangle
public import GraphMinor.Planar.Grid
import GraphMinor.GM07.Section9CoreProved
import GraphMinor.GM19.Section6aProved

/-!
# Graph Minors III, Section 6: Surfaces of Higher Genus

This file formalizes Section 6 of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64 (page 64):
- `theorem_6_1`, Theorem (6.1): for every surface $S$ of genus $g > 0$ and every graph $H$
  embedded in $S$, there is a number $k$ such that for every graph $G$ with no minor isomorphic
  to $H$ that can be embedded in $S$, there exists $X \subseteq V(G)$ with $|X| \le k$ such that
  $G \setminus X$ can be embedded on a surface whose components have genus $< g$.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Topology Classical
open Graph
open GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM19 GraphMinor.GM21 GraphMinor.Planar

universe u₁ v₁ u₂ v₂

/-! ## Transporting a `GraphDrawing` along an injective continuous map on `D.U` -/

/-- A map `ι : S → Z` that is continuous and injective on `D.U` induces a graph isomorphism
between `D.toGraph` and `(mapDrawingInjOn D ι hcont hinj).toGraph`. -/
noncomputable def isoMapDrawingInjOn {S Z : Type} [TopologicalSpace S] [CompactSpace S]
    [T2Space S] [TopologicalSpace Z] [T2Space Z]
    (D : Surface.Drawing S) (ι : S → Z)
    (hcont : ContinuousOn ι D.U) (hinj : InjOn ι D.U) :
    Iso D.toGraph (mapDrawingInjOn D ι hcont hinj).toGraph := by
  let D' := mapDrawingInjOn D ι hcont hinj
  have hinjV : InjOn ι D.V := hinj.mono D.V_subset_U
  have hinjE : InjOn (image ι) D.E := by
    intro e₁ he₁ e₂ he₂ heq
    have h₁ : e₁ ⊆ D.U := he₁.2.1.trans sdiff_subset
    have h₂ : e₂ ⊆ D.U := he₂.2.1.trans sdiff_subset
    ext x
    constructor
    · intro hx₁
      have : ι x ∈ ι '' e₂ := heq ▸ mem_image_of_mem ι hx₁
      obtain ⟨y, hy₂, hyx⟩ := this
      exact hinj (h₂ hy₂) (h₁ hx₁) hyx ▸ hy₂
    · intro hx₂
      have : ι x ∈ ι '' e₁ := heq.symm ▸ mem_image_of_mem ι hx₂
      obtain ⟨y, hy₁, hyx⟩ := this
      exact hinj (h₁ hy₁) (h₂ hx₂) hyx ▸ hy₁
  have hE_eq : D'.E = (image ι) '' D.E := mapDrawingInjOn_E D ι hcont hinj
  refine
    { vertexEquiv := Equiv.Set.imageOfInjOn ι D.V hinjV
      edgeEquiv :=
        (Equiv.Set.imageOfInjOn (image ι) D.E hinjE).trans
          (Equiv.subtypeEquivRight fun _ ↦ hE_eq.symm ▸ Iff.rfl)
      isLink_iff := ?_ }
  rintro ⟨e, he⟩ ⟨u, hu⟩ ⟨v, hv⟩
  change (e ∈ D.E ∧ u ∈ D.V ∧ v ∈ D.V ∧ closure e ∩ D.V = {u, v}) ↔
    (ι '' e ∈ D'.E ∧ ι u ∈ D'.V ∧ ι v ∈ D'.V ∧ closure (ι '' e) ∩ D'.V = {ι u, ι v})
  have he_sub : e ⊆ D.U := he.2.1.trans sdiff_subset
  have hcl_sub : closure e ⊆ D.U := D.isClosed_U.closure_subset_iff.mpr he_sub
  have hcomp : IsCompact (ι '' closure e) :=
    isClosed_closure.isCompact.image_of_continuousOn (hcont.mono hcl_sub)
  have hcl_eq : closure (ι '' e) = ι '' closure e := by
    apply Subset.antisymm (closure_minimal (image_mono subset_closure) hcomp.isClosed)
    rintro _ ⟨x, hx, rfl⟩
    exact ((hcont x (hcl_sub hx)).mono he_sub).mem_closure hx (mapsTo_image ι e)
  have hcap_eq : closure (ι '' e) ∩ D'.V = ι '' (closure e ∩ D.V) := by
    change closure (ι '' e) ∩ (ι '' D.V) = ι '' (closure e ∩ D.V)
    rw [hcl_eq]
    ext z
    constructor
    · rintro ⟨⟨x, hxcl, hxz⟩, ⟨y, hyV, hyz⟩⟩
      have hxy : y = x := hinj (D.V_subset_U hyV) (hcl_sub hxcl) (hyz.trans hxz.symm)
      exact ⟨x, ⟨hxcl, hxy ▸ hyV⟩, hxz⟩
    · rintro ⟨x, ⟨hxcl, hxV⟩, rfl⟩
      exact ⟨mem_image_of_mem ι hxcl, mem_image_of_mem ι hxV⟩
  constructor
  · rintro ⟨_, _, _, hcap⟩
    refine ⟨hE_eq ▸ mem_image_of_mem (image ι) he, mem_image_of_mem ι hu,
      mem_image_of_mem ι hv, ?_⟩
    rw [hcap_eq, hcap, image_pair]
  · rintro ⟨_, _, _, hcap⟩
    refine ⟨he, hu, hv, ?_⟩
    rw [hcap_eq] at hcap
    ext x
    constructor
    · intro hx
      have hιx : ι x ∈ ({ι u, ι v} : Set Z) := hcap ▸ mem_image_of_mem ι hx
      rcases hιx with hιu | hιv
      · exact Or.inl (hinj (D.V_subset_U hx.2) (D.V_subset_U hu) hιu)
      · rw [mem_singleton_iff] at hιv
        exact Or.inr (mem_singleton_iff.mpr (hinj (D.V_subset_U hx.2) (D.V_subset_U hv) hιv))
    · intro hx
      have hιx : ι x ∈ ι '' (closure e ∩ D.V) := by
        rw [hcap]
        rcases hx with rfl | hxv
        · exact Or.inl rfl
        · rw [mem_singleton_iff] at hxv
          subst hxv
          exact Or.inr (mem_singleton _)
      obtain ⟨y, hy, hyx⟩ := hιx
      have hyx' : y = x := by
        rcases hx with rfl | hxv
        · exact hinj (D.V_subset_U hy.2) (D.V_subset_U hu) hyx
        · rw [mem_singleton_iff] at hxv
          subst hxv
          exact hinj (D.V_subset_U hy.2) (D.V_subset_U hv) hyx
      exact hyx' ▸ hy

/-! ## Theorem (6.1) -/

/-- Graph Minors III, (6.1) (page 64):
> (6.1) *Let $S$ be a surface of genus $g > 0$, and let $H$ be a graph which may be embedded in $S$.
> Then there is a number $k$ with the following property. For every graph $G$ which has no minor
> isomorphic to $H$ but which can be embedded in $S$, there exists $X \subseteq V(G)$ with $|X| \le k$
> such that $G \setminus X$ can be embedded on a surface of genus $<g$.*

Here `S` is a closed surface homeomorphic to `SurfaceModel a b 0` of Euler genus
`g = 2 * a + b > 0` (and orientable genus `a` when `b = 0`). Deleting the `≤ k` vertices of `G`
lying on a `Γ_G.drawing`-normal non-null-homotopic `O`-arc `F` and cutting `S` along `F` via
`GM19.exists_cut_simpler` embeds `GM09.deleteVertices G X` in a surface `S'` each of whose connected
components `C ∈ spaceComponents S'` is simpler than `S` and has genus `2 * a' + b' < g`
(and `a' < a` when `b = 0`). -/
theorem theorem_6_1_proof {α₁ : Type u₁} {β₁ : Type v₁}
    (S : Type) [TopologicalSpace S] (hS : IsSurface S)
    (a b g : ℕ) (hg : 2 * a + b = g) (hg_pos : 0 < g)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (H : Graph α₁ β₁) (hH : Nonempty (GraphDrawing H S)) :
    ∃ k : ℕ, ∀ {α₂ : Type u₂} {β₂ : Type v₂} (G : Graph α₂ β₂),
      ¬ IsIsoMinor H G → Nonempty (GraphDrawing G S) →
      ∃ X ⊆ V(G), X.ncard ≤ k ∧
        ∃ (S' : Type) (_ : TopologicalSpace S'),
          IsSurface S' ∧
          Nonempty (GraphDrawing (GM09.deleteVertices G X) S') ∧
          ∀ C ∈ spaceComponents S',
            IsSimplerThan C S ∧
            ∃ a' b' c' : ℕ,
              Nonempty (C ≃ₜ SurfaceModel a' b' c') ∧
              (b = 0 → b' = 0 ∧ a' < a) ∧ 2 * a' + b' < g := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  obtain ⟨hom⟩ := he
  have : ConnectedSpace (SurfaceModel a b 0) := (isSurface_model a b 0).2
  have : ConnectedSpace S := hom.symm.surjective.connectedSpace hom.symm.continuous
  have : Nonempty S := inferInstance
  obtain ⟨_, hbd⟩ := bd_eq_empty_of_homeomorph_surfaceModel_zero ⟨hom⟩
  have hclS : IsClosedSurface S := GM07.isClosedSurface_of_bd_eq_empty hS hbd
  have hab : a + b ≥ 1 := by omega
  have hsph : ¬ IsSphere S := by
    rintro ⟨g_sph⟩
    obtain ⟨g_mod⟩ := GM19.isSphere_model
    have hcrit := (modelCriterion.2 a b 0 0 0 0).mp ⟨hom.symm.trans (g_sph.trans g_mod.symm)⟩
    omega
  obtain ⟨Γ_H⟩ := hH
  let DH : SurfaceDigraph S := toSurfaceDigraph Γ_H.drawing
  obtain ⟨N, hN⟩ :=
    GM07.theorem_9_2_proof hS a b hab ⟨hom⟩ DH
  refine ⟨N, fun {α₂ β₂} G hNoMinor ⟨Γ_G⟩ ↦ ?_⟩
  let DG : SurfaceDigraph S := toSurfaceDigraph Γ_G.drawing
  have hrep_lt : GM19.Drawing.rep Γ_G.drawing < (N : ℕ∞) := by
    by_contra hge
    have hrep_ge : (N : ℕ∞) ≤ GM19.Drawing.rep Γ_G.drawing := le_of_not_gt hge
    have hα_ge : N ≤ alpha Γ_G.drawing :=
      le_alpha_of_le_rep hS hbd hsph Γ_G.drawing hrep_ge
    have hDigMinor : IsDigraphMinor DH DG := hN DG hα_ge
    have hDrawMinor : IsIsoMinor Γ_H.drawing.toGraph Γ_G.drawing.toGraph :=
      isIsoMinor_of_isDigraphMinor hDigMinor
    exact hNoMinor ((Iso.isIsoMinor_congr Γ_H.iso Γ_G.iso).mpr hDrawMinor)
  change sInf {n : ℕ∞ | ∃ F : Set S,
    IsOArc F ∧ Γ_G.drawing.IsNormal F ∧ ¬ IsNullHomotopicOArc F ∧
      n = ((F ∩ Γ_G.drawing.V).ncard : ℕ)} < (N : ℕ∞) at hrep_lt
  rw [sInf_lt_iff] at hrep_lt
  obtain ⟨n₀, ⟨F, hF, hnorm, hnull, rfl⟩, hcard_lt⟩ := hrep_lt
  have hcard_le : (F ∩ Γ_G.drawing.V).ncard ≤ N := by
    have : (F ∩ Γ_G.drawing.V).ncard < N := WithTop.coe_lt_coe.mp hcard_lt
    omega
  let X : Set α₂ := {v ∈ V(G) | ∃ hv : v ∈ V(G), (Γ_G.iso.vertexEquiv ⟨v, hv⟩).1 ∈ F}
  have hX_sub : X ⊆ V(G) := fun _ hv ↦ hv.1
  have hX_card : X.ncard ≤ N := by
    let f : ↥X → ↥(F ∩ Γ_G.drawing.V) := fun v ↦
      ⟨(Γ_G.iso.vertexEquiv ⟨v.1, v.2.1⟩).1,
        v.2.2.choose_spec, (Γ_G.iso.vertexEquiv ⟨v.1, v.2.1⟩).2⟩
    have hf_inj : Function.Injective f := by
      intro u v huv
      have hval : (f u).1 = (f v).1 := congrArg Subtype.val huv
      have heq : (⟨u.1, u.2.1⟩ : V(G)) = ⟨v.1, v.2.1⟩ :=
        Γ_G.iso.vertexEquiv.injective (Subtype.ext hval)
      exact Subtype.ext (Subtype.mk.inj heq)
    have hfin_FV : (F ∩ Γ_G.drawing.V).Finite := Γ_G.drawing.finite_V.subset inter_subset_right
    have : Finite ↥(F ∩ Γ_G.drawing.V) := hfin_FV.to_subtype
    have hle := Nat.card_le_card_of_injective f hf_inj
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hle
    exact hle.trans hcard_le
  obtain ⟨Γ', hΓ'_U, _, hΓ'_sub, _, _, _, _⟩ :=
    GraphDrawing.ofSubgraph Γ_G (GM09.deleteVertices_le G X)
  have hDU : Γ'.drawing.U ⊆ Fᶜ := by
    intro x hxU hxF
    have hxV_G : x ∈ Γ_G.drawing.V := hnorm ⟨hxF, hΓ'_sub.U_subset hxU⟩
    rw [hΓ'_U] at hxU
    rcases hxU with hxV' | hxE'
    · obtain ⟨v, hv_del, hvG, rfl⟩ := mem_iUnion₂.mp hxV'
      exact hv_del.2 ⟨hvG, hvG, hxF⟩
    · obtain ⟨e, he_del, hxe⟩ := mem_iUnion₂.mp hxE'
      have heG : e ∈ E(G) := (GM09.deleteVertices_le G X).edgeSet_mono he_del
      obtain ⟨u, w, hl_del⟩ := (GM09.deleteVertices G X).exists_isLink_of_mem_edgeSet he_del
      have hlG : G.IsLink e u w := hl_del.mono (GM09.deleteVertices_le G X)
      have huG : u ∈ V(G) := hlG.left_mem
      have hwG : w ∈ V(G) := hlG.right_mem
      have hxe_cl : x ∈ closure (Γ_G.iso.edgeEquiv ⟨e, heG⟩).1 := by
        simpa [graphDrawingEdgeSet, heG] using hxe
      have hlink := (Γ_G.iso.isLink_iff ⟨e, heG⟩ ⟨u, huG⟩ ⟨w, hwG⟩).mp hlG
      have hx_ends : x ∈ ({(Γ_G.iso.vertexEquiv ⟨u, huG⟩).1,
          (Γ_G.iso.vertexEquiv ⟨w, hwG⟩).1} : Set S) := by
        rw [← hlink.2.2.2]
        exact ⟨hxe_cl, hxV_G⟩
      rcases hx_ends with rfl | hxw
      · exact hl_del.left_mem.2 ⟨huG, huG, hxF⟩
      · rw [mem_singleton_iff] at hxw
        subst hxw
        exact hl_del.right_mem.2 ⟨hwG, hwG, hxF⟩
  obtain ⟨S', tS', ψ, hS', hcut, hsimple⟩ := exists_cut_simpler hclS hF hnull
  have : CompactSpace S' := hS'.1
  have : T2Space S' := hS'.2.1
  have : Nonempty S' := by
    obtain ⟨x₀⟩ := ‹Nonempty S›
    obtain ⟨y₀, _⟩ := hcut.2.1 x₀
    exact ⟨y₀⟩
  have hFc : IsClosed F := hF.isCompact.isClosed
  have hbdS'_eq : bd S' = ψ ⁻¹' F := by
    apply Subset.antisymm _ hcut.2.2.2.2
    intro y hy
    by_contra hyF
    have h_in_bd : ψ y ∈ bd S := bd_of_bd_cutMap (IsCutting.isCutMap hcut) hFc hy hyF
    rw [hbd] at h_in_bd
    exact h_in_bd
  have hpre_compl : ψ ⁻¹' Fᶜ = (bd S')ᶜ := by rw [hbdS'_eq, preimage_compl]
  have himg_compl : ψ '' (bd S')ᶜ = Fᶜ := by
    apply Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      rw [← hpre_compl] at hy
      exact hy
    · intro x hx
      obtain ⟨y, rfl⟩ := hcut.2.1 x
      exact ⟨y, hpre_compl ▸ hx, rfl⟩
  have hoff : (bd S')ᶜ ⊆ ψ ⁻¹' Fᶜ := hpre_compl.symm.subset
  obtain ⟨e_oph, hs_oph, ht_oph, heq_oph⟩ :
      ∃ e : OpenPartialHomeomorph S' S,
        e.source = (bd S')ᶜ ∧ e.target = Fᶜ ∧ EqOn e ψ (bd S')ᶜ :=
    GM19.exists_oph (cuff_statement S' hS').1.isOpen_compl hcut.1.continuousOn
      (hcut.2.2.1.mono hoff)
      (fun u hu huo ↦ isOpen_image_of_isCutMap (IsCutting.isCutMap hcut) (hu.trans hoff) huo)
      himg_compl
  let σ : S → S' := e_oph.symm
  have hσ_cont : ContinuousOn σ Fᶜ := by
    change ContinuousOn e_oph.symm Fᶜ
    rw [← ht_oph]
    exact e_oph.continuousOn_symm
  have hσ_maps : MapsTo σ Fᶜ (bd S')ᶜ := by
    change MapsTo e_oph.symm Fᶜ (bd S')ᶜ
    rw [← hs_oph, ← ht_oph]
    exact e_oph.symm.mapsTo
  have hψσ : ∀ x ∈ Fᶜ, ψ (σ x) = x := fun x hx ↦
    (heq_oph (hσ_maps hx)).symm.trans (e_oph.right_inv (ht_oph.symm ▸ hx))
  have hσ_inj : InjOn σ Fᶜ := by
    intro x₁ hx₁ x₂ hx₂ heq
    rw [← hψσ x₁ hx₁, ← hψσ x₂ hx₂, heq]
  have hcont_U : ContinuousOn σ Γ'.drawing.U := hσ_cont.mono hDU
  have hinj_U : InjOn σ Γ'.drawing.U := hσ_inj.mono hDU
  let D' : Surface.Drawing S' := mapDrawingInjOn Γ'.drawing σ hcont_U hinj_U
  let iso_D' : Iso (GM09.deleteVertices G X) D'.toGraph :=
    Γ'.iso.trans (isoMapDrawingInjOn Γ'.drawing σ hcont_U hinj_U)
  refine ⟨X, hX_sub, hX_card, S', tS', hS', ⟨⟨D', iso_D'⟩⟩, fun C hC ↦ ?_⟩
  have hsimpC : IsSimplerThan C S := hsimple C hC
  obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, ⟨eC⟩, ⟨eS⟩, ha₁, hb₁, hlt⟩ := hsimple C hC
  obtain ⟨hc₂, hgen₂, horient₂⟩ := (modelCriterion.2 a₂ b₂ c₂ a b 0).mp ⟨eS.symm.trans hom⟩
  refine ⟨hsimpC, a₁, b₁, c₁, ⟨eC⟩, fun hb0 ↦ ?_, by omega⟩
  have hb₂0 : b₂ = 0 := horient₂.mpr hb0
  omega

end GraphMinor.GM03
