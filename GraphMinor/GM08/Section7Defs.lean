module

public import GraphMinor.GM08.Section6
public import GraphMinor.GM05.Defs
public import GraphMinor.GM05.SeriesParallelDefs

@[expose] public section

/-!
# Definitions and Transport Lemmas for Graph Minors VIII, Section 7

This file defines hypertrees, graph tree-width, and drawing tree-width from Section 7 (page 267) of
Robertson and Seymour, *Graph Minors. VIII. A Kuratowski theorem for general surfaces*,
J. Combin. Theory Ser. B **48** (1990), 255–288, proves their equivalence with the simple-shadow
tree-width of `GraphMinor.GM05`, and transports drawings and `(r, s)`-nests in a closed disc `Δ`
along `SphereDiscChart`.
-/

namespace GraphMinor
namespace GM08

open Set Function Topology Graph Surface

universe u v u' v' w

/-!
## Hypertrees and Tree-Width (Section 7, page 267)
-/

/-- Reindexing a hypertree along a finite type equivalence `e : ι ≃ ι'`. -/
theorem IsHypertree.relabel {α : Type u} {ι : Type w} {ι' : Type*} [Fintype ι] [Fintype ι']
    {V₀ : Set α} {T : SimpleGraph ι} {X : ι → Set α}
    (h : IsHypertree V₀ T X) (e : ι ≃ ι') :
    IsHypertree V₀ (T.map e.toEmbedding) (X ∘ e.symm) where
  finite_V := h.finite_V
  isTree := (SimpleGraph.Iso.map e T).isTree_iff.1 h.isTree
  iUnion_eq := by
    rw [← h.iUnion_eq]
    ext v
    simp only [Set.mem_iUnion, Function.comp_apply]
    exact e.symm.exists_congr fun _ => Iff.rfl
  inter_subset {_ _ _} hp := by
    apply h.inter_subset
    rw [← GM10.onTreePath_map e]
    simpa using hp

/-- A hypertree on any `[Fintype ι]` witnesses `GraphTreeWidthLE G w`. -/
theorem graphTreeWidthLE_of_isHypertree {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α} {w : ℕ}
    (hHT : IsHypertree V(G) T X) (hw : HypertreeWidthLE X w)
    (hlink : ∀ ⦃e : β⦄ ⦃u v : α⦄, G.IsLink e u v → ∃ t : ι, u ∈ X t ∧ v ∈ X t) :
    GraphTreeWidthLE G w := by
  let e := Fintype.equivFin ι
  refine ⟨Fin (Fintype.card ι), inferInstance, T.map e.toEmbedding, X ∘ e.symm,
    hHT.relabel e, fun t => hw (e.symm t), ?_⟩
  intro edge u v hl
  obtain ⟨t, hu, hv⟩ := hlink hl
  exact ⟨e t, by simpa using hu, by simpa using hv⟩

/-- `GraphTreeWidthLE G w` is equivalent to `GM05.TreeWidthLE (GM05.simpleShadow G) w` for any
graph `G` with finite vertex set. -/
theorem graphTreeWidthLE_iff_gm05 {α : Type u} {β : Type v} {G : Graph α β}
    (hV : V(G).Finite) (w : ℕ) :
    GraphTreeWidthLE G w ↔ GM05.TreeWidthLE (GM05.simpleShadow G) w := by
  constructor
  · rintro ⟨ι, hfin, T, X, hHT, hw, hlink⟩
    refine ⟨ι, hfin, T, X, ?_, hw⟩
    refine ⟨hHT.isTree, hHT.iUnion_eq, ?_, hHT.inter_subset⟩
    rintro u v ⟨_, e, hl⟩
    exact hlink hl
  · rintro ⟨ι, hfin, T, χ, hTD, hw⟩
    refine ⟨ι, hfin, T, χ, ⟨hV, hTD.isTree, hTD.iUnion_eq, hTD.inter_subset⟩, hw, ?_⟩
    intro e u v hl
    by_cases huv : u = v
    · subst huv
      have hu : u ∈ ⋃ t : ι, χ t := hTD.iUnion_eq.symm ▸ hl.left_mem
      obtain ⟨t, hut⟩ := Set.mem_iUnion.mp hu
      exact ⟨t, hut, hut⟩
    · exact hTD.adj_mem ⟨huv, e, hl⟩

/-- Isomorphic graphs have the same tree-width bounds. -/
theorem graphTreeWidthLE_of_iso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} (iso : GraphMinor.Iso G H) {w : ℕ}
    (h : GraphTreeWidthLE G w) : GraphTreeWidthLE H w := by
  classical
  obtain ⟨ι, hfin, T, X, hHT, hw, hlink⟩ := h
  let Y : ι → Set α' := fun t => (fun x : V(G) => (iso.vertexEquiv x).1) '' {x : V(G) | x.1 ∈ X t}
  have hHV : V(H).Finite := by
    have : Finite V(G) := hHT.finite_V.to_subtype
    have : Finite V(H) := Finite.of_equiv V(G) iso.vertexEquiv
    exact Set.toFinite V(H)
  refine ⟨ι, hfin, T, Y, ⟨hHV, hHT.isTree, ?_, ?_⟩, ?_, ?_⟩
  · ext y
    simp only [Set.mem_iUnion, Y, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨x, _, rfl⟩⟩
      exact (iso.vertexEquiv x).2
    · intro hy
      let xG := iso.vertexEquiv.symm ⟨y, hy⟩
      have hxV : xG.1 ∈ ⋃ t : ι, X t := hHT.iUnion_eq.symm ▸ xG.2
      obtain ⟨t, hxt⟩ := Set.mem_iUnion.mp hxV
      refine ⟨t, xG, hxt, ?_⟩
      simp [xG]
  · intro t t' t'' hp y ⟨⟨x₁, hx₁, hy₁⟩, ⟨x₂, hx₂, hy₂⟩⟩
    have hx_eq : x₁ = x₂ :=
      iso.vertexEquiv.injective (Subtype.ext (hy₁.trans hy₂.symm))
    subst hx_eq
    exact ⟨x₁, hHT.inter_subset hp ⟨hx₁, hx₂⟩, hy₁⟩
  · intro t
    have hinj : Function.Injective (fun x : V(G) => (iso.vertexEquiv x).1) :=
      fun a b hab => iso.vertexEquiv.injective (Subtype.ext hab)
    change ((fun x : V(G) => (iso.vertexEquiv x).1) '' {x : V(G) | x.1 ∈ X t}).ncard ≤ w + 1
    rw [Set.ncard_image_of_injective _ hinj]
    have hsub_inj : Function.Injective (Subtype.val : V(G) → α) := Subtype.val_injective
    have himg : Subtype.val '' ({x : V(G) | x.1 ∈ X t} : Set V(G)) = X t := by
      ext x
      constructor
      · rintro ⟨⟨_, _⟩, hz, rfl⟩
        exact hz
      · intro hx
        have hxV : x ∈ V(G) := hHT.iUnion_eq ▸ Set.mem_iUnion.mpr ⟨t, hx⟩
        exact ⟨⟨x, hxV⟩, hx, rfl⟩
    have hcard_eq : ({x : V(G) | x.1 ∈ X t} : Set V(G)).ncard = (X t).ncard := by
      conv_rhs => rw [← himg]
      rw [Set.ncard_image_of_injective _ hsub_inj]
    rw [hcard_eq]
    exact hw t
  · intro e' u' v' hl'
    have he' : e' ∈ E(H) := hl'.edge_mem
    have hu' : u' ∈ V(H) := hl'.left_mem
    have hv' : v' ∈ V(H) := hl'.right_mem
    let eG := iso.edgeEquiv.symm ⟨e', he'⟩
    let uG := iso.vertexEquiv.symm ⟨u', hu'⟩
    let vG := iso.vertexEquiv.symm ⟨v', hv'⟩
    have hlG : G.IsLink eG.1 uG.1 vG.1 := by
      rw [iso.isLink_iff eG uG vG]
      simpa [eG, uG, vG] using hl'
    obtain ⟨t, hut, hvt⟩ := hlink hlG
    refine ⟨t, ⟨uG, hut, ?_⟩, ⟨vG, hvt, ?_⟩⟩ <;> simp [uG, vG]

theorem graphTreeWidthLE_iff_of_iso {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} (iso : GraphMinor.Iso G H) {w : ℕ} :
    GraphTreeWidthLE G w ↔ GraphTreeWidthLE H w :=
  ⟨graphTreeWidthLE_of_iso iso, graphTreeWidthLE_of_iso iso.symm⟩

/-- For a drawing `Γ` of a graft `(G, T)` in `S`, the tree-width of `G` equals the tree-width of
`Γ.drawing` (GM VIII Section 7, page 267). -/
theorem graftDrawing_treeWidthLE_iff {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G : Graph α β} {T : Set α} (Γ : Surface.GraftDrawing G T S) (w : ℕ) :
    GraphTreeWidthLE G w ↔ DrawingTreeWidthLE Γ.drawing w :=
  graphTreeWidthLE_iff_of_iso Γ.iso

/-!
## Transporting Disc Drawings Along `SphereDiscChart`
-/

namespace SphereDiscChart

variable {S : Type u} [TopologicalSpace S]
variable {Δ : Set S} {f : S → OnePoint EuclideanPlane} {f' : OnePoint EuclideanPlane → S}

/-- For `A ⊆ Δ` in a closed disc `Δ`, `f` maps the closure of `A` intersected with `Δ` to the
closure of `f '' A`. When `A ⊆ K` for a closed subset `K ⊆ Δ`, `closure A ⊆ K ⊆ Δ`, so
`closure (f '' A) = f '' closure A`. -/
theorem closure_image_eq (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {K A : Set S} (hKΔ : K ⊆ Δ) (hKcl : IsClosed K) (hAK : A ⊆ K) :
    closure (f '' A) = f '' closure A := by
  have hcl_sub_K : closure A ⊆ K := closure_minimal hAK hKcl
  have hcl_sub_Δ : closure A ⊆ Δ := hcl_sub_K.trans hKΔ
  apply Subset.antisymm
  · have hcomp_Δ : IsCompact Δ := hΔ.isCompact
    have hcomp_cl : IsCompact (closure A) := by
      have heq : closure A = Δ ∩ closure A := (Set.inter_eq_self_of_subset_right hcl_sub_Δ).symm
      rw [heq]
      exact hcomp_Δ.inter_right isClosed_closure
    have hcomp_img : IsCompact (f '' closure A) := hcomp_cl.image_of_continuousOn (sc.fc.mono hcl_sub_Δ)
    exact closure_minimal (image_mono subset_closure) hcomp_img.isClosed
  · rintro _ ⟨x, hxcl, rfl⟩
    have hxΔ : x ∈ Δ := hcl_sub_Δ hxcl
    rw [mem_closure_iff]
    intro W hWopen hfxW
    have hcont : ContinuousOn f Δ := sc.fc
    rw [continuousOn_iff] at hcont
    obtain ⟨U, hUopen, hxU, hUsub⟩ := hcont x hxΔ W hWopen hfxW
    obtain ⟨z, hzU, hzA⟩ := mem_closure_iff.mp hxcl U hUopen hxU
    have hzΔ : z ∈ Δ := hKΔ (hAK hzA)
    exact ⟨f z, hUsub ⟨hzU, hzΔ⟩, mem_image_of_mem f hzA⟩

private theorem arcComponentsIn_image_gen {S₁ : Type*} {S₂ : Type*}
    [TopologicalSpace S₁] [TopologicalSpace S₂] {F : Set S₁} {φ : S₁ → S₂} {ψ : S₂ → S₁}
    (hφ : ContinuousOn φ F) (hψ : ContinuousOn ψ (φ '' F)) (hψφ : ∀ x ∈ F, ψ (φ x) = x) :
    arcComponentsIn (φ '' F) = image φ '' arcComponentsIn F := by
  have hφψ : ∀ y ∈ φ '' F, φ (ψ y) = y := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hψφ x hx]
  have hconn : ∀ {A : Set S₁}, A ⊆ F → IsPathConnected A → IsPathConnected (φ '' A) :=
    fun hA h => h.image' (hφ.mono hA)
  have hconn' : ∀ {B : Set S₂}, B ⊆ φ '' F → IsPathConnected B → IsPathConnected (ψ '' B) :=
    fun hB h => h.image' (hψ.mono hB)
  have hψsub : ∀ {B : Set S₂}, B ⊆ φ '' F → ψ '' B ⊆ F := by
    rintro B hB _ ⟨y, hy, rfl⟩
    obtain ⟨x, hx, rfl⟩ := hB hy
    rwa [hψφ x hx]
  have hφψim : ∀ {B : Set S₂}, B ⊆ φ '' F → φ '' (ψ '' B) = B := fun {B} hB => by
    rw [image_image]
    exact (image_congr fun y hy => hφψ y (hB hy)).trans (image_id' B)
  have hψφim : ∀ {A : Set S₁}, A ⊆ F → ψ '' (φ '' A) = A := fun {A} hA => by
    rw [image_image]
    exact (image_congr fun x hx => hψφ x (hA hx)).trans (image_id' A)
  ext C'
  constructor
  · rintro ⟨hne, hsub, hpc, hmax⟩
    refine ⟨ψ '' C', ⟨hne.image ψ, hψsub hsub, hconn' hsub hpc, ?_⟩, hφψim hsub⟩
    intro A hA hAc hCA
    have h₁ : C' ⊆ φ '' A := by
      have := image_mono (f := φ) hCA
      rwa [hφψim hsub] at this
    have h₂ := hmax _ (image_mono hA) (hconn hA hAc) h₁
    rw [← h₂, hψφim hA]
  · rintro ⟨C, ⟨hne, hsub, hpc, hmax⟩, rfl⟩
    refine ⟨hne.image φ, image_mono hsub, hconn hsub hpc, ?_⟩
    intro B hB hBc hCB
    have h₁ : C ⊆ ψ '' B := by
      have := image_mono (f := ψ) hCB
      rwa [hψφim hsub] at this
    have h₂ := hmax _ (hψsub hB) (hconn' hB hBc) h₁
    rw [← h₂, hφψim hB]

/-- Transport a `Drawing S` contained in a closed disc `Δ` along `SphereDiscChart Δ f f'` into
`OnePoint EuclideanPlane`, together with a graph isomorphism `Iso D.toGraph D'.toGraph`. -/
theorem exists_transport_drawing (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    (D : Surface.Drawing S) (hDU : D.U ⊆ Δ) :
    ∃ (D' : Surface.Drawing (OnePoint EuclideanPlane)) (iso : GraphMinor.Iso D.toGraph D'.toGraph),
      D'.U = f '' D.U ∧ D'.V = f '' D.V ∧ D'.E = image f '' D.E ∧
      (∀ e ∈ D.E, closure (f '' e) = f '' closure e) ∧
      (∀ x : V(D.toGraph), (iso.vertexEquiv x).1 = f x.1) ∧
      (∀ e : E(D.toGraph), (iso.edgeEquiv e).1 = f '' e.1) := by
  have hinj : InjOn f Δ := sc.injOn_f
  have hcompU : IsCompact D.U := by
    have heq : D.U = Δ ∩ D.U := (Set.inter_eq_self_of_subset_right hDU).symm
    rw [heq]
    exact hΔ.isCompact.inter_right D.isClosed_U
  have hclU' : IsClosed (f '' D.U) :=
    (hcompU.image_of_continuousOn (sc.fc.mono hDU)).isClosed
  have hsubUV : D.U \ D.V ⊆ Δ := sdiff_subset.trans hDU
  have harc : arcComponentsIn (f '' (D.U \ D.V)) = image f '' arcComponentsIn (D.U \ D.V) :=
    arcComponentsIn_image_gen (sc.fc.mono hsubUV)
      (sc.f'c.mono (image_mono hsubUV)) (fun x hx => sc.f'f (hsubUV hx))
  have hdiff : f '' D.U \ f '' D.V = f '' (D.U \ D.V) :=
    (sc.f_sdiff hDU (D.V_subset_U.trans hDU)).symm
  have hcl_edge : ∀ e ∈ D.E, closure (f '' e) = f '' closure e := fun e he =>
    sc.closure_image_eq hΔ hDU D.isClosed_U (fun x hx => (he.2.1 hx).1)
  have hcap : ∀ e ∈ D.E, closure (f '' e) ∩ f '' D.V = f '' (closure e ∩ D.V) := by
    intro e he
    rw [hcl_edge e he]
    have hcle : closure e ⊆ Δ := (closure_minimal (fun x hx => (he.2.1 hx).1) D.isClosed_U).trans hDU
    exact (InjOn.image_inter hinj hcle (D.V_subset_U.trans hDU)).symm
  let D' : Surface.Drawing (OnePoint EuclideanPlane) :=
    { U := f '' D.U
      V := f '' D.V
      V_subset_U := image_mono D.V_subset_U
      isClosed_U := hclU'
      finite_V := D.finite_V.image f
      finite_edges := by
        rw [hdiff, harc]
        exact D.finite_edges.image _
      edge_cond := by
        rw [hdiff, harc]
        rintro _ ⟨e, he, rfl⟩
        have hcle : closure e ⊆ Δ :=
          (closure_minimal (fun x hx => (he.2.1 hx).1) D.isClosed_U).trans hDU
        have hinje : InjOn f (closure e) := hinj.mono hcle
        rw [hcap e he]
        rcases D.edge_cond e he with ⟨u, v, huv, hc, hL⟩ | ⟨u, hc, hF⟩
        · left
          have hu_cl : u ∈ closure e := by
            have : u ∈ closure e ∩ D.V := hc ▸ by simp
            exact this.1
          have hv_cl : v ∈ closure e := by
            have : v ∈ closure e ∩ D.V := hc ▸ by simp
            exact this.1
          refine ⟨f u, f v, fun h => huv (hinje hu_cl hv_cl h), by rw [hc, image_pair], ?_⟩
          obtain ⟨φ₁, h0, h1⟩ := hL
          have hc₁ : Continuous fun t => f (φ₁ t).1 :=
            (sc.fc.mono hcle).comp_continuous (continuous_subtype_val.comp φ₁.continuous)
              fun t => (φ₁ t).2
          have hi₁ : Function.Injective fun t => f (φ₁ t).1 := fun x y h =>
            φ₁.injective (Subtype.ext (hinje (φ₁ x).2 (φ₁ y).2 h))
          have hr : range (fun t => f (φ₁ t).1) = closure (f '' e) := by
            rw [hcl_edge e he]
            ext y
            constructor
            · rintro ⟨t, rfl⟩
              exact ⟨_, (φ₁ t).2, rfl⟩
            · rintro ⟨x, hx, rfl⟩
              exact ⟨φ₁.symm ⟨x, hx⟩, by simp⟩
          let ψ := (hc₁.isClosedEmbedding hi₁).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hr)
          refine ⟨ψ, ?_, ?_⟩
          · change f (φ₁ 0).1 = f u
            rw [h0]
          · change f (φ₁ 1).1 = f v
            rw [h1]
        · right
          refine ⟨f u, by rw [hc, image_singleton], ?_⟩
          exact hcl_edge e he ▸ sc.oArc_f hcle hF }
  have hD'E : D'.E = image f '' D.E := by
    change arcComponentsIn (f '' D.U \ f '' D.V) = image f '' D.E
    rw [hdiff, harc]
    rfl
  have hv_bij : Set.BijOn f D.V D'.V := ⟨mapsTo_image f D.V, hinj.mono (D.V_subset_U.trans hDU), surjOn_image f D.V⟩
  have he_inj : InjOn (image f) D.E := by
    intro e₁ he₁ e₂ he₂ heq
    have h₁ : e₁ ⊆ Δ := fun x hx => hDU (he₁.2.1 hx).1
    have h₂ : e₂ ⊆ Δ := fun x hx => hDU (he₂.2.1 hx).1
    rw [← sc.f'_f h₁, ← sc.f'_f h₂, heq]
  have he_bij : Set.BijOn (image f) D.E D'.E := by
    rw [hD'E]
    exact ⟨mapsTo_image _ _, he_inj, surjOn_image _ _⟩
  let iso : GraphMinor.Iso D.toGraph D'.toGraph :=
    { vertexEquiv := hv_bij.equiv
      edgeEquiv := he_bij.equiv
      isLink_iff := by
        intro e x y
        change (e.1 ∈ D.E ∧ x.1 ∈ D.V ∧ y.1 ∈ D.V ∧ closure e.1 ∩ D.V = {x.1, y.1}) ↔
          (f '' e.1 ∈ D'.E ∧ f x.1 ∈ D'.V ∧ f y.1 ∈ D'.V ∧
            closure (f '' e.1) ∩ D'.V = {f x.1, f y.1})
        have heE : e.1 ∈ D.E := e.2
        have hxV : x.1 ∈ D.V := x.2
        have hyV : y.1 ∈ D.V := y.2
        have he'E : f '' e.1 ∈ D'.E := hD'E ▸ mem_image_of_mem _ heE
        have hx'V : f x.1 ∈ D'.V := mem_image_of_mem f hxV
        have hy'V : f y.1 ∈ D'.V := mem_image_of_mem f hyV
        constructor
        · rintro ⟨-, -, -, hcl⟩
          refine ⟨he'E, hx'V, hy'V, ?_⟩
          change closure (f '' e.1) ∩ f '' D.V = {f x.1, f y.1}
          rw [hcap e.1 heE, hcl, image_pair]
        · rintro ⟨-, -, -, hcl'⟩
          refine ⟨heE, hxV, hyV, ?_⟩
          change closure (f '' e.1) ∩ f '' D.V = {f x.1, f y.1} at hcl'
          rw [hcap e.1 heE, ← image_pair] at hcl'
          have hsub₁ : closure e.1 ∩ D.V ⊆ Δ := inter_subset_right.trans (D.V_subset_U.trans hDU)
          have hsub₂ : ({x.1, y.1} : Set S) ⊆ Δ := by
            rintro z (rfl | rfl)
            · exact hDU (D.V_subset_U hxV)
            · exact hDU (D.V_subset_U hyV)
          rw [← sc.f'_f hsub₁, ← sc.f'_f hsub₂, hcl'] }
  exact ⟨D', iso, rfl, rfl, hD'E, hcl_edge, fun _ => rfl, fun _ => rfl⟩

/-- Transport an `(r, s)`-nest from `D'` in `f '' Δ` back to `D` in `Δ` along `f'`. -/
noncomputable def pullBackNest (hΔ : IsClosedDisc Δ) (sc : SphereDiscChart Δ f f')
    {D : Surface.Drawing S} (hDU : D.U ⊆ Δ)
    {D' : Surface.Drawing (OnePoint EuclideanPlane)}
    (hD'U : D'.U = f '' D.U) (hD'V : D'.V = f '' D.V)
    {r s : ℕ} (N' : DrawingNest D' (f '' Δ) r s) :
    DrawingNest D Δ r s where
  circuit j :=
    { U := f' '' (N'.circuit j).U
      ins := f' '' (N'.circuit j).ins
      U_sub_drawing := by
        have hsub : (N'.circuit j).U ⊆ f '' D.U := hD'U ▸ (N'.circuit j).U_sub_drawing
        simpa [sc.f'_f hDU] using image_mono (f := f') hsub
      U_sub_disc := sc.f'_subset (N'.circuit j).U_sub_disc
      isOArc_U := sc.oArc_f' (N'.circuit j).U_sub_disc (N'.circuit j).isOArc_U
      isInside := by
        have hins := (N'.circuit j).isInside
        have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ (N'.circuit j).ins :=
          fun hm => sc.infty_notMem (hins.1 hm)
        have hbd : discBd (N'.circuit j).ins ⊆ f '' Δ :=
          hins.2.2.1 ▸ (N'.circuit j).U_sub_disc
        have hpull := sc.isInsideDisc_f'_of_infty_notMem hΔ hins.2.1 hinf hbd
        simpa [hins.2.2.1] using hpull.2.1 }
  inside_of_lt {i j} hij := by
    intro x hx
    obtain ⟨p, hpU, rfl⟩ := hx
    have hinside' := N'.inside_of_lt hij p hpU
    have hins_j := (N'.circuit j).isInside
    have hp_int : p ∈ discInt (N'.circuit j).ins :=
      (insideOArc_iff_mem_discInt (sc.disc_f Subset.rfl hΔ).1 hins_j).mp hinside'
    have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ (N'.circuit j).ins :=
      fun hm => sc.infty_notMem (hins_j.1 hm)
    have hbd : discBd (N'.circuit j).ins ⊆ f '' Δ :=
      hins_j.2.2.1 ▸ (N'.circuit j).U_sub_disc
    have hpull := (sc.isInsideDisc_f'_of_infty_notMem hΔ hins_j.2.1 hinf hbd).2.1
    have hpull_ins : IsInsideDisc Δ (f' '' (N'.circuit j).U) (f' '' (N'.circuit j).ins) := by
      simpa [hins_j.2.2.1] using hpull
    rw [insideOArc_iff_mem_discInt hΔ hpull_ins]
    refine ⟨mem_image_of_mem f' hp_int.1, ?_⟩
    rw [hpull_ins.2.2.1]
    rintro ⟨q, hqU, hfeq⟩
    have hpq : p = q := sc.injOn_f' (hins_j.1 hp_int.1) ((N'.circuit j).U_sub_disc hqU) hfeq.symm
    exact hp_int.2 (hins_j.2.2.1 ▸ hpq ▸ hqU)
  radialPath p := f' '' N'.radialPath p
  isPreconnected_radialPath p :=
    (N'.isPreconnected_radialPath p).image f' (sc.f'c.mono (N'.radialPath_sub_disc p))
  radialPath_sub_U p := by
    have hsub : N'.radialPath p ⊆ f '' D.U := hD'U ▸ N'.radialPath_sub_U p
    simpa [sc.f'_f hDU] using image_mono (f := f') hsub
  radialPath_sub_disc p := sc.f'_subset (N'.radialPath_sub_disc p)
  pairwise_disjoint_paths p q hpq := by
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨⟨x, hxP, rfl⟩, hxV⟩ ⟨⟨y, hyQ, hfeq⟩, _⟩
    have hxy : x = y := sc.injOn_f' (N'.radialPath_sub_disc p hxP) (N'.radialPath_sub_disc q hyQ) hfeq.symm
    subst hxy
    have hfxV : x ∈ D'.V := by
      rw [hD'V, ← sc.ff' (N'.radialPath_sub_disc p hxP)]
      exact mem_image_of_mem f hxV
    exact Set.disjoint_left.mp (N'.pairwise_disjoint_paths hpq) ⟨hxP, hfxV⟩ ⟨hyQ, hfxV⟩
  meets_inner p hs := by
    obtain ⟨z, hzP, hzC⟩ := N'.meets_inner p hs
    exact ⟨f' z, mem_image_of_mem f' hzP, mem_image_of_mem f' hzC⟩
  meets_outer p hs := by
    obtain ⟨z, hzP, hzC⟩ := N'.meets_outer p hs
    exact ⟨f' z, mem_image_of_mem f' hzP, mem_image_of_mem f' hzC⟩

end SphereDiscChart

end GM08
end GraphMinor
