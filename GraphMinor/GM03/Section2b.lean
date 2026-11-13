module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Section2a
import GraphMinor.Surface.SphereDisc
import GraphMinor.Surface.DiscFan
import GraphMinor.GM07.CylinderWheel
import GraphMinor.GM11.CircuitRegions
import GraphMinor.GM11.SphereRegion
import GraphMinor.GM11.Theorem75
import GraphMinor.GM22.Section4Basic

/-!
# Graph Minors III, Section 2 Shell Extension (`(2.2)`) and Nested Disc Crossing

This file proves the nested-disc Jordan crossing lemmas for region chains in a planar drawing `M`
and the inductive shell extension step for Graph Minors III, `(2.2)` (pages 52–54), including the
paper's numbered claims `(1)` (`lemma_2_2_claim_1`) and `(2)` (`lemma_2_2_claim_2`).
-/

@[expose] public section

namespace GraphMinor.GM03

open Function Topology Classical
open Graph SimpleGraph Set
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM11
open GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM22

universe u v

variable {α : Type u} {β : Type v}

instance instT2SpacePlanarDrawingS {G : Graph α β} (M : PlanarDrawing G) : T2Space M.S :=
  M.isClosedSurface.2.1

/-! ## Part 1: Canonical Subdrawings, Inside Discs, and Region-Chain Crossing -/

section SubdrawingAndDiscs

variable {S : Type} [TopologicalSpace S]

/-- Canonical `PlanarDrawing D.toGraph` on a sphere `S` with designated infinite region `r₀ ∈ D.R`. -/
def planarDrawingOfDrawing (hS : IsClosedSurface S) (hSph : IsSphere S)
    (D : Drawing S) (r₀ : Set S) (hr₀ : r₀ ∈ D.R) : PlanarDrawing D.toGraph where
  S := S
  topSpace := inferInstance
  isClosedSurface := hS
  isSphere := hSph
  graphDrawing :=
    { drawing := D
      iso :=
        { vertexEquiv := Equiv.refl _
          edgeEquiv := Equiv.refl _
          isLink_iff := fun _ _ _ => Iff.rfl } }
  infRegion := r₀
  infRegion_mem := hr₀

/-- For any subgraph `H ≤ D.toGraph`, `D.span V(H) E(H)` has vertex set `V(H)` and edge set `E(H)`. -/
theorem span_V_E_of_le [T2Space S] {D : Drawing S} {H : Graph S (Set S)} (hle : H ≤ D.toGraph) :
    (D.span V(H) E(H)).V = V(H) ∧ (D.span V(H) E(H)).E = E(H) := by
  have hVH : V(H) ⊆ D.V := hle.vertexSet_mono
  have hEH : E(H) ⊆ D.E := hle.edgeSet_mono
  have hE : (D.span V(H) E(H)).E = E(H) := by
    rw [D.span_E]
    exact inter_eq_left.mpr hEH
  have hV : (D.span V(H) E(H)).V = V(H) := by
    rw [D.span_V]
    refine Subset.antisymm (union_subset inter_subset_left (iUnion₂_subset fun e he => ?_))
      fun x hx => Or.inl ⟨hx, hVH hx⟩
    rintro x ⟨hxe, hxV⟩
    obtain ⟨a, b, hl⟩ := H.exists_isLink_of_mem_edgeSet he.1
    have hl' := hl.mono hle
    have hc : closure e ∩ D.V = {a, b} := hl'.2.2.2
    have hxab : x ∈ ({a, b} : Set S) := hc ▸ ⟨hxe, hxV⟩
    rcases hxab with rfl | rfl
    · exact hl.left_mem
    · exact hl.right_mem
  exact ⟨hV, hE⟩

/-- For any subgraph `H ≤ D.toGraph`, `D.span V(H) E(H)` is a subdrawing of `D` whose `.toGraph`
is `H`. -/
theorem span_toGraph_eq_of_le [T2Space S] {D : Drawing S} {H : Graph S (Set S)}
    (hle : H ≤ D.toGraph) :
    (D.span V(H) E(H)).IsSubdrawing D ∧ (D.span V(H) E(H)).toGraph = H := by
  obtain ⟨hV, hE⟩ := span_V_E_of_le hle
  have hsub : (D.span V(H) E(H)).IsSubdrawing D :=
    ⟨hV.subset.trans hle.vertexSet_mono, hE.subset.trans hle.edgeSet_mono⟩
  refine ⟨hsub, Graph.ext hV fun e u v => ?_⟩
  change (e ∈ (D.span V(H) E(H)).E ∧ u ∈ (D.span V(H) E(H)).V ∧ v ∈ (D.span V(H) E(H)).V ∧
    closure e ∩ (D.span V(H) E(H)).V = {u, v}) ↔ H.IsLink e u v
  rw [hV, hE]
  constructor
  · rintro ⟨he, hu, hv, hcap⟩
    obtain ⟨a, b, hl⟩ := H.exists_isLink_of_mem_edgeSet he
    have hlD := hl.mono hle
    have hcapD : closure e ∩ D.V = {a, b} := hlD.2.2.2
    have hcapH : closure e ∩ V(H) = {a, b} := by
      refine Subset.antisymm ?_ ?_
      · intro z hz
        exact hcapD ▸ ⟨hz.1, hle.vertexSet_mono hz.2⟩
      · intro z hz
        have hzD : z ∈ closure e ∩ D.V := by rw [hcapD]; exact hz
        rcases hz with rfl | rfl
        · exact ⟨hzD.1, hl.left_mem⟩
        · exact ⟨hzD.1, hl.right_mem⟩
    have hpair : ({u, v} : Set S) = {a, b} := hcap.symm.trans hcapH
    rcases pair_eq_pair_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hl
    · exact hl.symm
  · intro hl
    have hlD := hl.mono hle
    have hcapD : closure e ∩ D.V = {u, v} := hlD.2.2.2
    refine ⟨hl.edge_mem, hl.left_mem, hl.right_mem, Subset.antisymm ?_ ?_⟩
    · intro z hz
      exact hcapD ▸ ⟨hz.1, hle.vertexSet_mono hz.2⟩
    · intro z hz
      have hzD : z ∈ closure e ∩ D.V := by rw [hcapD]; exact hz
      rcases hz with rfl | rfl
      · exact ⟨hzD.1, hl.left_mem⟩
      · exact ⟨hzD.1, hl.right_mem⟩

/-- Two subdrawings of `D` with disjoint vertex sets have disjoint edge sets and disjoint `U`. -/
theorem subdrawing_disjoint_U_of_disjoint_V [T2Space S] {D R₁ R₂ : Drawing S}
    (h₁ : R₁.IsSubdrawing D) (h₂ : R₂.IsSubdrawing D) (hdisjV : Disjoint R₁.V R₂.V) :
    Disjoint R₁.E R₂.E ∧ Disjoint R₁.U R₂.U := by
  have hdisjE : Disjoint R₁.E R₂.E := by
    refine disjoint_left.mpr fun e he₁ he₂ => ?_
    obtain ⟨u, v, hl₁⟩ := R₁.toGraph.exists_isLink_of_mem_edgeSet he₁
    have huD : u ∈ closure e ∩ D.V := by
      rw [← h₁.closure_inter_V he₁, hl₁.2.2.2]
      exact mem_insert u {v}
    rw [← h₂.closure_inter_V he₂] at huD
    exact disjoint_left.mp hdisjV hl₁.left_mem huD.2
  refine ⟨hdisjE, disjoint_left.mpr fun x hx₁ hx₂ => ?_⟩
  by_cases hxV₁ : x ∈ R₁.V
  · by_cases hxV₂ : x ∈ R₂.V
    · exact disjoint_left.mp hdisjV hxV₁ hxV₂
    · obtain ⟨e₂, he₂, hxe₂⟩ := R₂.exists_edge_of_mem hx₂ hxV₂
      exact ((h₂.2 he₂).2.1 hxe₂).2 (h₁.1 hxV₁)
  · obtain ⟨e₁, he₁, hxe₁⟩ := R₁.exists_edge_of_mem hx₁ hxV₁
    by_cases hxV₂ : x ∈ R₂.V
    · exact ((h₁.2 he₁).2.1 hxe₁).2 (h₂.1 hxV₂)
    · obtain ⟨e₂, he₂, hxe₂⟩ := R₂.exists_edge_of_mem hx₂ hxV₂
      have heq : e₁ = e₂ := D.edge_eq_of_mem (h₁.2 he₁) (h₂.2 he₂) hxe₁ hxe₂
      exact disjoint_left.mp hdisjE he₁ (heq ▸ he₂)

/-- Forward vertex map from `V(G)` to `M.drawing.V`. -/
noncomputable def drawingFwdV {G : Graph α β} (M : PlanarDrawing G) (v : α) : M.S :=
  if hv : v ∈ V(G) then (M.graphDrawing.iso.vertexEquiv ⟨v, hv⟩).1
  else (region_nonempty M.infRegion_mem).choose

/-- Forward edge map from `E(G)` to `M.drawing.E`. -/
noncomputable def drawingFwdE {G : Graph α β} (M : PlanarDrawing G) (e : β) : Set M.S :=
  if he : e ∈ E(G) then (M.graphDrawing.iso.edgeEquiv ⟨e, he⟩).1
  else ∅

theorem gmap_fwd_of_planarDrawing {G : Graph α β} (M : PlanarDrawing G) :
    GM14.GMap G M.drawing.toGraph (drawingFwdV M) (drawingFwdE M) := by
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro v hv
    simp only [drawingFwdV, hv, ↓reduceDIte]
    exact (M.graphDrawing.iso.vertexEquiv ⟨v, hv⟩).2
  · intro u hu v hv huv
    simp only [drawingFwdV, hu, hv, ↓reduceDIte] at huv
    exact congrArg Subtype.val (M.graphDrawing.iso.vertexEquiv.injective (Subtype.ext huv))
  · intro x hx
    let v := M.graphDrawing.iso.vertexEquiv.symm ⟨x, hx⟩
    refine ⟨v.1, v.2, ?_⟩
    simp only [drawingFwdV, v.2, ↓reduceDIte]
    exact congrArg Subtype.val (M.graphDrawing.iso.vertexEquiv.apply_symm_apply ⟨x, hx⟩)
  · intro e he
    simp only [drawingFwdE, he, ↓reduceDIte]
    exact (M.graphDrawing.iso.edgeEquiv ⟨e, he⟩).2
  · intro e₁ he₁ e₂ he₂ heq
    simp only [drawingFwdE, he₁, he₂, ↓reduceDIte] at heq
    exact congrArg Subtype.val (M.graphDrawing.iso.edgeEquiv.injective (Subtype.ext heq))
  · intro e he
    let f := M.graphDrawing.iso.edgeEquiv.symm ⟨e, he⟩
    refine ⟨f.1, f.2, ?_⟩
    simp only [drawingFwdE, f.2, ↓reduceDIte]
    exact congrArg Subtype.val (M.graphDrawing.iso.edgeEquiv.apply_symm_apply ⟨e, he⟩)
  · intro e u v he hu hv
    simp only [drawingFwdV, drawingFwdE, he, hu, hv, ↓reduceDIte]
    exact M.graphDrawing.iso.isLink_iff ⟨e, he⟩ ⟨u, hu⟩ ⟨v, hv⟩

theorem graphDrawingVertexSet_eq_singleton {G : Graph α β} (M : PlanarDrawing G)
    {v : α} (hv : v ∈ V(G)) :
    graphDrawingVertexSet M.graphDrawing v = {drawingFwdV M v} := by
  ext x
  simp only [graphDrawingVertexSet, drawingFwdV, hv, ↓reduceDIte, mem_ofPred_eq, mem_singleton_iff]
  exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨trivial, h.symm⟩⟩

theorem graphDrawingEdgeSet_eq {G : Graph α β} (M : PlanarDrawing G)
    {e : β} (he : e ∈ E(G)) :
    graphDrawingEdgeSet M.graphDrawing e = drawingFwdE M e := by
  ext x
  simp only [graphDrawingEdgeSet, drawingFwdE, he, ↓reduceDIte, mem_iUnion]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

/-- The subdrawing of `M.drawing` corresponding to a subgraph `H ≤ G`. -/
noncomputable def subdrawingOfSubgraph {G : Graph α β} (M : PlanarDrawing G) (H : Graph α β) :
    Drawing M.S :=
  M.drawing.span (drawingFwdV M '' V(H)) (drawingFwdE M '' E(H))

theorem subdrawingOfSubgraph_spec {G : Graph α β} (M : PlanarDrawing G) {H : Graph α β}
    (hle : H ≤ G) :
    (subdrawingOfSubgraph M H).IsSubdrawing M.drawing ∧
    (subdrawingOfSubgraph M H).V = drawingFwdV M '' V(H) ∧
    (subdrawingOfSubgraph M H).E = drawingFwdE M '' E(H) ∧
    (subdrawingOfSubgraph M H).toGraph = (gmap_fwd_of_planarDrawing M).sub H ∧
    graphDrawingSubgraphU M.graphDrawing H = (subdrawingOfSubgraph M H).U := by
  let m := gmap_fwd_of_planarDrawing M
  have hsub_le : m.sub H ≤ M.drawing.toGraph := m.sub_le hle
  have hV_sub : V(m.sub H) = drawingFwdV M '' V(H) := rfl
  have hE_sub : E(m.sub H) = drawingFwdE M '' E(H) := m.edgeSet_sub hle
  have hspan_eq : subdrawingOfSubgraph M H = M.drawing.span V(m.sub H) E(m.sub H) := by
    rw [subdrawingOfSubgraph, hV_sub, hE_sub]
  obtain ⟨hV, hE⟩ := span_V_E_of_le hsub_le
  obtain ⟨hIsSub, hToGraph⟩ := span_toGraph_eq_of_le hsub_le
  rw [← hspan_eq] at hV hE hIsSub hToGraph
  refine ⟨hIsSub, hV.trans hV_sub, hE.trans hE_sub, hToGraph, ?_⟩
  rw [(subdrawingOfSubgraph M H).U_eq, hV, hE, hV_sub, hE_sub]
  refine Subset.antisymm (union_subset (iUnion₂_subset ?_) (iUnion₂_subset ?_))
    (union_subset ?_ (iUnion₂_subset ?_))
  · intro v hv
    rw [graphDrawingVertexSet_eq_singleton M (hle.vertexSet_mono hv), singleton_subset_iff]
    exact Or.inl (mem_image_of_mem _ hv)
  · intro e he
    rw [graphDrawingEdgeSet_eq M (hle.edgeSet_mono he)]
    exact subset_biUnion_of_mem (u := fun s => closure s) (mem_image_of_mem _ he) |>.trans
      subset_union_right
  · rintro _ ⟨v, hv, rfl⟩
    refine Or.inl (mem_iUnion₂.mpr ⟨v, hv, ?_⟩)
    rw [graphDrawingVertexSet_eq_singleton M (hle.vertexSet_mono hv)]
    rfl
  · rintro _ ⟨e, he, rfl⟩
    refine Subset.trans ?_ subset_union_right
    refine subset_biUnion_of_mem (u := fun a => closure (graphDrawingEdgeSet M.graphDrawing a))
      he |>.trans' ?_
    rw [graphDrawingEdgeSet_eq M (hle.edgeSet_mono he)]

/-- Every circuit `C` of `G` in `M` corresponds to a circuit subdrawing `subdrawingOfSubgraph M C`
of `M.drawing`. -/
theorem isCircuit_subdrawingOfSubgraph {G : Graph α β} (M : PlanarDrawing G) {C : Graph α β}
    (hC : IsGraphCircuit G C) :
    (subdrawingOfSubgraph M C).IsCircuit ∧
    (subdrawingOfSubgraph M C).IsSubdrawing M.drawing ∧
    graphDrawingSubgraphU M.graphDrawing C = (subdrawingOfSubgraph M C).U := by
  obtain ⟨hsub, hV, hE, htoG, hU⟩ := subdrawingOfSubgraph_spec M hC.1
  have hC' : IsGraphCircuit M.drawing.toGraph (subdrawingOfSubgraph M C).toGraph := by
    rw [htoG]
    exact (gmap_fwd_of_planarDrawing M).circuit hC
  obtain ⟨R, hR_circ, hR_sub, hRV, hRE⟩ := GM14.exists_circuit_drawing hC'
  have hR_eq : R = subdrawingOfSubgraph M C :=
    Drawing.ext_of_V_E hRV hRE
  exact ⟨hR_eq ▸ hR_circ, hsub, hU⟩

/-- Every circuit `C` of `G` in `M` bounds a unique inside closed disc `Δ` (`IsInsideDisc M C Δ`). -/
theorem exists_unique_insideDisc {G : Graph α β} (M : PlanarDrawing G) {C : Graph α β}
    (hC : IsGraphCircuit G C) :
    (∃ Δ : Set M.S, IsInsideDisc M C Δ) ∧
    ∀ Δ₁ Δ₂ : Set M.S, IsInsideDisc M C Δ₁ → IsInsideDisc M C Δ₂ → Δ₁ = Δ₂ := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  obtain ⟨hR_circ, hR_sub, hU⟩ := isCircuit_subdrawingOfSubgraph M hC
  have hOArc : IsOArc (subdrawingOfSubgraph M C).U :=
    GM11.IsCircuit.isOArc_U hR_circ
  obtain ⟨Δ₁, Δ₂, hne, hΔ₁, hΔ₂, hbd₁, hbd₂, huniv, hinter, hcomp, huniq⟩ :=
    sphere_disc M.S M.isSphere (subdrawingOfSubgraph M C).U hOArc
  have hinf_disj_F : Disjoint M.infRegion (subdrawingOfSubgraph M C).U := by
    refine disjoint_left.mpr fun x hxinf hxU => ?_
    exact region_subset M.infRegion_mem hxinf (hR_sub.U_subset hxU)
  obtain ⟨p, hp⟩ := region_nonempty M.infRegion_mem
  have hp_not_F : p ∉ (subdrawingOfSubgraph M C).U := disjoint_left.mp hinf_disj_F hp
  have hinf_sub_comp : M.infRegion ⊆ connectedComponentIn (univ \ (subdrawingOfSubgraph M C).U) p :=
    (region_isPreconnected M.infRegion_mem).subset_connectedComponentIn hp fun x hx =>
      ⟨mem_univ x, disjoint_left.mp hinf_disj_F hx⟩
  have hcomp_mem :
      connectedComponentIn (univ \ (subdrawingOfSubgraph M C).U) p ∈
        componentsIn (univ \ (subdrawingOfSubgraph M C).U) :=
    ⟨p, ⟨mem_univ p, hp_not_F⟩, rfl⟩
  rw [hcomp] at hcomp_mem
  have hnot_both : ¬ (Disjoint Δ₁ M.infRegion ∧ Disjoint Δ₂ M.infRegion) := by
    rintro ⟨hd₁, hd₂⟩
    have hp_univ : p ∈ Δ₁ ∪ Δ₂ := huniv ▸ mem_univ p
    rcases hp_univ with hp₁ | hp₂
    · exact disjoint_left.mp hd₁ hp₁ hp
    · exact disjoint_left.mp hd₂ hp₂ hp
  have hex : ∃ Δ : Set M.S, IsInsideDisc M C Δ := by
    rcases hcomp_mem with hcomp_eq | hcomp_eq
    · refine ⟨Δ₂, hΔ₂, hbd₂.trans hU.symm, disjoint_left.mpr fun x hx₂ hxinf => ?_⟩
      have hx₁ : x ∈ Δ₁ \ (subdrawingOfSubgraph M C).U := hcomp_eq ▸ hinf_sub_comp hxinf
      exact hx₁.2 (hinter ▸ ⟨hx₁.1, hx₂⟩)
    · rw [mem_singleton_iff] at hcomp_eq
      refine ⟨Δ₁, hΔ₁, hbd₁.trans hU.symm, disjoint_left.mpr fun x hx₁ hxinf => ?_⟩
      have hx₂ : x ∈ Δ₂ \ (subdrawingOfSubgraph M C).U := hcomp_eq ▸ hinf_sub_comp hxinf
      exact hx₂.2 (hinter ▸ ⟨hx₁, hx₂.1⟩)
  refine ⟨hex, fun D₁ D₂ hD₁ hD₂ => ?_⟩
  have h₁ := huniq D₁ hD₁.1 (hD₁.2.1.trans hU)
  have h₂ := huniq D₂ hD₂.1 (hD₂.2.1.trans hU)
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · rfl
  · exact (hnot_both ⟨hD₁.2.2, hD₂.2.2⟩).elim
  · exact (hnot_both ⟨hD₂.2.2, hD₁.2.2⟩).elim
  · rfl

/-- If `IsInsideDisc M C₁ Δ₁`, `IsInsideDisc M C₂ Δ₂`, `IsGraphCircuit G C₂`, and
`discBd Δ₂ ⊆ Δ₁`, then `Δ₂ ⊆ Δ₁`. -/
theorem insideDisc_subset_of_bd_subset {G : Graph α β} (M : PlanarDrawing G)
    {C₁ C₂ : Graph α β} {Δ₁ Δ₂ : Set M.S}
    (hC₂ : IsGraphCircuit G C₂)
    (hΔ₁ : IsInsideDisc M C₁ Δ₁) (hΔ₂ : IsInsideDisc M C₂ Δ₂)
    (hbd : discBd Δ₂ ⊆ Δ₁) : Δ₂ ⊆ Δ₁ := by
  obtain ⟨F, ⟨hF_sub, hF_disc, hF_bd, _⟩, _⟩ :=
    disc_oArc Δ₁ (discBd Δ₂) hΔ₁.1 hbd hΔ₂.1.isOArc_discBd
  have hF_inside : IsInsideDisc M C₂ F :=
    ⟨hF_disc, hF_bd.trans hΔ₂.2.1, hΔ₁.2.2.mono_left hF_sub⟩
  have huniq := (exists_unique_insideDisc M hC₂).2 Δ₂ F hΔ₂ hF_inside
  exact huniq ▸ hF_sub

/-- If `C₁, C₂` are vertex-disjoint circuits of `G` with `IsInsideDisc M C₁ Δ₁`,
`IsInsideDisc M C₂ Δ₂`, and `Δ₂ ⊆ Δ₁`, then `Δ₂ ⊆ interior Δ₁`. -/
theorem insideDisc_subset_interior_of_disjoint {G : Graph α β} (M : PlanarDrawing G)
    {C₁ C₂ : Graph α β} {Δ₁ Δ₂ : Set M.S}
    (hC₁ : IsGraphCircuit G C₁) (hC₂ : IsGraphCircuit G C₂)
    (hdisjV : Disjoint V(C₁) V(C₂))
    (hΔ₁ : IsInsideDisc M C₁ Δ₁) (hΔ₂ : IsInsideDisc M C₂ Δ₂) (hsub : Δ₂ ⊆ Δ₁) :
    Δ₂ ⊆ interior Δ₁ := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  obtain ⟨hR₁_circ, hR₁_sub, hU₁⟩ := isCircuit_subdrawingOfSubgraph M hC₁
  obtain ⟨_, hR₂_sub, hU₂⟩ := isCircuit_subdrawingOfSubgraph M hC₂
  have hdisj_RV : Disjoint (subdrawingOfSubgraph M C₁).V (subdrawingOfSubgraph M C₂).V := by
    rw [(subdrawingOfSubgraph_spec M hC₁.1).2.1, (subdrawingOfSubgraph_spec M hC₂.1).2.1]
    rw [Set.disjoint_left]
    rintro _ ⟨u, hu, rfl⟩ ⟨v, hv, huv⟩
    have heq := (gmap_fwd_of_planarDrawing M).bijV.injOn
      (hC₁.1.vertexSet_mono hu) (hC₂.1.vertexSet_mono hv) huv.symm
    exact Set.disjoint_left.mp hdisjV hu (heq ▸ hv)
  obtain ⟨_, hdisjU⟩ := subdrawing_disjoint_U_of_disjoint_V hR₁_sub hR₂_sub hdisj_RV
  have hfr₁ : frontier Δ₁ = (subdrawingOfSubgraph M C₁).U := by
    rw [GM11.IsClosedDisc.frontier_eq_discBd hS hΔ₁.1, hΔ₁.2.1, hU₁]
  have hfr₂ : frontier Δ₂ = (subdrawingOfSubgraph M C₂).U := by
    rw [GM11.IsClosedDisc.frontier_eq_discBd hS hΔ₂.1, hΔ₂.2.1, hU₂]
  intro x hx₂
  have hx₁ : x ∈ Δ₁ := hsub hx₂
  by_contra hx_not_int
  have hx_fr₁ : x ∈ frontier Δ₁ := ⟨subset_closure hx₁, hx_not_int⟩
  rw [hfr₁] at hx_fr₁
  obtain ⟨φ⟩ := GM11.IsCircuit.isOArc_U hR₁_circ
  have hU₁_range : (subdrawingOfSubgraph M C₁).U = range (Subtype.val ∘ φ) := by
    ext z
    exact ⟨fun hz => ⟨φ.symm ⟨z, hz⟩, by simp⟩, fun ⟨w, hw⟩ => hw ▸ (φ w).2⟩
  have hU₁_conn : IsPreconnected (subdrawingOfSubgraph M C₁).U := by
    rw [hU₁_range]
    exact isPreconnected_range (continuous_subtype_val.comp φ.continuous)
  have hdisj_fr₂ : Disjoint (subdrawingOfSubgraph M C₁).U (frontier Δ₂) := by
    rwa [hfr₂]
  rcases GM11.subset_or_disjoint_of_frontier hΔ₂.1.isClosed hU₁_conn hdisj_fr₂ with
    hU₁_sub_Δ₂ | hU₁_disj_Δ₂
  · have hx_fr₂_not : x ∉ frontier Δ₂ := disjoint_left.mp hdisj_fr₂ hx_fr₁
    have hx_int₂ : x ∈ interior Δ₂ := by
      by_contra hni₂
      exact hx_fr₂_not ⟨subset_closure hx₂, hni₂⟩
    exact hx_not_int (interior_mono hsub hx_int₂)
  · exact disjoint_left.mp hU₁_disj_Δ₂ hx_fr₁ hx₂

/-- For any closed disc `Δ` in a closed surface `S`, `discInt Δ = interior Δ`. -/
theorem discInt_eq_interior_of_isClosedDisc (hS : IsClosedSurface S) {Δ : Set S}
    (hΔ : IsClosedDisc Δ) : discInt Δ = interior Δ := by
  have : T2Space S := hS.2.1
  have hfr : frontier Δ = discBd Δ := GM11.IsClosedDisc.frontier_eq_discBd hS hΔ
  ext x
  simp only [discInt, mem_sdiff, ← hfr, frontier]
  constructor
  · rintro ⟨hxΔ, hnot⟩
    by_contra hx_int
    exact hnot ⟨subset_closure hxΔ, hx_int⟩
  · intro hx_int
    exact ⟨interior_subset hx_int, fun ⟨_, hni⟩ => hni hx_int⟩

/-- Every closed disc `Δ` in `M.S` with `discBd Δ ⊆ M.drawing.U` contains a region
`R ∈ M.drawing.R` in its interior `interior Δ`. -/
theorem exists_region_subset_interior_disc {G : Graph α β} (M : PlanarDrawing G) {Δ : Set M.S}
    (hΔ : IsClosedDisc Δ) (hbd : discBd Δ ⊆ M.drawing.U) :
    ∃ R ∈ M.drawing.R, R ⊆ interior Δ := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have : T2Space M.S := hS.2.1
  have hfr : frontier Δ = discBd Δ := GM11.IsClosedDisc.frontier_eq_discBd hS hΔ
  have hint_ne : (interior Δ).Nonempty := by
    rw [← discInt_eq_interior_of_isClosedDisc hS hΔ]
    exact hΔ.nonempty_discInt
  obtain ⟨y, hy_int, hy_not_U⟩ :=
    GM11.exists_notMem_U (Γ := M.drawing) hS isOpen_interior hint_ne
  obtain ⟨R, hR, hyR⟩ := GM11.exists_region_of_notMem hy_not_U
  have hdisj_fr : Disjoint R (frontier Δ) := by
    rw [hfr]
    refine disjoint_left.mpr fun z hzR hzBd => ?_
    exact GM11.region_subset hR hzR (hbd hzBd)
  have hR_sub_Δ : R ⊆ Δ := by
    rcases GM11.subset_or_disjoint_of_frontier hΔ.isClosed
        (GM11.region_isPreconnected hR) hdisj_fr with hsub | hdisj
    · exact hsub
    · exact (disjoint_left.mp hdisj hyR (interior_subset hy_int)).elim
  refine ⟨R, hR, fun z hzR => ?_⟩
  by_contra hz_not_int
  exact disjoint_left.mp hdisj_fr hzR ⟨subset_closure (hR_sub_Δ hzR), hz_not_int⟩

/-- **Jordan Region-Chain Crossing Lemma:**
If `Δ : Fin m → Set M.S` is a sequence of nested closed discs with `discBd (Δ i) ⊆ M.drawing.U`,
`Disjoint (Δ 0) M.infRegion`, and `Δ j ⊆ interior (Δ i)` for `i < j`, then in any region chain
`R_seq : Fin (k + 1) → Set M.S` of `M` starting at `R_seq 0 = M.infRegion`, for every `r ≤ k`
and `i : Fin m` with `r ≤ i.1`, `Disjoint (R_seq r) (Δ i)`. -/
theorem regionChain_disjoint_nested_discs {G : Graph α β} (M : PlanarDrawing G)
    {m : ℕ} {Δ : Fin m → Set M.S}
    (hΔ_disc : ∀ i : Fin m, IsClosedDisc (Δ i))
    (hΔ_bd : ∀ i : Fin m, discBd (Δ i) ⊆ M.drawing.U)
    (hΔ_inf : ∀ h0 : 0 < m, Disjoint (Δ ⟨0, h0⟩) M.infRegion)
    (hΔ_nest : ∀ ⦃i j : Fin m⦄, i < j → Δ j ⊆ interior (Δ i))
    {k : ℕ} {R_seq : Fin (k + 1) → Set M.S}
    (hR_mem : ∀ j : Fin (k + 1), R_seq j ∈ M.drawing.R)
    (hR_0 : R_seq ⟨0, Nat.zero_lt_succ k⟩ = M.infRegion)
    (hR_step : ∀ j : Fin k, ∃ v ∈ M.drawing.V,
      v ∈ closure (R_seq ⟨j.1, Nat.lt_succ_of_lt j.2⟩) ∧
      v ∈ closure (R_seq ⟨j.1 + 1, Nat.succ_lt_succ j.2⟩)) :
    ∀ (r : ℕ) (hr : r < k + 1) (i : Fin m), r ≤ i.1 →
      Disjoint (R_seq ⟨r, hr⟩) (Δ i) := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have : T2Space M.S := hS.2.1
  intro r
  induction r with
  | zero =>
    intro hr i _
    rw [hR_0]
    have h0 : 0 < m := i.pos
    have hsub0 : Δ i ⊆ Δ ⟨0, h0⟩ := by
      rcases Nat.eq_zero_or_pos i.1 with hi0 | hipos
      · have : i = ⟨0, h0⟩ := Fin.ext hi0
        rw [this]
      · exact (hΔ_nest (show (⟨0, h0⟩ : Fin m) < i from hipos)).trans interior_subset
    exact (hΔ_inf h0).symm.mono_right hsub0
  | succ r ih =>
    intro hr i hri
    have hr_lt : r < k := Nat.lt_of_succ_lt_succ hr
    have hi_pos : 0 < i.1 := by omega
    let i_prev : Fin m := ⟨i.1 - 1, by omega⟩
    have hprev_lt : i_prev < i := by
      change i.1 - 1 < i.1
      omega
    have hdisj_prev : Disjoint (R_seq ⟨r, Nat.lt_succ_of_lt hr_lt⟩) (Δ i_prev) :=
      ih (Nat.lt_succ_of_lt hr_lt) i_prev (by dsimp [i_prev]; omega)
    obtain ⟨v, _, hv1, hv2⟩ := hR_step ⟨r, hr_lt⟩
    have hv_not_int_prev : v ∉ interior (Δ i_prev) := by
      intro hv_int
      have hdisj_open :
          Disjoint (interior (Δ i_prev)) (R_seq ⟨r, Nat.lt_succ_of_lt hr_lt⟩) :=
        hdisj_prev.symm.mono_left interior_subset
      exact disjoint_left.mp (hdisj_open.closure_right isOpen_interior) hv_int hv1
    have hv_not_Δi : v ∉ Δ i := fun hv_Δi => hv_not_int_prev (hΔ_nest hprev_lt hv_Δi)
    have hRr1 : R_seq ⟨r + 1, hr⟩ ∈ M.drawing.R := hR_mem ⟨r + 1, hr⟩
    have hfr_i : frontier (Δ i) = discBd (Δ i) :=
      GM11.IsClosedDisc.frontier_eq_discBd hS (hΔ_disc i)
    have hdisj_fr : Disjoint (R_seq ⟨r + 1, hr⟩) (frontier (Δ i)) := by
      rw [hfr_i]
      refine disjoint_left.mpr fun z hzR hzBd => ?_
      exact GM11.region_subset hRr1 hzR (hΔ_bd i hzBd)
    rcases GM11.subset_or_disjoint_of_frontier (hΔ_disc i).isClosed
        (GM11.region_isPreconnected hRr1) hdisj_fr with hsub | hdisj
    · exfalso
      exact hv_not_Δi (closure_minimal hsub (hΔ_disc i).isClosed hv2)
    · exact hdisj

/-- In a drawing `M` with a `d$-shell `C_1, …, C_d`, any circuit
`C' ≤ deleteVertices G (⋃ i, V(C_i))` encloses a region `R ∈ M.drawing.R` that cannot be
reached from `M.infRegion` by a region chain of length `k ≤ d` (Graph Minors III, proof of `(2.3)`,
page 55). -/
theorem exists_region_no_chain_of_circuit_delete_shell {G : Graph α β} {M : PlanarDrawing G}
    {d : ℕ} {C : Fin d → Graph α β} (hShell : IsDShell M d C)
    (C' : Graph α β) (hC'_le : C' ≤ GM09.deleteVertices G (⋃ i : Fin d, V(C i)))
    (hCirc : GM09.IsGraphCircuit G C') :
    ∃ R ∈ M.drawing.R, ∀ k ≤ d, ¬ IsRegionChain M R k := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have hex_Δ : ∀ i : Fin d, ∃ Δ : Set M.S, IsInsideDisc M (C i) Δ :=
    fun i => (exists_unique_insideDisc M (hShell.isNested.1 i)).1
  choose Δ hΔ using hex_Δ
  obtain ⟨⟨Δ', hΔ'⟩, _⟩ := exists_unique_insideDisc M hCirc
  let Δ_ext : Fin (d + 1) → Set M.S := fun j =>
    if hj : j.1 < d then Δ ⟨j.1, hj⟩ else Δ'
  have hΔ_ext_disc : ∀ j : Fin (d + 1), IsClosedDisc (Δ_ext j) := by
    intro j
    dsimp [Δ_ext]
    split_ifs with hj
    · exact (hΔ ⟨j.1, hj⟩).1
    · exact hΔ'.1
  have hΔ_ext_bd : ∀ j : Fin (d + 1), discBd (Δ_ext j) ⊆ M.drawing.U := by
    intro j
    dsimp [Δ_ext]
    split_ifs with hj
    · rw [(hΔ ⟨j.1, hj⟩).2.1, (isCircuit_subdrawingOfSubgraph M (hShell.isNested.1 ⟨j.1, hj⟩)).2.2]
      exact (isCircuit_subdrawingOfSubgraph M (hShell.isNested.1 ⟨j.1, hj⟩)).2.1.U_subset
    · rw [hΔ'.2.1, (isCircuit_subdrawingOfSubgraph M hCirc).2.2]
      exact (isCircuit_subdrawingOfSubgraph M hCirc).2.1.U_subset
  have hΔ_ext_inf : ∀ h0 : 0 < d + 1, Disjoint (Δ_ext ⟨0, h0⟩) M.infRegion := by
    intro h0
    by_cases hd : 0 < d
    · simp only [Δ_ext, hd, ↓reduceDIte]
      exact (hΔ ⟨0, hd⟩).2.2
    · simp only [Δ_ext, hd, ↓reduceDIte]
      exact hΔ'.2.2
  have hΔ_shell_nest : ∀ ⦃i j : Fin d⦄, i < j → Δ j ⊆ interior (Δ i) := by
    intro i j hij
    obtain ⟨hdisjV, D_j, D_i, hDj, hDi, hsubD⟩ := hShell.isNested.2 hij
    have heq_j : Δ j = D_j := (exists_unique_insideDisc M (hShell.isNested.1 j)).2 _ _ (hΔ j) hDj
    have heq_i : Δ i = D_i := (exists_unique_insideDisc M (hShell.isNested.1 i)).2 _ _ (hΔ i) hDi
    exact insideDisc_subset_interior_of_disjoint M (hShell.isNested.1 i) (hShell.isNested.1 j)
      hdisjV (hΔ i) (hΔ j) (heq_j.symm ▸ heq_i.symm ▸ hsubD)
  have hΔ'_sub_shell : ∀ i : Fin d, Δ' ⊆ interior (Δ i) := by
    intro i
    have hdisj_Ci_C' : Disjoint V(C i) V(C') := by
      rw [Set.disjoint_left]
      intro v hvCi hvC'
      have hv_del : v ∈ V(G) \ ⋃ k : Fin d, V(C k) := hC'_le.vertexSet_mono hvC'
      exact hv_del.2 (mem_iUnion.mpr ⟨i, hvCi⟩)
    have hbd_sub : discBd Δ' ⊆ Δ i := by
      rw [hΔ'.2.1]
      rw [graphDrawingSubgraphU]
      refine union_subset (iUnion₂_subset fun v hvC' => ?_) (iUnion₂_subset fun e heC' => ?_)
      · have hv_del : v ∈ V(G) \ ⋃ k : Fin d, V(C k) := hC'_le.vertexSet_mono hvC'
        have hd_pos : 0 < d := i.pos
        rcases hShell.vertex_in_or_inside hd_pos v hv_del.1 with ⟨k, hvk⟩ | hinside
        · exact (hv_del.2 (mem_iUnion.mpr ⟨k, hvk⟩)).elim
        · obtain ⟨_, D_last, hD_last, hv_in⟩ := hinside
          let i_last : Fin d := ⟨d - 1, Nat.sub_lt hd_pos zero_lt_one⟩
          have heq_last : Δ i_last = D_last :=
            (exists_unique_insideDisc M (hShell.isNested.1 i_last)).2 _ _ (hΔ i_last) hD_last
          have hsub_last_i : Δ i_last ⊆ Δ i := by
            rcases eq_or_lt_of_le (show i.1 ≤ i_last.1 by dsimp [i_last]; omega) with heq | hlt
            · rw [Fin.ext heq]
            · exact (hΔ_shell_nest hlt).trans interior_subset
          exact hv_in.trans (heq_last ▸ hsub_last_i)
      · obtain ⟨u, w, hl⟩ := C'.exists_isLink_of_mem_edgeSet heC'
        have hlG : G.IsLink e u w := hl.mono hCirc.1
        have hu_del : u ∈ V(G) \ ⋃ k : Fin d, V(C k) := hC'_le.vertexSet_mono hl.left_mem
        have hd_pos : 0 < d := i.pos
        let i_last : Fin d := ⟨d - 1, Nat.sub_lt hd_pos zero_lt_one⟩
        have hu_in_i : graphDrawingVertexSet M.graphDrawing u ⊆ Δ i := by
          rcases hShell.vertex_in_or_inside hd_pos u hu_del.1 with ⟨k, huk⟩ | ⟨_, D_last, hD_last, hu_in⟩
          · exact (hu_del.2 (mem_iUnion.mpr ⟨k, huk⟩)).elim
          · have heq_last : Δ i_last = D_last :=
              (exists_unique_insideDisc M (hShell.isNested.1 i_last)).2 _ _ (hΔ i_last) hD_last
            have hsub_last_i : Δ i_last ⊆ Δ i := by
              rcases eq_or_lt_of_le (show i.1 ≤ i_last.1 by dsimp [i_last]; omega) with heq | hlt
              · rw [Fin.ext heq]
              · exact (hΔ_shell_nest hlt).trans interior_subset
            exact hu_in.trans (heq_last ▸ hsub_last_i)
        have he_mem : drawingFwdE M e ∈ (subdrawingOfSubgraph M C').E := by
          rw [(subdrawingOfSubgraph_spec M hCirc.1).2.2.1]
          exact mem_image_of_mem _ heC'
        have he_D : drawingFwdE M e ∈ M.drawing.E :=
          (subdrawingOfSubgraph_spec M hCirc.1).1.2 he_mem
        have hconn_e : IsPreconnected (drawingFwdE M e) :=
          he_D.2.2.1.isConnected.isPreconnected
        have hdisj_e_bd : Disjoint (drawingFwdE M e) (frontier (Δ i)) := by
          rw [GM11.IsClosedDisc.frontier_eq_discBd hS (hΔ i).1, (hΔ i).2.1,
            (isCircuit_subdrawingOfSubgraph M (hShell.isNested.1 i)).2.2]
          have hdisj_RV : Disjoint (subdrawingOfSubgraph M (C i)).V (subdrawingOfSubgraph M C').V := by
            rw [(subdrawingOfSubgraph_spec M (hShell.isNested.1 i).1).2.1,
              (subdrawingOfSubgraph_spec M hCirc.1).2.1, Set.disjoint_left]
            rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
            have heq := (gmap_fwd_of_planarDrawing M).bijV.injOn
              ((hShell.isNested.1 i).1.vertexSet_mono ha) (hCirc.1.vertexSet_mono hb) hab.symm
            exact Set.disjoint_left.mp hdisj_Ci_C' ha (heq ▸ hb)
          obtain ⟨_, hdisjU⟩ := subdrawing_disjoint_U_of_disjoint_V
            (isCircuit_subdrawingOfSubgraph M (hShell.isNested.1 i)).2.1
            (isCircuit_subdrawingOfSubgraph M hCirc).2.1 hdisj_RV
          exact hdisjU.symm.mono_left fun z hz =>
            (subdrawingOfSubgraph M C').closure_subset_U he_mem (subset_closure hz)
        rcases GM11.subset_or_disjoint_of_frontier (hΔ i).1.isClosed hconn_e hdisj_e_bd with
          he_sub | he_disj
        · rw [graphDrawingEdgeSet_eq M hlG.edge_mem]
          exact closure_minimal he_sub (hΔ i).1.isClosed
        · exfalso
          have hlD := ((gmap_fwd_of_planarDrawing M).link hlG.edge_mem hlG.left_mem hlG.right_mem).mp hlG
          have hu_cl : drawingFwdV M u ∈ closure (drawingFwdE M e) := by
            have : drawingFwdV M u ∈ closure (drawingFwdE M e) ∩ M.drawing.V := by
              rw [hlD.2.2.2]
              exact mem_insert _ _
            exact this.1
          have hu_Δi : drawingFwdV M u ∈ Δ i := by
            rw [graphDrawingVertexSet_eq_singleton M hu_del.1, singleton_subset_iff] at hu_in_i
            exact hu_in_i
          have hu_not_fr : drawingFwdV M u ∉ frontier (Δ i) := by
            rw [GM11.IsClosedDisc.frontier_eq_discBd hS (hΔ i).1, (hΔ i).2.1,
              (isCircuit_subdrawingOfSubgraph M (hShell.isNested.1 i)).2.2]
            intro hu_U
            have hu_RC' : drawingFwdV M u ∈ (subdrawingOfSubgraph M C').U := by
              apply (subdrawingOfSubgraph M C').V_subset_U
              rw [(subdrawingOfSubgraph_spec M hCirc.1).2.1]
              exact mem_image_of_mem _ hl.left_mem
            have hdisj_RV : Disjoint (subdrawingOfSubgraph M (C i)).V (subdrawingOfSubgraph M C').V := by
              rw [(subdrawingOfSubgraph_spec M (hShell.isNested.1 i).1).2.1,
                (subdrawingOfSubgraph_spec M hCirc.1).2.1, Set.disjoint_left]
              rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
              have heq := (gmap_fwd_of_planarDrawing M).bijV.injOn
                ((hShell.isNested.1 i).1.vertexSet_mono ha) (hCirc.1.vertexSet_mono hb) hab.symm
              exact Set.disjoint_left.mp hdisj_Ci_C' ha (heq ▸ hb)
            obtain ⟨_, hdisjU⟩ := subdrawing_disjoint_U_of_disjoint_V
              (isCircuit_subdrawingOfSubgraph M (hShell.isNested.1 i)).2.1
              (isCircuit_subdrawingOfSubgraph M hCirc).2.1 hdisj_RV
            exact Set.disjoint_left.mp hdisjU hu_U hu_RC'
          have hu_int : drawingFwdV M u ∈ interior (Δ i) := by
            by_contra hni
            exact hu_not_fr ⟨subset_closure hu_Δi, hni⟩
          have hdisj_open : Disjoint (interior (Δ i)) (drawingFwdE M e) :=
            he_disj.symm.mono_left interior_subset
          exact Set.disjoint_left.mp (hdisj_open.closure_right isOpen_interior) hu_int hu_cl
    have hsub_Δ : Δ' ⊆ Δ i := insideDisc_subset_of_bd_subset M hCirc (hΔ i) hΔ' hbd_sub
    exact insideDisc_subset_interior_of_disjoint M (hShell.isNested.1 i) hCirc
      hdisj_Ci_C' (hΔ i) hΔ' hsub_Δ
  have hΔ_ext_nest : ∀ ⦃i j : Fin (d + 1)⦄, i < j → Δ_ext j ⊆ interior (Δ_ext i) := by
    intro i j hij
    have hi_lt : i.1 < d := by omega
    by_cases hj_lt : j.1 < d
    · simp only [Δ_ext, hi_lt, hj_lt, ↓reduceDIte]
      exact hΔ_shell_nest hij
    · simp only [Δ_ext, hi_lt, hj_lt, ↓reduceDIte]
      exact hΔ'_sub_shell ⟨i.1, hi_lt⟩
  obtain ⟨R, hR_mem, hR_sub⟩ :=
    exists_region_subset_interior_disc M hΔ'.1 (by
      have := hΔ_ext_bd ⟨d, Nat.lt_succ_self d⟩
      simpa [Δ_ext] using this)
  refine ⟨R, hR_mem, fun k hkd ⟨R_seq, hseq_mem, hseq_0, hseq_k, hseq_step⟩ => ?_⟩
  have hdisj := regionChain_disjoint_nested_discs M hΔ_ext_disc hΔ_ext_bd hΔ_ext_inf hΔ_ext_nest
    hseq_mem hseq_0 hseq_step k (Nat.lt_succ_self k) ⟨d, Nat.lt_succ_self d⟩ hkd
  rw [hseq_k] at hdisj
  have hΔ_ext_d : Δ_ext ⟨d, Nat.lt_succ_self d⟩ = Δ' := by simp [Δ_ext]
  rw [hΔ_ext_d] at hdisj
  obtain ⟨x, hxR⟩ := GM11.region_nonempty hR_mem
  exact Set.disjoint_left.mp hdisj hxR (interior_subset (hR_sub hxR))

end SubdrawingAndDiscs

/-! ## Part 2: Surface Shell Invariant and Radius Preservation in `R_N` -/

section SurfaceShellInvariant

variable {S : Type} [TopologicalSpace S]

/-- For a subdrawing `N` of `D` and a region `R_N ∈ N.R`, `R_N \ D.U` is the union of the regions
`q ∈ D.R` that are contained in `R_N`. -/
theorem RN_sdiff_U_eq_biUnion_regions (hS : IsClosedSurface S) {D N : Drawing S}
    (hNs : N.IsSubdrawing D) {R_N : Set S} (hRN : R_N ∈ N.R) :
    R_N \ D.U = ⋃ (q ∈ D.R) (_ : q ⊆ R_N), q := by
  have : T2Space S := hS.2.1
  ext x
  simp only [mem_sdiff, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨hxRN, hxU⟩
    obtain ⟨q, hq, hxq⟩ := GM11.exists_region_of_notMem hxU
    have hq_sub : q ⊆ R_N :=
      GM11.subset_region hRN (GM11.region_isPreconnected hq)
        (Set.disjoint_left.mpr fun z hz hzNU => GM11.region_subset hq hz (hNs.U_subset hzNU))
        hxq hxRN
    exact ⟨q, hq, hq_sub, hxq⟩
  · rintro ⟨q, hq, hq_sub, hxq⟩
    exact ⟨hq_sub hxq, GM11.region_subset hq hxq⟩

/-- For a subdrawing `N` of `D` and a region `R_N ∈ N.R`, `closure R_N` is the union of `closure q`
over all regions `q ∈ D.R` with `q ⊆ R_N`. -/
theorem closure_RN_eq_biUnion_closure_regions (hS : IsClosedSurface S) [PreconnectedSpace S]
    {D N : Drawing S} (hNs : N.IsSubdrawing D) {R_N : Set S} (hRN : R_N ∈ N.R) :
    closure R_N = ⋃ (q ∈ D.R) (_ : q ⊆ R_N), closure q := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  apply Subset.antisymm
  · have hcl_sdiff : closure R_N ⊆ closure (R_N \ D.U) := by
      intro x hx
      rw [mem_closure_iff] at hx ⊢
      intro O hO hxO
      have hO_RN : IsOpen (O ∩ R_N) := hO.inter (GM11.region_isOpen hRN)
      obtain ⟨y, hyO, hyRN⟩ := hx O hO hxO
      obtain ⟨z, ⟨hzO, hzRN⟩, hzU⟩ :=
        GM11.exists_notMem_U (Γ := D) hS hO_RN ⟨y, hyO, hyRN⟩
      exact ⟨z, hzO, hzRN, hzU⟩
    have hfin : {q ∈ D.R | q ⊆ R_N}.Finite :=
      (GM11.finite_R hS D).subset fun q hq => hq.1
    have hcl_closed : IsClosed (⋃ (q ∈ D.R) (_ : q ⊆ R_N), closure q) := by
      have heq : (⋃ (q ∈ D.R) (_ : q ⊆ R_N), closure q) =
          ⋃ q ∈ {q ∈ D.R | q ⊆ R_N}, closure q := by
        ext z
        simp only [mem_iUnion, mem_ofPred_eq, exists_prop, and_assoc]
      rw [heq]
      exact hfin.isClosed_biUnion fun _ _ => isClosed_closure
    refine hcl_sdiff.trans (closure_minimal ?_ hcl_closed)
    rw [RN_sdiff_U_eq_biUnion_regions hS hNs hRN]
    exact iUnion₂_mono fun q hq => iUnion_mono fun hq_sub => subset_closure
  · exact iUnion₂_subset fun q _ => iUnion_subset fun hq_sub => closure_mono hq_sub

/-- If `R_N ∈ N.R` contains `r₀`, `N.U ⊆ interior Δ_last`, and every vertex of `D.V ∩ Δ_last` is in
`C_last.V ∪ N.V` (with `C_last.IsSubdrawing D` and `discBd Δ_last = C_last.U`), then every region
`q ∈ D.R` with `q ⊆ R_N` and `q ⊆ interior Δ_last` has a vertex of `C_last.V` in its closure. -/
theorem region_in_RN_incident_shell (hS : IsClosedSurface S)
    {D N C_last : Drawing S} {r₀ R_N Δ_last : Set S}
    (_hNs : N.IsSubdrawing D) (_hCs : C_last.IsSubdrawing D)
    (hr₀ : r₀ ∈ D.R) (hRN : R_N ∈ N.R) (hr₀_sub : r₀ ⊆ R_N)
    (hΔ : IsClosedDisc Δ_last) (_hbd : discBd Δ_last = C_last.U)
    (hΔ_disj_r₀ : Disjoint Δ_last r₀)
    (hV_split : ∀ v ∈ D.V, v ∈ Δ_last → v ∈ C_last.V ∨ v ∈ N.V)
    (hE_N : ∀ e ∈ D.E, closure e ∩ D.V ⊆ N.V → e ∈ N.E)
    {q : Set S} (hq : q ∈ D.R) (hq_RN : q ⊆ R_N) (hq_int : q ⊆ interior Δ_last) :
    ∃ u ∈ C_last.V, u ∈ closure q := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  have hq_cl_Δ : closure q ⊆ Δ_last :=
    closure_minimal (hq_int.trans interior_subset) hΔ.isClosed
  have hfr_not_sub : ¬ frontier q ⊆ N.U := by
    intro hfr_sub
    have hdisj_fr : Disjoint R_N (frontier q) := by
      refine Set.disjoint_left.mpr fun z hzRN hzfr => ?_
      exact GM11.region_subset hRN hzRN (hfr_sub hzfr)
    obtain ⟨z₀, hz₀⟩ := GM11.region_nonempty hq
    have hRN_sub_cl : R_N ⊆ closure q := by
      rcases GM11.subset_or_disjoint_of_frontier isClosed_closure
          (GM11.region_isPreconnected hRN)
          (hdisj_fr.mono_right frontier_closure_subset) with hsub | hdisj
      · exact hsub
      · exact (Set.disjoint_left.mp hdisj (hq_RN hz₀) (subset_closure hz₀)).elim
    obtain ⟨p₀, hp₀⟩ := GM11.region_nonempty hr₀
    exact Set.disjoint_left.mp hΔ_disj_r₀ (hq_cl_Δ (hRN_sub_cl (hr₀_sub hp₀))) hp₀
  obtain ⟨x, hx_fr, hx_not_NU⟩ := not_subset.mp hfr_not_sub
  have hx_cl : x ∈ closure q := hx_fr.1
  have hx_DU : x ∈ D.U := by
    rcases GM11.closure_region_subset hq hx_cl with hxq | hxU
    · have hx_int : x ∈ interior q := by rwa [(GM11.region_isOpen hq).interior_eq]
      exact (hx_fr.2 hx_int).elim
    · exact hxU
  have hx_Δ : x ∈ Δ_last := hq_cl_Δ hx_cl
  by_cases hxV : x ∈ D.V
  · rcases hV_split x hxV hx_Δ with hxC | hxN
    · exact ⟨x, hxC, hx_cl⟩
    · exact (hx_not_NU (N.V_subset_U hxN)).elim
  · obtain ⟨e, heD, hxe⟩ := D.exists_edge_of_mem hx_DU hxV
    have he_cl_q : closure e ⊆ closure q :=
      closure_minimal (GM11.edge_subset_closure_of_incident hS heD hq ⟨x, hxe, hx_cl⟩)
        isClosed_closure
    have he_not_N : e ∉ N.E := fun heN =>
      hx_not_NU (N.closure_subset_U heN (subset_closure hxe))
    have hnot_sub_NV : ¬ closure e ∩ D.V ⊆ N.V := fun hsub => he_not_N (hE_N e heD hsub)
    obtain ⟨u, ⟨hue, huV⟩, hu_not_N⟩ := not_subset.mp hnot_sub_NV
    have hu_cl_q : u ∈ closure q := he_cl_q hue
    have hu_C : u ∈ C_last.V :=
      (hV_split u huV (hq_cl_Δ hu_cl_q)).resolve_right hu_not_N
    exact ⟨u, hu_C, hu_cl_q⟩

/-- The subdrawing of `N` consisting of the vertices and edges incident with a region `R_N ∈ N.R`
(Graph Minors III, Section 2, page 53: "Let $C_{d'}$ be the subgraph of $H$ consisting of the
vertices and edges incident with the infinite region of $N$."). -/
noncomputable def perimDraw [T2Space S] (N : Drawing S) (R_N : Set S) : Drawing S :=
  N.span (N.V ∩ closure R_N) {e ∈ N.E | e ⊆ closure R_N}

theorem perimDraw_spec (hS : IsClosedSurface S) {N : Drawing S} {R_N : Set S} (hRN : R_N ∈ N.R) :
    haveI : T2Space S := hS.2.1
    (perimDraw N R_N).IsSubdrawing N ∧
    (perimDraw N R_N).V = N.V ∩ closure R_N ∧
    (perimDraw N R_N).E = {e ∈ N.E | e ⊆ closure R_N} ∧
    (perimDraw N R_N).U = frontier R_N ∧
    (perimDraw N R_N).toGraph ≤ N.toGraph := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  have hSub : (perimDraw N R_N).IsSubdrawing N := by
    unfold perimDraw
    exact Drawing.span_isSubdrawing N _ _
  have hE : (perimDraw N R_N).E = {e ∈ N.E | e ⊆ closure R_N} := by
    rw [perimDraw, N.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun h => h.1
  have hV : (perimDraw N R_N).V = N.V ∩ closure R_N := by
    rw [perimDraw, N.span_V]
    refine Subset.antisymm (union_subset ?_ (iUnion₂_subset ?_)) fun x hx => Or.inl ⟨hx, hx.1⟩
    · intro x hx
      exact hx.1
    · rintro e ⟨⟨heN, he_cl⟩, _⟩ x ⟨hxe, hxV⟩
      exact ⟨hxV, closure_minimal he_cl isClosed_closure hxe⟩
  have hU : (perimDraw N R_N).U = frontier R_N := by
    rw [(perimDraw N R_N).U_eq, hV, hE]
    refine Subset.antisymm (union_subset ?_ (iUnion₂_subset ?_)) ?_
    · rintro x ⟨hxV, hxcl⟩
      refine ⟨hxcl, ?_⟩
      rw [(GM11.region_isOpen hRN).interior_eq]
      exact fun hxRN => GM11.region_subset hRN hxRN (N.V_subset_U hxV)
    · rintro e ⟨heN, he_cl⟩ x hxe
      refine ⟨closure_minimal he_cl isClosed_closure hxe, ?_⟩
      rw [(GM11.region_isOpen hRN).interior_eq]
      exact fun hxRN => GM11.region_subset hRN hxRN (N.closure_subset_U heN hxe)
    · intro x hxfr
      have hxcl : x ∈ closure R_N := hxfr.1
      have hxU : x ∈ N.U := by
        rcases GM11.closure_region_subset hRN hxcl with hxRN | hxU
        · have hx_int : x ∈ interior R_N := by rwa [(GM11.region_isOpen hRN).interior_eq]
          exact (hxfr.2 hx_int).elim
        · exact hxU
      by_cases hxV : x ∈ N.V
      · exact Or.inl ⟨hxV, hxcl⟩
      · obtain ⟨e, heN, hxe⟩ := N.exists_edge_of_mem hxU hxV
        have he_cl : e ⊆ closure R_N :=
          GM11.edge_subset_closure_of_incident hS heN hRN ⟨x, hxe, hxcl⟩
        exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨heN, he_cl⟩, subset_closure hxe⟩)
  have hle : (perimDraw N R_N).toGraph ≤ N.toGraph := by
    refine ⟨hSub.1, fun e u v hl => ?_⟩
    exact ⟨hSub.2 hl.1, hSub.1 hl.2.1, hSub.1 hl.2.2.1, by
      rw [← hSub.closure_inter_V hl.1]
      exact hl.2.2.2⟩
  exact ⟨hSub, hV, hE, hU, hle⟩

/-- The subdrawing `N` of `D` obtained by deleting the vertices of `C 0, ..., C (d' - 1)` and all
edges incident with them (Graph Minors III, Section 2, page 52: "Let $H$ be the graph obtained from
$G'$ by deleting the vertices in $V(C_1), \dots, V(C_{d'-1})$ and the edges incident with them;
and let $N$ be the drawing of $H$ obtained from $M'$ by the same deletion."). -/
noncomputable def innerDraw [T2Space S] (D : Drawing S) (d' : ℕ) (C : Fin d' → Drawing S) :
    Drawing S :=
  D.span (D.V \ ⋃ i : Fin d', (C i).V)
    {e ∈ D.E | closure e ∩ D.V ⊆ D.V \ ⋃ i : Fin d', (C i).V}

theorem innerDraw_spec [T2Space S] (D : Drawing S) (d' : ℕ) (C : Fin d' → Drawing S) :
    (innerDraw D d' C).IsSubdrawing D ∧
    (innerDraw D d' C).V = D.V \ ⋃ i : Fin d', (C i).V ∧
    (innerDraw D d' C).E = {e ∈ D.E | closure e ∩ D.V ⊆ D.V \ ⋃ i : Fin d', (C i).V} ∧
    (innerDraw D d' C).toGraph ≤ D.toGraph := by
  have hSub : (innerDraw D d' C).IsSubdrawing D := by
    unfold innerDraw
    exact Drawing.span_isSubdrawing D _ _
  have hE : (innerDraw D d' C).E =
      {e ∈ D.E | closure e ∩ D.V ⊆ D.V \ ⋃ i : Fin d', (C i).V} := by
    rw [innerDraw, D.span_E]
    ext e
    simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
    exact fun h => h.1
  have hV : (innerDraw D d' C).V = D.V \ ⋃ i : Fin d', (C i).V := by
    rw [innerDraw, D.span_V]
    refine Subset.antisymm (union_subset ?_ (iUnion₂_subset ?_)) fun x hx => Or.inl ⟨hx, hx.1⟩
    · intro x hx
      exact hx.1
    · rintro e ⟨⟨_, he_sub⟩, _⟩ x hx
      exact he_sub hx
  have hle : (innerDraw D d' C).toGraph ≤ D.toGraph := by
    refine ⟨hSub.1, fun e u v hl => ?_⟩
    exact ⟨hSub.2 hl.1, hSub.1 hl.2.1, hSub.1 hl.2.2.1, by
      rw [← hSub.closure_inter_V hl.1]
      exact hl.2.2.2⟩
  exact ⟨hSub, hV, hE, hle⟩

/-- Surface-level `d'`-shell invariant for `D : Drawing S` with infinite region `r₀ ∈ D.R`,
bundling the subdrawings `C : Fin d' → Drawing S` and their inside closed discs
`Δ : Fin d' → Set S` together with the inductive region-chain bound `(S3)` for shell vertices. -/
structure SurfaceDShell (D : Drawing S) (r₀ : Set S) (d' : ℕ)
    (C : Fin d' → Drawing S) (Δ : Fin d' → Set S) : Prop where
  r₀_mem : r₀ ∈ D.R
  isSubdrawing : ∀ j : Fin d', (C j).IsSubdrawing D
  isCircuit : ∀ j : Fin d', (C j).IsCircuit
  isClosedDisc : ∀ j : Fin d', IsClosedDisc (Δ j)
  discBd_eq : ∀ j : Fin d', discBd (Δ j) = (C j).U
  disjoint_inf : ∀ j : Fin d', Disjoint (Δ j) r₀
  disjoint_V : ∀ ⦃j j' : Fin d'⦄, j < j' → Disjoint (C j).V (C j').V
  disc_subset_interior : ∀ ⦃j j' : Fin d'⦄, j < j' → Δ j' ⊆ interior (Δ j)
  vertex_in_or_inside : ∀ (hd' : 0 < d'), ∀ v ∈ D.V,
    (∃ j : Fin d', v ∈ (C j).V) ∨ v ∈ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)
  edge_inside_of_ends : ∀ (j : Fin d'), ∀ e ∈ D.E,
    (∀ v ∈ closure e ∩ D.V, ∀ i : Fin d', i ≤ j → v ∉ (C i).V) → e ⊆ interior (Δ j)
  edge_induced : ∀ (j : Fin d') ⦃e : Set S⦄ ⦃u v : S⦄,
    D.toGraph.IsLink e u v → u ∈ (C j).V → v ∈ (C j).V → e ∈ (C j).E
  shell_vertex_chain : ∀ (j : Fin d'), ∀ u ∈ (C j).V,
    ∃ r_u ∈ D.R, u ∈ closure r_u ∧ Disjoint r_u (Δ j) ∧
      ∃ k ≤ j.1, ∃ R_seq : Fin (k + 1) → Set S,
        (∀ m, R_seq m ∈ D.R) ∧
        R_seq ⟨0, Nat.zero_lt_succ k⟩ = r₀ ∧
        R_seq ⟨k, Nat.lt_succ_self k⟩ = r_u ∧
        (∀ m, Disjoint (R_seq m) (Δ j)) ∧
        ∀ m : Fin k, ∃ w ∈ D.V, w ∉ interior (Δ j) ∧
          w ∈ closure (R_seq ⟨m.1, Nat.lt_succ_of_lt m.2⟩) ∧
          w ∈ closure (R_seq ⟨m.1 + 1, Nat.succ_lt_succ m.2⟩)

/-- Base case `d' = 0` of `SurfaceDShell`. -/
theorem surfaceDShell_zero {D : Drawing S} {r₀ : Set S} (hr₀ : r₀ ∈ D.R) :
    SurfaceDShell D r₀ 0 Fin.elim0 Fin.elim0 where
  r₀_mem := hr₀
  isSubdrawing j := Fin.elim0 j
  isCircuit j := Fin.elim0 j
  isClosedDisc j := Fin.elim0 j
  discBd_eq j := Fin.elim0 j
  disjoint_inf j := Fin.elim0 j
  disjoint_V j := Fin.elim0 j
  disc_subset_interior j := Fin.elim0 j
  vertex_in_or_inside hd' := (Nat.not_lt_zero 0 hd').elim
  edge_inside_of_ends j := Fin.elim0 j
  edge_induced j := Fin.elim0 j
  shell_vertex_chain j := Fin.elim0 j

/-- Any `SurfaceDShell` on `D` induces `IsDShell` on `planarDrawingOfDrawing hS hSph D r₀ hr₀`. -/
theorem SurfaceDShell.toIsDShell (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D : Drawing S} {r₀ : Set S} {d' : ℕ} {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ) :
    IsDShell (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d' (fun j => (C j).toGraph) := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let M := planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem
  have hSub_le : ∀ j : Fin d', (C j).toGraph ≤ D.toGraph := fun j => by
    refine ⟨(hShell.isSubdrawing j).1, fun e u v hl => ?_⟩
    exact ⟨(hShell.isSubdrawing j).2 hl.1, (hShell.isSubdrawing j).1 hl.2.1,
      (hShell.isSubdrawing j).1 hl.2.2.1, by
        rw [← (hShell.isSubdrawing j).closure_inter_V hl.1]
        exact hl.2.2.2⟩
  have hFwdV : ∀ v ∈ D.V, drawingFwdV M v = v := fun v hv => by
    have hv' : v ∈ V(D.toGraph) := hv
    simp [drawingFwdV, M, planarDrawingOfDrawing, hv']
    rfl
  have hFwdE : ∀ e ∈ D.E, drawingFwdE M e = e := fun e he => by
    have he' : e ∈ E(D.toGraph) := he
    simp [drawingFwdE, M, planarDrawingOfDrawing, he']
    rfl
  have hSubdraw_U : ∀ j : Fin d', (subdrawingOfSubgraph M (C j).toGraph).U = (C j).U := fun j => by
    obtain ⟨_, hV, hE, _, _⟩ := subdrawingOfSubgraph_spec M (hSub_le j)
    have hVj : (subdrawingOfSubgraph M (C j).toGraph).V = (C j).V := by
      rw [hV]
      ext x
      constructor
      · rintro ⟨v, hv, rfl⟩
        rwa [hFwdV v ((hShell.isSubdrawing j).1 hv)]
      · intro hx
        exact ⟨x, hx, hFwdV x ((hShell.isSubdrawing j).1 hx)⟩
    have hEj : (subdrawingOfSubgraph M (C j).toGraph).E = (C j).E := by
      rw [hE]
      ext e
      constructor
      · rintro ⟨f, hf, rfl⟩
        rwa [hFwdE f ((hShell.isSubdrawing j).2 hf)]
      · intro he
        exact ⟨e, he, hFwdE e ((hShell.isSubdrawing j).2 he)⟩
    rw [(subdrawingOfSubgraph M (C j).toGraph).U_eq, (C j).U_eq, hVj, hEj]
    rfl
  have hInside : ∀ j : Fin d', IsInsideDisc M (C j).toGraph (Δ j) := fun j => by
    obtain ⟨_, _, _, _, hU⟩ := subdrawingOfSubgraph_spec M (hSub_le j)
    rw [hSubdraw_U j] at hU
    exact ⟨hShell.isClosedDisc j, (hShell.discBd_eq j).trans hU.symm, hShell.disjoint_inf j⟩
  refine ⟨⟨fun j => ?_, fun j j' hlt => ⟨hShell.disjoint_V hlt, ?_⟩⟩, ?_, ?_⟩
  · obtain ⟨u, W, hCyc, hPos, hV, hE⟩ := hShell.isCircuit j
    exact ⟨hSub_le j, u, W, hCyc, hPos, hV, hE⟩
  · exact ⟨Δ j', Δ j, hInside j', hInside j,
      (hShell.disc_subset_interior hlt).trans interior_subset⟩
  · intro hd' v hv
    rcases hShell.vertex_in_or_inside hd' v hv with ⟨j, hvj⟩ | hv_int
    · exact Or.inl ⟨j, hvj⟩
    · refine Or.inr ⟨⟨hv, ?_⟩, Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩,
        hInside ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩, ?_⟩
      · intro hvC
        have hv_bd : v ∈ discBd (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) := by
          rw [hShell.discBd_eq]
          exact (C _).V_subset_U hvC
        rw [← discInt_eq_interior_of_isClosedDisc hS
          (hShell.isClosedDisc ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)] at hv_int
        exact hv_int.2 hv_bd
      · intro x hx
        rw [graphDrawingVertexSet_eq_singleton M hv, hFwdV v hv] at hx
        rw [mem_singleton_iff.mp hx]
        exact interior_subset hv_int
  · intro j e u v hl hu hv
    exact hShell.edge_induced j hl hu hv

/-- Under `SurfaceDShell D r₀ d' C Δ`, for `0 < d'`, `innerDraw D d' C` is contained in
`interior (Δ ⟨d' - 1, ...⟩)`. -/
theorem SurfaceDShell.innerDraw_U_subset_interior [T2Space S]
    {D : Drawing S} {r₀ : Set S} {d' : ℕ} {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ) (hd' : 0 < d') :
    (innerDraw D d' C).U ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) := by
  obtain ⟨_, hV, hE, _⟩ := innerDraw_spec D d' C
  have hNV : (innerDraw D d' C).V ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) := by
    intro v hv
    rw [hV] at hv
    rcases hShell.vertex_in_or_inside hd' v hv.1 with ⟨j, hvj⟩ | hv_int
    · exact (hv.2 (mem_iUnion.mpr ⟨j, hvj⟩)).elim
    · exact hv_int
  rw [(innerDraw D d' C).U_eq]
  refine union_subset hNV (iUnion₂_subset fun e he => ?_)
  rw [hE] at he
  have he_int : e ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) := by
    refine hShell.edge_inside_of_ends ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩ e he.1 fun v hv i _ => ?_
    exact fun hvi => (he.2 hv).2 (mem_iUnion.mpr ⟨i, hvi⟩)
  intro x hxe
  by_cases hxV : x ∈ D.V
  · exact hNV (hV.symm ▸ he.2 ⟨hxe, hxV⟩)
  · exact he_int ((D.closure_diff_V he.1).subset ⟨hxe, hxV⟩)

/-- For a closed disc `Δ` in a sphere `S`, `Δᶜ` is connected and hence if `N.U ⊆ interior Δ` and
`r₀ ⊆ R_N ∈ N.R` with `Disjoint Δ r₀`, then `Δᶜ ⊆ R_N`. -/
theorem compl_disc_subset_RN (hS : IsClosedSurface S) (hSph : IsSphere S)
    {N : Drawing S} {r₀ R_N Δ : Set S}
    (hRN : R_N ∈ N.R) (hr₀_ne : r₀.Nonempty) (hr₀_sub : r₀ ⊆ R_N)
    (hΔ : IsClosedDisc Δ) (hΔ_disj_r₀ : Disjoint Δ r₀) (hNU : N.U ⊆ Δ) :
    Δᶜ ⊆ R_N := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  have hF : IsOArc (discBd Δ) := IsClosedDisc.isOArc_discBd hΔ
  obtain ⟨Δ₁, Δ₂, -, hΔ₁, hΔ₂, hb₁, hb₂, hcup, hcap, -, huniq⟩ := sphere_disc S hSph (discBd Δ) hF
  have hcompl_eq : Δᶜ = discInt Δ₁ ∨ Δᶜ = discInt Δ₂ := by
    rcases huniq Δ hΔ rfl with hΔ_eq | hΔ_eq
    · refine Or.inr (Subset.antisymm (fun x hx => ?_) (fun x hx hxΔ => hx.2 ?_))
      · rcases (hcup ▸ mem_univ x : x ∈ Δ₁ ∪ Δ₂) with hx₁ | hx₂
        · exact (hx (hΔ_eq ▸ hx₁)).elim
        · refine ⟨hx₂, fun hbd => hx ?_⟩
          rw [hb₂, ← hcap, ← hΔ_eq] at hbd
          exact hbd.1
      · rw [hb₂, ← hcap]
        exact ⟨hΔ_eq ▸ hxΔ, hx.1⟩
    · refine Or.inl (Subset.antisymm (fun x hx => ?_) (fun x hx hxΔ => hx.2 ?_))
      · rcases (hcup ▸ mem_univ x : x ∈ Δ₁ ∪ Δ₂) with hx₁ | hx₂
        · refine ⟨hx₁, fun hbd => hx ?_⟩
          rw [hb₁, ← hcap, ← hΔ_eq] at hbd
          exact hbd.2
        · exact (hx (hΔ_eq ▸ hx₂)).elim
      · rw [hb₁, ← hcap]
        exact ⟨hx.1, hΔ_eq ▸ hxΔ⟩
  have hconn : IsPreconnected Δᶜ := by
    rcases hcompl_eq with heq | heq
    · rw [heq]
      exact hΔ₁.isPreconnected_discInt
    · rw [heq]
      exact hΔ₂.isPreconnected_discInt
  obtain ⟨p₀, hp₀⟩ := hr₀_ne
  exact GM11.subset_region hRN hconn
    (Set.disjoint_left.mpr fun z hz hzN => hz (hNU hzN))
    (Set.disjoint_right.mp hΔ_disj_r₀ hp₀) (hr₀_sub hp₀)

/-- Under `SurfaceDShell D r₀ d' C Δ`, if `D'` agrees with `D` outside `interior (Δ_{d'-1})` when
`0 < d'`, then every region `q' ∈ D'.R` with `q' ⊆ R_{N'}` has a region chain from `r₀'` in `D'`
of length `≤ d'`. -/
theorem exists_region_chain_le_d'_of_sub_RN (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D D' : Drawing S} {r₀ r₀' R_N' : Set S} {d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hr₀' : r₀' ∈ D'.R)
    (hRN' : haveI : T2Space S := hS.2.1; R_N' ∈ (innerDraw D' d' C).R)
    (hr₀'_sub : r₀' ⊆ R_N')
    (hC_sub' : ∀ j : Fin d', (C j).IsSubdrawing D')
    (hV_split' : ∀ (hd' : 0 < d'), ∀ v ∈ D'.V,
      v ∈ Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩ →
        v ∈ (C ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩).V ∨
        haveI : T2Space S := hS.2.1; v ∈ (innerDraw D' d' C).V)
    (hr₀'_eq : 0 < d' → r₀' = r₀)
    (hR_out : ∀ (hd' : 0 < d') ⦃r : Set S⦄, r ∈ D.R →
      Disjoint r (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) → r ∈ D'.R)
    (hV_out : ∀ (hd' : 0 < d') ⦃w : S⦄, w ∈ D.V →
      w ∉ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) → w ∈ D'.V)
    {q' : Set S} (hq' : q' ∈ D'.R) (hq'_RN' : q' ⊆ R_N')
    (hq'_int : ∀ (hd' : 0 < d'), q' ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)) :
    ∃ k ≤ d', IsRegionChain (planarDrawingOfDrawing hS hSph D' r₀' hr₀') q' k := by
  have : T2Space S := hS.2.1
  by_cases hd' : 0 < d'
  · let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
    obtain ⟨hN's, hN'V, hN'E, _⟩ := innerDraw_spec D' d' C
    have hE_N' : ∀ e ∈ D'.E, closure e ∩ D'.V ⊆ (innerDraw D' d' C).V →
        e ∈ (innerDraw D' d' C).E := by
      intro e he hsub
      rw [hN'E]
      exact ⟨he, hN'V ▸ hsub⟩
    obtain ⟨u, huC, hu_cl_q'⟩ :=
      region_in_RN_incident_shell hS hN's (hC_sub' j_last) hr₀' hRN' hr₀'_sub
        (hShell.isClosedDisc j_last) (hShell.discBd_eq j_last)
        (hr₀'_eq hd' ▸ hShell.disjoint_inf j_last) (hV_split' hd') hE_N' hq' hq'_RN' (hq'_int hd')
    obtain ⟨r_u, hru_D, hu_cl_ru, hru_disj, k, hk_le, R_seq, hseq_D, hseq_0, hseq_k,
        hseq_disj, hseq_step⟩ := hShell.shell_vertex_chain j_last u huC
    let R_seq' : Fin (k + 1 + 1) → Set S := fun m =>
      if hm : m.1 < k + 1 then R_seq ⟨m.1, hm⟩ else q'
    refine ⟨k + 1, by omega, R_seq', ?_, ?_, ?_, ?_⟩
    · intro m
      by_cases hm : m.1 < k + 1
      · simp only [R_seq', hm, ↓reduceDIte]
        exact hR_out hd' (hseq_D ⟨m.1, hm⟩) (hseq_disj ⟨m.1, hm⟩)
      · simp only [R_seq', hm, ↓reduceDIte]
        exact hq'
    · simp only [R_seq', Nat.zero_lt_succ, ↓reduceDIte, hseq_0]
      exact (hr₀'_eq hd').symm
    · have hnot : ¬ (k + 1 < k + 1) := lt_irrefl (k + 1)
      simp only [R_seq', hnot, ↓reduceDIte]
      rfl
    · intro m
      by_cases hm : m.1 < k
      · obtain ⟨w, hwD, hw_not_int, hw1, hw2⟩ := hseq_step ⟨m.1, hm⟩
        refine ⟨w, hV_out hd' hwD hw_not_int, ?_, ?_⟩
        · have hm1 : m.1 < k + 1 := Nat.lt_succ_of_lt hm
          simp only [R_seq', hm1, ↓reduceDIte]
          exact hw1
        · have hm2 : m.1 + 1 < k + 1 := Nat.succ_lt_succ hm
          simp only [R_seq', hm2, ↓reduceDIte]
          exact hw2
      · have hmk : m.1 = k := by omega
        refine ⟨u, (hC_sub' j_last).1 huC, ?_, ?_⟩
        · have hm1 : m.1 < k + 1 := by omega
          simp only [R_seq', hm1, ↓reduceDIte]
          have hmk' : (⟨m.1, hm1⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext hmk
          rw [hmk', hseq_k]
          exact hu_cl_ru
        · have hm2 : ¬ (m.1 + 1 < k + 1) := by omega
          simp only [R_seq', hm2, ↓reduceDIte]
          exact hu_cl_q'
  · have hd'0 : d' = 0 := Nat.eq_zero_of_not_pos hd'
    subst hd'0
    obtain ⟨_, hV, hE, _⟩ := innerDraw_spec D' 0 C
    have hV' : (innerDraw D' 0 C).V = D'.V := by
      rw [hV]
      ext x
      simp
    have hE' : (innerDraw D' 0 C).E = D'.E := by
      rw [hE]
      ext e
      simp only [mem_ofPred_eq, and_iff_left_iff_imp]
      rintro _ x ⟨_, hxV⟩
      exact ⟨hxV, by simp⟩
    have hU' : (innerDraw D' 0 C).U = D'.U := by
      rw [(innerDraw D' 0 C).U_eq, D'.U_eq, hV', hE']
    have hR' : (innerDraw D' 0 C).R = D'.R := by
      change componentsIn (univ \ (innerDraw D' 0 C).U) = componentsIn (univ \ D'.U)
      rw [hU']
    have hRN'_D : R_N' ∈ D'.R := hR' ▸ hRN'
    obtain ⟨z₀, hz₀⟩ := GM11.region_nonempty hq'
    have hq'_eq_RN' : q' = R_N' := GM11.region_eq_of_mem hq' hRN'_D hz₀ (hq'_RN' hz₀)
    obtain ⟨p₀, hp₀⟩ := GM11.region_nonempty hr₀'
    have hr₀'_eq_RN' : r₀' = R_N' := GM11.region_eq_of_mem hr₀' hRN'_D hp₀ (hr₀'_sub hp₀)
    refine ⟨0, le_rfl, fun _ => r₀', fun _ => hr₀', rfl, hr₀'_eq_RN'.trans hq'_eq_RN'.symm, ?_⟩
    intro j
    exact Fin.elim0 j

/-- Any vertex `w ∈ (innerDraw D' d' C).V ∩ closure R_N'` (with `w ∈ interior (Δ_{d'-1})` when
`0 < d'`) lies in `closure q_w` for some region `q_w ∈ D'.R` with `q_w ⊆ R_N'` and a region chain
from `r₀'` in `D'` of length `≤ d'`. -/
theorem exists_region_chain_le_d'_of_vertex_in_RN [PreconnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D D' : Drawing S} {r₀ r₀' R_N' : Set S} {d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ)
    (hr₀' : r₀' ∈ D'.R)
    (hRN' : haveI : T2Space S := hS.2.1; R_N' ∈ (innerDraw D' d' C).R)
    (hr₀'_sub : r₀' ⊆ R_N')
    (hC_sub' : ∀ j : Fin d', (C j).IsSubdrawing D')
    (hV_split' : ∀ (hd' : 0 < d'), ∀ v ∈ D'.V,
      v ∈ Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩ →
        v ∈ (C ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩).V ∨
        haveI : T2Space S := hS.2.1; v ∈ (innerDraw D' d' C).V)
    (hr₀'_eq : 0 < d' → r₀' = r₀)
    (hR_out : ∀ (hd' : 0 < d') ⦃r : Set S⦄, r ∈ D.R →
      Disjoint r (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) → r ∈ D'.R)
    (hV_out : ∀ (hd' : 0 < d') ⦃w : S⦄, w ∈ D.V →
      w ∉ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) → w ∈ D'.V)
    {w : S} (hw_cl : w ∈ closure R_N')
    (hw_int : ∀ (hd' : 0 < d'), w ∈ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)) :
    ∃ q_w ∈ D'.R, q_w ⊆ R_N' ∧ w ∈ closure q_w ∧
      ∃ k ≤ d', IsRegionChain (planarDrawingOfDrawing hS hSph D' r₀' hr₀') q_w k := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hN's, _, _, _⟩ := innerDraw_spec D' d' C
  have hcl_eq := closure_RN_eq_biUnion_closure_regions hS hN's hRN'
  rw [hcl_eq] at hw_cl
  simp only [mem_iUnion, exists_prop] at hw_cl
  obtain ⟨q_w, hqw_R, hqw_RN', hw_cl_qw⟩ := hw_cl
  have hqw_int : ∀ (hd' : 0 < d'), q_w ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) := by
    intro hd'
    let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
    obtain ⟨z, hz_int, hz_qw⟩ :=
      mem_closure_iff.mp hw_cl_qw (interior (Δ j_last)) isOpen_interior (hw_int hd')
    have hfr_sub : frontier (interior (Δ j_last)) ⊆ D'.U := by
      refine frontier_interior_subset.trans ?_
      rw [GM11.IsClosedDisc.frontier_eq_discBd hS (hShell.isClosedDisc j_last),
        hShell.discBd_eq j_last]
      exact (hC_sub' j_last).U_subset
    have hdisj_fr : Disjoint q_w (frontier (interior (Δ j_last))) :=
      Set.disjoint_left.mpr fun x hxq hxfr => GM11.region_subset hqw_R hxq (hfr_sub hxfr)
    have hsub_cl : q_w ⊆ closure (interior (Δ j_last)) := by
      rcases GM11.subset_or_disjoint_of_frontier isClosed_closure
          (GM11.region_isPreconnected hqw_R)
          (hdisj_fr.mono_right frontier_closure_subset) with hsub | hdisj
      · exact hsub
      · exact (Set.disjoint_left.mp hdisj hz_qw (subset_closure hz_int)).elim
    intro x hxq
    have hx_Δ : x ∈ Δ j_last :=
      closure_minimal interior_subset (hShell.isClosedDisc j_last).isClosed (hsub_cl hxq)
    rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)]
    refine ⟨hx_Δ, fun hx_bd => ?_⟩
    rw [hShell.discBd_eq j_last] at hx_bd
    exact GM11.region_subset hqw_R hxq ((hC_sub' j_last).U_subset hx_bd)
  obtain ⟨k, hkd', hchain⟩ :=
    exists_region_chain_le_d'_of_sub_RN hS hSph hShell hr₀' hRN' hr₀'_sub hC_sub' hV_split'
      hr₀'_eq hR_out hV_out hqw_R hqw_RN' hqw_int
  exact ⟨q_w, hqw_R, hqw_RN', hw_cl_qw, k, hkd', hchain⟩

/-- Splicing a region chain of length `k₁` from `r₀'` to `q_w` in `D'` with a suffix of a region
chain in `D` starting at `m₀ + 1` (via a shared vertex `w ∈ D'.V ∩ closure q_w ∩ closure (R_seq (m₀ + 1))`),
where `k₁ ≤ m₀` and `k ≤ d`, yields a region chain in `D'` of length `≤ d`. -/
theorem splice_regionChain {D' : Drawing S} {r₀' q_w q' : Set S}
    (hS : IsClosedSurface S) (hSph : IsSphere S) (hr₀' : r₀' ∈ D'.R)
    {d k m₀ k₁ : ℕ} (hkd : k ≤ d) (hm₀_lt : m₀ < k) (hk₁_le : k₁ ≤ m₀)
    {R_seq : Fin (k + 1) → Set S}
    (hseq_k : R_seq ⟨k, Nat.lt_succ_self k⟩ = q')
    (hchain₁ : IsRegionChain (planarDrawingOfDrawing hS hSph D' r₀' hr₀') q_w k₁)
    {w : S} (hw_V' : w ∈ D'.V) (hw_qw : w ∈ closure q_w)
    (hw_next : w ∈ closure (R_seq ⟨m₀ + 1, Nat.succ_lt_succ hm₀_lt⟩))
    (hR_suf : ∀ m : Fin (k + 1), m₀ < m.1 → R_seq m ∈ D'.R)
    (hV_suf : ∀ m : Fin k, m₀ < m.1 → ∃ v ∈ D'.V,
      v ∈ closure (R_seq ⟨m.1, Nat.lt_succ_of_lt m.2⟩) ∧
      v ∈ closure (R_seq ⟨m.1 + 1, Nat.succ_lt_succ m.2⟩)) :
    ∃ k' ≤ d, IsRegionChain (planarDrawingOfDrawing hS hSph D' r₀' hr₀') q' k' := by
  obtain ⟨R₁, hR₁_mem, hR₁_0, hR₁_k₁, hR₁_step⟩ := hchain₁
  let k' := k₁ + (k - m₀)
  have hk'_le : k' ≤ d := by omega
  let R' : Fin (k' + 1) → Set S := fun j =>
    if hj : j.1 ≤ k₁ then R₁ ⟨j.1, Nat.lt_succ_of_le hj⟩
    else R_seq ⟨m₀ + (j.1 - k₁), by omega⟩
  refine ⟨k', hk'_le, R', ?_, ?_, ?_, ?_⟩
  · intro j
    have hj_bound : j.1 < k₁ + (k - m₀) + 1 := j.2
    by_cases hj : j.1 ≤ k₁
    · simp only [R', hj, ↓reduceDIte]
      exact hR₁_mem ⟨j.1, Nat.lt_succ_of_le hj⟩
    · simp only [R', hj, ↓reduceDIte]
      exact hR_suf ⟨m₀ + (j.1 - k₁), by omega⟩ (show m₀ < m₀ + (j.1 - k₁) by omega)
  · simp only [R', Nat.zero_le, ↓reduceDIte]
    exact hR₁_0
  · have hnot : ¬ (k' ≤ k₁) := by omega
    simp only [R', hnot, ↓reduceDIte]
    have hidx : (⟨m₀ + (k' - k₁), by omega⟩ : Fin (k + 1)) = ⟨k, Nat.lt_succ_self k⟩ :=
      Fin.ext (show m₀ + (k' - k₁) = k by omega)
    rw [hidx, hseq_k]
  · intro j
    have hj_bound : j.1 < k₁ + (k - m₀) := j.2
    by_cases hj_lt : j.1 < k₁
    · obtain ⟨v, hvV, hv1, hv2⟩ := hR₁_step ⟨j.1, hj_lt⟩
      refine ⟨v, hvV, ?_, ?_⟩
      · have hj1 : j.1 ≤ k₁ := hj_lt.le
        simpa [R', hj1] using hv1
      · have hj2 : j.1 + 1 ≤ k₁ := hj_lt
        simpa [R', hj2] using hv2
    · by_cases hj_eq : j.1 = k₁
      · refine ⟨w, hw_V', ?_, ?_⟩
        · have hj1 : j.1 ≤ k₁ := hj_eq.le
          simp only [R', hj1, ↓reduceDIte]
          have hidx : (⟨j.1, Nat.lt_succ_of_le hj1⟩ : Fin (k₁ + 1)) =
              ⟨k₁, Nat.lt_succ_self k₁⟩ := Fin.ext hj_eq
          rw [hidx, hR₁_k₁]
          exact hw_qw
        · have hj2 : ¬ (j.1 + 1 ≤ k₁) := by omega
          simp only [R', hj2, ↓reduceDIte]
          have hidx : (⟨m₀ + (j.1 + 1 - k₁), by omega⟩ : Fin (k + 1)) =
              ⟨m₀ + 1, Nat.succ_lt_succ hm₀_lt⟩ :=
            Fin.ext (show m₀ + (j.1 + 1 - k₁) = m₀ + 1 by omega)
          rw [hidx]
          exact hw_next
      · have hm_lt : m₀ + (j.1 - k₁) < k := by omega
        obtain ⟨v, hvV, hv1, hv2⟩ :=
          hV_suf ⟨m₀ + (j.1 - k₁), hm_lt⟩ (show m₀ < m₀ + (j.1 - k₁) by omega)
        refine ⟨v, hvV, ?_, ?_⟩
        · have hj1 : ¬ (j.1 ≤ k₁) := by omega
          simp only [R', hj1, ↓reduceDIte]
          exact hv1
        · have hj2 : ¬ (j.1 + 1 ≤ k₁) := by omega
          simp only [R', hj2, ↓reduceDIte]
          have hidx : (⟨m₀ + (j.1 + 1 - k₁), by omega⟩ : Fin (k + 1)) =
              ⟨m₀ + (j.1 - k₁) + 1, Nat.succ_lt_succ hm_lt⟩ :=
            Fin.ext (show m₀ + (j.1 + 1 - k₁) = m₀ + (j.1 - k₁) + 1 by omega)
          rw [hidx]
          exact hv2

/-- **Unified Radius Preservation Lemma**: modifying `D` inside `R_N` (and inside
`interior (Δ_{d'-1})` when `0 < d'`) preserves `HasDrawingRadiusLE _ d` whenever `d' < d`. -/
theorem hasDrawingRadiusLE_of_modify_in_RN [PreconnectedSpace S]
    (hS : IsClosedSurface S) (hSph : IsSphere S)
    {D D' : Drawing S} {r₀ r₀' R_N R_N' : Set S} {d d' : ℕ}
    {C : Fin d' → Drawing S} {Δ : Fin d' → Set S}
    (hShell : SurfaceDShell D r₀ d' C Δ) (hd'_lt : d' < d)
    (hrad : HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem) d)
    (hr₀' : r₀' ∈ D'.R)
    (hRN : haveI : T2Space S := hS.2.1; R_N ∈ (innerDraw D d' C).R)
    (hr₀_sub : r₀ ⊆ R_N)
    (hRN' : haveI : T2Space S := hS.2.1; R_N' ∈ (innerDraw D' d' C).R)
    (hr₀'_sub : r₀' ⊆ R_N')
    (hC_sub' : ∀ j : Fin d', (C j).IsSubdrawing D')
    (hV_split' : ∀ (hd' : 0 < d'), ∀ v ∈ D'.V,
      v ∈ Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩ →
        v ∈ (C ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩).V ∨
        haveI : T2Space S := hS.2.1; v ∈ (innerDraw D' d' C).V)
    (hr₀'_eq : 0 < d' → r₀' = r₀)
    (hR_out : ∀ (hd' : 0 < d') ⦃r : Set S⦄, r ∈ D.R →
      Disjoint r (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) → r ∈ D'.R)
    (hV_out : ∀ (hd' : 0 < d') ⦃w : S⦄, w ∈ D.V →
      w ∉ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩) → w ∈ D'.V)
    (hV_RN_sub : haveI : T2Space S := hS.2.1;
      (innerDraw D d' C).V ∩ closure R_N ⊆ (innerDraw D' d' C).V ∩ closure R_N')
    (hV_RN'_int : ∀ (hd' : 0 < d') ⦃w : S⦄,
      (haveI : T2Space S := hS.2.1; w ∈ (innerDraw D' d' C).V) →
      w ∈ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩))
    (hR_disj_RN : ∀ ⦃q : Set S⦄, q ∈ D.R → Disjoint q R_N → q ∈ D'.R)
    (hV_disj_RN : ∀ ⦃w : S⦄, w ∈ D.V → w ∉ R_N → w ∈ D'.V)
    (hR_cases : ∀ q' ∈ D'.R,
      (q' ⊆ R_N' ∧ ∀ hd' : 0 < d', q' ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)) ∨
      (q' ∈ D.R ∧ ¬ (q' ⊆ R_N ∧
        ∀ hd' : 0 < d', q' ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩))) ∨
      (∃ v₀, (haveI : T2Space S := hS.2.1; v₀ ∈ (innerDraw D' d' C).V) ∧
        v₀ ∈ closure R_N' ∧ v₀ ∈ closure q')) :
    HasDrawingRadiusLE (planarDrawingOfDrawing hS hSph D' r₀' hr₀') d := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  let M := planarDrawingOfDrawing hS hSph D r₀ hShell.r₀_mem
  let M' := planarDrawingOfDrawing hS hSph D' r₀' hr₀'
  let InZone : Set S → Prop := fun r =>
    r ⊆ R_N ∧ ∀ hd' : 0 < d', r ⊆ interior (Δ ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩)
  have hNotInZone_R : ∀ ⦃r : Set S⦄, r ∈ D.R → ¬ InZone r → r ∈ D'.R := by
    intro r hr hnot
    obtain ⟨hNs, _, _, _⟩ := innerDraw_spec D d' C
    have hr_RN_or_disj : r ⊆ R_N ∨ Disjoint r R_N := by
      by_cases h : (r ∩ R_N).Nonempty
      · obtain ⟨z, hzr, hzRN⟩ := h
        exact Or.inl (GM11.subset_region hRN (GM11.region_isPreconnected hr)
          (Set.disjoint_left.mpr fun x hxr hxN => GM11.region_subset hr hxr (hNs.U_subset hxN))
          hzr hzRN)
      · exact Or.inr (Set.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp h))
    rcases hr_RN_or_disj with hr_RN | hr_disj
    · have hd' : 0 < d' := by
        by_contra hd'0
        exact hnot ⟨hr_RN, fun h => (hd'0 h).elim⟩
      let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
      have hr_not_int : ¬ (r ⊆ interior (Δ j_last)) := fun h => hnot ⟨hr_RN, fun _ => h⟩
      have hr_disj_Δ : Disjoint r (Δ j_last) := by
        by_contra hnot_disj
        obtain ⟨z, hzr, hzΔ⟩ := not_disjoint_iff.mp hnot_disj
        have hz_not_bd : z ∉ discBd (Δ j_last) := by
          rw [hShell.discBd_eq j_last]
          exact fun hzC => GM11.region_subset hr hzr ((hShell.isSubdrawing j_last).U_subset hzC)
        have hz_int : z ∈ interior (Δ j_last) := by
          rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)]
          exact ⟨hzΔ, hz_not_bd⟩
        have hfr_sub : frontier (Δ j_last) ⊆ D.U := by
          rw [GM11.IsClosedDisc.frontier_eq_discBd hS (hShell.isClosedDisc j_last),
            hShell.discBd_eq j_last]
          exact (hShell.isSubdrawing j_last).U_subset
        rcases GM11.subset_or_disjoint_of_frontier (hShell.isClosedDisc j_last).isClosed
            (GM11.region_isPreconnected hr)
            (Set.disjoint_left.mpr fun x hxr hxfr =>
              GM11.region_subset hr hxr (hfr_sub hxfr)) with hsub | hdisj
        · refine hr_not_int fun x hxr => ?_
          rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)]
          refine ⟨hsub hxr, fun hx_bd => ?_⟩
          rw [hShell.discBd_eq j_last] at hx_bd
          exact GM11.region_subset hr hxr ((hShell.isSubdrawing j_last).U_subset hx_bd)
        · exact Set.disjoint_left.mp hdisj hzr hzΔ
      exact hR_out hd' hr hr_disj_Δ
    · exact hR_disj_RN hr hr_disj
  have hNotInZone_V : ∀ ⦃r : Set S⦄ ⦃w : S⦄, r ∈ D.R → ¬ InZone r →
      w ∈ D.V → w ∈ closure r → w ∈ D'.V := by
    intro r w hr hnot hwD hw_cl
    by_cases hw_RN : w ∈ R_N
    · have hd' : 0 < d' := by
        by_contra hd'0
        obtain ⟨hNs, _, _, _⟩ := innerDraw_spec D d' C
        obtain ⟨z, hzRN, hzr⟩ :=
          mem_closure_iff.mp hw_cl R_N (GM11.region_isOpen hRN) hw_RN
        have hr_RN : r ⊆ R_N :=
          GM11.subset_region hRN (GM11.region_isPreconnected hr)
            (Set.disjoint_left.mpr fun x hxr hxN => GM11.region_subset hr hxr (hNs.U_subset hxN))
            hzr hzRN
        exact hnot ⟨hr_RN, fun h => (hd'0 h).elim⟩
      let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
      have hw_not_int : w ∉ interior (Δ j_last) := by
        intro hw_int
        obtain ⟨hNs, _, _, _⟩ := innerDraw_spec D d' C
        obtain ⟨z, ⟨hzRN, hz_int⟩, hzr⟩ :=
          mem_closure_iff.mp hw_cl (R_N ∩ interior (Δ j_last))
            ((GM11.region_isOpen hRN).inter isOpen_interior) ⟨hw_RN, hw_int⟩
        have hr_RN : r ⊆ R_N :=
          GM11.subset_region hRN (GM11.region_isPreconnected hr)
            (Set.disjoint_left.mpr fun x hxr hxN => GM11.region_subset hr hxr (hNs.U_subset hxN))
            hzr hzRN
        have hfr_sub : frontier (Δ j_last) ⊆ D.U := by
          rw [GM11.IsClosedDisc.frontier_eq_discBd hS (hShell.isClosedDisc j_last),
            hShell.discBd_eq j_last]
          exact (hShell.isSubdrawing j_last).U_subset
        have hr_sub_Δ : r ⊆ Δ j_last := by
          rcases GM11.subset_or_disjoint_of_frontier (hShell.isClosedDisc j_last).isClosed
              (GM11.region_isPreconnected hr)
              (Set.disjoint_left.mpr fun x hxr hxfr =>
                GM11.region_subset hr hxr (hfr_sub hxfr)) with hsub | hdisj
          · exact hsub
          · exact (Set.disjoint_left.mp hdisj hzr (interior_subset hz_int)).elim
        refine hnot ⟨hr_RN, fun _ x hxr => ?_⟩
        rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j_last)]
        refine ⟨hr_sub_Δ hxr, fun hx_bd => ?_⟩
        rw [hShell.discBd_eq j_last] at hx_bd
        exact GM11.region_subset hr hxr ((hShell.isSubdrawing j_last).U_subset hx_bd)
      exact hV_out hd' hwD hw_not_int
    · exact hV_disj_RN hwD hw_RN
  intro q' hq'
  rcases hR_cases q' hq' with ⟨hq'_RN', hq'_int⟩ | ⟨hq'_D, hq'_not_zone⟩ |
      ⟨v₀, hv₀_N', hv₀_cl_RN', hv₀_cl_q'⟩
  · obtain ⟨k, hkd', hchain⟩ :=
      exists_region_chain_le_d'_of_sub_RN hS hSph hShell hr₀' hRN' hr₀'_sub hC_sub' hV_split'
        hr₀'_eq hR_out hV_out hq' hq'_RN' hq'_int
    exact ⟨k, hkd'.trans hd'_lt.le, hchain⟩
  · obtain ⟨k, hkd, R_seq, hseq_R, hseq_0, hseq_k, hseq_step⟩ := hrad q' hq'_D
    by_cases hall_out : ∀ m : Fin (k + 1), ¬ InZone (R_seq m)
    · have hd' : 0 < d' := by
        by_contra hd'0
        exact hall_out ⟨0, Nat.zero_lt_succ k⟩
          ⟨hseq_0.symm ▸ hr₀_sub, fun h => (hd'0 h).elim⟩
      refine ⟨k, hkd, R_seq, fun m => hNotInZone_R (hseq_R m) (hall_out m),
        hseq_0.trans (hr₀'_eq hd').symm, hseq_k, fun m => ?_⟩
      obtain ⟨w, hwD, hw1, hw2⟩ := hseq_step m
      exact ⟨w, hNotInZone_V (hseq_R ⟨m.1, Nat.lt_succ_of_lt m.2⟩)
        (hall_out ⟨m.1, Nat.lt_succ_of_lt m.2⟩) hwD hw1, hw1, hw2⟩
    · push Not at hall_out
      let S_in : Finset (Fin (k + 1)) := Finset.univ.filter fun m => InZone (R_seq m)
      have hS_ne : S_in.Nonempty := by
        obtain ⟨m, hm⟩ := hall_out
        exact ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hm⟩⟩
      let m_max := S_in.max' hS_ne
      have hm_max_zone : InZone (R_seq m_max) := (Finset.mem_filter.mp (Finset.max'_mem S_in hS_ne)).2
      have hm_max_lt : m_max.1 < k := by
        refine lt_of_le_of_ne (Nat.le_of_lt_succ m_max.2) fun heq => ?_
        have hmk : m_max = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext heq
        rw [hmk, hseq_k] at hm_max_zone
        exact hq'_not_zone hm_max_zone
      have hgt_not_zone : ∀ m : Fin (k + 1), m_max.1 < m.1 → ¬ InZone (R_seq m) := by
        intro m hlt hzone
        have hle : m ≤ m_max :=
          Finset.le_max' S_in m (Finset.mem_filter.mpr ⟨Finset.mem_univ m, hzone⟩)
        exact not_le_of_gt hlt hle
      have hd'_le_m : d' ≤ m_max.1 := by
        by_contra hlt
        push Not at hlt
        have hd' : 0 < d' := by omega
        let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
        have hdisj :=
          regionChain_disjoint_nested_discs M
            (fun i => hShell.isClosedDisc i)
            (fun i => by
              change discBd (Δ i) ⊆ D.U
              rw [hShell.discBd_eq i]
              exact (hShell.isSubdrawing i).U_subset)
            (fun h0 => hShell.disjoint_inf ⟨0, h0⟩)
            (fun i j hij => hShell.disc_subset_interior hij)
            hseq_R hseq_0 hseq_step m_max.1 m_max.2 j_last
            (show m_max.1 ≤ d' - 1 by omega)
        obtain ⟨z, hz⟩ := GM11.region_nonempty (hseq_R m_max)
        exact Set.disjoint_left.mp hdisj hz (interior_subset (hm_max_zone.2 hd' hz))
      obtain ⟨w, hwD, hw1, hw2⟩ := hseq_step ⟨m_max.1, hm_max_lt⟩
      have hV_suf : ∀ m : Fin k, m_max.1 < m.1 → ∃ v ∈ D'.V,
          v ∈ closure (R_seq ⟨m.1, Nat.lt_succ_of_lt m.2⟩) ∧
          v ∈ closure (R_seq ⟨m.1 + 1, Nat.succ_lt_succ m.2⟩) := by
        intro m hlt
        obtain ⟨v, hvD, hv1, hv2⟩ := hseq_step m
        exact ⟨v, hNotInZone_V (hseq_R ⟨m.1, Nat.lt_succ_of_lt m.2⟩)
          (hgt_not_zone ⟨m.1, Nat.lt_succ_of_lt m.2⟩ hlt) hvD hv1, hv1, hv2⟩
      by_cases hw_N : w ∈ (innerDraw D d' C).V
      · have hw_N' : w ∈ (innerDraw D' d' C).V ∩ closure R_N' :=
          hV_RN_sub ⟨hw_N, closure_mono hm_max_zone.1 hw1⟩
        obtain ⟨hN's, _, _, _⟩ := innerDraw_spec D' d' C
        obtain ⟨q_w, _, _, hw_cl_qw, k₁, hk₁_le, hchain₁⟩ :=
          exists_region_chain_le_d'_of_vertex_in_RN hS hSph hShell hr₀' hRN' hr₀'_sub
            hC_sub' hV_split' hr₀'_eq hR_out hV_out hw_N'.2
            (fun hd' => hV_RN'_int hd' hw_N'.1)
        exact splice_regionChain hS hSph hr₀' hkd hm_max_lt (hk₁_le.trans hd'_le_m) hseq_k
          hchain₁ (hN's.1 hw_N'.1) hw_cl_qw hw2
          (fun m hlt => hNotInZone_R (hseq_R m) (hgt_not_zone m hlt)) hV_suf
      · obtain ⟨_, hNV, _, _⟩ := innerDraw_spec D d' C
        rw [hNV] at hw_N
        have hw_C : ∃ j : Fin d', w ∈ (C j).V := by
          by_contra hnot_C
          exact hw_N ⟨hwD, fun h => hnot_C (mem_iUnion.mp h)⟩
        obtain ⟨j, hw_Cj⟩ := hw_C
        have hd' : 0 < d' := pos_of_gt j.2
        let j_last : Fin d' := ⟨d' - 1, Nat.sub_lt hd' zero_lt_one⟩
        have hw_Δ_last : w ∈ Δ j_last :=
          closure_minimal ((hm_max_zone.2 hd').trans interior_subset)
            (hShell.isClosedDisc j_last).isClosed hw1
        have hj_eq : j = j_last := by
          by_contra hne
          have hlt : j < j_last :=
            lt_of_le_of_ne (Fin.le_def.mpr (Nat.le_sub_one_of_lt j.2)) hne
          have hw_int_j : w ∈ interior (Δ j) := hShell.disc_subset_interior hlt hw_Δ_last
          rw [← discInt_eq_interior_of_isClosedDisc hS (hShell.isClosedDisc j)] at hw_int_j
          exact hw_int_j.2 (hShell.discBd_eq j ▸ (C j).V_subset_U hw_Cj)
        rw [hj_eq] at hw_Cj
        obtain ⟨r_w, hrw_D, hw_cl_rw, hrw_disj, k₁, hk₁_le, R_seq₁, hseq₁_D, hseq₁_0, hseq₁_k,
            hseq₁_disj, hseq₁_step⟩ := hShell.shell_vertex_chain j_last w hw_Cj
        have hchain₁ : IsRegionChain M' r_w k₁ := by
          refine ⟨R_seq₁, fun m => hR_out hd' (hseq₁_D m) (hseq₁_disj m),
            hseq₁_0.trans (hr₀'_eq hd').symm, hseq₁_k, fun m => ?_⟩
          obtain ⟨v, hvD, hv_not_int, hv1, hv2⟩ := hseq₁_step m
          exact ⟨v, hV_out hd' hvD hv_not_int, hv1, hv2⟩
        exact splice_regionChain hS hSph hr₀' hkd hm_max_lt
          (hk₁_le.trans ((Nat.sub_le d' 1).trans hd'_le_m)) hseq_k
          hchain₁ ((hC_sub' j_last).1 hw_Cj) hw_cl_rw hw2
          (fun m hlt => hNotInZone_R (hseq_R m) (hgt_not_zone m hlt)) hV_suf
  · obtain ⟨hN's, _, _, _⟩ := innerDraw_spec D' d' C
    obtain ⟨q_v, hqv_R, _, hv₀_cl_qv, k₁, hk₁_le, R₁, hR₁_mem, hR₁_0, hR₁_k₁, hR₁_step⟩ :=
      exists_region_chain_le_d'_of_vertex_in_RN hS hSph hShell hr₀' hRN' hr₀'_sub
        hC_sub' hV_split' hr₀'_eq hR_out hV_out hv₀_cl_RN'
        (fun hd' => hV_RN'_int hd' hv₀_N')
    let R_seq' : Fin (k₁ + 1 + 1) → Set S := fun m =>
      if hm : m.1 < k₁ + 1 then R₁ ⟨m.1, hm⟩ else q'
    refine ⟨k₁ + 1, by omega, R_seq', ?_, ?_, ?_, ?_⟩
    · intro m
      by_cases hm : m.1 < k₁ + 1
      · simpa only [R_seq', hm, ↓reduceDIte] using hR₁_mem ⟨m.1, hm⟩
      · simpa only [R_seq', hm, ↓reduceDIte] using hq'
    · simp only [R_seq', Nat.zero_lt_succ, ↓reduceDIte, hR₁_0]
    · simp [R_seq']
    · intro m
      by_cases hm : m.1 < k₁
      · obtain ⟨w, hwV, hw1, hw2⟩ := hR₁_step ⟨m.1, hm⟩
        refine ⟨w, hwV, ?_, ?_⟩
        · have hm1 : m.1 < k₁ + 1 := Nat.lt_succ_of_lt hm
          simpa [R_seq', hm1] using hw1
        · have hm2 : m.1 + 1 < k₁ + 1 := Nat.succ_lt_succ hm
          simpa [R_seq', hm2] using hw2
      · have hmk : m.1 = k₁ := by omega
        refine ⟨v₀, hN's.1 hv₀_N', ?_, ?_⟩
        · have hm1 : m.1 < k₁ + 1 := by omega
          simp only [R_seq', hm1, ↓reduceDIte]
          have hmk' : (⟨m.1, hm1⟩ : Fin (k₁ + 1)) = ⟨k₁, Nat.lt_succ_self k₁⟩ := Fin.ext hmk
          rw [hmk', hR₁_k₁]
          exact hv₀_cl_qv
        · have hm2 : ¬ (m.1 + 1 < k₁ + 1) := by omega
          simp only [R_seq', hm2, ↓reduceDIte]
          exact hv₀_cl_q'

end SurfaceShellInvariant

end GraphMinor.GM03
