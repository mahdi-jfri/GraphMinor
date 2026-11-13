module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.CutStages
import GraphMinor.GM08.Section15EdgeLabels
import GraphMinor.GM08.Section15VertexDecoder
import GraphMinor.GM08.Section15PullbackEdges
import GraphMinor.GM08.Section15CutRoots
import GraphMinor.GM08.Section15ArcPullback
import GraphMinor.GM08.Section9GraftDrawing

/-!
# The cut graft with original edge labels

Label the cut edges by the original edges and decode each lifted vertex
by the cutting map and the old drawing bijection. The resulting graph
maps exactly to the original graph, has paired fibres, and satisfies
the proved cut root rule. Its drawing in the cut surface has the required
index bound. These are the finite reconstruction data in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface Graph

universe u v w

/-- Construct the labelled cut graft, with its drawing, index estimate,
and paired-fibre quotient onto the original graft. This is the labelled
short-tube construction in VIII (15.4), page 282. -/
theorem exists_labelled_graft_of_arc_cut {S Y : Type w}
    [TopologicalSpace S] [TopologicalSpace Y] [Nonempty S]
    {α : Type u} {β : Type v} [Nonempty α] {X : Graft α β}
    (hS : IsSurface S) (gd : GraftDrawing X.G X.T S)
    {F : Set S} {ψ : Y → S} (hcut : GM07.IsCutAlongSet F ψ) (hc : IsCutting ψ F)
    (H : Drawing Y) (hp : GM07.IsPullbackDrawing ψ gd.drawing H) (hH : H.IsProper)
    (he : ∀ e' ∈ H.E, ∃ e ∈ gd.drawing.E, e' = ψ ⁻¹' e) :
    ∃ A : Graft Y β, EmbedsGraft Y A ∧
      A.index ≤ X.index + 2 * (gd.drawing.V ∩ F).ncard ∧
      ∃ f : Y → α, X.G = A.G.map f ∧
        (∀ x, {y ∈ V(A.G) | f y = x}.ncard ≤ 2) ∧
        ∀ y ∈ V(A.G), y ∈ A.T ↔
          f y ∈ X.T ∨ ∃ z ∈ V(A.G), z ≠ y ∧ f z = f y := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace Y := hcut.isSurface.1
  have hE := pullback_drawing_edges_eq hc.2.1 hp he
  have hpre : ∀ e ∈ gd.drawing.E, ψ ⁻¹' e ∈ H.E :=
    fun e he => hE.symm ▸ mem_image_of_mem _ he
  have hbij : BijOn (preimage ψ) gd.drawing.E H.E := by
    refine ⟨hpre, hc.2.1.preimage_injective.injOn, ?_⟩
    intro e he'
    obtain ⟨d, hd, rfl⟩ := he e he'
    exact ⟨d, hd, rfl⟩
  let edges := gd.iso.edgeEquiv.trans (hbij.equiv (preimage ψ))
  obtain ⟨K, i, hKV, hKE, hiv, hlink⟩ := exists_graph_with_edge_equiv H.toGraph E(X.G) edges
  change V(K) = H.V at hKV
  have hlinks : ∀ (e : E(X.G)) (x y : Y), K.IsLink e.1 x y ↔
      H.toGraph.IsLink (ψ ⁻¹' (gd.iso.edgeEquiv e).1) x y := hlink
  let A : Graft Y β := {
    G := K
    T := H.V ∩ bd Y
    T_subset := hKV.symm ▸ inter_subset_left
    finite_G := ⟨hKV.symm ▸ H.finite_V, hKE.symm ▸ X.finite_G.2⟩ }
  have hdraw : EmbedsGraft Y A := by
    refine ⟨{
      drawing := H
      iso := i
      isProper := hH
      T_subset_V := A.T_subset
      mem_bd_iff := ?_ }⟩
    intro y hy
    rw [hiv ⟨y, hy⟩]
    exact (and_iff_right (show y ∈ H.V from hKV ▸ hy)).symm
  have hindex : A.index ≤ X.index + 2 * (gd.drawing.V ∩ F).ncard := by
    change (H.V ∩ bd Y).ncard ≤ X.T.ncard + 2 * (gd.drawing.V ∩ F).ncard
    rw [hp.2, ← graftDrawing_boundary_ncard gd]
    exact boundary_vertices_ncard_le_of_arc_cut gd.drawing.finite_V hcut hc
  obtain ⟨f, hmem, hcoord, hfib, hroot⟩ := exists_vertex_decoder_of_drawing gd H hp.2
  have htarget : ∀ (e : E(X.G)) (x y : Y),
      H.toGraph.IsLink (ψ ⁻¹' (gd.iso.edgeEquiv e).1) x y → X.G.IsLink e.1 (f x) (f y) := by
    intro e x y hl
    have hx : x ∈ H.V := hl.left_mem
    have hy : y ∈ H.V := hl.right_mem
    have him := isLink_image_of_pullback_edge hc.1 hc.1.isClosedMap hc.2.1 hp
      (gd.iso.edgeEquiv e).2 hl
    apply (gd.iso.isLink_iff e ⟨f x, hmem x hx⟩ ⟨f y, hmem y hy⟩).mpr
    change gd.drawing.toGraph.IsLink (gd.iso.edgeEquiv e).1
      (gd.iso.vertexEquiv ⟨f x, hmem x hx⟩).1 (gd.iso.vertexEquiv ⟨f y, hmem y hy⟩).1
    rw [← gd.iso.fv_of_mem (hmem x hx), ← gd.iso.fv_of_mem (hmem y hy), hcoord x hx, hcoord y hy]
    exact him
  have hmap : K.map f = X.G := by
    apply Graph.ext
    · change f '' V(K) = V(X.G)
      rw [hKV]
      apply subset_antisymm
      · rintro x ⟨y, hy, rfl⟩
        exact hmem y hy
      · intro x hx
        obtain ⟨y, hy⟩ := hc.2.1 (gd.iso.vertexEquiv ⟨x, hx⟩).1
        have hyH : y ∈ H.V := by
          rw [hp.2]
          change ψ y ∈ gd.drawing.V
          rw [hy]
          exact (gd.iso.vertexEquiv ⟨x, hx⟩).2
        have hfy : f y = x := by
          apply gd.iso.fv_injOn (hmem y hyH) hx
          rw [hcoord y hyH, hy, gd.iso.fv_of_mem hx]
        exact ⟨y, hyH, hfy⟩
    · intro e x y
      change (∃ a b, K.IsLink e a b ∧ f a = x ∧ f b = y) ↔ X.G.IsLink e x y
      constructor
      · rintro ⟨a, b, hl, rfl, rfl⟩
        have heK : e ∈ E(X.G) := hKE ▸ hl.edge_mem
        exact htarget ⟨e, heK⟩ a b ((hlinks ⟨e, heK⟩ a b).mp hl)
      · intro hl
        have heK : e ∈ E(K) := hKE.symm ▸ hl.edge_mem
        obtain ⟨a, b, hab⟩ := K.exists_isLink_of_mem_edgeSet heK
        have him := htarget ⟨e, hl.edge_mem⟩ a b ((hlinks ⟨e, hl.edge_mem⟩ a b).mp hab)
        rcases him.eq_and_eq_or_eq_and_eq hl with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · exact ⟨a, b, hab, ha, hb⟩
        · exact ⟨b, a, hab.symm, hb, ha⟩
  have hf : ∀ x, {y ∈ V(A.G) | f y = x}.ncard ≤ 2 := by
    intro x
    by_cases hn : {y ∈ V(A.G) | f y = x} = ∅
    · rw [hn, ncard_empty]
      exact Nat.zero_le _
    · obtain ⟨z, hz⟩ := nonempty_iff_ne_empty.mpr hn
      have hzH : z ∈ H.V := hKV ▸ hz.1
      have hsub : {y ∈ V(A.G) | f y = x} ⊆ ψ ⁻¹' {ψ z} := by
        intro y hy
        have hyH : y ∈ H.V := hKV ▸ hy.1
        exact (hfib y hyH z hzH).mp (hy.2.trans hz.2.symm)
      exact (ncard_le_ncard hsub (hcut.finite_fiber (ψ z))).trans (cutting_fibre_ncard_le_two hc (ψ z))
  refine ⟨A, hdraw, hindex, f, hmap.symm, hf, ?_⟩
  intro y hy
  have hyH : y ∈ H.V := hKV ▸ hy
  have hyold : y ∈ ψ ⁻¹' gd.drawing.V := hp.2 ▸ hyH
  have hr := arc_cut_root_rule hcut hc y hyold
  rw [← hp.2] at hr
  change y ∈ H.V ∩ bd Y ↔ _
  constructor
  · intro h
    rcases hr.mp h with hold | ⟨z, hz, hzy, heq⟩
    · exact .inl ((hroot y hyH).mpr hold.2)
    · exact .inr ⟨z, hKV.symm ▸ hz, hzy, (hfib z hz y hyH).mpr heq⟩
  · rintro (hold | ⟨z, hz, hzy, heq⟩)
    · exact hr.mpr (.inl ⟨hyold, (hroot y hyH).mp hold⟩)
    · have hzH : z ∈ H.V := hKV ▸ hz
      exact hr.mpr (.inr ⟨z, hzH, hzy, (hfib z hzH y hyH).mp heq⟩)

end GraphMinor.GM08
