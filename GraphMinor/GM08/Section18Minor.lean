module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM07.Section2Base
import GraphMinor.GM11.Walks
import GraphMinor.GM16.DrawingGraphPaths

/-!
# Turning VII boundary-rooted minors into graph simulations

The branch subdrawings in a boundary-rooted minor give connected branch
subgraphs. Their endpoint conditions give the incidence and loop conditions
of a graph simulation. This is the minor-to-simulation step needed when
VIII (18.1) applies VII (9.1).
-/

public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface GraphMinor.GM11

universe w

private theorem digraph_isLink_ends {S : Type w} [TopologicalSpace S] [T1Space S]
    (D : GM07.SurfaceDigraph S) {e : Set S} (he : e ∈ D.G.E) :
    D.G.toGraph.IsLink e (D.plus e) (D.minus e) := by
  refine ⟨he, D.plus_mem e he, D.minus_mem e he, ?_⟩
  exact (GM07.tilde_eq_closure_inter_V D.G he).symm.trans (D.ends_eq e he).symm

private theorem digraph_inc_iff {S : Type w} [TopologicalSpace S] [T1Space S]
    (D : GM07.SurfaceDigraph S) {e : Set S} (he : e ∈ D.G.E) (x : S) :
    D.G.toGraph.Inc e x ↔ x = D.plus e ∨ x = D.minus e := by
  have hl := digraph_isLink_ends D he
  constructor
  · intro hx
    exact hx.eq_or_eq_of_isLink hl
  · rintro (rfl | rfl)
    · exact hl.inc_left
    · exact hl.inc_right

private theorem digraph_isLoopAt_iff {S : Type w} [TopologicalSpace S] [T1Space S]
    (D : GM07.SurfaceDigraph S) {e : Set S} (he : e ∈ D.G.E) (x : S) :
    D.G.toGraph.IsLoopAt e x ↔ x = D.plus e ∧ x = D.minus e := by
  have hl := digraph_isLink_ends D he
  constructor
  · intro hx
    exact ⟨hx.eq_of_inc hl.inc_left, hx.eq_of_inc hl.inc_right⟩
  · rintro ⟨rfl, heq⟩
    rwa [← heq] at hl

private theorem graphConnected_of_drawing_connected {S : Type w} [TopologicalSpace S]
    (D : Drawing S) (h : D.IsConnected) : GraphConnected D.toGraph := by
  refine ⟨h.1, fun x hx y hy => ?_⟩
  obtain ⟨W⟩ := h.2 x hx y hy
  induction W with
  | nil _ => exact .refl
  | cons hl _ ih => exact .head ⟨_, hl⟩ (ih hl.right_mem hy)

/-- VII's boundary-rooted minor is a simulation of the underlying graphs.
This proves the graph part of the conversion used by VIII (18.1), page 285. -/
theorem isGraphSimulatedIn_of_boundaryRootedMinor {S : Type w} [TopologicalSpace S] [T1Space S]
    {H G : GM07.SurfaceDigraph S} (h : GM07.IsBoundaryRootedMinor H G) :
    ∃ ηv ηe, IsGraphSimulation H.G.toGraph G.G.toGraph ηv ηe ∧
      ∀ v ∈ H.G.V ∩ bd S, v ∈ ηv v := by
  obtain ⟨_, φv, φe, hsub, hedge, hdis, hinj, havoid, hends, hroot⟩ := h
  have howner : ∀ {v z : S}, v ∈ H.G.V → z ∈ H.G.V →
      ∀ {x : S}, x ∈ (φv v).V → x ∈ (φv z).V → v = z := by
    intro v z hv hz x hxv hxz
    by_contra hne
    exact disjoint_left.mp (hdis v hv z hz hne) hxv hxz
  refine ⟨fun v => (φv v).V, φe, ?_, hroot⟩
  refine {
    vertex_nonempty := fun v hv => (hsub v hv).2.1
    vertex_subset := fun v hv => (hsub v hv).1.1
    edge_mem := hedge
    vertex_disjoint := hdis
    edge_injOn := ?_
    inc_iff := ?_
    isLoopAt_iff := ?_
    connected := ?_ }
  · intro e he f hf heq
    by_contra hne
    exact hinj e he f hf hne heq
  · intro v hv e he
    rw [digraph_inc_iff H he]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨G.plus (φe e), (hends e he).1,
          (digraph_inc_iff G (hedge e he) _).mpr (Or.inl rfl)⟩
      · exact ⟨G.minus (φe e), (hends e he).2,
          (digraph_inc_iff G (hedge e he) _).mpr (Or.inr rfl)⟩
    · rintro ⟨x, hx, hinc⟩
      rcases (digraph_inc_iff G (hedge e he) x).mp hinc with rfl | rfl
      · exact Or.inl (howner hv (H.plus_mem e he) hx (hends e he).1)
      · exact Or.inr (howner hv (H.minus_mem e he) hx (hends e he).2)
  · intro v hv e he
    rw [digraph_isLoopAt_iff H he]
    constructor
    · rintro ⟨hp, hm⟩ x hx
      rcases (digraph_inc_iff G (hedge e he) x).mp hx with rfl | rfl
      · simpa only [← hp] using (hends e he).1
      · simpa only [← hm] using (hends e he).2
    · intro hall
      have hp := hall _ ((digraph_isLink_ends G (hedge e he)).inc_left)
      have hm := hall _ ((digraph_isLink_ends G (hedge e he)).inc_right)
      exact ⟨howner hv (H.plus_mem e he) hp (hends e he).1,
        howner hv (H.minus_mem e he) hm (hends e he).2⟩
  · intro v hv
    have hle : (φv v).toGraph ≤ G.G.toGraph.deleteEdges (φe '' H.G.E) := by
      refine ⟨(hsub v hv).1.1, fun e x y hl => ?_⟩
      refine ⟨(GM16.toGraph_le_of_isSubdrawing (hsub v hv).1).isLink_mono hl, ?_⟩
      rintro ⟨f, hf, rfl⟩
      exact havoid v hv f hf hl.1
    exact ⟨(φv v).toGraph, hle, rfl, graphConnected_of_drawing_connected _ (hsub v hv).2.2⟩

/-- The graft represented by a drawing, rooted at its boundary vertices,
as in VIII Section 5, page 262. -/
@[expose] def boundaryGraft {S : Type w} [TopologicalSpace S] [T1Space S]
    (D : Drawing S) : Graft S (Set S) where
  G := D.toGraph
  T := D.V ∩ bd S
  T_subset := inter_subset_left
  finite_G := ⟨D.finite_V, D.finite_edges⟩

/-- The boundary-rooted minor of VII yields a simulation of the represented
grafts, including the boundary roots. This is the conversion in VIII (18.1). -/
theorem isGraftSimulatedIn_boundaryGraft_of_boundaryRootedMinor {S : Type w}
    [TopologicalSpace S] [T1Space S] {H G : GM07.SurfaceDigraph S}
    (h : GM07.IsBoundaryRootedMinor H G) :
    IsGraftSimulatedIn (boundaryGraft H.G) (boundaryGraft G.G) := by
  obtain ⟨ηv, ηe, hmodel, hroot⟩ := isGraphSimulatedIn_of_boundaryRootedMinor h
  refine ⟨ηv, ηe, hmodel, ?_, ?_⟩
  · exact congrArg Set.ncard h.1.symm
  · intro v hv
    exact ⟨v, hroot v hv, h.1.subset hv⟩

end GraphMinor.GM08
