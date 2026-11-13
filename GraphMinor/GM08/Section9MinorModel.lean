module

public import GraphMinor.GM07.Defs
public import GraphMinor.Minor.Model
import GraphMinor.GM16.DrawingGraphPaths
import GraphMinor.GM19.Section6a

/-!
# Forgetting the directions in the minor used by VIII (9.3)

A boundary-rooted minor of surface digraphs gives an undirected minor
model. Its branch drawings supply the connected branch sets, and its
chosen edges join the prescribed branches. The chosen edges lie in no
branch drawing, so the branches stay connected after those edges are
deleted, as required by a graph simulation.
-/

public section

namespace GraphMinor.GM08

open Set Surface Graph

universe u

private theorem surfaceDigraph_isLink {S : Type u} [TopologicalSpace S] [T1Space S]
    (H : GM07.SurfaceDigraph S) {e : Set S} (he : e ∈ H.G.E) :
    H.G.toGraph.IsLink e (H.plus e) (H.minus e) := by
  refine ⟨he, H.plus_mem e he, H.minus_mem e he, ?_⟩
  rw [← GM19.tilde_eq_inter_V H.G he]
  exact (H.ends_eq e he).symm

private theorem adj_chain_of_walk {α β : Type*} {G : Graph α β} {x y : α}
    (W : GraphWalk G x y) : Relation.ReflTransGen G.Adj x y := by
  induction W with
  | nil _ => exact .refl
  | cons h _ ih => exact ih.head ⟨_, h⟩

/-- The undirected graph simulation underlying the boundary-rooted minor
used in VIII (9.3), page 270. Boundary roots retain their own vertices. -/
theorem exists_minorModel_of_boundaryRootedMinor {S : Type u} [TopologicalSpace S] [T1Space S]
    {H G : GM07.SurfaceDigraph S} (h : GM07.IsBoundaryRootedMinor H G) :
    ∃ (ηv : S → Set S) (ηe : Set S → Set S),
      IsMinorModel H.G.toGraph G.G.toGraph ηv ηe ∧
      ∀ v ∈ H.G.V ∩ bd S, v ∈ ηv v := by
  obtain ⟨-, φv, φe, hφv, hφe, hdis, hinj, hoff, hends, hroots⟩ := h
  have heq : ∀ v ∈ H.G.V, ∀ w ∈ H.G.V, ∀ x,
      x ∈ (φv v).V → x ∈ (φv w).V → v = w := by
    intro v hv w hw x hx hx'
    by_contra hne
    exact disjoint_left.mp (hdis v hv w hw hne) hx hx'
  refine ⟨fun v => (φv v).V, φe, ?_, hroots⟩
  refine {
    vertex_nonempty := fun v hv => (hφv v hv).2.1
    vertex_subset := fun v hv => (hφv v hv).1.1
    edge_mem := hφe
    vertex_disjoint := hdis
    edge_injOn := fun e he f hf heq => by
      by_contra hne
      exact hinj e he f hf hne heq
    inc_iff := ?_
    isLoopAt_iff := ?_
    connected := ?_ }
  · intro v hv e he
    have hH := surfaceDigraph_isLink H he
    have hG := surfaceDigraph_isLink G (hφe e he)
    constructor
    · intro hi
      rcases hi.eq_or_eq_of_isLink hH with rfl | rfl
      · exact ⟨_, (hends e he).1, hG.inc_left⟩
      · exact ⟨_, (hends e he).2, hG.inc_right⟩
    · rintro ⟨x, hx, hix⟩
      rcases hix.eq_or_eq_of_isLink hG with rfl | rfl
      · have hv' := heq v hv (H.plus e) (H.plus_mem e he) _ hx (hends e he).1
        subst v
        exact hH.inc_left
      · have hv' := heq v hv (H.minus e) (H.minus_mem e he) _ hx (hends e he).2
        subst v
        exact hH.inc_right
  · intro v hv e he
    have hH := surfaceDigraph_isLink H he
    have hG := surfaceDigraph_isLink G (hφe e he)
    constructor
    · intro hl x hx
      have hp : H.plus e = v := by
        rcases hH.inc_left.eq_or_eq_of_isLink hl with h | h <;> exact h
      have hm : H.minus e = v := by
        rcases hH.inc_right.eq_or_eq_of_isLink hl with h | h <;> exact h
      rcases hx.eq_or_eq_of_isLink hG with rfl | rfl
      · simpa only [hp] using (hends e he).1
      · simpa only [hm] using (hends e he).2
    · intro hall
      have hp := heq (H.plus e) (H.plus_mem e he) v hv _
        (hends e he).1 (hall _ hG.inc_left)
      have hm := heq (H.minus e) (H.minus_mem e he) v hv _
        (hends e he).2 (hall _ hG.inc_right)
      change H.G.toGraph.IsLink e v v
      simpa only [hp, hm] using hH
  · intro v hv
    have hsub := GM16.toGraph_le_of_isSubdrawing (hφv v hv).1
    refine ⟨(φv v).toGraph, ⟨hsub.vertexSet_mono, ?_⟩, rfl,
      (hφv v hv).2.1, ?_⟩
    · intro e x y hl
      rw [deleteEdges_isLink]
      refine ⟨hl.mono hsub, ?_⟩
      rintro ⟨f, hf, rfl⟩
      exact hoff v hv f hf hl.edge_mem
    · intro x hx y hy
      obtain ⟨W⟩ := (hφv v hv).2.2.2 x hx y hy
      exact adj_chain_of_walk W

end GraphMinor.GM08
