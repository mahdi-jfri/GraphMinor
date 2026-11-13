module

public import GraphMinor.GM01.Defs
public import GraphMinor.Hypergraph.Basic

/-!
# Path separators in the two simple-graph representations

For the Menger application in Graph Minors I, (4.2), a simple graph is
also used as a subgraph of the complete graph. Paths in the former map
to paths in the latter by the identity vertex map. A path contained in
the latter lifts back edge by edge with the same support. Consequently
the two path-separator predicates agree.
-/

public section

namespace GraphMinor.GM01

open Set SimpleGraph

/-- A complete-graph path contained in a simple graph lifts to a walk of
that graph with exactly the same vertex support. -/
theorem lift_path_to_simpleGraph {α : Type*} (S : SimpleGraph α) (P : Path α)
    (hP : P.toSubgraph ≤ SimpleGraph.toSubgraph S le_top) :
    ∃ w : S.Walk P.first P.last, w.support = P.walk.support ∧ w.IsPath := by
  have lift : ∀ {a b : α} (w : (⊤ : SimpleGraph α).Walk a b),
      w.toSubgraph ≤ SimpleGraph.toSubgraph S le_top →
      ∃ w' : S.Walk a b, w'.support = w.support := by
    intro a b w
    induction w with
    | nil => intro _; exact ⟨.nil, rfl⟩
    | @cons a a' b hadj w ih =>
      intro hle
      have ha : S.Adj a a' := (subgraphOfAdj_le_iff _ _).mp (le_sup_left.trans hle)
      obtain ⟨w', hw'⟩ := ih (le_sup_right.trans hle)
      exact ⟨w'.cons ha, by simp only [Walk.support_cons, hw']⟩
  obtain ⟨w, hw⟩ := lift P.walk hP
  refine ⟨w, hw, ?_⟩
  apply w.isPath_def.mpr
  rw [hw]
  exact P.isPath.support_nodup

/-- The Section 2 subgraph separator predicate agrees with meeting every
path of the simple graph, as required to apply Menger in (4.2). -/
theorem separates_toSubgraph_iff_paths {α : Type*} (S : SimpleGraph α) (X A B : Set α) :
    Separates (SimpleGraph.toSubgraph S le_top) X A B ↔
      ∀ p : PathFromTo S A B, ∃ v ∈ p.walk.support, v ∈ X := by
  classical
  let K := SimpleGraph.toSubgraph S le_top
  let hom : S →g (⊤ : SimpleGraph α) := ⟨id, fun h ↦ (top_adj _ _).mpr h.ne⟩
  have map_le : ∀ {a b : α} (w : S.Walk a b), (w.map hom).toSubgraph ≤ K := by
    intro a b w
    induction w with
    | nil => exact (singletonSubgraph_le_iff _ _).mpr (mem_univ _)
    | cons hadj w ih =>
      exact sup_le (subgraphOfAdj_le_of_adj K hadj) ih
  constructor
  · intro hsep p
    by_contra hmiss
    let P : Path α := ⟨p.first, p.last, p.walk.map hom, p.isPath.map Function.injective_id⟩
    have hFrom : P.IsFromTo K A B := ⟨map_le p.walk, p.first_mem, p.last_mem⟩
    apply hsep P hFrom
    apply Set.disjoint_left.mpr
    intro x hx hxX
    have hxMap : x ∈ (p.walk.map hom).support := (Walk.mem_verts_toSubgraph _).mp hx
    have hSupport : (p.walk.map hom).support = p.walk.support := by
      rw [Walk.support_map]
      change List.map id p.walk.support = p.walk.support
      exact List.map_id _
    exact hmiss ⟨x, hSupport ▸ hxMap, hxX⟩
  · intro hpaths P hFrom hAvoid
    obtain ⟨w, hw, hPath⟩ := lift_path_to_simpleGraph S P hFrom.1
    let p : PathFromTo S A B := ⟨P.first, P.last, w, hPath, hFrom.2.1, hFrom.2.2⟩
    obtain ⟨v, hv, hvX⟩ := hpaths p
    have hvP : v ∈ P.verts := (Walk.mem_verts_toSubgraph _).mpr (hw ▸ hv)
    exact Set.disjoint_left.mp hAvoid hvP hvX

end GraphMinor.GM01
