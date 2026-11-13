module

public import GraphMinor.Kruskal.ForestSimple
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Passing multigraph trees to simple trees

We lift a walk of the underlying simple graph to a multigraph walk by
choosing an edge for each step. The vertex lists agree under subtype
inclusion. Distinct edges of a simple-graph walk lift to distinct original
edges, since an original edge has just one unordered pair of ends.
Consequently a simple-graph cycle would contradict the multigraph's forest
condition. Connectivity transfers through adjacency as well.
-/

public section

namespace GraphMinor.Kruskal

open Graph Surface SimpleGraph Set

private noncomputable def liftWalk {α β : Type*} (G : Graph α β)
    {a b : V(G)} : G.toSimpleGraph.Walk a b → GraphWalk G a.val b.val
  | .nil => .nil a.property
  | .cons hadj rest => .cons (Classical.choose_spec hadj.2) (liftWalk G rest)

private theorem liftWalk_support {α β : Type*} (G : Graph α β)
    {a b : V(G)} (w : G.toSimpleGraph.Walk a b) :
    (liftWalk G w).support = w.support.map Subtype.val := by
  induction w with
  | nil => rfl
  | cons hadj rest ih =>
    simp only [liftWalk, GraphWalk.support, Walk.support_cons, List.map_cons, ih]

private theorem liftWalk_length {α β : Type*} (G : Graph α β)
    {a b : V(G)} (w : G.toSimpleGraph.Walk a b) :
    (liftWalk G w).length = w.length := by
  induction w with
  | nil => rfl
  | cons hadj rest ih =>
    change (liftWalk G rest).length + 1 = rest.length + 1
    exact congrArg (· + 1) ih

private theorem edge_mem_of_liftWalk_edge_mem {α β : Type*} (G : Graph α β)
    {a b : V(G)} (w : G.toSimpleGraph.Walk a b) {e : β} {x y : V(G)}
    (he : G.IsLink e x y) (hm : e ∈ (liftWalk G w).edges) :
    s(x, y) ∈ w.edges := by
  induction w with
  | nil => exact False.elim (List.not_mem_nil hm)
  | @cons a c b hadj rest ih =>
    change e ∈ Classical.choose hadj.2 :: (liftWalk G rest).edges at hm
    rcases List.mem_cons.1 hm with heq | hm
    · subst e
      have hc := Classical.choose_spec hadj.2
      have hp : s(x, y) = s(a, c) := by
        rcases he.eq_and_eq_or_eq_and_eq hc with h | h
        · exact Sym2.eq_iff.2 (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
        · exact Sym2.eq_iff.2 (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
      rw [hp]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hm)

private theorem liftWalk_edges_nodup {α β : Type*} (G : Graph α β)
    {a b : V(G)} (w : G.toSimpleGraph.Walk a b) (hw : w.edges.Nodup) :
    (liftWalk G w).edges.Nodup := by
  induction w with
  | nil => exact List.nodup_nil
  | @cons a c b hadj rest ih =>
    obtain ⟨hhead, htail⟩ := List.nodup_cons.1 hw
    refine List.nodup_cons.2 ⟨?_, ih htail⟩
    intro hm
    exact hhead (edge_mem_of_liftWalk_edge_mem G rest (Classical.choose_spec hadj.2) hm)

/-- A circuit in the underlying simple graph lifts to a simple closed walk
of the original multigraph. Thus the forest condition implies acyclicity. -/
theorem isAcyclic_toSimpleGraph_of_forest {α β : Type*} {G : Graph α β}
    (hforest : IsGraphForest G) : G.toSimpleGraph.IsAcyclic := by
  intro a w hw
  have hW : (liftWalk G w).IsSimpleClosed := by
    constructor
    · rw [liftWalk_support, ← List.map_tail]
      exact hw.support_nodup.map Subtype.val_injective
    · exact liftWalk_edges_nodup G w hw.edges_nodup
  have hzero := hforest a.val (liftWalk G w) hW
  rw [liftWalk_length] at hzero
  exact hw.not_nil (Walk.length_eq_zero_iff.1 hzero)

private theorem reachable_toSimpleGraph {α β : Type*} {G : Graph α β} [G.Loopless]
    {x y : α} (hx : x ∈ V(G)) (h : Relation.ReflTransGen G.Adj x y) :
    ∃ hy : y ∈ V(G), Relation.ReflTransGen G.toSimpleGraph.Adj ⟨x, hx⟩ ⟨y, hy⟩ := by
  induction h with
  | refl => exact ⟨hx, .refl⟩
  | @tail z y hrest hzy ih =>
    obtain ⟨hz, ih⟩ := ih
    have hy : y ∈ V(G) := hzy.elim fun e he ↦ he.right_mem
    exact ⟨hy, .tail ih ((G.toSimpleGraph_adj_iff ⟨z, hz⟩ ⟨y, hy⟩).2 hzy)⟩

/-- An undirected multigraph tree, as used in IV (1.2), gives a Mathlib
simple tree on its actual vertex set. -/
theorem isTree_toSimpleGraph {α β : Type*} {G : Graph α β}
    (hG : GM04.IsUndirectedTree G) : G.toSimpleGraph.IsTree := by
  let := forest_loopless hG.2
  have hconn : G.toSimpleGraph.Connected := by
    let root : V(G) := ⟨hG.1.1.some, hG.1.1.some_mem⟩
    let : Nonempty V(G) := ⟨root⟩
    constructor
    intro a b
    rw [SimpleGraph.reachable_iff_reflTransGen]
    obtain ⟨_, h⟩ := reachable_toSimpleGraph a.property (hG.1.2 a a.property b b.property)
    exact h
  exact ⟨hconn, isAcyclic_toSimpleGraph_of_forest hG.2⟩

end GraphMinor.Kruskal
