module

public import GraphMinor.GM01.Defs
public import GraphMinor.GM05.Defs
public import GraphMinor.Minor.Basic
import GraphMinor.GM01.Basic
import GraphMinor.GM05.Main

/-!
# Restricting the size of a grid minor

For the grid theorem cited as Graph Minors X, (7.4), page 173, a bound
for a larger grid also gives a bound for any smaller grid. We prove this
by mapping each vertex to the vertex with the same two coordinates.
The branch sets of the resulting minor model are single vertices.
We then derive the grid bound for the simple-graph tree-width of Graph
Minors V from its proved theorem.
-/

public section

namespace GraphMinor.GM10

open SimpleGraph GM01

universe u

/-- A grid is a minor of every grid with at least as many rows and columns.
This is the size restriction used when applying the grid theorem in
Graph Minors X, (7.4), page 173. -/
theorem isIsoMinor_gridGraph_of_le {m n : ℕ} (h : m ≤ n) :
    IsIsoMinor (gridGraph m) (gridGraph n) := by
  let f : Fin m × Fin m → Fin n × Fin n :=
    fun p ↦ (Fin.castLE h p.1, Fin.castLE h p.2)
  have hf : Function.Injective f := by
    intro p q hpq
    apply Prod.ext
    · exact Fin.ext (congrArg (fun x : Fin n × Fin n ↦ x.1.val) hpq)
    · exact Fin.ext (congrArg (fun x : Fin n × Fin n ↦ x.2.val) hpq)
  have hadj : ∀ {p q}, (pathGraph m □ pathGraph m).Adj p q →
      (pathGraph n □ pathGraph n).Adj (f p) (f q) := by
    intro p q hpq
    simp only [boxProd_adj, pathGraph_adj] at hpq ⊢
    rcases hpq with ⟨heq, hadj⟩ | ⟨heq, hadj⟩
    · exact Or.inl ⟨heq, congrArg (Fin.castLE h) hadj⟩
    · exact Or.inr ⟨heq, congrArg (Fin.castLE h) hadj⟩
  unfold gridGraph
  rw [ofSimpleGraph_eq_toGraph (pathGraph n □ pathGraph n)]
  let G := SimpleGraph.toSubgraph (pathGraph n □ pathGraph n) le_top
  let K := fun p : Fin m × Fin m ↦ (GM01.Path.singleton (f p)).toSubgraph
  apply isIsoMinor_ofSimpleGraph_of_connected_subgraphs
    (pathGraph m □ pathGraph m) (Set.toFinite G.verts) K
  · intro p
    refine ⟨fun _ _ ↦ trivial, fun x y hxy ↦ ?_⟩
    have : ¬ (GM01.Path.singleton (f p)).toSubgraph.Adj x y := by
      simp [GM01.Path.singleton, GM01.Path.toSubgraph]
    exact (this hxy).elim
  · intro p
    exact (GM01.Path.singleton _).connected_toSubgraph
  · intro p q hpq
    change Disjoint (GM01.Path.singleton (f p)).verts (GM01.Path.singleton (f q)).verts
    rw [GM01.Path.singleton_verts, GM01.Path.singleton_verts, Set.disjoint_singleton]
    exact hf.ne hpq
  · intro p q hpq
    refine ⟨f p, ?_, f q, ?_, hadj hpq⟩
    · change f p ∈ (GM01.Path.singleton (f p)).verts
      simp
    · change f q ∈ (GM01.Path.singleton (f q)).verts
      simp

/-- The grid theorem cited in Graph Minors X, (7.4), page 173, for the
simple-graph tree-width used in Graph Minors V. The bound follows from
Graph Minors V, (7.3), page 108, by taking its contrapositive. -/
theorem exists_grid_minor_bound_simpleGraph (θ : ℕ) :
    ∃ φ : ℕ, ∀ {V : Type u} (G : (⊤ : SimpleGraph V).Subgraph),
      G.verts.Finite → φ ≤ GM05.treeWidth G →
        IsIsoMinor (gridGraph θ) (toGraph G) := by
  refine ⟨GM05.θ₉ (2 * (θ + 3)) + 1, ?_⟩
  intro V G hG hwidth
  by_contra hno
  have hbound := GM05.treeWidth_le_of_not_isIsoMinor_proved
    (θ := 2 * (θ + 3)) (by omega)
    (show Even (2 * (θ + 3)) from ⟨θ + 3, by omega⟩) hG hno
    (isIsoMinor_gridGraph_of_le (show θ ≤ 2 * (θ + 3) by omega))
  omega

end GraphMinor.GM10
