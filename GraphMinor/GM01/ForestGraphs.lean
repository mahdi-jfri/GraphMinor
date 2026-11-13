module

public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
import GraphMinor.Minor.Basic

/-!
# Forests as multigraphs

Graph Minors I allows loops and multiple edges in general graphs. A forest
has neither, and its underlying simple graph is acyclic. We use these
conditions to define forests and give the explicit isomorphism with their
underlying simple graphs. This lets the forest-minor construction in the
proof of (1.1) apply to the paper's multigraphs.
-/

@[expose] public section

namespace GraphMinor.GM01

open Graph SimpleGraph

variable {α β : Type*}

/-- A forest in Graph Minors I, (1.1), page 39: a simple graph with no cycles.
The paper allows loops and multiple edges in general graphs, but neither
can occur in a forest. -/
def IsForest (G : Graph α β) : Prop := G.Simple ∧ G.toSimpleGraph.IsAcyclic

/-- A simple multigraph is isomorphic to the multigraph obtained from its
underlying simple graph. Vertices are unchanged. Each unordered adjacent
pair is sent to its unique edge in the original graph. -/
noncomputable def simpleGraphIso (G : Graph α β) [G.Simple] :
    GraphMinor.Iso (Graph.ofSimpleGraph G.toSimpleGraph) G := by
  classical
  have choose_edge : ∀ e : G.toSimpleGraph.edgeSet, ∃ f : E(G),
      ∀ x y : V(G), G.IsLink f x y ↔ e.val = s(x, y) := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hadj : G.toSimpleGraph.Adj x y := he
      obtain ⟨f, hf⟩ := (G.toSimpleGraph_adj_iff x y).mp hadj
      refine ⟨⟨f, hf.edge_mem⟩, ?_⟩
      intro a b
      constructor
      · intro hab
        rcases hf.eq_and_eq_or_eq_and_eq hab with h | h
        · exact Sym2.eq_iff.mpr (Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
        · exact Sym2.eq_iff.mpr (Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
      · intro hab
        rcases Sym2.eq_iff.mp hab with h | h
        · rcases h with ⟨rfl, rfl⟩
          exact hf
        · rcases h with ⟨rfl, rfl⟩
          exact hf.symm
  let f (e : G.toSimpleGraph.edgeSet) : E(G) := (choose_edge e).choose
  have spec (e : G.toSimpleGraph.edgeSet) (x y : V(G)) :
      G.IsLink (f e) x y ↔ e.val = s(x, y) := (choose_edge e).choose_spec x y
  have hinj : Function.Injective f := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ h
    apply Subtype.ext
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hlink := (spec ⟨s(x, y), he⟩ x y).mpr rfl
      change G.IsLink (f ⟨s(x, y), he⟩) x y at hlink
      rw [h] at hlink
      exact ((spec ⟨e', he'⟩ x y).mp hlink).symm
  have hsurj : Function.Surjective f := by
    intro e
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.property
    let a : V(G) := ⟨x, hxy.left_mem⟩
    let b : V(G) := ⟨y, hxy.right_mem⟩
    have hadj : G.toSimpleGraph.Adj a b := (G.toSimpleGraph_adj_iff a b).mpr ⟨e, hxy⟩
    let e' : G.toSimpleGraph.edgeSet := ⟨s(a, b), hadj⟩
    refine ⟨e', Subtype.ext ?_⟩
    exact ((spec e' a b).mpr rfl).eq hxy
  refine
    { vertexEquiv :=
        { toFun := fun v ↦ v.val
          invFun := fun v ↦ ⟨v, Set.mem_univ _⟩
          left_inv := fun v ↦ Subtype.ext rfl
          right_inv := fun v ↦ rfl }
      edgeEquiv := Equiv.ofBijective f ⟨hinj, hsurj⟩
      isLink_iff := ?_ }
  intro e x y
  change (e.val = s(x.val, y.val) ∧ e.val ∈ G.toSimpleGraph.edgeSet) ↔
    G.IsLink (f e) x.val y.val
  exact (and_iff_left e.property).trans (spec e x.val y.val).symm

end GraphMinor.GM01
