module

public import Mathlib.Combinatorics.Graph.Simple

/-!
# Selecting edges of the underlying simple graph

To use simple-graph paths in the proof of Graph Minors I, (1.1), choose
one original edge for every adjacent pair of distinct vertices. Distinct
unordered pairs have distinct chosen edges because an edge has a unique
unordered pair of ends. Loops and unused parallel edges are left out.
-/

public section

namespace GraphMinor.GM01

open Graph

/-- The underlying simple graph embeds into the original graph by the
identity on vertices and a choice of one edge per adjacent pair. The
edge map is injective and the displayed equivalence specifies its ends. -/
theorem exists_simpleGraph_edge_embedding {α β : Type*} (G : Graph α β) :
    ∃ f : G.toSimpleGraph.edgeSet ↪ E(G),
      ∀ (e : G.toSimpleGraph.edgeSet) (x y : V(G)),
        G.IsLink (f e) x y ↔ e.val = s(x,y) := by
  classical
  have choose_edge : ∀ e : G.toSimpleGraph.edgeSet, ∃ f : E(G),
      ∀ x y : V(G), G.IsLink f x y ↔ e.val = s(x,y) := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hadj : G.toSimpleGraph.Adj x y := he
      obtain ⟨f, hf⟩ := hadj.2
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
      G.IsLink (f e) x y ↔ e.val = s(x,y) := (choose_edge e).choose_spec x y
  have hinj : Function.Injective f := by
    rintro ⟨e, he⟩ ⟨e', he'⟩ h
    apply Subtype.ext
    induction e using Sym2.inductionOn with
    | hf x y =>
      have hlink := (spec ⟨s(x,y), he⟩ x y).mpr rfl
      change G.IsLink (f ⟨s(x,y), he⟩) x y at hlink
      rw [h] at hlink
      exact ((spec ⟨e', he'⟩ x y).mp hlink).symm
  exact ⟨⟨f, hinj⟩, spec⟩

end GraphMinor.GM01
