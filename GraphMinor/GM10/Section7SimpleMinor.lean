module

public import GraphMinor.Minor.Basic
public import GraphMinor.GM01.Defs

/-!
# Passing from a graph to its underlying simple graph

To apply the grid theorem cited in Graph Minors X, (7.4), page 173,
we keep one edge between each pair of adjacent distinct vertices and
delete loops. This subgraph is isomorphic to the underlying simple graph.
The construction chooses edges only on the edge set, so it also works
when the ambient edge type is empty.
-/

public section

namespace GraphMinor.GM10

open Graph SimpleGraph

universe u v
variable {α : Type u} {β : Type v}

/-- The underlying simple graph of a graph is isomorphic to a minor of
that graph: keep one edge between each pair of distinct adjacent vertices. -/
theorem isIsoMinor_ofSimpleGraph_toSimpleGraph (G : Graph α β) :
    IsIsoMinor (Graph.ofSimpleGraph G.toSimpleGraph) G := by
  classical
  let H := Graph.ofSimpleGraph G.toSimpleGraph
  have hchoice : ∀ e : E(H), ∃ f : β, ∀ x y : V(G),
      H.IsLink e x y → G.IsLink f x.val y.val := by
    intro e
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet e.property
    have hadj : G.toSimpleGraph.Adj x y := by
      exact (SimpleGraph.mem_edgeSet _).1 (hxy.1 ▸ hxy.2)
    obtain ⟨f, hf⟩ := hadj.2
    refine ⟨f, fun a b hab ↦ ?_⟩
    rcases hxy.eq_and_eq_or_eq_and_eq hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf
    · exact hf.symm
  let f : E(H) → β := fun e ↦ (hchoice e).choose
  have hlink : ∀ e : E(H), ∀ x y : V(G),
      H.IsLink e x y → G.IsLink (f e) x.val y.val :=
    fun e ↦ (hchoice e).choose_spec
  have hf : Function.Injective f := by
    intro e d heq
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet e.property
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet d.property
    have hl := hlink e x y hxy
    have hl' : G.IsLink (f e) a.val b.val := heq ▸ hlink d a b hab
    apply Subtype.ext
    rcases hl.eq_and_eq_or_eq_and_eq hl' with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hxa : x = a := Subtype.ext hx
      have hyb : y = b := Subtype.ext hy
      exact hxy.1.trans (by rw [hxa, hyb]; exact hab.1.symm)
    · have hxb : x = b := Subtype.ext hx
      have hya : y = a := Subtype.ext hy
      exact hxy.1.trans (by rw [hxb, hya, Sym2.eq_swap]; exact hab.1.symm)
  let K := G.restrict (Set.range f)
  have hEK : E(K) = Set.range f := by
    ext e
    simp only [K, Graph.edgeSet_restrict, Set.mem_inter_iff]
    constructor
    · exact And.right
    · rintro ⟨d, rfl⟩
      obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet d.property
      exact ⟨(hlink d x y hxy).edge_mem, Set.mem_range_self d⟩
  have hIso : Iso H K := {
    vertexEquiv := Equiv.Set.univ V(G)
    edgeEquiv := (Equiv.ofInjective f hf).trans
      (Equiv.subtypeEquivRight fun e ↦ by rw [hEK])
    isLink_iff := by
      rintro e ⟨x, _⟩ ⟨y, _⟩
      change H.IsLink e x y ↔ K.IsLink (f e) x.val y.val
      constructor
      · intro hxy
        exact ⟨Set.mem_range_self e, hlink e x y hxy⟩
      · rintro ⟨_, hxy⟩
        obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet e.property
        have hl := hlink e a b hab
        rcases hl.eq_and_eq_or_eq_and_eq hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have hax : a = x := Subtype.ext ha
          have hby : b = y := Subtype.ext hb
          exact hax ▸ hby ▸ hab
        · have hay : a = y := Subtype.ext ha
          have hbx : b = x := Subtype.ext hb
          exact hbx ▸ hay ▸ hab.symm }
  have hKG : IsIsoMinor K G := by
    obtain ⟨K', hK', C, hC, hIso'⟩ := IsIsoMinor.refl K
    exact ⟨K', hK'.trans Graph.restrict_le, C, hC, hIso'⟩
  exact hIso.isIsoMinor_left hKG

end GraphMinor.GM10
