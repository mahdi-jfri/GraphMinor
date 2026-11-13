module

public import GraphMinor.Minor.Basic
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Realizing simple branch trees with original graph edges

For II (4.8), choose a spanning tree in the simple graph of a branch.
Each edge of that tree must be represented by one original graph edge.
Choose independently on the subtype of tree edges. Different tree edges
have different endpoint pairs, so the chosen original edges are distinct.
Keeping exactly those edges gives the required subgraph with every
original vertex, including isolated vertices of a spanning subgraph.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set
universe u v

/-- A spanning simple subgraph of the underlying simple graph can be
realized using one original edge per simple edge. The displayed
isomorphism sends a vertex of the simple graph to that same original
vertex and sends each simple edge to its chosen representative. -/
theorem exists_subgraph_iso_of_simple_graph_on {α : Type u} {β : Type v}
    (G : Graph α β) (S : Set α) (hS : S ⊆ V(G)) (T : SimpleGraph S)
    (hle : ∀ {a b : S}, T.Adj a b → G.Adj a.val b.val) :
    ∃ K ≤ G, V(K) = S ∧ ∃ φ : Iso (Graph.ofSimpleGraph T) K,
      ∀ x : V(Graph.ofSimpleGraph T), (φ.vertexEquiv x).val = x.val.val := by
  classical
  let H := Graph.ofSimpleGraph T
  have hchoice : ∀ e : E(H), ∃ f : β, ∀ x y : S,
      H.IsLink e x y → G.IsLink f x.val y.val := by
    intro e
    obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet e.property
    have hadj : G.Adj x.val y.val := by
      exact hle ((SimpleGraph.mem_edgeSet _).1 (hxy.1 ▸ hxy.2))
    obtain ⟨f, hf⟩ := hadj
    refine ⟨f, fun a b hab ↦ ?_⟩
    rcases hxy.eq_and_eq_or_eq_and_eq hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hf
    · exact hf.symm
  let f : E(H) → β := fun e ↦ (hchoice e).choose
  have hlink : ∀ e : E(H), ∀ x y : S,
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
  let K := (G.restrict (Set.range f)).induce S
  have hEK : E(K) = Set.range f := by
    ext e
    constructor
    · intro he
      obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet he
      exact hxy.1.1
    · rintro ⟨d, rfl⟩
      obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet d.property
      exact (show K.IsLink (f d) x.val y.val from
        ⟨⟨Set.mem_range_self d, hlink d x y hxy⟩, x.property, y.property⟩).edge_mem
  let hIso : Iso H K := {
    vertexEquiv := Equiv.Set.univ S
    edgeEquiv := (Equiv.ofInjective f hf).trans
      (Equiv.subtypeEquivRight fun e ↦ by rw [hEK])
    isLink_iff := by
      rintro e ⟨x, _⟩ ⟨y, _⟩
      change H.IsLink e x y ↔ K.IsLink (f e) x.val y.val
      constructor
      · intro hxy
        exact ⟨⟨Set.mem_range_self e, hlink e x y hxy⟩, x.property, y.property⟩
      · rintro ⟨⟨_, hxy⟩, _, _⟩
        obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet e.property
        have hl := hlink e a b hab
        rcases hl.eq_and_eq_or_eq_and_eq hxy with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · have hax : a = x := Subtype.ext ha
          have hby : b = y := Subtype.ext hb
          exact hax ▸ hby ▸ hab
        · have hay : a = y := Subtype.ext ha
          have hbx : b = x := Subtype.ext hb
          exact hbx ▸ hay ▸ hab.symm }
  exact ⟨K, (Graph.induce_le (G := G.restrict (Set.range f)) hS).trans
    Graph.restrict_le, rfl, hIso, fun x => congrArg Subtype.val (Equiv.Set.univ_apply S x)⟩

/-- A spanning simple subgraph of the underlying simple graph can be
realized by original edges while retaining all original vertices. -/
theorem exists_subgraph_iso_of_simple_subgraph {α : Type u} {β : Type v}
    (G : Graph α β) (T : SimpleGraph V(G)) (hle : T ≤ G.toSimpleGraph) :
    ∃ K ≤ G, V(K) = V(G) ∧ Nonempty (Iso (Graph.ofSimpleGraph T) K) := by
  obtain ⟨K, hK, hV, φ, _⟩ := exists_subgraph_iso_of_simple_graph_on
    G V(G) (Subset.refl _) T (fun h => (hle h).2)
  exact ⟨K, hK, hV, ⟨φ⟩⟩

end GraphMinor.GM02
