module

public import GraphMinor.GM01.Defs

/-!
# A subgraph and its graph on its vertex type

The rooted forest proof switches between a simple subgraph of a complete
graph and the same graph with its vertex set as the vertex type. We give
the explicit multigraph isomorphism. Vertices are unchanged, and an edge
on a pair of subtype vertices is sent to that pair of original vertices.
-/

@[expose] public section

namespace GraphMinor.GM01

open Graph SimpleGraph

/-- The isomorphism from the graph on a simple subgraph's vertex type to
its multigraph representation. The vertex map removes the redundant
universal-set subtype, and the edge map applies subtype inclusion to ends. -/
noncomputable def subgraphSimpleGraphIso {α : Type*}
    (H : (⊤ : SimpleGraph α).Subgraph) :
    GraphMinor.Iso (Graph.ofSimpleGraph H.coe) (toGraph H) := by
  let mapEdge : E(Graph.ofSimpleGraph H.coe) → E(toGraph H) := fun e ↦
    ⟨Sym2.map Subtype.val e.val, by
      obtain ⟨edge, he⟩ := e
      induction edge using Sym2.inductionOn with
      | hf x y => exact he⟩
  have hinj : Function.Injective mapEdge := by
    intro e e' heq
    apply Subtype.ext
    exact Sym2.map.injective Subtype.val_injective (congrArg Subtype.val heq)
  have hsurj : Function.Surjective mapEdge := by
    rintro ⟨edge, he⟩
    induction edge using Sym2.inductionOn with
    | hf x y =>
      have hadj : H.Adj x y := he
      let a : H.verts := ⟨x, hadj.fst_mem⟩
      let b : H.verts := ⟨y, hadj.snd_mem⟩
      exact ⟨⟨s(a, b), hadj⟩, Subtype.ext rfl⟩
  refine
    { vertexEquiv :=
        { toFun := fun v ↦ v.val
          invFun := fun v ↦ ⟨v, Set.mem_univ _⟩
          left_inv := fun v ↦ Subtype.ext rfl
          right_inv := fun v ↦ rfl }
      edgeEquiv := Equiv.ofBijective mapEdge ⟨hinj, hsurj⟩
      isLink_iff := ?_ }
  intro e x y
  change (e.val = s(x.val, y.val) ∧ e.val ∈ H.coe.edgeSet) ↔
    (Sym2.map Subtype.val e.val = s(x.val.val, y.val.val) ∧ H.Adj x.val.val y.val.val)
  constructor
  · intro he
    have hadj := he.2
    rw [he.1] at hadj
    exact ⟨congrArg (Sym2.map Subtype.val) he.1, hadj⟩
  · intro he
    exact ⟨Sym2.map.injective Subtype.val_injective he.1, e.property⟩

end GraphMinor.GM01
