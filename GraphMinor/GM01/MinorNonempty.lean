module

public import GraphMinor.Statement

/-!
# A nonempty minor has a nonempty target

The maximal family on page 60 of Graph Minors I consists of disjoint
sets whose induced graphs have nonempty tree minors. Each such set
must be nonempty. A vertex of the minor maps under its isomorphism
to a contracted vertex, which comes from a vertex of the chosen
subgraph and hence from the target graph.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- A graph with a nonempty minor has a vertex. This supplies the
nonempty sets in the maximal-family bound on page 60 of GM01. -/
theorem minor_vertexSet_nonempty {α β ν ε : Type*} {H : Graph ν ε} {G : Graph α β}
    (h : IsIsoMinor H G) (hH : V(H).Nonempty) : V(G).Nonempty := by
  obtain ⟨v, hv⟩ := hH
  obtain ⟨K, hKG, C, _, ⟨iso⟩⟩ := h
  have hx := (iso.vertexEquiv ⟨v, hv⟩).property
  simp only [contract, vertexSet_deleteEdges, vertexSet_map] at hx
  obtain ⟨x, hxK, _⟩ := hx
  exact ⟨x, hKG.vertexSet_mono hxK⟩

end GraphMinor.GM01
