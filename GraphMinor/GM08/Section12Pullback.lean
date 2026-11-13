module

public import GraphMinor.GM08.Section12Subspace
import Mathlib.Combinatorics.Graph.Delete

/-!
# Pulling a drawn piece back to the original graph

A subgraph of a drawing corresponds, under its drawing isomorphism,
to a subgraph of the original graph. Restrict the original vertices
and edges to their inverse images. This gives the exact vertex and
edge sets needed for the smaller labels on VIII, page 272.
-/

public section

namespace GraphMinor.GM08

open Set Graph

/-- Pull a subgraph back through an isomorphism. The vertex and edge
sets are the inverse images, as required of a foundation label in the
derived portrait used in VIII, Section 12. -/
theorem exists_subgraph_of_iso {α β γ δ : Type*} [Nonempty γ] [Nonempty δ]
    {G : Graph α β} {H H' : Graph γ δ} (a : Iso G H) (hH : H' ≤ H) :
    ∃ G' : Graph α β, G' ≤ G ∧
      V(G') = {v ∈ V(G) | a.fv v ∈ V(H')} ∧
      E(G') = {e ∈ E(G) | a.fe e ∈ E(H')} ∧
      IsGraphBij G' H' a.fv a.fe := by
  let V' := {v ∈ V(G) | a.fv v ∈ V(H')}
  let E' := {e ∈ E(G) | a.fe e ∈ E(H')}
  let G' := (G.induce V').restrict E'
  have hle : G' ≤ G := Graph.restrict_le.trans (G.induce_le (sep_subset _ _))
  have hV : V(G') = V' := rfl
  have hE : E(G') = E' := by
    apply inter_eq_right.mpr
    intro e he
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he.1
    have hxyH := a.isLink_fv hxy
    have hxyH' : H'.IsLink (a.fe e) (a.fv x) (a.fv y) :=
      (Graph.IsSubgraph.isLink_iff hH he.2).mpr hxyH
    exact ⟨x, y, hxy, ⟨hxy.left_mem, hxyH'.left_mem⟩,
      ⟨hxy.right_mem, hxyH'.right_mem⟩⟩
  refine ⟨G', hle, hV, hE, a.isGraphBij.restrict hle hH ?_ ?_⟩
  · intro v hv
    change (v ∈ V' ↔ _)
    exact ⟨fun h => h.2, fun h => ⟨hv, h⟩⟩
  · intro e he
    rw [hE]
    exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩

end GraphMinor.GM08
