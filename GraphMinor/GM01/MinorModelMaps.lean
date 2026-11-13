module

public import GraphMinor.Minor.Model

/-!
# Enlarging the target of a minor model

The last-block assertion in Graph Minors I, (4.1), page 55, first builds
a comb model inside the subdivision and then regards it in `H`. Existing
edge ends do not change when a graph is enlarged, and the connected
branch subgraphs remain connected after the same model edges are deleted.
Thus the actual model maps can be retained in the larger target.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Retain the branch and edge maps of a model when enlarging its target. -/
theorem minorModel_mono {α β γ δ : Type*} {H : Graph γ δ} {N G : Graph α β}
    {ηv : γ → Set α} {ηe : δ → β} (h : IsMinorModel H N ηv ηe) (hNG : N ≤ G) :
    IsMinorModel H G ηv ηe := by
  have hInc : ∀ e ∈ E(N), ∀ x, N.Inc e x ↔ G.Inc e x := by
    intro e he x
    constructor
    · rintro ⟨y, hxy⟩
      exact ⟨y, hxy.mono hNG⟩
    · rintro ⟨y, hxy⟩
      exact ⟨y, (hNG.isLink_iff he).mpr hxy⟩
  refine
    { vertex_nonempty := h.vertex_nonempty
      vertex_subset := fun v hv ↦ (h.vertex_subset v hv).trans hNG.vertexSet_mono
      edge_mem := fun e he ↦ hNG.edgeSet_mono (h.edge_mem e he)
      vertex_disjoint := h.vertex_disjoint
      edge_injOn := h.edge_injOn
      inc_iff := ?_
      isLoopAt_iff := ?_
      connected := ?_ }
  · intro v hv e he
    rw [h.inc_iff v hv e he]
    constructor
    · rintro ⟨x, hx, hxe⟩
      exact ⟨x, hx, (hInc _ (h.edge_mem e he) x).mp hxe⟩
    · rintro ⟨x, hx, hxe⟩
      exact ⟨x, hx, (hInc _ (h.edge_mem e he) x).mpr hxe⟩
  · intro v hv e he
    rw [h.isLoopAt_iff v hv e he]
    exact ⟨fun hall x hx ↦ hall x ((hInc _ (h.edge_mem e he) x).mpr hx),
      fun hall x hx ↦ hall x ((hInc _ (h.edge_mem e he) x).mp hx)⟩
  · intro v hv
    obtain ⟨K, hKN, hV, hconn⟩ := h.connected v hv
    exact ⟨K, hKN.trans (Graph.deleteEdges_mono_left hNG _), hV, hconn⟩

end GraphMinor.GM01
