module

public import GraphMinor.Compute.GM06PuncturedGraphPort
public import Mathlib.Combinatorics.Graph.Basic

/-!
# Interpreting a computed component's attachment in the graph

For Reduction 2 in VI (5.7), page 133, the endpoint labels describe
the actual graph links. The computed component attaches to the
rest of this graph only at the removed vertex. Translate each
actual edge back to its active endpoint pair and use the proved
attachment property of the finite search graph, in either orientation.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Compute
universe u v

/-- The labelled finite component has no exit in the actual graph
except at the removed vertex. Only vertex labels and link incidence
are assumed about the finite representation. -/
theorem computed_punctured_component_port
    {S : Type u} {E : Type v} {n : ℕ} (G : Graph S E)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ S)
    (edge : Fin tagged.length → E)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.edgeSet, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (cut source : Fin n) (hsource : source ≠ cut) :
    ∀ e a b, G.IsLink e a b →
      a ∈ vertex '' {r | (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source r} ∩ G.vertexSet →
      b ∈ vertex '' {r | (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source r} ∩ G.vertexSet ∨
        b = vertex cut := by
  intro e a b hl ha
  obtain ⟨a₀, ha₀, hva⟩ := ha.1
  obtain ⟨j, hj, hje⟩ := hcover e hl.edge_mem
  have hjlink := hlinks j hj
  rw [hje] at hjlink
  rcases hl.eq_and_eq_or_eq_and_eq hjlink with h | h
  · have hja : a₀ = tagged[j].1.1 := vertex.injective (hva.trans h.1)
    have hport := gm06PuncturedGraphData_reachable_port tagged cut source hsource
      (List.getElem_mem j.isLt) hj (hja ▸ ha₀)
    rcases hport with hb | hb
    · exact Or.inl ⟨⟨tagged[j].1.2, hb, h.2.symm⟩, hl.right_mem⟩
    · exact Or.inr (h.2.trans (congrArg vertex hb))
  · have hja : a₀ = tagged[j].1.2 := vertex.injective (hva.trans h.1)
    have hport := gm06PuncturedGraphData_reachable_port_right tagged cut source hsource
      (List.getElem_mem j.isLt) hj (hja ▸ ha₀)
    rcases hport with hb | hb
    · exact Or.inl ⟨⟨tagged[j].1.1, hb, h.2.symm⟩, hl.right_mem⟩
    · exact Or.inr (h.2.trans (congrArg vertex hb))

end GraphMinor.GM06
