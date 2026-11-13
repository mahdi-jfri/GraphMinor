module

public import GraphMinor.GM06.Section5ComputedComponentOutside

/-!
# Completeness of the finite Reduction 2 tests

A proper retained side of a one-vertex separation either omits
a vertex or an attachment loop. A missing vertex supplies a live
source whose searched component misses the protected vertices.
A missing loop supplies an active endpoint pair with both ends
at the cut vertex. Thus the finite tests used by VI (5.7), page 133,
cover every separation of the required kind.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Compute

/-- Every proper one-vertex separation retaining the protected
vertices is detected by a punctured component or the initial-loop test. -/
theorem computed_reduction2_search_complete
    {α β : Type*} {n : ℕ} {G G₁ G₂ : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) (vertex : Fin n ↪ α)
    (tagged : List ((Fin n × Fin n) × ℕ)) (edge : Fin tagged.length → β)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.edgeSet, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (A : Finset (Fin n)) (hV : G.vertexSet = vertex '' (A : Set (Fin n)))
    (cut : Fin n) (hover : G₁.vertexSet ∩ G₂.vertexSet ⊆ {vertex cut})
    (hne : G₁ ≠ G) (Q : Finset (Fin n))
    (hQ : vertex '' (Q : Set (Fin n)) ⊆ G₁.vertexSet) :
    (∃ source ∈ A,
      (Q ∩ GraphMinor.Compute.reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0) ∨
      ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut := by
  rcases proper_separation_has_outside_vertex_or_cut_loop hsep hover hne with
      ⟨a, ha, haNot⟩ | ⟨e, hl, _⟩
  · left
    obtain ⟨source, hsourceA, hsource⟩ := hV ▸ ha
    refine ⟨source, hsourceA, ?_⟩
    exact computed_punctured_component_zero_of_separation hsep vertex tagged edge hlinks cut source
      hover (fun hs => haNot (hsource ▸ hs)) Q hQ
  · right
    obtain ⟨j, hj, hje⟩ := hcover e hl.edge_mem
    have hjlink := hlinks j hj
    rw [hje] at hjlink
    rcases hl.eq_and_eq_or_eq_and_eq hjlink with h | h
    · exact ⟨j, hj, (vertex.injective h.1).symm, (vertex.injective h.2).symm⟩
    · exact ⟨j, hj, (vertex.injective h.2).symm, (vertex.injective h.1).symm⟩

end GraphMinor.GM06
