module

public import GraphMinor.GM06.Section5SeparationOutside
public import GraphMinor.Compute.GM06PuncturedAdjActive
public import GraphMinor.Compute.BFS

/-!
# A discarded vertex has a linkage-disjoint searched component

For the completeness of Reduction 2 in VI (5.7), page 133, start
outside the retained side of its separation. Every searched edge
avoids the shared vertex, so its walk stays outside that side.
Consequently a mask contained in the retained side has zero
intersection with the searched source component.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Compute

/-- A searched component starting outside one separation side stays
outside it, since all searched edges avoid the shared vertex. -/
theorem computed_punctured_component_notMem_left
    {α β : Type*} {n : ℕ} {G G₁ G₂ : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) (vertex : Fin n ↪ α)
    (tagged : List ((Fin n × Fin n) × ℕ)) (edge : Fin tagged.length → β)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (cut source : Fin n) (hover : G₁.vertexSet ∩ G₂.vertexSet ⊆ {vertex cut})
    (hsource : vertex source ∉ G₁.vertexSet) {v : Fin n}
    (hv : (gm06PuncturedGraphData tagged cut).vertexGraph.Reachable source v) :
    vertex v ∉ G₁.vertexSet := by
  let H : SimpleGraph (Fin n) := (gm06PuncturedGraphData tagged cut).vertexGraph
  have hwalk := (SimpleGraph.reachable_iff_reflTransGen (G := H) source v).mp hv
  clear hv
  induction hwalk with
  | refl => exact hsource
  | @tail a b _ hab ih =>
    obtain ⟨_, hbc, j, hactive, hends⟩ := gm06PuncturedGraphData_adj_active tagged cut hab
    have hl : G.IsLink (edge j) (vertex a) (vertex b) := by
      rcases hends with h | h
      · simpa only [h.1, h.2] using hlinks j hactive
      · simpa only [h.1, h.2] using (hlinks j hactive).symm
    exact separation_link_notMem_left hsep hover hl ih (fun he => hbc (vertex.injective he))

/-- Any protected mask lying in the retained side misses the computed
component of a source outside that side. -/
theorem computed_punctured_component_zero_of_separation
    {α β : Type*} {n : ℕ} {G G₁ G₂ : Graph α β}
    (hsep : IsGraphSeparation G G₁ G₂) (vertex : Fin n ↪ α)
    (tagged : List ((Fin n × Fin n) × ℕ)) (edge : Fin tagged.length → β)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (cut source : Fin n) (hover : G₁.vertexSet ∩ G₂.vertexSet ⊆ {vertex cut})
    (hsource : vertex source ∉ G₁.vertexSet) (Q : Finset (Fin n))
    (hQ : vertex '' (Q : Set (Fin n)) ⊆ G₁.vertexSet) :
    (Q ∩ GraphMinor.Compute.reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvQ, hvReach⟩ := Finset.mem_inter.mp hv
  have hreach := (GraphMinor.Compute.mem_reachSet _ source v).mp hvReach
  exact computed_punctured_component_notMem_left hsep vertex tagged edge hlinks cut source hover hsource hreach
    (hQ ⟨v, hvQ, rfl⟩)

end GraphMinor.GM06
