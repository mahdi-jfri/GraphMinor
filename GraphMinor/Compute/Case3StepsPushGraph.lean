module

public import GraphMinor.Compute.Case3StepsPushMultigraph

/-!
# The restored member has the same named graph edges

Restoring compact labels adds isolated ambient vertices but no edge. The
ordered renaming identifies its compact graph with the induced graph on
the original list. Its edge set is exactly the renamed compact edge set,
and multiplicity bounds against an ambient input graph are preserved.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The compact graph restored through its vertex list is the induced
subgraph of its ambient-label extension. -/
theorem case3PushMultigraph_relabel {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    relabelGraph (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
      (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective) D.toGMDigraph.toGraph =
        (case3PushMultigraph S D).toGMDigraph.toGraph.induce S.toNatSet := by
  have h := case3Induce_relabel_eq (case3PushMultigraph S D) S
  rw [case3PushMultigraph_induce] at h
  exact h

/-- Every edge of the restored graph has both ends in the original list. -/
theorem case3PushMultigraph_edge_ends {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (e : ℕ × ℕ × ℕ) (he : e ∈ (case3PushMultigraph S D).toGMDigraph.edgeSet) :
    e.1 ∈ S.toNatSet ∧ e.2.1 ∈ S.toNatSet := by
  classical
  obtain ⟨hu, hv, hk⟩ := he
  have hpos : 0 < (case3PushMultigraph S D).edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩ := Nat.zero_lt_of_lt hk
  have huS : (⟨e.1, hu⟩ : Fin N) ∈ S := by
    by_contra h
    rw [case3PushMultigraph_edgeMult_zero S D _ _ (Or.inl h)] at hpos
    exact Nat.not_lt_zero _ hpos
  have hvS : (⟨e.2.1, hv⟩ : Fin N) ∈ S := by
    by_contra h
    rw [case3PushMultigraph_edgeMult_zero S D _ _ (Or.inr h)] at hpos
    exact Nat.not_lt_zero _ hpos
  exact ⟨⟨⟨e.1, hu⟩, huS, rfl⟩, ⟨⟨e.2.1, hv⟩, hvS, rfl⟩⟩

/-- The extra isolated ambient vertices do not affect the restored edge set. -/
theorem case3PushMultigraph_edgeSet_induce {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    E((case3PushMultigraph S D).toGMDigraph.toGraph.induce S.toNatSet) =
      E((case3PushMultigraph S D).toGMDigraph.toGraph) := by
  rw [edgeSet_induce]
  ext e
  constructor
  · rintro ⟨u, v, hlink, _, _⟩
    exact hlink.edge_mem
  · intro he
    have hends := case3PushMultigraph_edge_ends S D e he
    exact ⟨e.1, e.2.1, ⟨he, Or.inr ⟨rfl, rfl⟩⟩, hends.1, hends.2⟩

/-- The restored multigraph has exactly the renamed compact edge triples,
including every directed parallel copy. -/
theorem case3PushMultigraph_edgeSet {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    E((case3PushMultigraph S D).toGMDigraph.toGraph) =
      origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective '' E(D.toGMDigraph.toGraph) := by
  rw [← case3PushMultigraph_edgeSet_induce, ← case3PushMultigraph_relabel, edgeSet_relabelGraph]

/-- Any multiplicity bound on the ordered compact graph also holds after
restoring its labels to the original ambient vertex type. -/
theorem case3PushMultigraph_le {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (G : MultiDigraph N) (hD : D ≤ G.induce (S.orderEmbOfFin rfl)) :
    case3PushMultigraph S D ≤ G := by
  classical
  intro u v
  by_cases hu : u ∈ S
  · by_cases hv : v ∈ S
    · obtain ⟨a, rfl⟩ := (show u ∈ Set.range (S.orderEmbOfFin rfl) from (S.range_orderEmbOfFin rfl).symm ▸ hu)
      obtain ⟨b, rfl⟩ := (show v ∈ Set.range (S.orderEmbOfFin rfl) from (S.range_orderEmbOfFin rfl).symm ▸ hv)
      rw [case3PushMultigraph_edgeMult_image]
      exact hD a b
    · rw [case3PushMultigraph_edgeMult_zero S D _ _ (Or.inr hv)]
      exact Nat.zero_le _
  · rw [case3PushMultigraph_edgeMult_zero S D _ _ (Or.inl hu)]
    exact Nat.zero_le _

end GraphMinor.Compute
