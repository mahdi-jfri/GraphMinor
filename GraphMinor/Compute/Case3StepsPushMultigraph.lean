module

public import GraphMinor.Compute.Case3StepsInduceTransport
public import GraphMinor.Compute.Algorithm99Relabel

/-!
# Restoring a compact member to the original ambient vertex type

A compact multigraph on an increasing vertex list is extended by zero
outside that list. Each directed parallel class keeps its entire prefix
of copy numbers. This restores the ambient labels required by the wall
output of XIII (9.9), step 6, without adding any edge.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Extend an ordered compact multigraph by zero outside its original vertex list. -/
noncomputable def case3PushMultigraph {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    MultiDigraph N where
  edgeMult u v :=
    if hu : u ∈ S then
      if hv : v ∈ S then D.edgeMult ((S.orderIsoOfFin rfl).symm ⟨u, hu⟩)
        ((S.orderIsoOfFin rfl).symm ⟨v, hv⟩) else 0
    else 0

/-- Every directed multiplicity is restored exactly at the original endpoints. -/
theorem case3PushMultigraph_edgeMult_image {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (u v : Fin S.card) :
    (case3PushMultigraph S D).edgeMult (S.orderEmbOfFin rfl u) (S.orderEmbOfFin rfl v) = D.edgeMult u v := by
  classical
  have hu := S.orderEmbOfFin_mem rfl u
  have hv := S.orderEmbOfFin_mem rfl v
  have hiu : (⟨S.orderEmbOfFin rfl u, hu⟩ : S) = S.orderIsoOfFin rfl u := rfl
  have hiv : (⟨S.orderEmbOfFin rfl v, hv⟩ : S) = S.orderIsoOfFin rfl v := rfl
  simp only [case3PushMultigraph, hu, hv, ↓reduceDIte, hiu, hiv, OrderIso.symm_apply_apply]

/-- No restored edge has an endpoint outside the original vertex list. -/
theorem case3PushMultigraph_edgeMult_zero {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (u v : Fin N) (hout : u ∉ S ∨ v ∉ S) :
    (case3PushMultigraph S D).edgeMult u v = 0 := by
  classical
  rcases hout with hu | hv
  · simp only [case3PushMultigraph, hu, ↓reduceDIte]
  · simp only [case3PushMultigraph, hv, ↓reduceDIte]
    split <;> rfl

/-- Restricting the restored graph to its increasing vertex list recovers
the supplied compact graph exactly. -/
theorem case3PushMultigraph_induce {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    (case3PushMultigraph S D).induce (S.orderEmbOfFin rfl) = D := by
  ext u v
  exact case3PushMultigraph_edgeMult_image S D u v

/-- Deleting the added isolated vertices removes no restored edge. -/
theorem case3PushMultigraph_delete_compl {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    (case3PushMultigraph S D).deleteVertices Sᶜ = case3PushMultigraph S D := by
  classical
  ext u v
  rw [MultiDigraph.deleteVertices_edgeMult]
  split_ifs with h
  · rfl
  · have hout : u ∉ S ∨ v ∉ S := by
      simpa only [Finset.mem_compl, not_not, not_and_or] using h
    exact (case3PushMultigraph_edgeMult_zero S D u v hout).symm

/-- Restoring the ordered vertex list preserves the positive-pair order
used by the multigraph encoding. -/
theorem case3PushMultigraph_activePairs {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    (case3PushMultigraph S D).activePairsList = D.activePairsList.map
      (Prod.map (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)) := by
  let P := case3PushMultigraph S D
  have hmap := P.activePairsList_deleteVertices_eq_map Sᶜ
  rw [case3PushMultigraph_delete_compl] at hmap
  have hc : (P.deleteVerticesCompact Sᶜ).activePairsList.map
        (Prod.map (compactEmb Sᶜ) (compactEmb Sᶜ)) =
      (P.induce (S.orderEmbOfFin rfl)).activePairsList.map
        (Prod.map (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)) := by
    unfold MultiDigraph.deleteVerticesCompact compactEmb
    exact congrArg (fun T : Finset (Fin N) => (P.induce (T.orderEmbOfFin rfl)).activePairsList.map
      (Prod.map (T.orderEmbOfFin rfl) (T.orderEmbOfFin rfl))) (compl_compl S)
  rw [hc, case3PushMultigraph_induce] at hmap
  exact hmap

/-- The restored graph and compact graph contain exactly the same number
of positive directed pairs. -/
theorem case3PushMultigraph_numActivePairs {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    (case3PushMultigraph S D).numActivePairs = D.numActivePairs := by
  change (case3PushMultigraph S D).activePairsList.length = D.activePairsList.length
  rw [case3PushMultigraph_activePairs, List.length_map]

/-- Restoring labels changes no directed copy count. -/
theorem case3PushMultigraph_numEdges {N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card) :
    (case3PushMultigraph S D).numEdges = D.numEdges := by
  rw [← MultiDigraph.sumEdgeMult_activePairsList (case3PushMultigraph S D),
    case3PushMultigraph_activePairs, MultiDigraph.sumEdgeMult_eq_map_sum, List.map_map]
  change ((D.activePairsList.map (fun p => (case3PushMultigraph S D).edgeMult
    (S.orderEmbOfFin rfl p.1) (S.orderEmbOfFin rfl p.2))).sum) = _
  simp only [case3PushMultigraph_edgeMult_image]
  exact (D.sumEdgeMult_eq_map_sum D.activePairsList).symm.trans D.sumEdgeMult_activePairsList

end GraphMinor.Compute
