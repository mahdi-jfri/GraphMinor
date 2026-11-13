module

public import GraphMinor.Compute.GM06SuccessorInput
public import GraphMinor.GM06.Defs
public import GraphMinor.Compute.GM06EndpointValency
import GraphMinor.Compute.GM06LabelledValency

/-!
# Interpreting the graph part of a cylinder input

The vertex and edge labels correspond bijectively to the actual graph.
The listed ends match the actual link relation. These conditions only
interpret supplied graph data. They contain no reduction, successor
linkage, or feasibility assertion. The remaining geometric fields of
the cylinder input are interpreted separately.
-/

public section
namespace GraphMinor.Compute
universe u v

/-- Bijections interpreting only the vertices, edges and ends of the finite input. -/
structure GM06SuccessorGraphRep (x : GM06SuccessorInput) {α : Type u} {β : Type v}
    (G : Graph α β) where
  vertex : Fin x.vertexCount ≃ G.vertexSet
  pairs : List (Fin x.vertexCount × Fin x.vertexCount)
  endpoints : x.endpoints = gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))
  edge : Fin pairs.length ≃ G.edgeSet
  link : ∀ i : Fin pairs.length,
    G.IsLink (edge i).val (vertex pairs[i.val].1).val (vertex pairs[i.val].2).val

namespace GM06SuccessorGraphRep

/-- The endpoint count in the input is the actual valency at the interpreted vertex. -/
theorem vertexValency_eq {x : GM06SuccessorInput} {α : Type u} {β : Type v}
    {G : Graph α β} (h : GM06SuccessorGraphRep x G) (a : Fin x.vertexCount) :
    GM06.vertexValency G (h.vertex a).val = x.endpoints.count a.val := by
  rw [h.endpoints]
  exact gm06LabelledVertexValency G (fun a => (h.vertex a).val)
    (Subtype.val_injective.comp h.vertex.injective) h.pairs h.edge h.link a

/-- The supplied vertex count is the cardinality of the actual vertex set. -/
theorem vertexCount_eq {x : GM06SuccessorInput} {α : Type u} {β : Type v}
    {G : Graph α β} (h : GM06SuccessorGraphRep x G) : x.vertexCount = G.vertexSet.ncard := by
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_congr h.vertex

/-- The list of supplied edge ends has one entry per actual edge. -/
theorem pairCount_eq {x : GM06SuccessorInput} {α : Type u} {β : Type v}
    {G : Graph α β} (h : GM06SuccessorGraphRep x G) : h.pairs.length = G.edgeSet.ncard := by
  simpa only [Nat.card_fin, Nat.card_coe_set_eq] using Nat.card_congr h.edge

/-- The endpoint array has two positions per actual edge, also for loops. -/
theorem endpoints_length {x : GM06SuccessorInput} {α : Type u} {β : Type v}
    {G : Graph α β} (h : GM06SuccessorGraphRep x G) :
    x.endpoints.length = 2 * G.edgeSet.ncard := by
  rw [h.endpoints, gm06EndpointWords_length, List.length_map, h.pairCount_eq]

/-- Every supplied endpoint is a valid vertex label. -/
theorem endpoint_lt {x : GM06SuccessorInput} {α : Type u} {β : Type v}
    {G : Graph α β} (h : GM06SuccessorGraphRep x G) {a : ℕ} (ha : a ∈ x.endpoints) :
    a < x.vertexCount := by
  rw [h.endpoints] at ha
  obtain ⟨p, hp, ha⟩ := List.mem_flatMap.mp ha
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact p.1.isLt
  · exact p.2.isLt

end GM06SuccessorGraphRep
end GraphMinor.Compute
