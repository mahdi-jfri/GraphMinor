module

public import GraphMinor.GM06.Defs
public import GraphMinor.Compute.GM06EndpointValency
import GraphMinor.Compute.GM06ValencyRepresentation
import Mathlib.Data.List.Count

/-!
# Interpreting numeric vertex labels in an actual graph

The vertices of a drawing need not be natural numbers. An injective
labelling interprets finite vertex labels as actual vertices. Edge
labels are in bijection with the actual edge set, with the supplied
ends. This ordinary input correspondence preserves valency.
-/

public section
namespace GraphMinor.Compute
universe u v

private theorem map_pair_endpoints {α β : Type*} (f : α → β) (pairs : List (α × α)) :
    ((pairs.map fun p => (f p.1, f p.2)).flatMap fun p => [p.1, p.2]) =
      (pairs.flatMap fun p => [p.1, p.2]).map f := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
    simpa only [List.map_cons, List.flatMap_cons, List.map_append, List.map_cons,
      List.map_nil] using congrArg (fun xs => [f p.1, f p.2] ++ xs) ih

/-- Numeric endpoint counts equal actual valency under injective vertex labels
and a bijection with the actual edges and their supplied ends. -/
theorem gm06LabelledVertexValency {n : ℕ} {α : Type u} {β : Type v}
    (G : Graph α β) (vertex : Fin n → α) (hv : Function.Injective vertex)
    (pairs : List (Fin n × Fin n)) (edge : Fin pairs.length ≃ G.edgeSet)
    (hlink : ∀ i : Fin pairs.length,
      G.IsLink (edge i).val (vertex pairs[i.val].1) (vertex pairs[i.val].2)) (a : Fin n) :
    GM06.vertexValency G (vertex a) =
      (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).count a.val := by
  classical
  let actual := pairs.map fun p => (vertex p.1, vertex p.2)
  have hlen : actual.length = pairs.length := List.length_map _
  let actualEdge : Fin actual.length ≃ G.edgeSet := (finCongr hlen).trans edge
  have hactual (i : Fin actual.length) :
      G.IsLink (actualEdge i).val actual[i.val].1 actual[i.val].2 := by
    simpa only [actualEdge, Equiv.trans_apply, actual, List.getElem_map, finCongr_apply_coe]
      using hlink ((finCongr hlen) i)
  have hh := gm06VertexValency_eq_endpoint_count G actual actualEdge hactual (vertex a)
  rw [map_pair_endpoints, List.count_map_of_injective _ vertex hv] at hh
  have hnum : gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val)) =
      (pairs.flatMap fun p => [p.1, p.2]).map Fin.val := map_pair_endpoints Fin.val pairs
  rw [hnum, List.count_map_of_injective _ Fin.val Fin.val_injective]
  exact hh

end GraphMinor.Compute
