module

public import GraphMinor.GM06.Defs
public import GraphMinor.Compute.GM06DegreeScan
import GraphMinor.Compute.GM06ValencyRepresentation
public import GraphMinor.Compute.GM06EndpointValency
import Mathlib.Data.List.Count

/-!
# Correctness of the RAM valency query for a labelled graph

Finite vertices have labels in `Fin n`, and the edge list is in
bijection with the actual edge set. Erasing the `Fin` bounds gives the
word array used by the RAM. Injectivity of the labels preserves endpoint
counts, so the program returns the graph's actual valency.
-/

public section
namespace GraphMinor.Compute
open TwoPaths
universe u

/-- Numeric endpoint words retain the occurrence count of every finite vertex label. -/
theorem gm06FiniteEndpointWords_valency {n : ℕ} {β : Type u}
    (G : Graph (Fin n) β) (pairs : List (Fin n × Fin n))
    (edge : Fin pairs.length ≃ G.edgeSet)
    (hlink : ∀ i : Fin pairs.length, G.IsLink (edge i).val pairs[i.val].1 pairs[i.val].2)
    (a : Fin n) :
    GM06.vertexValency G a =
      (gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))).count a.val := by
  have hwords : gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val)) =
      (pairs.flatMap fun p => [p.1, p.2]).map Fin.val := by
    clear hlink edge
    induction pairs with
    | nil => rfl
    | cons p pairs ih =>
      simpa only [List.map_cons, gm06EndpointWords, List.flatMap_cons,
        List.map_append, List.map_cons, List.map_nil, List.append_assoc] using
        congrArg (fun xs => [p.1.val, p.2.val] ++ xs) ih
  rw [hwords, List.count_map_of_injective _ Fin.val Fin.val_injective]
  exact gm06VertexValency_eq_endpoint_count G pairs edge hlink a

/-- The endpoint RAM scan computes the actual graph valency, counting loops twice. -/
theorem gm06DegreeProg_exec_on_graph {w n : ℕ} {β : Type u} (ends : ℕ)
    (G : Graph (Fin n) β) (pairs : List (Fin n × Fin n))
    (edge : Fin pairs.length ≃ G.edgeSet)
    (hlink : ∀ i : Fin pairs.length, G.IsLink (edge i).val pairs[i.val].1 pairs[i.val].2)
    (a : Fin n) (s : State) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hm : 2 * pairs.length < 2 ^ w)
    (ha : s.arrs ends = gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val)))
    (hr : s.regs 22 = a.val) :
    ∃ s' t, Exec w (gm06DegreeProg ends) s s' t ∧
      t ≤ 7 + 28 * pairs.length ∧ Keeps [20, 21] [] s s' ∧
      s'.regs 21 = GM06.vertexValency G a := by
  let xs := gm06EndpointWords (pairs.map fun p => (p.1.val, p.2.val))
  have hlen : xs.length = 2 * pairs.length := by
    simp only [xs, gm06EndpointWords_length, List.length_map]
  have hwords : ∀ x ∈ xs, x < 2 ^ w := by
    intro x hx
    obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
    obtain ⟨p, _, rfl⟩ := List.mem_map.mp hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact p.1.isLt.trans hn
    · exact p.2.isLt.trans hn
  obtain ⟨s', t, he, ht, hk, hd⟩ := gm06DegreeProg_exec ends xs a.val s hw
    (hlen ▸ hm) hwords (a.isLt.trans hn) ha hr
  refine ⟨s', t, he, ?_, hk, hd.trans (gm06FiniteEndpointWords_valency G pairs edge hlink a).symm⟩
  rw [hlen] at ht
  omega

end GraphMinor.Compute
