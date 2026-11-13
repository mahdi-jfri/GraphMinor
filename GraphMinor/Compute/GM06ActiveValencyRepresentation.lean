module

public import GraphMinor.Compute.GM06LabelledValency
public import GraphMinor.Compute.GM06ActiveEndpointSum
import GraphMinor.Compute.GM06ActiveEdgeLabels

/-!
# Actual valency from persistent active endpoint labels

The reduction loop in VI (5.7), page 133, retains original edge
indices while clearing their activity bits. Enumerate just those
indices whose bit is one. Their bijection with the drawing's edges
allows the ordinary labelled valency theorem to apply. The masked
endpoint-sum identity then gives exactly the current graph valency,
including twice the number of active loops.
-/

public section
namespace GraphMinor.Compute
universe u v

/-- The active endpoint-bit sum equals actual vertex valency from
primitive active links, injective labels and complete edge coverage. -/
theorem gm06ActiveLabelledVertexValency {n : ℕ} {α : Type u} {β : Type v}
    (G : Graph α β) (vertex : Fin n → α) (hv : Function.Injective vertex)
    (tagged : List ((Fin n × Fin n) × ℕ)) (edge : Fin tagged.length → β)
    (hinj : Set.InjOn edge {j | tagged[j.val].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j.val].2 = 1 →
      G.IsLink (edge j) (vertex tagged[j.val].1.1) (vertex tagged[j.val].1.2))
    (hcover : ∀ e ∈ G.edgeSet, ∃ j : Fin tagged.length, tagged[j.val].2 = 1 ∧ edge j = e)
    (a : Fin n) :
    GM06.vertexValency G (vertex a) =
      (gm06ActiveEndpointBits
        (gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
        (tagged.map Prod.snd) a.val).sum := by
  classical
  let labels := gm06ActiveEdgeIndices tagged
  let pairs := labels.map fun j => tagged[j.val].1
  have hlen : pairs.length = labels.length := List.length_map _
  obtain ⟨e, he⟩ := exists_active_edge_position_equiv tagged edge G.edgeSet hinj
    (fun j hj => (hlinks j hj).edge_mem) hcover
  let ePair : Fin pairs.length ≃ G.edgeSet := (finCongr hlen).trans e
  have hpair (i : Fin pairs.length) :
      G.IsLink (ePair i).val (vertex pairs[i.val].1) (vertex pairs[i.val].2) := by
    let j : Fin labels.length := (finCongr hlen) i
    have hjactive : tagged[labels[j.val]].2 = 1 :=
      (gm06ActiveEdgeIndices_mem_iff tagged labels[j.val]).mp (List.getElem_mem j.isLt)
    have hh := hlinks labels[j.val] hjactive
    simpa only [ePair, Equiv.trans_apply, he, pairs, List.getElem_map, finCongr_apply_coe, j] using hh
  have hpairs : pairs = (tagged.filter fun p => p.2 == 1).map Prod.fst := by
    calc
      pairs = (labels.map fun j => tagged[j.val]).map Prod.fst := by
        simp only [pairs, List.map_map, Function.comp_def]
      _ = _ := congrArg (List.map Prod.fst) (gm06ActiveEdgeIndices_map_get tagged)
  have hval := gm06LabelledVertexValency G vertex hv pairs ePair hpair a
  rw [hpairs] at hval
  simp only [List.map_map, Function.comp_def] at hval
  have hsum := gm06ActiveEndpointBits_sum_eq_filtered_count
    (tagged.map fun p => ((p.1.1.val, p.1.2.val), p.2)) a.val
  simp only [List.map_map, Function.comp_def, List.filter_map] at hsum
  exact hval.trans hsum.symm

end GraphMinor.Compute
