module

public import GraphMinor.GM06.Section3Induce
public import GraphMinor.Compute.GM06InducedEdgeBits
import GraphMinor.GM11.Walks

/-!
# Interpreting the induced active-edge mask

Reduction 2 in VI (5.7), page 133, keeps the drawing induced on
the retained live vertices. The RAM mask keeps exactly active
edges with two retained endpoints. The original edge labels and
endpoint pairs therefore still describe every edge of the new
drawing, with the same incidence and no renumbering.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute

/-- The computed induced mask has exactly the links and edge coverage
needed to interpret the next drawing state with the same original labels. -/
theorem induced_mask_links_and_cover
    {S : Type*} [TopologicalSpace S] [T1Space S] {n : ℕ} (G : Drawing S)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ S)
    (edge : Fin tagged.length → Set S)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (C : Finset (Fin n)) (hC : vertex '' (C : Set (Fin n)) ⊆ G.V) :
    (∀ j : Fin tagged.length,
      (gm06InducedEdgeBits tagged C)[j.val]'(by rw [gm06InducedEdgeBits_length]; exact j.isLt) = 1 →
      (induceDrawing G (vertex '' (C : Set (Fin n)))).toGraph.IsLink
        (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2)) ∧
    (∀ e ∈ (induceDrawing G (vertex '' (C : Set (Fin n)))).E,
      ∃ j : Fin tagged.length,
        (gm06InducedEdgeBits tagged C)[j.val]'(by rw [gm06InducedEdgeBits_length]; exact j.isLt) = 1 ∧ edge j = e) := by
  constructor
  · intro j hj
    obtain ⟨hactive, hu, hv⟩ := (gm06InducedEdgeBits_getElem_eq_one tagged C j.isLt).mp hj
    rw [induceDrawing_toGraph_eq_induce G hC, Graph.induce_isLink]
    exact ⟨hlinks j hactive, ⟨tagged[j].1.1, hu, rfl⟩, ⟨tagged[j].1.2, hv, rfl⟩⟩
  · intro e he
    rw [induceDrawing_E] at he
    obtain ⟨j, hj, hje⟩ := hcover e he.1
    have hl := hlinks j hj
    rw [hje] at hl
    have hends : {vertex tagged[j].1.1, vertex tagged[j].1.2} ⊆ vertex '' (C : Set (Fin n)) := by
      rw [← hl.2.2.2]
      exact he.2
    have hu : tagged[j].1.1 ∈ C := by
      obtain ⟨u, hu, hue⟩ := hends (mem_insert _ _)
      exact vertex.injective hue ▸ hu
    have hv : tagged[j].1.2 ∈ C := by
      obtain ⟨v, hv, hve⟩ := hends (mem_insert_of_mem _ (mem_singleton _))
      exact vertex.injective hve ▸ hv
    exact ⟨j, (gm06InducedEdgeBits_getElem_eq_one tagged C j.isLt).mpr ⟨hj, hu, hv⟩, hje⟩

end GraphMinor.GM06
