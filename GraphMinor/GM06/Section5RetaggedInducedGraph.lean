module

public import GraphMinor.GM06.Section5InducedMaskGraph
public import GraphMinor.Compute.GM06EdgeMaskData

/-!
# Reinterpreting the updated component-search input

After Reduction 2 installs an induced activity mask, pair that
mask with the unchanged endpoint rows. The resulting finite
active graph has exactly the links and edge coverage of the
retained drawing. Thus the next search uses the same original
edge indices and no new graph certificate.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.Compute

/-- Retagging by the computed induced mask preserves the primitive
link and edge-coverage interpretation of the active drawing. -/
theorem retagged_induced_mask_links_and_cover
    {S : Type*} [TopologicalSpace S] [T1Space S] {n : ℕ} (G : Drawing S)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n ↪ S)
    (edge : Fin tagged.length → Set S)
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (C : Finset (Fin n)) (hC : vertex '' (C : Set (Fin n)) ⊆ G.V) :
    let mask := gm06InducedEdgeBits tagged C
    let updated := gm06RetagEdges tagged mask
    let edge' : Fin updated.length → Set S :=
      fun j => edge (Fin.cast (gm06RetagEdges_length tagged mask) j)
    (∀ j : Fin updated.length, updated[j].2 = 1 →
      (induceDrawing G (vertex '' (C : Set (Fin n)))).toGraph.IsLink
        (edge' j) (vertex updated[j].1.1) (vertex updated[j].1.2)) ∧
    (∀ e ∈ (induceDrawing G (vertex '' (C : Set (Fin n)))).E,
      ∃ j : Fin updated.length, updated[j].2 = 1 ∧ edge' j = e) := by
  dsimp only
  have hlen := gm06InducedEdgeBits_length tagged C
  obtain ⟨hnewLinks, hnewCover⟩ := induced_mask_links_and_cover G tagged vertex edge hlinks hcover C hC
  constructor
  · intro j hj
    let oldj : Fin tagged.length := Fin.cast (gm06RetagEdges_length tagged (gm06InducedEdgeBits tagged C)) j
    have hi : j.val < tagged.length := oldj.isLt
    have hrow := gm06RetagEdges_getElem tagged (gm06InducedEdgeBits tagged C) hlen hi
    have hjbit : (gm06InducedEdgeBits tagged C)[j.val]'(by rw [hlen]; exact hi) = 1 := by
      simpa [hrow] using hj
    have hh := hnewLinks oldj hjbit
    simpa [hrow, oldj] using hh
  · intro e he
    obtain ⟨j, hj, hje⟩ := hnewCover e he
    let newj : Fin (gm06RetagEdges tagged (gm06InducedEdgeBits tagged C)).length :=
      Fin.cast (gm06RetagEdges_length tagged (gm06InducedEdgeBits tagged C)).symm j
    refine ⟨newj, ?_, ?_⟩
    · have hrow := gm06RetagEdges_getElem tagged (gm06InducedEdgeBits tagged C) hlen j.isLt
      simpa [hrow, newj] using hj
    · simpa only [newj, Fin.cast_cast, Fin.cast_eq_self] using hje

end GraphMinor.GM06
