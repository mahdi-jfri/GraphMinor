module

public import GraphMinor.GM11.Section5
import GraphMinor.GM11.Walks

/-!
# Interpreting one cleared activity bit

The loop branch of Reduction 2 and the edge deletion of Reduction 1
in VI (5.7), page 133, clear one original edge's activity bit.
Distinct active edge labels ensure that this removes exactly that edge.
The remaining active labels still give all links and cover all
edges of the drawing with that edge deleted.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Clearing one edge flag preserves the primitive edge-label
interpretation of the drawing with precisely that edge deleted. -/
theorem deleted_mask_links_and_cover
    {S : Type*} [TopologicalSpace S] [T2Space S] {n : ℕ} (G : Drawing S)
    (tagged : List ((Fin n × Fin n) × ℕ)) (vertex : Fin n → S)
    (edge : Fin tagged.length → Set S)
    (hinj : Set.InjOn edge {j | tagged[j].2 = 1})
    (hlinks : ∀ j : Fin tagged.length, tagged[j].2 = 1 →
      G.toGraph.IsLink (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2))
    (hcover : ∀ e ∈ G.E, ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ edge j = e)
    (d : Fin tagged.length) (hd : tagged[d].2 = 1) :
    (∀ j : Fin tagged.length,
      ((tagged.map Prod.snd).set d.val 0)[j.val]'(by simp only [List.length_set, List.length_map]; exact j.isLt) = 1 →
      (G.deleteEdge (edge d)).toGraph.IsLink
        (edge j) (vertex tagged[j].1.1) (vertex tagged[j].1.2)) ∧
    (∀ e ∈ (G.deleteEdge (edge d)).E,
      ∃ j : Fin tagged.length,
        ((tagged.map Prod.snd).set d.val 0)[j.val]'(by simp only [List.length_set, List.length_map]; exact j.isLt) = 1 ∧ edge j = e) := by
  let F := G.deleteEdge (edge d)
  have hFV : F.V = G.V := GraphMinor.GM11.deleteEdge_V G (edge d)
  have hFE : F.E = G.E \ {edge d} := GraphMinor.GM11.deleteEdge_E G (edge d)
  have hFG : F.IsSubdrawing G := ⟨by rw [hFV], by rw [hFE]; exact sdiff_subset⟩
  constructor
  · intro j hj
    have hjd : j ≠ d := by
      intro heq
      subst j
      have hz := List.getElem_set_self (l := tagged.map Prod.snd) (i := d.val) (a := 0)
        (by simpa only [List.length_set, List.length_map] using d.isLt)
      rw [hz] at hj
      exact Nat.zero_ne_one hj
    have hjdVal : d.val ≠ j.val := fun h => hjd (Fin.ext h.symm)
    have hactive : tagged[j].2 = 1 := by
      simpa [List.getElem_set_ne hjdVal] using hj
    have heNot : edge j ∉ ({edge d} : Set (Set S)) :=
      fun h => hjd (hinj hactive hd (mem_singleton_iff.mp h))
    have heF : edge j ∈ F.E := by rw [hFE]; exact ⟨(hlinks j hactive).edge_mem, heNot⟩
    exact (hFG.isLink_iff heF).mpr (hlinks j hactive)
  · intro e he
    change e ∈ F.E at he
    rw [hFE] at he
    obtain ⟨j, hj, hje⟩ := hcover e he.1
    have hjdVal : d.val ≠ j.val := by
      intro hh
      have hdj : d = j := Fin.ext hh
      exact he.2 (mem_singleton_iff.mpr (hje.symm.trans (congrArg edge hdj.symm)))
    refine ⟨j, ?_, hje⟩
    simpa [List.getElem_set_ne hjdVal] using hj

end GraphMinor.GM06
