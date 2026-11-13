module

public import GraphMinor.Compute.GM06Alg34EdgeRanks
public import GraphMinor.Compute.GM06Alg34RankLabels

/-!
# Edge ranks agree with the induced payload

The rank of a surviving old edge counts the retained labels before it.
This equals its position in the filtered old edge list, which is the
edge numbering used in the finite induced drawing payload.
-/

public section
namespace GraphMinor.Compute.GM06DrawingData

/-- Each surviving edge's RAM prefix-sum entry is exactly its new label
in the induced payload. -/
theorem edgeRanks_get (x : GM06DrawingData) (vs : List (Fin x.n))
    (e : Fin x.ends.length) (he : x.activeCell vs (.inr (.inl e)) = true) :
    (gm06EdgeRanks x vs)[e.val]'(by simp [gm06EdgeRanks]) =
      (gm06ListIndex (x.activeEdges vs) e
        (by simp only [activeEdges, List.mem_filter, List.mem_finRange, true_and]; exact he)).val := by
  simp only [gm06EdgeRanks, List.getElem_ofFn, gm06ListIndex]
  rw [gm06EdgeMask, List.ofFn_eq_map, ← List.map_take]
  have hs := List.sum_map_ite (fun e => x.activeCell vs (.inr (.inl e)) = true)
    (fun _ => (1 : ℕ)) (fun _ => (0 : ℕ)) ((List.finRange x.ends.length).take e.val)
  simp at hs
  rw [List.map_take, hs]
  have hh := gm06_idxOf_filter_eq_length_take (fun e => x.activeCell vs (.inr (.inl e)))
    (List.finRange x.ends.length) e (List.mem_finRange e) he
  simpa [activeEdges] using hh.symm

end GraphMinor.Compute.GM06DrawingData
