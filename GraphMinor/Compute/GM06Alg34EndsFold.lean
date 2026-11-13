module

public import GraphMinor.Compute.GM06Alg34PairWrites
public import GraphMinor.Compute.GM06Alg34InducedData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# The endpoint emission fold equals the induced endpoint section

Deleted edges contribute no writes. Filtering them out leaves the
ordered surviving edge list. Its list indices are precisely the new
edge labels, so the consecutive-pair filling lemma identifies the
emitter's result with the endpoint section of the induced payload.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The new endpoint pairs with finite labels read as natural words. -/
def gm06RelabelledPairs (x : GM06DrawingData) (vs : List (Fin x.n)) : List (ℕ × ℕ) :=
  (x.activeEnds vs).map (fun p => (p.1.val, p.2.val))

/-- There is one new endpoint pair for each surviving edge. -/
theorem gm06RelabelledPairs_length (x : GM06DrawingData) (vs : List (Fin x.n)) :
    (gm06RelabelledPairs x vs).length = (x.activeEdges vs).length := by
  simp only [gm06RelabelledPairs, List.length_map, GM06DrawingData.activeEnds_length]

private theorem alg34_endpoint_write_unguarded (x : GM06DrawingData) (vs : List (Fin x.n))
    (e : Fin x.ends.length) (dst : List ℕ) :
    gm06RelabelEndsWrite x vs e dst =
      if x.activeCell vs (.inr (.inl e)) then
        gm06PairWrite dst (2 * (x.activeEdges vs).idxOf e)
          ((gm06RelabelledPairs x vs).getD ((x.activeEdges vs).idxOf e) (0, 0))
      else dst := by
  by_cases he : x.activeCell vs (.inr (.inl e)) = true
  · have hemem : e ∈ x.activeEdges vs := by
      simp only [GM06DrawingData.activeEdges, List.mem_filter, List.mem_finRange, true_and]
      exact he
    have hi : (x.activeEdges vs).idxOf e < (gm06RelabelledPairs x vs).length := by
      rw [gm06RelabelledPairs_length]
      exact List.idxOf_lt_length_iff.mpr hemem
    simp only [gm06RelabelEndsWrite, dite_eq_left he, he, ↓reduceIte,
      gm06PairWrite, gm06ListIndex]
    rw [List.getD_eq_getElem _ _ hi]
    simp only [gm06RelabelledPairs, List.getElem_map]
  · simp [gm06RelabelEndsWrite, he]

/-- Emitting all old edges fills precisely the endpoint section of the
computed induced payload, independently of old output-array contents. -/
theorem gm06RelabelEndsWrite_fold_all (x : GM06DrawingData) (vs : List (Fin x.n))
    (dst : List ℕ) (hlen : dst.length = 2 * (x.activeEdges vs).length) :
    (List.finRange x.ends.length).foldl (fun dst e => gm06RelabelEndsWrite x vs e dst) dst =
      (x.inducedData vs).endpointWords := by
  let F := fun dst (e : Fin x.ends.length) => gm06PairWrite dst (2 * (x.activeEdges vs).idxOf e)
    ((gm06RelabelledPairs x vs).getD ((x.activeEdges vs).idxOf e) (0, 0))
  have hfilter : (List.finRange x.ends.length).foldl
      (fun dst e => gm06RelabelEndsWrite x vs e dst) dst = (x.activeEdges vs).foldl F dst := by
    change _ = ((List.finRange x.ends.length).filter
      (fun e => x.activeCell vs (.inr (.inl e)))).foldl F dst
    rw [List.foldl_filter]
    congr 1
    funext dst e
    exact alg34_endpoint_write_unguarded x vs e dst
  rw [hfilter]
  have hmap := congrArg (fun L => L.foldl F dst) (List.map_get_finRange (x.activeEdges vs))
  rw [List.foldl_map] at hmap
  rw [← hmap]
  have hidx : ∀ i : Fin (x.activeEdges vs).length,
      (x.activeEdges vs).idxOf ((x.activeEdges vs).get i) = i.val := by
    intro i
    exact congrArg Fin.val (gm06ListIndex_get_index _ (x.activeEdges_nodup vs) i)
  simp only [F, hidx]
  let f := fun i : Fin (x.activeEdges vs).length => (gm06RelabelledPairs x vs).getD i.val (0, 0)
  have hh := gm06PairWrite_fold f [] dst (by omega)
  simp only [List.length_nil, Nat.zero_add, List.nil_append] at hh
  rw [List.drop_eq_nil_of_le hlen.le, List.append_nil] at hh
  rw [hh]
  have hf : List.ofFn f = gm06RelabelledPairs x vs := by
    apply List.ext_getElem (by simp [gm06RelabelledPairs_length])
    intro i hi hi'
    simp only [List.getElem_ofFn, f, List.getD_eq_getElem _ _ hi']
  rw [hf]
  simp only [gm06RelabelledPairs, List.flatMap_map]
  rfl

end GraphMinor.Compute
