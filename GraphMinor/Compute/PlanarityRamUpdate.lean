module

public import GraphMinor.Compute.PlanarityRamPrefix

/-!
# Updating keys and lowpoint pairs in search memory

Finishing an edge in Part I, Section 1 changes its key and then the lowpoint
pair of its parent's edge. Each update touches only its own columns. The
proofs use the live-prefix relation to keep the unchanged columns fixed.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- Replace the key of one oriented edge. -/
def setEdgeKey (search : Search) (i key : ℕ) : Search :=
  { search with edges := search.edges.set! i { search.edges[i]! with key := key } }

/-- Replace the two lowpoints of one oriented edge. -/
def setEdgePair (search : Search) (i : ℕ) (pair : LowPair) : Search :=
  { search with edges := search.edges.set! i { search.edges[i]! with pair := pair } }

private theorem map_setEdge_same (edges : Array EdgeRecord) (i : ℕ) (hi : i < edges.size)
    (e : EdgeRecord) (f : EdgeRecord → ℕ) (hf : f e = f edges[i]) :
    (edges.set! i e).toList.map f = edges.toList.map f := by
  rw [Array.toList_set!, List.map_set, hf]
  have hh := List.set_getElem_self (as := edges.toList.map f) (i := i) (by simpa using hi)
  simpa using hh

/-- A key write represents exactly the functional key update. -/
theorem SearchAt.write_key {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (i key : ℕ) (hi : i < search.edges.size) :
    SearchAt N M (s.writeArr Field.key.array i key) (setEdgeKey search i key) := by
  obtain ⟨hd, hp, hpe, hc, hpost, hdepth, hparent, hparentEdge,
    htail, hhead, htree, hlow, hlow2, hkey, horder⟩ := h
  have same (f : EdgeRecord → ℕ)
      (hf : f { search.edges[i]! with key := key } = f search.edges[i]) :
      ((setEdgeKey search i key).edges.toList.map f) = search.edges.toList.map f :=
    map_setEdge_same search.edges i hi _ f hf
  have hget : search.edges[i]! = search.edges[i] := getElem!_pos search.edges i hi
  refine ⟨hd, hp, hpe, ?_, hpost, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [setEdgeKey] using hc
  · exact hdepth.of_arr_eq (by simp [Field.array])
  · exact hparent.of_arr_eq (by simp [Field.array])
  · exact hparentEdge.of_arr_eq (by simp [Field.array])
  · rw [same EdgeRecord.source (by simp [hget])]
    exact htail.of_arr_eq (by simp [Field.array])
  · rw [same EdgeRecord.target (by simp [hget])]
    exact hhead.of_arr_eq (by simp [Field.array])
  · rw [same (fun e => e.tree.toNat) (by simp [hget])]
    exact htree.of_arr_eq (by simp [Field.array])
  · rw [same (fun e => e.pair.low) (by simp [hget])]
    exact hlow.of_arr_eq (by simp [Field.array])
  · rw [same (fun e => e.pair.second) (by simp [hget])]
    exact hlow2.of_arr_eq (by simp [Field.array])
  · simpa only [setEdgeKey, Array.toList_set!, List.map_set] using hkey.write_existing i key
  · exact horder.of_arr_eq (by simp [Field.array])

/-- Two lowpoint writes represent exactly the functional pair update. -/
theorem SearchAt.write_pair {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (i : ℕ) (pair : LowPair) (hi : i < search.edges.size) :
    SearchAt N M ((s.writeArr Field.low.array i pair.low).writeArr Field.low2.array i pair.second)
      (setEdgePair search i pair) := by
  obtain ⟨hd, hp, hpe, hc, hpost, hdepth, hparent, hparentEdge,
    htail, hhead, htree, hlow, hlow2, hkey, horder⟩ := h
  have same (f : EdgeRecord → ℕ)
      (hf : f { search.edges[i]! with pair := pair } = f search.edges[i]) :
      ((setEdgePair search i pair).edges.toList.map f) = search.edges.toList.map f :=
    map_setEdge_same search.edges i hi _ f hf
  have hget : search.edges[i]! = search.edges[i] := getElem!_pos search.edges i hi
  refine ⟨hd, hp, hpe, ?_, hpost, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [setEdgePair] using hc
  · exact hdepth.of_arr_eq (by simp [Field.array])
  · exact hparent.of_arr_eq (by simp [Field.array])
  · exact hparentEdge.of_arr_eq (by simp [Field.array])
  · rw [same EdgeRecord.source (by simp [hget])]
    exact htail.of_arr_eq (by simp [Field.array])
  · rw [same EdgeRecord.target (by simp [hget])]
    exact hhead.of_arr_eq (by simp [Field.array])
  · rw [same (fun e => e.tree.toNat) (by simp [hget])]
    exact htree.of_arr_eq (by simp [Field.array])
  · have hl := (hlow.write_existing i pair.low).of_arr_eq
      (s' := (s.writeArr Field.low.array i pair.low).writeArr Field.low2.array i pair.second)
      (by simp [Field.array])
    simpa only [setEdgePair, Array.toList_set!, List.map_set] using hl
  · have hl := (hlow2.of_arr_eq (s' := s.writeArr Field.low.array i pair.low)
      (by simp [Field.array])).write_existing i pair.second
    simpa only [setEdgePair, Array.toList_set!, List.map_set] using hl
  · rw [same EdgeRecord.key (by simp [hget])]
    exact hkey.of_arr_eq (by simp [Field.array])
  · exact horder.of_arr_eq (by simp [Field.array])

end GraphMinor.Compute.PlanarityRam
