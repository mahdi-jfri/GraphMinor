module

public import GraphMinor.Compute.PlanarityRamPrefix

/-!
# Writing discovered-vertex data

The DFS marks a newly discovered vertex with its depth, parent vertex, and
incoming edge. Each tagged optional value occupies one existing array
slot. These lemmas relate the three writes to functional array updates.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- A tagged depth write represents the corresponding functional update. -/
theorem SearchAt.write_depth {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (i : ℕ) (value : Option ℕ) :
    SearchAt N M (s.writeArr Field.depth.array i (optionWord value))
      { search with depth := search.depth.set! i value } := by
  obtain ⟨hd, hp, hpe, hc, hpost, hdepth, hparent, hparentEdge,
    htail, hhead, htree, hlow, hlow2, hkey, horder⟩ := h
  refine ⟨?_, ?_, ?_, hc, hpost, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hd
  · simpa using hp
  · simpa using hpe
  · simpa only [Array.toList_set!, List.map_set] using hdepth.write_existing i (optionWord value)
  · exact hparent.of_arr_eq (by simp [Field.array])
  · exact hparentEdge.of_arr_eq (by simp [Field.array])
  · exact htail.of_arr_eq (by simp [Field.array])
  · exact hhead.of_arr_eq (by simp [Field.array])
  · exact htree.of_arr_eq (by simp [Field.array])
  · exact hlow.of_arr_eq (by simp [Field.array])
  · exact hlow2.of_arr_eq (by simp [Field.array])
  · exact hkey.of_arr_eq (by simp [Field.array])
  · exact horder.of_arr_eq (by simp [Field.array])

/-- A tagged parent write represents the corresponding functional update. -/
theorem SearchAt.write_parent {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (i : ℕ) (value : Option ℕ) :
    SearchAt N M (s.writeArr Field.parent.array i (optionWord value))
      { search with parent := search.parent.set! i value } := by
  obtain ⟨hd, hp, hpe, hc, hpost, hdepth, hparent, hparentEdge,
    htail, hhead, htree, hlow, hlow2, hkey, horder⟩ := h
  refine ⟨?_, ?_, ?_, hc, hpost, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hd
  · simpa using hp
  · simpa using hpe
  · exact hdepth.of_arr_eq (by simp [Field.array])
  · simpa only [Array.toList_set!, List.map_set] using hparent.write_existing i (optionWord value)
  · exact hparentEdge.of_arr_eq (by simp [Field.array])
  · exact htail.of_arr_eq (by simp [Field.array])
  · exact hhead.of_arr_eq (by simp [Field.array])
  · exact htree.of_arr_eq (by simp [Field.array])
  · exact hlow.of_arr_eq (by simp [Field.array])
  · exact hlow2.of_arr_eq (by simp [Field.array])
  · exact hkey.of_arr_eq (by simp [Field.array])
  · exact horder.of_arr_eq (by simp [Field.array])

/-- A tagged parentEdge write represents the corresponding functional update. -/
theorem SearchAt.write_parentEdge {N M : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (i : ℕ) (value : Option ℕ) :
    SearchAt N M (s.writeArr Field.parentEdge.array i (optionWord value))
      { search with parentEdge := search.parentEdge.set! i value } := by
  obtain ⟨hd, hp, hpe, hc, hpost, hdepth, hparent, hparentEdge,
    htail, hhead, htree, hlow, hlow2, hkey, horder⟩ := h
  refine ⟨?_, ?_, ?_, hc, hpost, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hd
  · simpa using hp
  · simpa using hpe
  · exact hdepth.of_arr_eq (by simp [Field.array])
  · exact hparent.of_arr_eq (by simp [Field.array])
  · simpa only [Array.toList_set!, List.map_set] using hparentEdge.write_existing i (optionWord value)
  · exact htail.of_arr_eq (by simp [Field.array])
  · exact hhead.of_arr_eq (by simp [Field.array])
  · exact htree.of_arr_eq (by simp [Field.array])
  · exact hlow.of_arr_eq (by simp [Field.array])
  · exact hlow2.of_arr_eq (by simp [Field.array])
  · exact hkey.of_arr_eq (by simp [Field.array])
  · exact horder.of_arr_eq (by simp [Field.array])

end GraphMinor.Compute.PlanarityRam
