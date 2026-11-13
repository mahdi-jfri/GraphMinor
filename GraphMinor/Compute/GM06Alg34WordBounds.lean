module

public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Bounds for the values in the supplied encoding

A label is smaller than its vertex or edge count. Every list length
and section count is bounded by the space occupied by its section.
These facts bound every encoded value by the finite input size and
justify copying a complete payload with logarithmic RAM words.
-/

public section
namespace GraphMinor.Compute

private theorem region_flatMap (rs : List (List ℕ × List ℕ)) :
    gm06RegionWords rs = rs.flatMap (fun r =>
      GM06DrawingData.listWords r.1 ++ GM06DrawingData.listWords r.2) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [gm06RegionWords, List.flatMap_cons, ih]

private theorem chunk_length_le {α : Type*} (L : List α) (f : α → List ℕ)
    (a : α) (ha : a ∈ L) : (f a).length ≤ (L.flatMap f).length := by
  induction L with
  | nil => simp at ha
  | cons b L ih =>
    simp only [List.mem_cons] at ha
    simp only [List.flatMap_cons, List.length_append]
    rcases ha with rfl | ha
    · omega
    · exact (ih ha).trans (Nat.le_add_left _ _)

private theorem listWords_bound (L : List ℕ) (B : ℕ)
    (hlen : L.length ≤ B) (hval : ∀ v ∈ L, v ≤ B) :
    ∀ v ∈ GM06DrawingData.listWords L, v ≤ B := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact hlen
  · exact hval v hv

private theorem lists_count_le (L : List (List ℕ)) :
    L.length ≤ (L.flatMap GM06DrawingData.listWords).length := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      GM06DrawingData.listWords]
    omega

private theorem listsWords_bound (L : List (List ℕ)) (B : ℕ)
    (hlen : (GM06DrawingData.listsWords L).length ≤ B)
    (hval : ∀ A ∈ L, ∀ v ∈ A, v ≤ B) :
    ∀ v ∈ GM06DrawingData.listsWords L, v ≤ B := by
  intro v hv
  rcases List.mem_cons.mp hv with rfl | hv
  · have hc := lists_count_le L
    simp only [GM06DrawingData.listsWords, List.length_cons] at hlen
    omega
  · obtain ⟨A, hA, hv⟩ := List.mem_flatMap.mp hv
    have hA' := chunk_length_le L GM06DrawingData.listWords A hA
    simp only [GM06DrawingData.listsWords, List.length_cons] at hlen
    simp only [GM06DrawingData.listWords, List.length_cons] at hA'
    exact listWords_bound A B (by omega) (hval A hA) v hv

/-- Every supplied word is bounded by the vertex count plus array length. -/
theorem gm06Words_le_size (x : GM06DrawingData) : ∀ v ∈ x.words, v ≤ x.size := by
  have hlen := x.words_length
  have hsize := x.words_length_le_size
  have hn := x.counts_le_size.1
  have hm := x.counts_le_size.2.1
  have hr := x.counts_le_size.2.2
  have hregions : x.regions.flatMap (fun r =>
      GM06DrawingData.listWords (r.vertices.map Fin.val) ++
        GM06DrawingData.listWords (r.edges.map Fin.val)) = x.regionWords := by
    simp only [GM06DrawingData.regionWords, region_flatMap, GM06DrawingData.raw,
      List.flatMap_map]
  intro v hv
  rw [x.words_layout] at hv
  simp only [List.mem_append] at hv
  rcases hv with (((hv | hv) | hv) | hv) | hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl
    · exact hn
    · exact hm
    · exact hr
  · obtain ⟨e, _, he⟩ := List.mem_flatMap.mp hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact e.1.isLt.le.trans hn
    · exact e.2.isLt.le.trans hn
  · rw [← hregions] at hv
    obtain ⟨r, hR, hv⟩ := List.mem_flatMap.mp hv
    have hrecord := chunk_length_le x.regions (fun r =>
      GM06DrawingData.listWords (r.vertices.map Fin.val) ++
        GM06DrawingData.listWords (r.edges.map Fin.val)) r hR
    rw [hregions] at hrecord
    simp only [List.length_append, GM06DrawingData.listWords, List.length_cons,
      List.length_map] at hrecord
    rcases List.mem_append.mp hv with hv | hv
    · exact listWords_bound _ _ (by simp only [List.length_map]; omega)
        (by intro a ha; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha; exact i.isLt.le.trans hn) v hv
    · exact listWords_bound _ _ (by simp only [List.length_map]; omega)
        (by intro a ha; obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha; exact i.isLt.le.trans hm) v hv
  · exact listsWords_bound _ _ (by change x.cuffWords.length ≤ x.size; omega)
      (by
        intro A hA a ha
        obtain ⟨L, _, rfl⟩ := List.mem_map.mp hA
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        exact i.isLt.le.trans hn) v hv
  · exact listsWords_bound _ _ (by change x.divisionWords.length ≤ x.size; omega)
      (by
        intro A hA a ha
        obtain ⟨L, _, rfl⟩ := List.mem_map.mp hA
        obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
        exact i.isLt.le.trans hn) v hv

end GraphMinor.Compute
