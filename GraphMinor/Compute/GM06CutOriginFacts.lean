module

public import GraphMinor.Compute.GM06CutRowsProgram
public import GraphMinor.Compute.GM06CutMarkFacts
import GraphMinor.Compute.GM06FaceBuffers

/-!
# Copied origins and bounds for the complete cut encoding

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) connects
copied ends according to their induced vertex rows. Scattering those rows'
vertex indices gives the exact origin of each copied end. The no-collision
lemma for copied rotations makes every such lookup unique. The size
and word lemmas also justify reading the encoded rotation buffer in
later endpoint and component passes.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Every row produced by splitting one vertex is one of its two selected rows. -/
theorem gm06SplitVertexRows_mem_iff (position : Option GM06CutPosition) (row copied : List ℕ) :
    copied ∈ gm06SplitVertexRows position row ↔
      copied = gm06CutSelectedRow position row true ∨ copied = gm06CutSelectedRow position row false := by
  rw [gm06SplitVertexRows_eq_selected]
  simp

/-- Each copied row is at most as long as its old row and all its
darts stay in the four-slot copied edge space. -/
theorem gm06SplitVertexRows_row_bounds {m : ℕ} (position : Option GM06CutPosition)
    (row copied : List ℕ) (hc : copied ∈ gm06SplitVertexRows position row)
    (hkeys : ∀ d ∈ row, d < 2 * m) :
    copied.length ≤ row.length ∧ ∀ d ∈ copied, d < 4 * m := by
  obtain ⟨left, rfl⟩ : ∃ left, copied = gm06CutSelectedRow position row left := by
    rcases (gm06SplitVertexRows_mem_iff position row copied).mp hc with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  refine ⟨gm06CutSelectedRow_length_le _ _ _, ?_⟩
  intro q hq
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  exact gm06CutOutputDart_lt position left (hkeys d (List.mem_filter.mp hd).1)

/-- Every copied row has the bound of an actual original row. -/
theorem gm06SplitRotationRows_row_bounds {m : ℕ} (marks : GM06CutTables)
    (rows : List (List ℕ)) (copied : List ℕ) (hc : copied ∈ gm06SplitRotationRows marks rows)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * m) :
    copied.length ≤ rows.flatten.length ∧ ∀ d ∈ copied, d < 4 * m := by
  obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
  have hrow : p.1 ∈ rows := List.fst_mem_of_mem_zipIdx hp
  have hlocal := gm06SplitVertexRows_row_bounds _ p.1 copied hc
    (fun d hd => hkeys d (List.mem_flatten.mpr ⟨p.1, hrow, hd⟩))
  exact ⟨hlocal.1.trans (List.sublist_flatten_of_mem hrow).length_le, hlocal.2⟩

/-- A length-prefixed row encoding consists of words once its count,
individual row lengths and entries are words. -/
theorem gm06EncodeRows_words {w : ℕ} (rows : List (List ℕ))
    (hc : rows.length < 2 ^ w) (hl : ∀ row ∈ rows, row.length < 2 ^ w)
    (hd : ∀ d ∈ rows.flatten, d < 2 ^ w) : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  · obtain ⟨row, hr, hx⟩ := List.mem_flatMap.mp hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hl row hr
    · exact hd x (List.mem_flatten.mpr ⟨row, hr, hx⟩)

/-- The entire computed copied-row encoding contains only words,
including its doubled vertex-slot count and every row header. -/
theorem gm06SplitRotationRows_words {w m : ℕ} (marks : GM06CutTables) (rows : List (List ℕ))
    (hm : 4 * m < 2 ^ w) (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * m) :
    ∀ x ∈ gm06EncodeRows (gm06SplitRotationRows marks rows), x < 2 ^ w := by
  have hL := gm06FaceCode_length rows
  apply gm06EncodeRows_words
  · rw [gm06SplitRotationRows_length]
    omega
  · intro row hr
    have hb := (gm06SplitRotationRows_row_bounds marks rows row hr hkeys).1
    omega
  · intro d hd
    obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
    exact ((gm06SplitRotationRows_row_bounds marks rows row hr hkeys).2 d hd).trans hm

/-- The origin-scatter keys are exactly all the listed copied darts. -/
theorem gm06CutOriginPairs_keys (rows : List (List ℕ)) :
    (gm06CutOriginPairs rows).map Prod.fst = rows.flatten := by
  unfold gm06CutOriginPairs
  rw [List.map_flatMap]
  simp only [List.map_map, Function.comp_def, List.map_id']
  change ((rows.zipIdx).flatMap (fun p => p.1)) = rows.flatten
  have he : rows.zipIdx.flatMap (fun p => p.1) = (rows.zipIdx.map Prod.fst).flatten := by
    simp only [List.flatMap]
  rw [he, List.zipIdx_map_fst]

/-- Every dart in a copied vertex row contributes that vertex's origin write. -/
theorem gm06CutOriginPairs_mem (rows : List (List ℕ)) (row : List ℕ) (v d : ℕ)
    (hr : (row, v) ∈ rows.zipIdx) (hd : d ∈ row) : (d, v) ∈ gm06CutOriginPairs rows :=
  List.mem_flatMap.mpr ⟨(row, v), hr, List.mem_map.mpr ⟨d, hd, rfl⟩⟩

/-- The computed origin table gives exactly the vertex index of each
listed outgoing end, assuming only that no dart is repeated across rows. -/
theorem gm06CutOrigins_getElem? {m v d : ℕ} (rows : List (List ℕ)) (row : List ℕ)
    (hnd : rows.flatten.Nodup) (hr : (row, v) ∈ rows.zipIdx) (hd : d ∈ row) (hb : d < 4 * m) :
    (gm06CutOrigins m rows)[d]? = some v := by
  exact gm06Scatter_getElem?_of_mem _ _ (by rw [gm06CutOriginPairs_keys]; exact hnd) _
    (gm06CutOriginPairs_mem rows row v d hr hd) (by simpa using hb)

/-- No copied origin word exceeds the number of copied vertex slots. -/
theorem gm06CutOrigins_bound {m n : ℕ} (rows : List (List ℕ)) (hn : rows.length ≤ n)
    (hnpos : 0 < n) : ∀ v ∈ gm06CutOrigins m rows, v < n := by
  unfold gm06CutOrigins
  apply gm06Scatter_forall (fun v => v < n) _ _ _
    (by intro v hv; have hzero := (List.mem_replicate.mp hv).2; omega)
  intro p hp
  obtain ⟨q, hq, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨d, _, rfl⟩ := List.mem_map.mp hp
  have hq' : q.2 < rows.length := by simpa using List.snd_lt_add_of_mem_zipIdx hq
  exact hq'.trans_le hn

end GraphMinor.Compute
