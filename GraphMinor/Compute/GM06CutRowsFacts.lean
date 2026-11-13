module

public import GraphMinor.Compute.GM06CutTables

/-!
# Distinct copied dart labels and induced cut rows

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) keeps each
nonpath end once and both copies of each path end. Projection of
a copied end recovers its original end, so ends from distinct old
rows cannot collide. Within one split row, a nonpath end has one
assigned side and a path end has two distinct side tags. These
facts prove that all computed cut rotations together have no
repeated dart. The two induced subsequences also give the stated
bound of twice the old number of directed ends.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Every dart retained in a copied rotation projects to that old row. -/
theorem gm06CutRotation_project_mem (p : GM06CutPosition) (row : List ℕ)
    (left : Bool) {q : ℕ} (hq : q ∈ gm06CutRotation p row left) :
    gm06UncutDart q ∈ row := by
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
  rw [gm06CutRowDart_project]
  exact (List.mem_filter.mp hd).1

/-- Left and right rows never share a copied dart, even when an
old loop has its two ends assigned to different vertex copies. -/
theorem gm06CutRotation_disjoint (p : GM06CutPosition) (row : List ℕ) :
    List.Disjoint (gm06CutRotation p row true) (gm06CutRotation p row false) := by
  apply List.disjoint_left.mpr
  intro q hl hr
  obtain ⟨a, ha, hqa⟩ := List.mem_map.mp hl
  obtain ⟨b, hb, hqb⟩ := List.mem_map.mp hr
  have hab : a = b := by
    have he := congrArg gm06UncutDart (hqa.trans hqb.symm)
    simpa only [gm06CutRowDart_project] using he
  subst b
  by_cases hp : a ∈ p.pathEnds
  · have he : gm06CutDart a 0 = gm06CutDart a 1 := by
      simpa only [gm06CutRowDart, hp, ↓reduceIte, Bool.not_true,
        Bool.not_false, Bool.toNat_false, Bool.toNat_true] using hqa.trans hqb.symm
    exact gm06CutDart_left_ne_right a he
  · have hs₁ : gm06CutDartLeft p row a = true := by simpa [hp] using (List.mem_filter.mp ha).2
    have hs₂ : gm06CutDartLeft p row a = false := by simpa [hp] using (List.mem_filter.mp hb).2
    exact Bool.noConfusion (hs₁.symm.trans hs₂)

/-- The two copied rows of one old vertex have no repeated dart. -/
theorem gm06SplitVertexRows_nodup (position : Option GM06CutPosition) (row : List ℕ)
    (hn : row.Nodup) : (gm06SplitVertexRows position row).flatten.Nodup := by
  cases position with
  | none =>
    simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil]
    apply hn.map
    intro a b he
    have hp := congrArg gm06UncutDart he
    simpa only [gm06UncutDart_cut _ 0 (by decide)] using hp
  | some p =>
    simpa only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.nodup_append] using
      ⟨gm06CutRotation_nodup p row true hn, gm06CutRotation_nodup p row false hn,
        List.disjoint_iff_ne.mp (gm06CutRotation_disjoint p row)⟩

/-- Every outgoing dart of either vertex slot comes from that old row. -/
theorem gm06SplitVertexRows_project_mem (position : Option GM06CutPosition) (row : List ℕ)
    {q : ℕ} (hq : q ∈ (gm06SplitVertexRows position row).flatten) :
    gm06UncutDart q ∈ row := by
  cases position with
  | none =>
    simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil] at hq
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hq
    simpa only [gm06UncutDart_cut _ 0 (by decide)] using hd
  | some p =>
    simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_append] at hq
    rcases hq with hq | hq
    · exact gm06CutRotation_project_mem p row true hq
    · exact gm06CutRotation_project_mem p row false hq

/-- Every old outgoing dart survives in at least one of the vertex slots. -/
theorem gm06SplitVertexRows_covers (position : Option GM06CutPosition) (row : List ℕ)
    {d : ℕ} (hd : d ∈ row) :
    ∃ q ∈ (gm06SplitVertexRows position row).flatten, gm06UncutDart q = d := by
  cases position with
  | none =>
    exact ⟨gm06CutDart d 0, by
      simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil]
      exact List.mem_map.mpr ⟨d, hd, rfl⟩, gm06UncutDart_cut _ _ (by decide)⟩
  | some p =>
    by_cases hp : d ∈ p.pathEnds
    · exact ⟨gm06CutDart d 0, by
        simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append]
        exact Or.inl (gm06CutRotation_path_mem p row d hd hp).1,
        gm06UncutDart_cut _ _ (by decide)⟩
    · let side := gm06CutDartLeft p row d
      have hm : gm06CutDart d 0 ∈ gm06CutRotation p row side :=
        (gm06CutRotation_nonpath_mem p row d hp side).mpr ⟨hd, rfl⟩
      refine ⟨gm06CutDart d 0, ?_, gm06UncutDart_cut _ _ (by decide)⟩
      simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append]
      cases hs : side
      · exact Or.inr (hs ▸ hm)
      · exact Or.inl (hs ▸ hm)

/-- Each copied row is a relabelled subsequence of its old row. -/
theorem gm06CutRotation_length_le (p : GM06CutPosition) (row : List ℕ) (left : Bool) :
    (gm06CutRotation p row left).length ≤ row.length := by
  simp only [gm06CutRotation, List.length_map]
  exact List.length_filter_le _ _

/-- Splitting one vertex introduces at most two copies of each end. -/
theorem gm06SplitVertexRows_length_le (position : Option GM06CutPosition) (row : List ℕ) :
    (gm06SplitVertexRows position row).flatten.length ≤ 2 * row.length := by
  cases position with
  | none => simp [gm06SplitVertexRows]; omega
  | some p =>
    have hl := gm06CutRotation_length_le p row true
    have hr := gm06CutRotation_length_le p row false
    simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
    omega

private theorem flatten_flatMap {α β : Type*} (xs : List α) (f : α → List (List β)) :
    (xs.flatMap f).flatten = xs.flatMap (fun x => (f x).flatten) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.flatMap_cons, List.flatten_append, ih]

private theorem splitIndexed_nodup (marks : GM06CutTables) (rows : List (List ℕ × ℕ))
    (hn : (rows.map Prod.fst).flatten.Nodup) :
    (rows.flatMap (fun p => (gm06SplitVertexRows (gm06CutPositionAt marks p.2) p.1).flatten)).Nodup := by
  induction rows with
  | nil => exact .nil
  | cons p ps ih =>
    simp only [List.map_cons, List.flatten_cons, List.nodup_append] at hn
    rw [List.flatMap_cons, List.nodup_append]
    refine ⟨gm06SplitVertexRows_nodup _ _ hn.1, ih hn.2.1, ?_⟩
    intro q hq r hqs heq
    subst r
    have hq' := gm06SplitVertexRows_project_mem _ _ hq
    obtain ⟨r, hr, hqr⟩ := List.mem_flatMap.mp hqs
    have hqr' := gm06SplitVertexRows_project_mem _ _ hqr
    exact hn.2.2 _ hq' _ (List.mem_flatten.mpr
      ⟨r.1, List.mem_map.mpr ⟨r, hr, rfl⟩, hqr'⟩) rfl

/-- All copied rotation rows together contain each copied dart at most once. -/
theorem gm06SplitRotationRows_nodup (marks : GM06CutTables) (rows : List (List ℕ))
    (hn : rows.flatten.Nodup) : (gm06SplitRotationRows marks rows).flatten.Nodup := by
  have h := splitIndexed_nodup marks rows.zipIdx (by simpa using hn)
  simpa only [gm06SplitRotationRows, flatten_flatMap] using h

/-- The global copied directed-end count is at most twice the old count. -/
theorem gm06SplitRotationRows_length_le (marks : GM06CutTables) (rows : List (List ℕ)) :
    (gm06SplitRotationRows marks rows).flatten.length ≤ 2 * rows.flatten.length := by
  simp only [gm06SplitRotationRows, flatten_flatMap, List.length_flatMap]
  calc
    _ ≤ (rows.zipIdx.map (fun p => 2 * p.1.length)).sum :=
      List.sum_le_sum (fun p _ => gm06SplitVertexRows_length_le _ _)
    _ = 2 * rows.flatten.length := by
      have hm : rows.zipIdx.map (fun p => 2 * p.1.length) =
          rows.map (fun r => 2 * r.length) := by
        calc
          _ = (rows.zipIdx.map Prod.fst).map (fun r : List ℕ => 2 * r.length) := by
            simp only [List.map_map, Function.comp_def]
          _ = _ := by rw [List.zipIdx_map_fst]
      rw [hm]
      clear hm
      simp only [List.length_flatten]
      induction rows with
      | nil => rfl
      | cons r rs ih => simpa only [List.map_cons, List.sum_cons, Nat.mul_add] using
          (congrArg (fun x => 2 * r.length + x) ih)

end GraphMinor.Compute
