module

public import GraphMinor.Compute.GM06CutAdjacencyMath

/-!
# Permanent label bounds for the computed cut graph

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) searches all
copied vertices and edges after the local interval assignments.
These lemmas derive the search-array bounds from the original finite
input. They include the empty vertex space, so no dummy origin or
nonempty-graph assumption is needed. The live copies remain distinct.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A copied live vertex projects to a live original vertex. -/
theorem gm06CutVertices_project_mem (marks : GM06CutTables) (live : List ℕ) {v : ℕ}
    (hv : v ∈ gm06CutVertices marks live) : v / 2 ∈ live := by
  obtain ⟨u, hu, hv⟩ := List.mem_flatMap.mp hv
  split_ifs at hv
  · have heq : v = gm06CutVertex u true := by simpa only [List.mem_singleton] using hv
    simpa only [heq, gm06CutVertex_project] using hu
  · rcases List.mem_cons.mp hv with heq | hv
    · simpa only [heq, gm06CutVertex_project] using hu
    · have heq : v = gm06CutVertex u false := by simpa only [List.mem_singleton] using hv
      simpa only [heq, gm06CutVertex_project] using hu

/-- Live copied labels lie in the doubled original vertex space. -/
theorem gm06CutVertices_bound {n : ℕ} (marks : GM06CutTables) (live : List ℕ)
    (hlive : ∀ v ∈ live, v < n) : ∀ v ∈ gm06CutVertices marks live, v < 2 * n := by
  intro v hv
  have h := hlive _ (gm06CutVertices_project_mem marks live hv)
  omega

/-- The local one- or two-copy list has no repeated vertex label. -/
theorem gm06CutVertexCopies_nodup (marks : GM06CutTables) (v : ℕ) :
    (gm06CutVertexCopies marks v).Nodup := by
  unfold gm06CutVertexCopies
  split_ifs <;> simp

/-- Distinct live input vertices give disjoint copy lists. -/
theorem gm06CutVertices_nodup (marks : GM06CutTables) (live : List ℕ) (hnd : live.Nodup) :
    (gm06CutVertices marks live).Nodup := by
  induction live with
  | nil => simp [gm06CutVertices]
  | cons u live ih =>
    have hu : u ∉ live := (List.nodup_cons.mp hnd).1
    have ht : (gm06CutVertices marks live).Nodup := ih (List.nodup_cons.mp hnd).2
    change ((if gm06CutPositionAt marks u = none then [gm06CutVertex u true]
      else [gm06CutVertex u true, gm06CutVertex u false]) ++ gm06CutVertices marks live).Nodup
    refine List.Nodup.append ?_ ht ?_
    · simpa only [gm06CutVertexCopies, gm06CutVertex, Bool.not_true, Bool.not_false,
        Bool.toNat_true, Bool.toNat_false, Nat.add_zero] using gm06CutVertexCopies_nodup marks u
    · apply List.disjoint_left.mpr
      intro v hv hv'
      have hproject := gm06CutVertices_project_mem marks live hv'
      have heq : v / 2 = u := by
        split_ifs at hv
        · have heq : v = gm06CutVertex u true := by simpa only [List.mem_singleton] using hv
          rw [heq, gm06CutVertex_project]
        · rcases List.mem_cons.mp hv with rfl | hv
          · exact gm06CutVertex_project _ _
          · have heq : v = gm06CutVertex u false := by simpa only [List.mem_singleton] using hv
            rw [heq, gm06CutVertex_project]
      exact hu (heq ▸ hproject)

/-- Every copied dart stays inside the allocated permanent edge space. -/
theorem gm06CutDataOfLinkage_dart_bounds {n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * (m + inner.length + outer.length)) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    (∀ d ∈ data.rotations.flatten, d < 4 * (m + inner.length + outer.length)) ∧
      (∀ d ∈ data.activeDarts, d < 4 * (m + inner.length + outer.length)) ∧
      data.activeDarts.length ≤ 4 * (m + inner.length + outer.length) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨row, hr, hd⟩ := List.mem_flatten.mp hd
    exact (gm06SplitRotationRows_row_bounds _ rows row hr hkeys).2 d hd
  · intro d hd
    exact ((gm06CutDataOfLinkage_active_iff n m origins paths inner outer rows live d).mp hd).1
  · exact (List.length_filter_le _ _).trans (by simp only [List.length_range]; exact le_rfl)

/-- Origin labels lie in the copied vertex space even when the
original graph is empty. Empty input forces an empty origin table. -/
theorem gm06CutDataOfLinkage_origin_bounds {n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ)
    (hrows : rows.length = n) (horig : origins.length = 2 * m)
    (hv : ∀ v ∈ origins, v < n) (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n) :
    ∀ v ∈ (gm06CutDataOfLinkage n m origins paths inner outer rows live).origins, v < 2 * n := by
  by_cases hn : 0 < n
  · exact gm06CutOrigins_bound _ (by rw [gm06SplitRotationRows_length, hrows]) (by omega)
  · have hn0 : n = 0 := by omega
    have ho0 : origins = [] := List.eq_nil_iff_forall_not_mem.mpr (fun v h => by have := hv v h; omega)
    have hi0 : inner = [] := List.eq_nil_iff_forall_not_mem.mpr (fun v h => by have := hci v h; omega)
    have hc0 : outer = [] := List.eq_nil_iff_forall_not_mem.mpr (fun v h => by have := hco v h; omega)
    have hm0 : m = 0 := by rw [ho0] at horig; simp only [List.length_nil] at horig; omega
    have hlen := (gm06CutDataOfLinkage_sizes n m origins paths inner outer rows live).2.1
    have he : (gm06CutDataOfLinkage n m origins paths inner outer rows live).origins = [] :=
      List.eq_nil_iff_length_eq_zero.mpr (by simpa only [hm0, hi0, hc0, List.length_nil] using hlen)
    simp only [he, List.not_mem_nil, false_implies, implies_true]

/-- Every inner cuff index has an in-range positive copied dart. -/
theorem gm06CutDataOfLinkage_inner_dart_bound {n m i : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ) (hi : i < inner.length) :
    4 * (m + i) < (gm06CutDataOfLinkage n m origins paths inner outer rows live).origins.length := by
  rw [(gm06CutDataOfLinkage_sizes n m origins paths inner outer rows live).2.1]
  omega

private theorem getD_zero_le (table : List ℕ) (bound v : ℕ)
    (h : ∀ x ∈ table, x ≤ bound) : table[v]?.getD 0 ≤ bound := by
  cases he : table[v]? with
  | none => simp only [he, Option.getD_none]; omega
  | some x => simpa only [he, Option.getD_some] using h x (List.mem_of_getElem? he)

/-- Every decoded path end is an ordinary dart. Auxiliary cuff
ends cannot become duplicate linkage-edge tags. -/
theorem gm06CutPositionAt_pathEnds_bound {n m v : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m) (p : GM06CutPosition)
    (hp : gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) v = some p) :
    ∀ d ∈ p.pathEnds, d < 2 * m := by
  let marks := gm06BuildCutTables n m origins paths inner outer
  have hi : ∀ x ∈ marks.incoming, x ≤ 2 * m :=
    gm06Scatter_forall _ _ _ (gm06CutPathEndPairs_bound origins paths.flatten true hd)
      (fun x hx => by have := (List.mem_replicate.mp hx).2; omega)
  have ho : ∀ x ∈ marks.outgoing, x ≤ 2 * m :=
    gm06Scatter_forall _ _ _ (gm06CutPathEndPairs_bound origins paths.flatten false hd)
      (fun x hx => by have := (List.mem_replicate.mp hx).2; omega)
  have hia := getD_zero_le marks.incoming (2 * m) v hi
  have hob := getD_zero_le marks.outgoing (2 * m) v ho
  change gm06CutPositionAt marks v = some p at hp
  unfold gm06CutPositionAt at hp
  dsimp only at hp
  split_ifs at hp with ha hb hb
  · cases Option.some.inj hp
    intro d hd'
    simp only [GM06CutPosition.pathEnds, List.mem_singleton] at hd'
    omega
  · cases Option.some.inj hp
    intro d hd'
    simp only [GM06CutPosition.pathEnds, List.mem_singleton] at hd'
    omega
  · cases Option.some.inj hp
    intro d hd'
    simp only [GM06CutPosition.pathEnds, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hd'
    omega

/-- A copied end uses one of the two ordinary edge slots or the
single retained slot of an auxiliary cuff edge. -/
theorem gm06CutOutputDart_edge_mem {m c d : ℕ} (position : Option GM06CutPosition) (left : Bool)
    (hd : d < 2 * (m + c))
    (hpath : ∀ p, position = some p → ∀ a ∈ p.pathEnds, a < 2 * m) :
    gm06CutOutputDart position left d / 2 ∈
      List.range (2 * m) ++ (List.range' m c).map (fun e => 2 * e) := by
  have hmod := Nat.mod_lt d (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div d 2
  by_cases hsmall : d < 2 * m
  · apply List.mem_append_left
    apply List.mem_range.mpr
    have hbound := gm06CutOutputDart_lt position left hsmall
    omega
  · have hlabel : gm06CutOutputDart position left d / 2 = 2 * (d / 2) := by
      cases position with
      | none => simp only [gm06CutOutputDart, gm06CutDart]; omega
      | some p =>
        have hp : d ∉ p.pathEnds := fun h => hsmall (hpath p rfl d h)
        simp only [gm06CutOutputDart, gm06CutRowDart, hp, ↓reduceIte, gm06CutDart]
        omega
    apply List.mem_append_right
    apply List.mem_map.mpr
    exact ⟨d / 2, List.mem_range'_1.mpr (by omega), hlabel.symm⟩

/-- Bound (8) for all copied edge labels: ordinary edges may be
duplicated, but each auxiliary cuff edge is retained only once. -/
theorem gm06CutDataOfLinkage_edge_count_le {n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (live : List ℕ)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * (m + inner.length + outer.length)) :
    (gm06CutEdgeLabels (gm06CutDataOfLinkage n m origins paths inner outer rows live)).length ≤
      2 * m + inner.length + outer.length := by
  let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
  let labels := List.range (2 * m) ++ (List.range' m (inner.length + outer.length)).map (fun e => 2 * e)
  have hsub : ∀ e ∈ gm06CutEdgeLabels data, e ∈ labels := by
    intro e he
    have hactive := ((gm06CutEdgeLabels_mem_iff data e).mp he).1
    have hrot := ((gm06CutDataOfLinkage_active_iff n m origins paths inner outer rows live (2 * e)).mp hactive).2
    obtain ⟨copied, hc, hdart⟩ := List.mem_flatten.mp hrot
    obtain ⟨pair, hpair, hcopied⟩ := List.mem_flatMap.mp hc
    obtain ⟨left, hrow⟩ : ∃ left, copied = gm06CutSelectedRow
        (gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) pair.2) pair.1 left := by
      rcases (gm06SplitVertexRows_mem_iff _ _ _).mp hcopied with h | h
      · exact ⟨true, h⟩
      · exact ⟨false, h⟩
    rw [hrow] at hdart
    obtain ⟨d, hd', heq⟩ := List.mem_map.mp hdart
    have hdrow : d ∈ rows.flatten := List.mem_flatten.mpr
      ⟨pair.1, List.fst_mem_of_mem_zipIdx hpair, (List.mem_filter.mp hd').1⟩
    have hout := gm06CutOutputDart_edge_mem
      (m := m) (d := d) (c := inner.length + outer.length)
      (gm06CutPositionAt (gm06BuildCutTables n m origins paths inner outer) pair.2) left (by have := hkeys d hdrow; omega)
      (fun p hp => gm06CutPositionAt_pathEnds_bound (n := n) (v := pair.2) origins paths inner outer hd p hp)
    change gm06CutOutputDart _ _ d = 2 * e at heq
    simpa only [heq, Nat.mul_div_cancel_left _ (by decide : 0 < 2)] using hout
  have hle := ((gm06CutEdgeLabels_nodup data).subperm hsub).length_le
  simpa only [labels, List.length_append, List.length_range, List.length_map, List.length_range',
    Nat.add_assoc] using hle

end GraphMinor.Compute
