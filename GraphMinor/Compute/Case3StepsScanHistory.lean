module

public import GraphMinor.Compute.Case3StepsScanCostBounds

/-!
# Advancing the retained scan history

Every retained entry comes from an earlier candidate label. The next
selected label is therefore fresh. Appending its code preserves uniqueness
and covers exactly one more interior candidate. The capacity and count
bounds apply before invoking the member program.
-/

public section

namespace GraphMinor.Compute

/-- The stored encoding appends exactly the next serialized member record. -/
theorem case3SelectedRecordsEncoding_append_singleton {N : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N)
    (entries : List (Case3SelectedGroup x Z × List ℕ)) (i : Case3SelectedGroup x Z) (code : List ℕ) :
    case3SelectedRecordsEncoding x D Z e (entries ++ [(i, code)]) =
      case3SelectedRecordsEncoding x D Z e entries ++ (case3SelectedRecord x D Z e i code).enc := by
  simp only [case3SelectedRecordsEncoding, case3SelectedRecordList, List.map_append,
    List.map_cons, List.map_nil, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- A label equal to the next index cannot already occur in the retained history. -/
theorem case3ScanHistory_fresh (x : Alg81Input) (Z : Finset (Fin x.n)) (k : ℕ)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hlabels : ∀ p ∈ entries, case3RawIndexLabel x p.1.1 < k)
    (i : Case3SelectedGroup x Z) (hi : case3RawIndexLabel x i.1 = k) :
    i ∉ entries.map Prod.fst := by
  intro hm
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
  have hlt := hlabels p hp
  rw [heq, hi] at hlt
  exact Nat.lt_irrefl _ hlt

/-- Appending a fresh selected candidate preserves uniqueness. -/
theorem case3ScanHistory_nodup_append {I : Type*} (entries : List (I × List ℕ))
    (hn : (entries.map Prod.fst).Nodup) (i : I) (code : List ℕ)
    (hi : i ∉ entries.map Prod.fst) : ((entries ++ [(i, code)]).map Prod.fst).Nodup := by
  rw [List.map_append]
  apply List.nodup_append.mpr
  refine ⟨hn, by simp, ?_⟩
  intro j hj q hq heq
  have hqi : q = i := by simpa only [List.map_cons, List.map_nil, List.mem_cons,
    List.not_mem_nil, or_false] using hq
  exact hi ((heq.trans hqi) ▸ hj)

/-- The next retained record count is bounded by the whole candidate range. -/
theorem case3ScanHistory_count_succ_le (x : Alg81Input) (Z : Finset (Fin x.n))
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hn : (entries.map Prod.fst).Nodup) (i : Case3SelectedGroup x Z)
    (hi : i ∉ entries.map Prod.fst) : entries.length + 1 ≤ x.n + (case3InputEdges x).length := by
  have hcard := (List.nodup_cons.mpr ⟨hi, hn⟩).length_le_card
  simp only [List.length_cons, List.length_map] at hcard
  exact hcard.trans (case3SelectedGroups_card_le x Z)

/-- Adding the current candidate extends coverage to the next index. -/
theorem case3ScanHistory_coverage_append (x : Alg81Input) (Z P : Finset (Fin x.n)) (k : ℕ)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hcover : ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P → case3RawIndexLabel x j.1 < k →
        j ∈ entries.map Prod.fst)
    (i : Case3SelectedGroup x Z) (hi : case3RawIndexLabel x i.1 = k) (code : List ℕ) :
    ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P → case3RawIndexLabel x j.1 < k + 1 →
        j ∈ (entries ++ [(i, code)]).map Prod.fst := by
  intro j hj hjk
  rw [List.map_append]
  by_cases hprev : case3RawIndexLabel x j.1 < k
  · exact List.mem_append_left _ (hcover j hj hprev)
  · have heq : case3RawIndexLabel x j.1 = case3RawIndexLabel x i.1 := by omega
    have hji : j = i := Subtype.ext (case3RawIndexLabel_injective x heq)
    subst j
    exact List.mem_append_right _ (by simp)

/-- Skipping a label containing no interior selected member extends the
coverage assertion without adding a record. -/
theorem case3ScanHistory_coverage_skip (x : Alg81Input) (Z P : Finset (Fin x.n)) (k : ℕ)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hcover : ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P → case3RawIndexLabel x j.1 < k →
        j ∈ entries.map Prod.fst)
    (hskip : ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P → case3RawIndexLabel x j.1 ≠ k) :
    ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P → case3RawIndexLabel x j.1 < k + 1 →
        j ∈ entries.map Prod.fst := by
  intro j hj hjk
  exact hcover j hj (by have hne := hskip j hj; omega)

/-- The next candidate's reserved record capacity fits the remaining
buffer allocated from the ambient vertex and edge counts. -/
theorem case3ScanHistory_fresh_capacity {N B : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (e : Fin x.n ↪ Fin N) (hn : x.n ≤ N)
    (entries : List (Case3SelectedGroup x d.core.Z × List ℕ))
    (hcodes : ∀ p ∈ entries, IsValidBranchDecompCode B (case3CompactMember x D d.core.Z p.1) p.2)
    (hnodup : (entries.map Prod.fst).Nodup) (i : Case3SelectedGroup x d.core.Z)
    (hi : i ∉ entries.map Prod.fst) :
    case3SelectedRecordCapacity x D d.core.Z i ≤
      24 * (N + D.numEdges + 1) - (case3SelectedRecordsEncoding x D d.core.Z e entries).length := by
  have hsum := case3SelectedRecordsEncoding_add_fresh_capacity_le x D d.core.Z e entries hcodes hnodup i hi
  have htotal := case3SelectedRecordCapacity_sum_le x D hG d hd hdiv
  omega

end GraphMinor.Compute
