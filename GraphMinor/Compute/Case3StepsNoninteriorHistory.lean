module

public import GraphMinor.Compute.Case3StepsScanHistory
public import GraphMinor.Compute.Case3StepsPlaceholderCode

/-!
# Capacity and coverage when adding noninterior records

The second scan retains all interior records and fills the remaining
selected members with placeholders. Each placeholder satisfies the same
capacity bound. Already stored noninterior labels precede the scan index,
so a new noninterior label is fresh and extends full-member coverage.
-/

public section

namespace GraphMinor.Compute

/-- A prescribed placeholder fits the selected member's reserved capacity. -/
theorem case3SelectedRecord_placeholder_length_le {N : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (e : Fin x.n ↪ Fin N) (i : Case3SelectedGroup x Z) :
    (case3SelectedRecord x D Z e i (case3PlaceholderCode (case3CompactMember x D Z i).numEdges)).enc.length ≤
      case3SelectedRecordCapacity x D Z i := by
  unfold case3SelectedRecord case3SelectedRecordCapacity
  rw [case3BranchRecord_placeholder_length]
  omega

/-- A noninterior candidate at the current label cannot already occur in
a history whose noninterior labels have all been processed earlier. -/
theorem case3NoninteriorHistory_fresh (x : Alg81Input) (Z P : Finset (Fin x.n)) (k : ℕ)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hlabels : ∀ p ∈ entries, ¬ Disjoint (case3SelectedMember x Z p.1).verts P →
      case3RawIndexLabel x p.1.1 < k)
    (i : Case3SelectedGroup x Z) (hnon : ¬ Disjoint (case3SelectedMember x Z i).verts P)
    (hi : case3RawIndexLabel x i.1 = k) : i ∉ entries.map Prod.fst := by
  intro hm
  obtain ⟨p, hp, heq⟩ := List.mem_map.mp hm
  have hnonp : ¬ Disjoint (case3SelectedMember x Z p.1).verts P := heq ▸ hnon
  have hlt := hlabels p hp hnonp
  rw [heq, hi] at hlt
  exact Nat.lt_irrefl _ hlt

/-- Appending the current candidate extends coverage of all interior
members and the already processed noninterior labels. -/
theorem case3NoninteriorHistory_coverage_append (x : Alg81Input) (Z P : Finset (Fin x.n)) (k : ℕ)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hcover : ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P ∨ case3RawIndexLabel x j.1 < k →
        j ∈ entries.map Prod.fst)
    (i : Case3SelectedGroup x Z) (hi : case3RawIndexLabel x i.1 = k) (code : List ℕ) :
    ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P ∨ case3RawIndexLabel x j.1 < k + 1 →
        j ∈ (entries ++ [(i, code)]).map Prod.fst := by
  intro j hj
  rw [List.map_append]
  rcases hj with hj | hj
  · exact List.mem_append_left _ (hcover j (Or.inl hj))
  · by_cases hprev : case3RawIndexLabel x j.1 < k
    · exact List.mem_append_left _ (hcover j (Or.inr hprev))
    · have heq : case3RawIndexLabel x j.1 = case3RawIndexLabel x i.1 := by omega
      have hji : j = i := Subtype.ext (case3RawIndexLabel_injective x heq)
      subst j
      exact List.mem_append_right _ (by simp)

/-- Skipping an absent or interior current label preserves the coverage
assertion for the second scan. -/
theorem case3NoninteriorHistory_coverage_skip (x : Alg81Input) (Z P : Finset (Fin x.n)) (k : ℕ)
    (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hcover : ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P ∨ case3RawIndexLabel x j.1 < k →
        j ∈ entries.map Prod.fst)
    (hskip : ∀ j : Case3SelectedGroup x Z, case3RawIndexLabel x j.1 = k →
      Disjoint (case3SelectedMember x Z j).verts P) :
    ∀ j : Case3SelectedGroup x Z,
      Disjoint (case3SelectedMember x Z j).verts P ∨ case3RawIndexLabel x j.1 < k + 1 →
        j ∈ entries.map Prod.fst := by
  intro j hj
  rcases hj with hj | hj
  · exact hcover j (Or.inl hj)
  · by_cases hprev : case3RawIndexLabel x j.1 < k
    · exact hcover j (Or.inr hprev)
    · exact hcover j (Or.inl (hskip j (by omega)))

/-- Every fresh member capacity still fits after branch and placeholder
records, provided each retained record satisfies its encoding bound. -/
theorem case3NoninteriorHistory_fresh_capacity {N : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (hG : D.toSimpleGraph = x.G) (d : Alg86DivisionOutput x)
    (hd : IsValidAlg86DivisionOutput x d)
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z))
    (e : Fin x.n ↪ Fin N) (hn : x.n ≤ N)
    (entries : List (Case3SelectedGroup x d.core.Z × List ℕ))
    (hbounds : ∀ p ∈ entries, (case3SelectedRecord x D d.core.Z e p.1 p.2).enc.length ≤
      case3SelectedRecordCapacity x D d.core.Z p.1)
    (hnodup : (entries.map Prod.fst).Nodup) (i : Case3SelectedGroup x d.core.Z)
    (hi : i ∉ entries.map Prod.fst) :
    case3SelectedRecordCapacity x D d.core.Z i ≤
      24 * (N + D.numEdges + 1) - (case3SelectedRecordsEncoding x D d.core.Z e entries).length := by
  have hsum := case3SelectedRecordsEncoding_add_fresh_capacity_le_of_bounds x D d.core.Z e entries hbounds hnodup i hi
  have htotal := case3SelectedRecordCapacity_sum_le x D hG d hd hdiv
  omega

end GraphMinor.Compute
