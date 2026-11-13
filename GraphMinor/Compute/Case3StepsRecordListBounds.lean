module

public import GraphMinor.Compute.Case3StepsRecordLists

/-!
# Bounds and parser validity of the completed member list

A record's full edge count is its routed member's count. Candidates occur
at most once, so summing their record edge lengths cannot exceed the
compass edge count. Both the returned branch code and the noninterior
placeholder satisfy the parser checks with the actual compass lists.
-/

public section

namespace GraphMinor.Compute

open GraphMinor.Transport

/-- Either permitted code form gives a valid record relative to the
computed original-label compass lists. -/
theorem case3SelectedRecord_isValid {N B : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (e : Fin x.n ↪ Fin N) (i : Case3SelectedGroup x Z) (code : List ℕ)
    (hc : IsValidBranchDecompCode B (case3CompactMember x D Z i) code ∨
      code = case3PlaceholderCode (case3CompactMember x D Z i).numEdges) :
    isValidMemberRecord N D.numEdges (List.ofFn (fun u : Fin x.n => (e u).1))
      (D.multiEdgeTriples.map (origEdgeEmb e e.injective))
      (case3SelectedRecord x D Z e i code) = true := by
  have hn0 : x.n ≤ N := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective e e.injective
  have hcard : (case3SelectedMember x Z i).verts.card ≤ x.n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (case3SelectedMember x Z i).verts
  have hn : (case3SelectedMember x Z i).verts.card ≤ N := hcard.trans hn0
  have hm : (case3CompactMember x D Z i).numEdges ≤ D.numEdges := by
    rw [case3CompactMember_numEdges x D hG Z hdiv i]
    exact MultiDigraph.numEdges_mono (case3RoutedMember_le x D Z _)
  have hlists := case3SelectedRecord_lists_subset x D Z e i code
  rcases hc with hc | rfl
  · exact case3BranchRecord_isValidMemberRecord _ _ _ code _ _ hn hm hlists.1 hlists.2 hc
  · exact case3BranchRecord_placeholder_isValidMemberRecord _ _ _ _ _ hn hm hlists.1 hlists.2

private theorem list_sum_le {I : Type*} [Fintype I] (l : List I) (hn : l.Nodup)
    (f : I → ℕ) : (l.map f).sum ≤ ∑ i : I, f i := by
  classical
  have heq : (l.map f).sum = ∑ i ∈ l.toFinset, f i := by
    induction l with
    | nil => simp only [List.map_nil, List.sum_nil, List.toFinset_nil, Finset.sum_empty]
    | cons a l ih =>
      have ha := List.nodup_cons.mp hn
      have ha' : a ∉ l.toFinset := by simpa only [List.mem_toFinset] using ha.1
      simp only [List.map_cons, List.sum_cons, List.toFinset_cons,
        Finset.sum_insert ha', ih ha.2]
  rw [heq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intro i _ _; exact Nat.zero_le _)

/-- The complete record list charges every directed compass copy at most once. -/
theorem case3SelectedRecordList_edge_sum_le {N : ℕ} (x : Alg81Input)
    (D : MultiDigraph x.n) (hG : D.toSimpleGraph = x.G) (Z : Finset (Fin x.n))
    (hdiv : GM13.IsSocietyDivision x.toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers x Z))
    (e : Fin x.n ↪ Fin N) (entries : List (Case3SelectedGroup x Z × List ℕ))
    (hn : (entries.map Prod.fst).Nodup) :
    ((case3SelectedRecordList x D Z e entries).map (fun r => r.eList.length)).sum ≤ D.numEdges := by
  have heq : ((case3SelectedRecordList x D Z e entries).map (fun r => r.eList.length)).sum =
      ((entries.map Prod.fst).map (fun i =>
        (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges)).sum := by
    induction entries with
    | nil => rfl
    | cons p entries ih =>
      simp only [case3SelectedRecordList, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih (List.nodup_cons.mp hn).2]
      congr 1
      simp only [case3SelectedRecord, case3BranchRecord, List.length_map,
        MultiDigraph.length_multiEdgeTriples, case3CompactMember_numEdges x D hG Z hdiv]
  rw [heq]
  exact (list_sum_le _ hn _).trans (case3SelectedMembers_sum_numEdges_le x D Z)

end GraphMinor.Compute
