module

public import GraphMinor.Compute.CrossingOpsApexLists

/-!
# Storage bounds for the numerical apex graph

The apex contributes one edge for each cycle vertex. Its packed list length is twice
the old edge count plus twice the cycle length. The active marks are the old marks
followed by one final mark for the apex.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Adding the apex appends one active mark to the old active array. -/
theorem apex_activeList {N : ℕ} (S : Finset (Fin N)) :
    List.ofFn (fun u : Fin (N + 1) => if u ∈ apexFinVerts S then 1 else 0) =
      List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) ++ [1] := by
  rw [List.ofFn_succ']
  simp only [mem_apexFinVerts_last, ite_true, mem_apexFinVerts_castSucc, List.concat_eq_append]

/-- The packed apex lists have exactly two entries per old or new edge. -/
theorem length_flatUpTo_apexList {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) (D : List (Fin N)) (hD : D.Nodup) :
    (flatUpTo (apexList lists D) (N + 1)).length = 2 * G.edgeSet.ncard + 2 * D.length := by
  classical
  have hsum : (∑ u : Fin N, (if u ∈ D then 1 else 0)) = D.length := by
    have hh : (∑ u : Fin N, (if u ∈ D.toFinset then 1 else 0)) = D.toFinset.card := by
      simp
      congr 1
      ext u
      simp
    simpa only [List.mem_toFinset, List.toFinset_card_of_nodup hD] using hh
  have hsumOld : (∑ u : Fin N, (lists u).length) = 2 * G.edgeSet.ncard := by
    have hh := length_flatUpTo_eq (H := G) (L := listOf lists)
      (fun u => by simpa [listOf_fin] using h u)
    rw [length_flatUpTo, ← Fin.sum_univ_eq_sum_range] at hh
    simpa only [listOf_fin] using hh
  have hlen : ∀ u : Fin N, (apexList lists D u.val).length =
      (lists u).length + (if u ∈ D then 1 else 0) := by
    intro u
    simp only [apexList, u.isLt, dite_true, Fin.eta, List.length_append]
    split <;> simp
  rw [flatUpTo_succ, List.length_append, length_flatUpTo,
    ← Fin.sum_univ_eq_sum_range (fun u => (apexList lists D u).length)]
  simp_rw [hlen]
  simp only [Finset.sum_add_distrib, hsumOld, hsum, apexList,
    lt_self_iff_false, dite_false, ite_true, List.length_map]
  omega

/-- The numerical apex graph adds exactly one edge for every cycle vertex. -/
theorem apexFinGraph_edge_ncard {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (h : IsAdjListFamily G lists) (D : List (Fin N)) (hD : D.Nodup) :
    (apexFinGraph G D).edgeSet.ncard = G.edgeSet.ncard + D.length := by
  have hh := length_flatUpTo_eq (isAdjListFamily_apexList h D hD)
  have hl := length_flatUpTo_apexList h D hD
  omega

end GraphMinor.Compute.Crossing
