module

public import GraphMinor.Compute.Case3StepsPlaceholderCode
public import GraphMinor.Compute.Algorithm99TransportOrig

/-!
# Checking the member records in the final block

The case (iii) parser checks the vertex and edge lists and the parent and
leaf bounds. Renaming preserves the lists without repetitions. Valid
branch codes supply the tree bounds for interior members. The prescribed
one-vertex record supplies the same bounds for all other members.
-/

public section

namespace GraphMinor.Compute

open GraphMinor.Transport

/-- Both endpoints of every renamed edge occur in the member's vertex list. -/
theorem case3BranchRecord_endpoints {n N : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ) :
    let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
    ∀ e ∈ r.eList, e.1 ∈ r.vList ∧ e.2.1 ∈ r.vList := by
  dsimp only
  intro e he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
  have ha' := (G.mem_multiEdgeTriples_iff a).mp ha
  rcases a with ⟨u, v, k⟩
  obtain ⟨hu, hv, _⟩ := ha'
  constructor
  · exact List.mem_map.mpr ⟨⟨u, hu⟩, List.mem_finRange _, rfl⟩
  · exact List.mem_map.mpr ⟨⟨v, hv⟩, List.mem_finRange _, rfl⟩

private theorem record_valid_of_tree_bounds {n N m : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ)
    (Kv : List ℕ) (Ke : List (ℕ × ℕ × ℕ)) (hn : n ≤ N) (hm : G.numEdges ≤ m)
    (hv : ∀ v ∈ (case3BranchRecord G (origVertexEmb orig hinj)
      (origEdgeEmb orig hinj) code).vList, v ∈ Kv)
    (he : ∀ e ∈ (case3BranchRecord G (origVertexEmb orig hinj)
      (origEdgeEmb orig hinj) code).eList, e ∈ Ke)
    (ht : let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
      1 ≤ r.t_len ∧ r.t_len ≤ 2 * r.eList.length + 1 ∧
      r.parList.getD 0 0 < r.t_len ∧
      (∀ z, 0 < z → z < r.t_len → r.parList.getD z 0 < z) ∧
      ∀ u ∈ r.tauList, u < r.t_len) :
    isValidMemberRecord N m Kv Ke
      (case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code) = true := by
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have hlengths := case3BranchRecord_lengths G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have hend := case3BranchRecord_endpoints G orig hinj code
  have hnv : r.vList.Nodup := by
    exact (List.nodup_finRange n).map (fun a b hab => Fin.ext ((origVertexEmb orig hinj).injective hab))
  have hne := case3BranchRecord_edges_nodup G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code
  have hvl : r.vList.length ≤ N := by
    simpa only [r, case3BranchRecord, List.length_map, List.length_finRange] using hn
  have hel : r.eList.length ≤ m := by
    simpa only [r, case3BranchRecord, List.length_map, G.length_multiEdgeTriples] using hm
  unfold isValidMemberRecord
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hvl, hnv⟩, hv⟩, hel⟩, hne⟩,
    fun e he' => ⟨he e he', hend e he'⟩⟩, ht.1, ht.2.1⟩, hlengths.1⟩,
    ht.2.2.1, fun z hz hp => ht.2.2.2.1 z hp (List.mem_range.mp hz)⟩,
    hlengths.2⟩, ht.2.2.2.2⟩

/-- Interior records pass the finite parser checks when their lists lie
in the serialized compass lists. -/
theorem case3BranchRecord_isValidMemberRecord {n N m B : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig) (code : List ℕ)
    (Kv : List ℕ) (Ke : List (ℕ × ℕ × ℕ)) (hn : n ≤ N) (hm : G.numEdges ≤ m)
    (hv : ∀ v ∈ (case3BranchRecord G (origVertexEmb orig hinj)
      (origEdgeEmb orig hinj) code).vList, v ∈ Kv)
    (he : ∀ e ∈ (case3BranchRecord G (origVertexEmb orig hinj)
      (origEdgeEmb orig hinj) code).eList, e ∈ Ke)
    (hcode : IsValidBranchDecompCode B G code) :
    isValidMemberRecord N m Kv Ke
      (case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) code) = true :=
  record_valid_of_tree_bounds G orig hinj code Kv Ke hn hm hv he
    (case3BranchRecord_tree_bounds G _ _ code hcode)

/-- The noninterior placeholder passes the same checks for any edge count. -/
theorem case3BranchRecord_placeholder_isValidMemberRecord {n N m : ℕ} (G : MultiDigraph n)
    (orig : Fin n → Fin N) (hinj : Function.Injective orig)
    (Kv : List ℕ) (Ke : List (ℕ × ℕ × ℕ)) (hn : n ≤ N) (hm : G.numEdges ≤ m)
    (hv : ∀ v ∈ (case3BranchRecord G (origVertexEmb orig hinj)
      (origEdgeEmb orig hinj) (case3PlaceholderCode G.numEdges)).vList, v ∈ Kv)
    (he : ∀ e ∈ (case3BranchRecord G (origVertexEmb orig hinj)
      (origEdgeEmb orig hinj) (case3PlaceholderCode G.numEdges)).eList, e ∈ Ke) :
    isValidMemberRecord N m Kv Ke
      (case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
        (case3PlaceholderCode G.numEdges)) = true := by
  apply record_valid_of_tree_bounds G orig hinj _ Kv Ke hn hm hv he
  obtain ⟨ht, hp, hτ⟩ := case3BranchRecord_placeholder_fields G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
  dsimp only
  rw [ht, hp, hτ]
  refine ⟨by omega, by omega, by decide, ?_, ?_⟩
  · intro z hz hzl
    omega
  · intro u hu
    have hu0 := (List.mem_replicate.mp hu).2
    omega

/-- Enlarging the ambient edge bound retains every parser check. -/
theorem case3IsValidMemberRecord_mono_edges {N m m' : ℕ}
    (Kv : List ℕ) (Ke : List (ℕ × ℕ × ℕ)) (r : Case3MemberRecord)
    (h : isValidMemberRecord N m Kv Ke r = true) (hm : m ≤ m') :
    isValidMemberRecord N m' Kv Ke r = true := by
  simp only [isValidMemberRecord, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at h ⊢
  rcases h with ⟨hvlen, hvnd, hvsub, helen, hrest⟩
  exact ⟨hvlen, hvnd, hvsub, helen.trans hm, hrest⟩

end GraphMinor.Compute
