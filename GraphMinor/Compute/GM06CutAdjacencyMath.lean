module

public import GraphMinor.Compute.GM06CutNeighbourMarks
public import GraphMinor.Compute.GM06CutComponents

/-!
# Adjacency obtained from the copied rotation rows

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) connects the
copied ends using their assigned origins. The origin pass writes
each outgoing end at exactly its vertex row. Hence a row's reverse-end
origins give precisely its neighbours in the underlying search graph.
Filtering a dense label range removes repetitions from parallel edges.
This file proves that correspondence for the computed cut data.
-/

@[expose] public section
namespace GraphMinor.Compute
open SimpleGraph

/-- The two parity cases of a directed end and its reverse. -/
theorem gm06DartMate_end_cases (d : ℕ) :
    (d = 2 * (d / 2) ∧ gm06DartMate d = 2 * (d / 2) + 1) ∨
      (d = 2 * (d / 2) + 1 ∧ gm06DartMate d = 2 * (d / 2)) := by
  have hm := Nat.mod_lt d (by decide : 0 < 2)
  have he := Nat.mod_add_div d 2
  unfold gm06DartMate
  split_ifs <;> omega

/-- Both active ends of a dart give its retained permanent edge label. -/
theorem gm06CutEdgeLabels_of_pair (data : GM06CutData) (d : ℕ)
    (hd : d ∈ data.activeDarts) (hm : gm06DartMate d ∈ data.activeDarts) :
    d / 2 ∈ gm06CutEdgeLabels data := by
  apply (gm06CutEdgeLabels_mem_iff data _).mpr
  rcases gm06DartMate_end_cases d with ⟨h₀, h₁⟩ | ⟨h₁, h₀⟩
  · exact ⟨h₀ ▸ hd, h₁ ▸ hm⟩
  · exact ⟨h₀ ▸ hm, h₁ ▸ hd⟩

/-- The two stored endpoints are the source and reverse-origin of
either directed end, in one of the two possible orders. -/
theorem gm06CutEndpoints_dart (data : GM06CutData) (d : ℕ) :
    gm06CutEndpoints data (d / 2) = (data.origins[d]?.getD 0, gm06CutNeighbourHead data.origins d) ∨
      gm06CutEndpoints data (d / 2) = (gm06CutNeighbourHead data.origins d, data.origins[d]?.getD 0) := by
  rcases gm06DartMate_end_cases d with ⟨h₀, h₁⟩ | ⟨h₁, h₀⟩
  · exact Or.inl (Prod.ext (congrArg (fun i => data.origins[i]?.getD 0) h₀.symm)
      (congrArg (fun i => data.origins[i]?.getD 0) h₁.symm))
  · exact Or.inr (Prod.ext (congrArg (fun i => data.origins[i]?.getD 0) h₀.symm)
      (congrArg (fun i => data.origins[i]?.getD 0) h₁.symm))

/-- Every indexed row contributes exactly its own origin values,
and every listed dart occurs in that unique indexed row. -/
theorem gm06CutOrigins_row_iff {m d v : ℕ} (rows : List (List ℕ))
    (hnd : rows.flatten.Nodup) (hd : d ∈ rows.flatten) (hdBound : d < 4 * m) (hv : v < rows.length) :
    (gm06CutOrigins m rows)[d]?.getD 0 = v ↔ d ∈ rows[v] := by
  have zip_mem : ∀ i (hi : i < rows.length), (rows[i], i) ∈ rows.zipIdx := by
    intro i hi
    apply List.mem_iff_getElem.mpr
    exact ⟨i, by simpa using hi, by simp only [List.getElem_zipIdx, Nat.zero_add]⟩
  constructor
  · intro horg
    obtain ⟨row, hr, hdr⟩ := List.mem_flatten.mp hd
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hr
    have hz : (row, i) ∈ rows.zipIdx := by simpa only [heq] using zip_mem i hi
    have hlookup := gm06CutOrigins_getElem? rows row hnd hz hdr hdBound
    have hiv : i = v := by simpa only [hlookup, Option.getD_some] using horg
    subst i
    simpa only [heq] using hdr
  · intro hdr
    have hlookup := gm06CutOrigins_getElem? rows rows[v] hnd (zip_mem v hv) hdr hdBound
    simp only [hlookup, Option.getD_some]

/-- The input-to-cut-data pure function satisfies the exact row-origin
correspondence, assuming only distinct original outgoing ends. -/
theorem gm06CutDataOfLinkage_origin_row_iff {n m d v : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ) (rows : List (List ℕ)) (live : List ℕ)
    (hrows : rows.length = n) (hnd : rows.flatten.Nodup)
    (hd : d ∈ (gm06CutDataOfLinkage n m origins paths inner outer rows live).activeDarts) (hv : v < 2 * n) :
    let data := gm06CutDataOfLinkage n m origins paths inner outer rows live
    data.origins[d]?.getD 0 = v ↔ d ∈ data.rotations[v]?.getD [] := by
  have hactive := (gm06CutDataOfLinkage_active_iff n m origins paths inner outer rows live d).mp hd
  let marks := gm06BuildCutTables n m origins paths inner outer
  let copied := gm06SplitRotationRows marks rows
  have hv' : v < copied.length := by simpa only [copied, gm06SplitRotationRows_length, hrows] using hv
  have he := gm06CutOrigins_row_iff copied (gm06SplitRotationRows_nodup marks rows hnd) hactive.2 hactive.1 hv'
  change (gm06CutOrigins (m + inner.length + outer.length) copied)[d]?.getD 0 = v ↔ d ∈ copied[v]?.getD []
  simpa only [List.getElem?_eq_getElem hv', Option.getD_some] using he

/-- The exact candidate criterion for one reverse-end neighbour. -/
theorem gm06CutNeighbourCandidates_mem_iff (origins active live row : List ℕ) (u v : ℕ) :
    v ∈ gm06CutNeighbourCandidates origins active live u row ↔
      ∃ d ∈ row, d ∈ active ∧ gm06DartMate d ∈ active ∧ u ∈ live ∧ v ∈ live ∧ v ≠ u ∧
        gm06CutNeighbourHead origins d = v := by
  constructor
  · intro hv
    obtain ⟨d, hd, he⟩ := List.mem_map.mp hv
    obtain ⟨hdr, hk⟩ := List.mem_filter.mp hd
    have hp := of_decide_eq_true hk
    exact ⟨d, hdr, hp.1, hp.2.1, hp.2.2.1, he ▸ hp.2.2.2.1, he ▸ hp.2.2.2.2, he⟩
  · rintro ⟨d, hd, hda, hma, hul, hvl, hvu, he⟩
    apply List.mem_map.mpr
    refine ⟨d, List.mem_filter.mpr ⟨hd, ?_⟩, he⟩
    simp only [gm06CutNeighbourKeep, decide_eq_true_eq, he]
    exact ⟨hda, hma, hul, hvl, hvu⟩

/-- Reverse-end neighbours in an indexed row are exactly graph
adjacency when the origin table identifies that row. -/
theorem gm06CutGraph_adj_iff_candidates {n : ℕ} (data : GM06CutData)
    (hproper : ∀ d ∈ data.activeDarts, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD []) (u v : Fin n) :
    (gm06CutGraph n data).Adj u v ↔
      v.val ∈ gm06CutNeighbourCandidates data.origins data.activeDarts data.vertices u.val (data.rotations[u.val]?.getD []) := by
  rw [gm06CutNeighbourCandidates_mem_iff]
  constructor
  · rintro ⟨hne, hul, hvl, e, he, hends⟩
    have hactive := (gm06CutEdgeLabels_mem_iff data e).mp he
    have hmate₀ : gm06DartMate (2 * e) = 2 * e + 1 := by unfold gm06DartMate; split_ifs <;> omega
    have hmate₁ : gm06DartMate (2 * e + 1) = 2 * e := by unfold gm06DartMate; split_ifs <;> omega
    rcases hends with hends | hends
    · have ho : data.origins[2 * e]?.getD 0 = u.val := congrArg Prod.fst hends
      have hh : gm06CutNeighbourHead data.origins (2 * e) = v.val := by
        simpa only [gm06CutNeighbourHead, hmate₀, gm06CutEndpoints, Prod.snd] using congrArg Prod.snd hends
      exact ⟨2 * e, (hproper _ hactive.1 u).mp ho, hactive.1, by simpa only [hmate₀] using hactive.2,
        hul, hvl, fun h => hne (Fin.ext h.symm), hh⟩
    · have ho : data.origins[2 * e + 1]?.getD 0 = u.val := congrArg Prod.snd hends
      have hh : gm06CutNeighbourHead data.origins (2 * e + 1) = v.val := by
        simpa only [gm06CutNeighbourHead, hmate₁, gm06CutEndpoints, Prod.fst] using congrArg Prod.fst hends
      exact ⟨2 * e + 1, (hproper _ hactive.2 u).mp ho, hactive.2, by simpa only [hmate₁] using hactive.1,
        hul, hvl, fun h => hne (Fin.ext h.symm), hh⟩
  · rintro ⟨d, hd, hda, hma, hul, hvl, hvu, hh⟩
    have ho := (hproper d hda u).mpr hd
    have hends := gm06CutEndpoints_dart data d
    rw [ho, hh] at hends
    exact ⟨fun h => hvu (congrArg Fin.val h).symm, hul, hvl, d / 2, gm06CutEdgeLabels_of_pair data d hda hma, hends⟩

/-- Duplicate-free adjacency lists obtained by filtering the permanent
vertex range after reverse-end candidates have been marked. -/
def gm06CutAdjacencyLists (n : ℕ) (data : GM06CutData) (u : Fin n) : List ℕ :=
  (List.range n).filter (fun v => decide (v ∈ gm06CutNeighbourCandidates data.origins
    data.activeDarts data.vertices u.val (data.rotations[u.val]?.getD [])))

/-- The finite row construction represents exactly the cut search graph. -/
theorem gm06CutAdjacencyLists_spec {n : ℕ} (data : GM06CutData)
    (hproper : ∀ d ∈ data.activeDarts, ∀ u : Fin n,
      data.origins[d]?.getD 0 = u.val ↔ d ∈ data.rotations[u.val]?.getD []) :
    IsAdjListFamily (gm06CutGraph n data) (gm06CutAdjacencyLists n data) := by
  intro u
  refine ⟨?_, (List.nodup_range (n := n)).filter _, ?_, ?_⟩
  · intro v hv
    exact List.mem_range.mp (List.mem_filter.mp hv).1
  · exact (List.length_filter_le _ _).trans (by simp)
  · intro v
    simp only [gm06CutAdjacencyLists, List.mem_filter, List.mem_range, v.isLt, true_and, decide_eq_true_eq]
    exact (gm06CutGraph_adj_iff_candidates data hproper u v).symm

end GraphMinor.Compute
