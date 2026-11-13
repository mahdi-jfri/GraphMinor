module

public import GraphMinor.Compute.GM06CutRowsFacts
public import GraphMinor.Compute.GM06CutPathMembership

/-!
# Exact copied-end membership in the induced rotations

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) keeps each
nonlinkage end once and each linkage end twice. The side tag encodes
that distinction. This file proves exact membership for each tag,
first at one original vertex and then across all indexed rows.
Projection identifies the old end, while the tag identifies its
ordinary or duplicated copy. These facts support global reversal.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A copied dart uniquely determines its old dart and side tag. -/
theorem gm06CutDart_inj {d e tag other : ℕ} (ht : tag < 2) (ho : other < 2) :
    gm06CutDart d tag = gm06CutDart e other ↔ d = e ∧ tag = other := by
  constructor
  · intro heq
    have hde := congrArg gm06UncutDart heq
    simp only [gm06UncutDart_cut _ _ ht, gm06UncutDart_cut _ _ ho] at hde
    subst e
    exact ⟨rfl, by unfold gm06CutDart at heq; omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Recover an end and its side tag from any permanent copied label. -/
theorem gm06CutDart_rebuild (q : ℕ) :
    gm06CutDart (gm06UncutDart q) ((q / 2) % 2) = q := by
  unfold gm06CutDart gm06UncutDart
  omega

/-- In one copied row, an unduplicated end has tag zero. -/
theorem gm06CutRotation_nonpath_tag {d tag : ℕ} (p : GM06CutPosition)
    (row : List ℕ) (left : Bool) (ht : tag < 2) (hp : d ∉ p.pathEnds)
    (hm : gm06CutDart d tag ∈ gm06CutRotation p row left) : tag = 0 := by
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hm
  have hproj := congrArg gm06UncutDart heq
  have hed : e = d := by simpa only [gm06CutRowDart_project, gm06UncutDart_cut _ _ ht] using hproj
  subst e
  have hlabel : gm06CutDart d 0 = gm06CutDart d tag := by simpa only [gm06CutRowDart, hp, ↓reduceIte] using heq
  exact ((gm06CutDart_inj (by decide) ht).mp hlabel).2.symm

/-- A vertex retains the tag-zero copy of every old end and retains
tag one exactly for its decoded linkage ends. -/
theorem gm06SplitVertexRows_cut_mem_iff {d tag : ℕ} (position : Option GM06CutPosition)
    (row : List ℕ) (ht : tag < 2) :
    gm06CutDart d tag ∈ (gm06SplitVertexRows position row).flatten ↔
      d ∈ row ∧ (tag = 0 ∨ ∃ p, position = some p ∧ d ∈ p.pathEnds) := by
  cases position with
  | none =>
    simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_map, reduceCtorEq, false_and, exists_false, or_false]
    constructor
    · rintro ⟨e, he, heq⟩
      obtain ⟨hed, htag⟩ := (gm06CutDart_inj (by decide) ht).mp heq
      exact ⟨hed ▸ he, htag.symm⟩
    · rintro ⟨hd, rfl⟩
      exact ⟨d, hd, rfl⟩
  | some p =>
    simp only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.mem_append, Option.some.injEq]
    constructor
    · intro h
      have hd : d ∈ row := by
        have hm : gm06CutDart d tag ∈ (gm06SplitVertexRows (some p) row).flatten := by
          simpa only [gm06SplitVertexRows, List.flatten_cons, List.flatten_nil, List.append_nil, List.mem_append] using h
        simpa only [gm06UncutDart_cut _ _ ht] using gm06SplitVertexRows_project_mem (some p) row hm
      refine ⟨hd, ?_⟩
      by_cases hp : d ∈ p.pathEnds
      · exact Or.inr ⟨p, rfl, hp⟩
      · exact Or.inl (h.elim (gm06CutRotation_nonpath_tag p row true ht hp)
          (gm06CutRotation_nonpath_tag p row false ht hp))
    · rintro ⟨hd, htag | hp⟩
      · subst tag
        by_cases hp : d ∈ p.pathEnds
        · exact Or.inl (gm06CutRotation_path_mem p row d hd hp).1
        · let left := gm06CutDartLeft p row d
          have hm := (gm06CutRotation_nonpath_mem p row d hp left).mpr ⟨hd, rfl⟩
          cases hs : left
          · exact Or.inr (hs ▸ hm)
          · exact Or.inl (hs ▸ hm)
      · obtain ⟨p', heq, hp⟩ := hp
        subst p'
        have hm := gm06CutRotation_path_mem p row d hd hp
        have htag : tag = 0 ∨ tag = 1 := by omega
        exact htag.elim (fun h => Or.inl (h ▸ hm.1)) (fun h => Or.inr (h ▸ hm.2))

/-- A copied end occurs globally exactly when one indexed old row
contains it and gives it the indicated copy. -/
theorem gm06SplitRotationRows_cut_mem_iff {d tag : ℕ} (marks : GM06CutTables)
    (rows : List (List ℕ)) (ht : tag < 2) :
    gm06CutDart d tag ∈ (gm06SplitRotationRows marks rows).flatten ↔
      ∃ pair ∈ rows.zipIdx, d ∈ pair.1 ∧
        (tag = 0 ∨ ∃ p, gm06CutPositionAt marks pair.2 = some p ∧ d ∈ p.pathEnds) := by
  constructor
  · intro h
    obtain ⟨copied, hc, hd⟩ := List.mem_flatten.mp h
    obtain ⟨pair, hp, hlocal⟩ := List.mem_flatMap.mp hc
    exact ⟨pair, hp, (gm06SplitVertexRows_cut_mem_iff _ _ ht).mp
      (List.mem_flatten.mpr ⟨copied, hlocal, hd⟩)⟩
  · rintro ⟨pair, hp, hd⟩
    have hlocal := (gm06SplitVertexRows_cut_mem_iff (gm06CutPositionAt marks pair.2) pair.1 ht).mpr hd
    obtain ⟨copied, hc, hd⟩ := List.mem_flatten.mp hlocal
    exact List.mem_flatten.mpr ⟨copied, List.mem_flatMap.mpr ⟨pair, hp, hc⟩, hd⟩

end GraphMinor.Compute
