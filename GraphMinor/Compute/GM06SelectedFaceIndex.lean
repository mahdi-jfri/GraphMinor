module

public import GraphMinor.Compute.GM06SelectedFace
public import GraphMinor.Compute.GM06FaceBuffers
import GraphMinor.Compute.GM06CutPathMembership

/-!
# Reading a selected face index from the computed owner table

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) chooses the
face containing the reverse inner cuff end. FACE_ROWS already writes
each dart's face number, starting at one. This file proves that its
owner table gives exactly the selected row index. Zero means the
end is absent. The positive case derives the row and target membership
from actual scatter writes, rather than an assumed lookup certificate.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A face owner is zero for absent darts and the row index plus one otherwise. -/
def gm06SelectedFaceOwner (q : ℕ) (rows : List (List ℕ)) (d : ℕ) : ℕ :=
  (gm06FaceOwners q rows)[d]?.getD 0

/-- The optional zero-based face index read from its actual owner table. -/
def gm06SelectedFaceIndex (q : ℕ) (rows : List (List ℕ)) (d : ℕ) : Option ℕ :=
  let owner := gm06SelectedFaceOwner q rows d
  if owner = 0 then none else some (owner - 1)

/-- A zero owner is exactly absence from the face rows. -/
theorem gm06SelectedFaceOwner_zero_iff {q d : ℕ} (rows : List (List ℕ)) (hd : d < q) :
    gm06SelectedFaceOwner q rows d = 0 ↔ d ∉ rows.flatten := by
  have hi : d < (gm06FaceOwners q rows).length := by simpa only [gm06FaceOwners_length] using hd
  simpa only [gm06SelectedFaceOwner, List.getElem?_eq_getElem hi, Option.getD_some, Option.some.injEq] using
    gm06FaceOwners_zero_iff q rows d hd

/-- Failed owner-index selection is exactly failed face-row selection. -/
theorem gm06SelectedFaceIndex_none_iff {q d : ℕ} (rows : List (List ℕ)) (hd : d < q) :
    gm06SelectedFaceIndex q rows d = none ↔ gm06SelectFaceRow rows d = none := by
  rw [gm06SelectFaceRow_none_iff, ← gm06SelectedFaceOwner_zero_iff rows hd]
  unfold gm06SelectedFaceIndex
  by_cases h : gm06SelectedFaceOwner q rows d = 0 <;> simp only [h, ↓reduceIte, reduceCtorEq]

/-- A nonzero owner identifies its actual indexed face row and the
exact result of selected-face lookup. -/
theorem gm06SelectedFaceIndex_some {q d i : ℕ} (rows : List (List ℕ))
    (hd : d < q) (hnd : rows.flatten.Nodup) (hi : gm06SelectedFaceIndex q rows d = some i) :
    ∃ hrow : i < rows.length, d ∈ rows[i] ∧ gm06SelectFaceRow rows d = some rows[i] := by
  let owner := gm06SelectedFaceOwner q rows d
  have howner : owner ≠ 0 ∧ owner - 1 = i := by
    change (if owner = 0 then none else some (owner - 1)) = some i at hi
    split_ifs at hi with hz
    exact ⟨hz, Option.some.inj hi⟩
  have hbound : d < (gm06FaceOwners q rows).length := by simpa only [gm06FaceOwners_length] using hd
  have hlookup : (gm06FaceOwners q rows)[d]? = some owner := by
    simp only [owner, gm06SelectedFaceOwner, List.getElem?_eq_getElem hbound, Option.getD_some]
  have hp : (d, owner) ∈ gm06FaceOwnerPairs rows := by
    rcases gm06Scatter_getElem?_source (gm06FaceOwnerPairs rows) (List.replicate q 0) d owner
      (by simpa using hd) hlookup with hz | hp
    · simp only [List.getElem?_replicate, hd, ↓reduceIte, Option.some.injEq] at hz
      exact False.elim (howner.1 hz.symm)
    · exact hp
  obtain ⟨pair, hpair, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hp
  have heqd : e = d := congrArg Prod.fst heq
  have hindex : pair.2 = i := by
    have hval := congrArg Prod.snd heq
    change pair.2 + 1 = owner at hval
    omega
  have hrow := List.mem_zipIdx hpair
  have hir : i < rows.length := by simpa only [hindex, Nat.zero_add] using hrow.2.1
  have hroweq : pair.1 = rows[i] := by simpa only [hindex, Nat.sub_zero] using hrow.2.2
  have hdin : d ∈ rows[i] := by rw [← hroweq, ← heqd]; exact he
  exact ⟨hir, hdin, gm06SelectFaceRow_eq_some rows d rows[i] hnd (List.getElem_mem hir) hdin⟩

/-- Reading the optional indexed row agrees with direct face-row selection. -/
theorem gm06SelectedFaceIndex_getElem? {q d : ℕ} (rows : List (List ℕ))
    (hd : d < q) (hnd : rows.flatten.Nodup) :
    (gm06SelectedFaceIndex q rows d).bind (fun i => rows[i]?) = gm06SelectFaceRow rows d := by
  cases hi : gm06SelectedFaceIndex q rows d with
  | none =>
    have hs := (gm06SelectedFaceIndex_none_iff rows hd).mp hi
    simp only [Option.bind_none, hs]
  | some i =>
    obtain ⟨hir, _, hs⟩ := gm06SelectedFaceIndex_some rows hd hnd hi
    simp only [Option.bind_some, List.getElem?_eq_getElem hir, hs]

end GraphMinor.Compute
