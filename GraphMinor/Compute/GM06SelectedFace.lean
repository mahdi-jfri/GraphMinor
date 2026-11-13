module

public import GraphMinor.Compute.GM06FaceRowsProgram
public import GraphMinor.Compute.GM06FaceIncidence

/-!
# Selecting the inner-cuff face of a cut component

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) selects the
face orbit containing the reverse inner cuff dart. This file gives the
exact finite row lookup. Distinct face darts make its successful
answer unique. The selected row retains the face orbit and successor
properties already proved for FACE_ROWS, and its origins and edge
labels define the two incidence tables `gm06IncV` and `gm06IncE`.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Select the first face row containing the specified directed end. -/
def gm06SelectFaceRow {D : Type*} [DecidableEq D] : List (List D) → D → Option (List D)
  | [], _ => none
  | row :: rows, d => if d ∈ row then some row else gm06SelectFaceRow rows d

/-- Successful selection returns an actual row containing the target dart. -/
theorem gm06SelectFaceRow_some {D : Type*} [DecidableEq D] (rows : List (List D)) (d : D) (row : List D)
    (h : gm06SelectFaceRow rows d = some row) : row ∈ rows ∧ d ∈ row := by
  induction rows with
  | nil => simp [gm06SelectFaceRow] at h
  | cons first rows ih =>
    by_cases hd : d ∈ first
    · have he : first = row := by simpa only [gm06SelectFaceRow, hd, ↓reduceIte, Option.some.injEq] using h
      exact ⟨he ▸ List.mem_cons_self, he ▸ hd⟩
    · obtain ⟨hr, hdr⟩ := ih (by simpa only [gm06SelectFaceRow, hd, ↓reduceIte] using h)
      exact ⟨List.mem_cons_of_mem _ hr, hdr⟩

/-- Lookup fails exactly when no face row contains the target dart. -/
theorem gm06SelectFaceRow_none_iff {D : Type*} [DecidableEq D] (rows : List (List D)) (d : D) :
    gm06SelectFaceRow rows d = none ↔ d ∉ rows.flatten := by
  induction rows with
  | nil => simp [gm06SelectFaceRow]
  | cons row rows ih =>
    by_cases hd : d ∈ row <;> simp [gm06SelectFaceRow, hd, ih]

/-- Distinct face darts force lookup to return any row containing the target. -/
theorem gm06SelectFaceRow_eq_some {D : Type*} [DecidableEq D] (rows : List (List D)) (d : D) (row : List D)
    (hnd : rows.flatten.Nodup) (hr : row ∈ rows) (hd : d ∈ row) : gm06SelectFaceRow rows d = some row := by
  induction rows with
  | nil => simp at hr
  | cons first rows ih =>
    have hn : first.Nodup ∧ rows.flatten.Nodup ∧
        (∀ a ∈ first, ∀ b ∈ rows.flatten, a ≠ b) := by simpa only [List.flatten_cons, List.nodup_append] using hnd
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [gm06SelectFaceRow, hd, ↓reduceIte]
    · have hnot : d ∉ first := fun h => hn.2.2 d h d (List.mem_flatten.mpr ⟨row, hr, hd⟩) rfl
      simpa only [gm06SelectFaceRow, hnot, ↓reduceIte] using ih hn.2.1 hr

/-- Exactly one row contains each dart that occurs in the disjoint face rows. -/
theorem gm06SelectFaceRow_unique {D : Type*} [DecidableEq D] (rows : List (List D)) (d : D)
    (hnd : rows.flatten.Nodup) (hd : d ∈ rows.flatten) : ∃! row, row ∈ rows ∧ d ∈ row := by
  obtain ⟨row, hr, hdr⟩ := List.mem_flatten.mp hd
  refine ⟨row, ⟨hr, hdr⟩, ?_⟩
  intro other ho
  have h₁ := gm06SelectFaceRow_eq_some rows d row hnd hr hdr
  have h₂ := gm06SelectFaceRow_eq_some rows d other hnd ho.1 ho.2
  exact Option.some.inj (h₂.symm.trans h₁)

/-- Injective relabelling commutes with selected-face lookup. -/
theorem gm06SelectFaceRow_map {D E : Type*} [DecidableEq D] [DecidableEq E] (f : D → E)
    (hf : Function.Injective f) (rows : List (List D)) (d : D) :
    gm06SelectFaceRow (rows.map (List.map f)) (f d) = (gm06SelectFaceRow rows d).map (List.map f) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hm : f d ∈ row.map f ↔ d ∈ row := by
      simp only [List.mem_map, hf.eq_iff, exists_eq_right]
    by_cases hd : d ∈ row <;> simp [gm06SelectFaceRow, hm, hd, ih]

/-- The selected face of a component from its actual rotation rows. -/
def gm06SelectedFace {m : ℕ} (rotations : List (List (Fin (2 * m)))) (active : List (Fin (2 * m)))
    (reverseInner : Fin (2 * m)) : Option (List (Fin (2 * m))) :=
  gm06SelectFaceRow (gm06ActiveFaceRows rotations active) reverseInner

/-- Equation (10) as a pure finite output, retaining the selected row
and both dense incidence tables. -/
def gm06SelectedFaceIncidence {m : ℕ} (n : ℕ) (origins : List ℕ)
    (rotations : List (List (Fin (2 * m)))) (active : List (Fin (2 * m))) (reverseInner : Fin (2 * m)) :
    Option (List ℕ × List ℕ × List ℕ) :=
  (gm06SelectedFace rotations active reverseInner).map (fun row =>
    let darts := row.map Fin.val
    (darts, gm06IncV n origins darts, gm06IncE m darts))

/-- The reverse inner cuff dart selects exactly its complete face
orbit, and the returned cyclic row follows the computed face successor. -/
theorem gm06SelectedFace_spec {m : ℕ} (rotations : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (reverseInner : Fin (2 * m))
    (hnd : rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ active ↔ d ∈ rotations.flatten)
    (hmate : ∀ d ∈ active, gm06DartReversal m d ∈ active) (hd : reverseInner ∈ active) :
    ∃ row, gm06SelectedFace rotations active reverseInner = some row ∧ reverseInner ∈ row ∧
      (∀ other ∈ gm06ActiveFaceRows rotations active, reverseInner ∈ other → other = row) ∧
      ∃ start ∈ active, row = gm06OrbitTrace (gm06FacePermutation rotations) start (2 * m) ∧
        List.IsChain (fun a b => gm06FacePermutation rotations a = b) (row ++ [start]) := by
  have hs := gm06ActiveFaceRows_spec rotations active hnd hcover hmate
  obtain ⟨row, ⟨hr, hdr⟩, huniq⟩ := hs.2.2.1 reverseInner hd
  refine ⟨row, gm06SelectFaceRow_eq_some _ _ _ hs.1 hr hdr, hdr,
    fun other ho hdo => huniq other ⟨ho, hdo⟩, hs.2.2.2 row hr⟩

/-- A reverse cuff dart is absent exactly when its selected face is absent. -/
theorem gm06SelectedFace_none_iff {m : ℕ} (rotations : List (List (Fin (2 * m))))
    (active : List (Fin (2 * m))) (reverseInner : Fin (2 * m))
    (hnd : rotations.flatten.Nodup)
    (hcover : ∀ d, d ∈ active ↔ d ∈ rotations.flatten)
    (hmate : ∀ d ∈ active, gm06DartReversal m d ∈ active) :
    gm06SelectedFace rotations active reverseInner = none ↔ reverseInner ∉ active := by
  rw [gm06SelectedFace, gm06SelectFaceRow_none_iff]
  exact not_congr ((gm06ActiveFaceRows_spec rotations active hnd hcover hmate).2.1 reverseInner)

/-- Successful selected-face incidence consists exactly of that row's
origin and edge-label membership tables, `gm06IncV` and `gm06IncE`. -/
theorem gm06SelectedFaceIncidence_eq {m n : ℕ} (origins : List ℕ)
    (rotations : List (List (Fin (2 * m)))) (active : List (Fin (2 * m)))
    (reverseInner : Fin (2 * m)) (row : List (Fin (2 * m)))
    (hrow : gm06SelectedFace rotations active reverseInner = some row) :
    gm06SelectedFaceIncidence n origins rotations active reverseInner =
      some (row.map Fin.val, gm06IncV n origins (row.map Fin.val), gm06IncE m (row.map Fin.val)) := by
  simp only [gm06SelectedFaceIncidence, hrow, Option.map_some]

end GraphMinor.Compute
