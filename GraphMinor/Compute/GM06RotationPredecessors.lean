module

public import GraphMinor.Compute.GM06FaceRows
public import GraphMinor.Compute.GM06DartMate
public import Mathlib.GroupTheory.Perm.List

/-!
# Reading the face permutation from rotation rows

Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) first
computes clockwise predecessors in the supplied counterclockwise rotations.
For each row, pair its first dart with its last and every later dart
with its preceding dart. Scatter these pairs into a table. The rows
have disjoint darts, so no later write changes an earlier predecessor.
The resulting table is the inverse of the rotation permutation. Dart
reversal followed by this inverse is the face successor.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scatter a list of label/value pairs into a table, in list order. -/
def gm06Scatter : List (ℕ × ℕ) → List ℕ → List ℕ
  | [], table => table
  | p :: ps, table => gm06Scatter ps (table.set p.1 p.2)

/-- Scatter writes keep the allocated label space. -/
theorem gm06Scatter_length (pairs : List (ℕ × ℕ)) (table : List ℕ) :
    (gm06Scatter pairs table).length = table.length := by
  induction pairs generalizing table with
  | nil => rfl
  | cons p ps ih => simpa only [gm06Scatter, List.length_set] using ih (table.set p.1 p.2)

/-- A label absent from the keys is left unchanged. -/
theorem gm06Scatter_getElem?_of_not_mem (pairs : List (ℕ × ℕ)) (table : List ℕ)
    (d : ℕ) (hd : d ∉ pairs.map Prod.fst) :
    (gm06Scatter pairs table)[d]? = table[d]? := by
  induction pairs generalizing table with
  | nil => rfl
  | cons p ps ih =>
    have hne : d ≠ p.1 := by intro heq; exact hd (by simp [heq])
    have htail : d ∉ ps.map Prod.fst := fun h => hd (by simp [h])
    rw [gm06Scatter, ih _ htail, List.getElem?_set_ne hne.symm]

/-- With distinct keys, each scattered value is found at its key. -/
theorem gm06Scatter_getElem?_of_mem (pairs : List (ℕ × ℕ)) (table : List ℕ)
    (hn : (pairs.map Prod.fst).Nodup) (p : ℕ × ℕ) (hp : p ∈ pairs)
    (hb : p.1 < table.length) : (gm06Scatter pairs table)[p.1]? = some p.2 := by
  induction pairs generalizing table with
  | nil => cases hp
  | cons q ps ih =>
    have hnd := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [gm06Scatter, gm06Scatter_getElem?_of_not_mem ps _ p.1 hnd.1,
        List.getElem?_set_self hb]
    · exact ih (table.set q.1 q.2) hnd.2 hp (by simpa using hb)

/-- Clockwise predecessor pairs of a counterclockwise rotation row. -/
def gm06RotationPredecessorPairs {D : Type*} (row : List D) : List (D × D) :=
  row.zip (row.getLast?.toList ++ row.dropLast)

/-- Every outgoing dart occurs once as a key in its rotation row. -/
theorem gm06RotationPredecessorPairs_keys {D : Type*} (row : List D) :
    (gm06RotationPredecessorPairs row).map Prod.fst = row := by
  unfold gm06RotationPredecessorPairs
  apply List.map_fst_zip
  cases row with
  | nil => simp
  | cons d ds => simp [List.getLast?_eq_some_getLast (by simp : d :: ds ≠ [])]

/-- Each predecessor pair consists of darts of that row. -/
theorem gm06RotationPredecessorPairs_mem {D : Type*} (row : List D) {d p : D}
    (h : (d, p) ∈ gm06RotationPredecessorPairs row) : d ∈ row ∧ p ∈ row := by
  have hz := List.of_mem_zip h
  refine ⟨hz.1, ?_⟩
  rcases List.mem_append.mp hz.2 with hp | hp
  · exact List.mem_of_mem_getLast? (by simpa using hp)
  · exact List.mem_of_mem_dropLast hp

/-- The predecessor in each pair is sent to its key by the row's
counterclockwise cyclic permutation. -/
theorem gm06RotationPredecessorPairs_apply {D : Type*} [DecidableEq D]
    (row : List D) (hn : row.Nodup) {d p : D}
    (h : (d, p) ∈ gm06RotationPredecessorPairs row) : row.formPerm p = d := by
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp h
  have hik : i < row.length := by
    have hh := congrArg List.length (gm06RotationPredecessorPairs_keys row)
    have he : (gm06RotationPredecessorPairs row).length = row.length := by simpa only [List.length_map] using hh
    exact hi.trans_le he.le
  have hzip : (row[i], (row.getLast?.toList ++ row.dropLast)[i]'(by
      cases row with
      | nil => simp at hik
      | cons a as => simpa [List.getLast?_eq_some_getLast (by simp : a :: as ≠ [])] using hik)) = (d, p) := by
    simpa only [gm06RotationPredecessorPairs, List.getElem_zip] using heq
  rcases row with _ | ⟨a, as⟩
  · simp at hik
  cases i with
  | zero =>
    have hd : a = d := congrArg Prod.fst hzip
    have hp : (a :: as).getLast (by simp) = p := by
      simpa only [List.getLast?_eq_some_getLast (by simp : a :: as ≠ []), Option.toList_some,
        List.singleton_append, List.getElem_cons_zero] using congrArg Prod.snd hzip
    rw [← hp, List.formPerm_apply_getLast]
    exact hd
  | succ i =>
    have hp : (a :: as)[i] = p := by
      have hh := congrArg Prod.snd hzip
      simpa only [List.getLast?_eq_some_getLast (by simp : a :: as ≠ []),
        Option.toList_some, List.singleton_append, List.getElem_cons_succ,
        List.getElem_dropLast] using hh
    have hd : (a :: as)[i + 1] = d := congrArg Prod.fst hzip
    rw [← hp, List.formPerm_apply_lt_getElem _ hn i hik]
    exact hd

/-- Rotation permutation read from all rows. Rows with no darts and
single-dart rows contribute the identity. -/
def gm06RotationPermutation {D : Type*} [DecidableEq D] : List (List D) → Equiv.Perm D
  | [] => 1
  | row :: rows => row.formPerm * gm06RotationPermutation rows

private theorem rotationPermutation_fixed {D : Type*} [DecidableEq D]
    (rows : List (List D)) (d : D) (hd : d ∉ rows.flatten) :
    gm06RotationPermutation rows d = d := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have hd₁ : d ∉ row := fun h => hd (by simp [h])
    have hd₂ : d ∉ rows.flatten := fun h => hd (by simp [h])
    simp only [gm06RotationPermutation, Equiv.Perm.mul_apply, ih hd₂,
      List.formPerm_apply_of_notMem hd₁]

/-- The global permutation agrees with a dart's own rotation row. -/
theorem gm06RotationPermutation_apply_row {D : Type*} [DecidableEq D]
    (rows : List (List D)) (hn : rows.flatten.Nodup) (row : List D)
    (hr : row ∈ rows) (d : D) (hd : d ∈ row) :
    gm06RotationPermutation rows d = row.formPerm d := by
  induction rows with
  | nil => cases hr
  | cons first rows ih =>
    have hn' : first.Nodup ∧ rows.flatten.Nodup ∧
        (∀ a ∈ first, ∀ b ∈ rows.flatten, a ≠ b) := by
      simpa only [List.flatten_cons, List.nodup_append] using hn
    have hnd : first.Nodup ∧ rows.flatten.Nodup ∧ List.Disjoint first rows.flatten :=
      ⟨hn'.1, hn'.2.1, fun a ha hb => hn'.2.2 a ha a hb rfl⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · have ht : d ∉ rows.flatten := fun h => hnd.2.2 hd h
      simp only [gm06RotationPermutation, Equiv.Perm.mul_apply, rotationPermutation_fixed rows d ht]
    · have hx : row.formPerm d ∈ row := List.formPerm_apply_mem_of_mem hd
      have hnot : row.formPerm d ∉ first :=
        fun h => hnd.2.2 h (List.mem_flatten.mpr ⟨row, hr, hx⟩)
      simp only [gm06RotationPermutation, Equiv.Perm.mul_apply, ih hnd.2.1 hr,
        List.formPerm_apply_of_notMem hnot]

/-- Natural predecessor-pair data read from the rows, without a
precomputed permutation or answer in the input. -/
def gm06RotationPredecessors (n : ℕ) (rows : List (List ℕ)) : List ℕ :=
  gm06Scatter (rows.flatMap gm06RotationPredecessorPairs) (List.range n)

/-- Scattering rotation predecessors computes exactly sigma inverse,
including identity values at unused permanent labels. -/
theorem gm06RotationPredecessors_eq_inverse {n : ℕ} (rows : List (List (Fin n)))
    (hn : rows.flatten.Nodup) :
    gm06RotationPredecessors n (rows.map (List.map Fin.val)) =
      List.ofFn (fun d : Fin n => ((gm06RotationPermutation rows).symm d).val) := by
  have hmap : (rows.map (List.map Fin.val)).flatMap gm06RotationPredecessorPairs =
      (rows.flatMap gm06RotationPredecessorPairs).map (fun p => (p.1.val, p.2.val)) := by
    clear hn
    induction rows with
    | nil => rfl
    | cons row rows ih =>
      simp only [List.map_cons, List.flatMap_cons, List.map_append, ih]
      congr 1
      simp only [gm06RotationPredecessorPairs, List.getLast?_map, Option.toList_map,
        ← List.map_dropLast, ← List.map_append, List.zip_map]
      rfl
  have hkeys : (rows.flatMap gm06RotationPredecessorPairs).map Prod.fst = rows.flatten := by
    simp only [List.map_flatMap, gm06RotationPredecessorPairs_keys]
    exact List.flatMap_id'
  have hkeysNat : (((rows.map (List.map Fin.val)).flatMap gm06RotationPredecessorPairs).map Prod.fst) =
      rows.flatten.map Fin.val := by
    rw [hmap]
    calc
      _ = ((rows.flatMap gm06RotationPredecessorPairs).map Prod.fst).map Fin.val := by
        simp only [List.map_map, Function.comp_def]
      _ = _ := congrArg (List.map Fin.val) hkeys
  apply List.ext_getElem (by simp [gm06RotationPredecessors, gm06Scatter_length])
  intro i hi hi'
  have hin : i < n := by simpa only [gm06RotationPredecessors, gm06Scatter_length, List.length_range] using hi
  let d : Fin n := ⟨i, hin⟩
  have hnd : (((rows.map (List.map Fin.val)).flatMap gm06RotationPredecessorPairs).map Prod.fst).Nodup := by
    rw [hkeysNat]
    exact hn.map Fin.val_injective
  simp only [List.getElem_ofFn]
  by_cases hd : d ∈ rows.flatten
  · have hm : d ∈ (rows.flatMap gm06RotationPredecessorPairs).map Prod.fst := by rw [hkeys]; exact hd
    obtain ⟨⟨a, p⟩, hp, ha⟩ := List.mem_map.mp hm
    dsimp only at ha
    subst a
    obtain ⟨row, hrow, hp⟩ := List.mem_flatMap.mp hp
    have hrownd := (List.nodup_flatten.mp hn).1 row hrow
    have hmrow := gm06RotationPredecessorPairs_mem row hp
    have hs : gm06RotationPermutation rows p = d :=
      (gm06RotationPermutation_apply_row rows hn row hrow p hmrow.2).trans
        (gm06RotationPredecessorPairs_apply row hrownd hp)
    have hsymm : (gm06RotationPermutation rows).symm d = p :=
      (gm06RotationPermutation rows).symm_apply_eq.mpr hs.symm
    have hpair : (i, p.val) ∈ (rows.map (List.map Fin.val)).flatMap gm06RotationPredecessorPairs := by
      rw [hmap]
      exact List.mem_map.mpr ⟨(d, p), List.mem_flatMap.mpr ⟨row, hrow, hp⟩, rfl⟩
    have hg := gm06Scatter_getElem?_of_mem _ (List.range n) hnd _ hpair (by simpa using hin)
    have hg' : (gm06RotationPredecessors n (rows.map (List.map Fin.val)))[i] = p.val := by
      change (gm06RotationPredecessors n (rows.map (List.map Fin.val)))[i]? = some p.val at hg
      exact Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hg)
    change _ = ((gm06RotationPermutation rows).symm d).val
    rw [hsymm]
    exact hg'
  · have hnot : i ∉ ((rows.map (List.map Fin.val)).flatMap gm06RotationPredecessorPairs).map Prod.fst := by
      rw [hkeysNat]
      intro hm
      obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
      have heq' : a = d := Fin.ext heq
      exact hd (heq' ▸ ha)
    have hg := gm06Scatter_getElem?_of_not_mem _ (List.range n) i hnot
    have hf : (gm06RotationPermutation rows).symm d = d :=
      (gm06RotationPermutation rows).symm_apply_eq.mpr (rotationPermutation_fixed rows d hd).symm
    change _ = ((gm06RotationPermutation rows).symm d).val
    rw [hf]
    change (gm06RotationPredecessors n (rows.map (List.map Fin.val)))[i]? = (List.range n)[i]? at hg
    rw [List.getElem?_eq_getElem hi, List.getElem?_range hin] at hg
    exact Option.some.inj hg

/-- Reversal as a permutation of the finite dart-label space. -/
def gm06DartReversal (m : ℕ) : Equiv.Perm (Fin (2 * m)) where
  toFun d := ⟨gm06DartMate d.val, gm06DartMate_lt d.isLt⟩
  invFun d := ⟨gm06DartMate d.val, gm06DartMate_lt d.isLt⟩
  left_inv d := Fin.ext (gm06DartMate_involutive d.val)
  right_inv d := Fin.ext (gm06DartMate_involutive d.val)

/-- The face successor phi = sigma inverse tau, computed from the rotations. -/
def gm06FacePermutation {m : ℕ} (rows : List (List (Fin (2 * m)))) :
    Equiv.Perm (Fin (2 * m)) :=
  (gm06DartReversal m).trans (gm06RotationPermutation rows).symm

/-- Exact row output directly from rotations, with deterministic label order. -/
def gm06FaceRowsOfRotations {m : ℕ} (rows : List (List (Fin (2 * m)))) :
    List (List (Fin (2 * m))) :=
  gm06FaceRows (gm06FacePermutation rows) (2 * m) (List.finRange (2 * m))

/-- The face rows read from rotations are complete orbits, with each
dart in exactly one row and every row following sigma inverse tau. -/
theorem gm06FaceRowsOfRotations_spec {m : ℕ} (rows : List (List (Fin (2 * m)))) :
    (∀ d, ∃! row, row ∈ gm06FaceRowsOfRotations rows ∧ d ∈ row) ∧
    (∀ row ∈ gm06FaceRowsOfRotations rows, ∃ d,
      row = gm06OrbitTrace (gm06FacePermutation rows) d (2 * m) ∧
      List.IsChain (fun a b => gm06FacePermutation rows a = b) (row ++ [d])) := by
  have hf : Fintype.card (Fin (2 * m)) ≤ 2 * m := by simp
  refine ⟨fun d => gm06FaceRows_unique_row _ _ hf _ List.mem_finRange d, ?_⟩
  intro row hr
  obtain ⟨d, rfl⟩ := (gm06FaceRows_spec (gm06FacePermutation rows) (2 * m) hf
    (List.finRange (2 * m)) List.mem_finRange).2.1 row hr
  exact ⟨d, rfl, gm06OrbitTrace_follows _ _ _ hf⟩

end GraphMinor.Compute
