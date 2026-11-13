module

public import GraphMinor.Compute.GM06OrbitWriter
public import GraphMinor.Compute.GM06ListEncoding
import Mathlib.Data.List.Chain

/-!
# Buffers and row labels for face enumeration

FACE_ROWS in Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
keeps completed rows and the row label of each visited dart. A zero
label means unseen; labels of completed rows start at one. The RAM
output uses the usual length-prefixed row encoding in a buffer.
There are at most as many nonempty rows as darts, so twice the dart
count plus one words suffice. The lemmas here describe these finite
buffers and the exact change made by appending a completed orbit.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Label writes for completed rows, numbered starting after `base`. -/
def gm06FaceOwnerPairs (rows : List (List ℕ)) (base : ℕ := 0) : List (ℕ × ℕ) :=
  (rows.zipIdx base).flatMap (fun p => p.1.map (fun d => (d, p.2 + 1)))

/-- The owner table of completed rows. Zero denotes an unseen dart. -/
def gm06FaceOwners (n : ℕ) (rows : List (List ℕ)) : List ℕ :=
  gm06Scatter (gm06FaceOwnerPairs rows) (List.replicate n 0)

/-- The owner table has one slot per permanent dart label. -/
theorem gm06FaceOwners_length (n : ℕ) (rows : List (List ℕ)) :
    (gm06FaceOwners n rows).length = n := by simp [gm06FaceOwners, gm06Scatter_length]

/-- The keys of owner writes are precisely the darts of the rows. -/
theorem gm06FaceOwnerPairs_keys (rows : List (List ℕ)) (base : ℕ) :
    (gm06FaceOwnerPairs rows base).map Prod.fst = rows.flatten := by
  induction rows generalizing base with
  | nil => rfl
  | cons row rows ih =>
    simp only [gm06FaceOwnerPairs, List.zipIdx_cons, List.flatMap_cons,
      List.map_append, List.map_map, Function.comp_def, List.map_id', List.flatten_cons]
    rw [show (List.flatMap (fun p : List ℕ × ℕ => List.map (fun d => (d, p.2 + 1)) p.1)
      (rows.zipIdx (base + 1))).map Prod.fst = rows.flatten from ih (base + 1)]

/-- Every owner written for a completed row is positive. -/
theorem gm06FaceOwnerPairs_positive (rows : List (List ℕ)) (base : ℕ) :
    ∀ p ∈ gm06FaceOwnerPairs rows base, 0 < p.2 := by
  intro p hp
  obtain ⟨q, _, hp⟩ := List.mem_flatMap.mp hp
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
  exact Nat.succ_pos _

/-- Appending a row adds exactly its owner writes with the next label. -/
theorem gm06FaceOwners_append (n : ℕ) (rows : List (List ℕ)) (row : List ℕ) :
    gm06FaceOwners n (rows ++ [row]) =
      gm06Scatter (row.map (fun d => (d, rows.length + 1))) (gm06FaceOwners n rows) := by
  simp only [gm06FaceOwners, gm06FaceOwnerPairs, List.zipIdx_append,
    List.flatMap_append, List.zipIdx_singleton, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, Nat.zero_add, gm06Scatter_append]

private theorem scatter_zero_iff (pairs : List (ℕ × ℕ)) (table : List ℕ) (d : ℕ)
    (hd : d < table.length) (hp : ∀ p ∈ pairs, 0 < p.2) :
    (gm06Scatter pairs table)[d]? = some 0 ↔
      d ∉ pairs.map Prod.fst ∧ table[d]? = some 0 := by
  induction pairs generalizing table with
  | nil => simp [gm06Scatter]
  | cons p ps ih =>
    rw [gm06Scatter, ih _ (by simpa using hd) (fun q hq => hp q (by simp [hq]))]
    have hpos := hp p List.mem_cons_self
    by_cases hkey : p.1 = d
    · subst d
      simp [List.getElem?_set_self hd, Nat.ne_of_gt hpos]
    · simp only [List.getElem?_set_ne hkey, List.map_cons, List.mem_cons, not_or]
      constructor
      · rintro ⟨hnot, hzero⟩
        exact ⟨⟨Ne.symm hkey, hnot⟩, hzero⟩
      · rintro ⟨⟨_, hnot⟩, hzero⟩
        exact ⟨hnot, hzero⟩

/-- A zero owner is equivalent to absence from all completed rows. -/
theorem gm06FaceOwners_zero_iff (n : ℕ) (rows : List (List ℕ)) (d : ℕ) (hd : d < n) :
    (gm06FaceOwners n rows)[d]? = some 0 ↔ d ∉ rows.flatten := by
  rw [gm06FaceOwners, scatter_zero_iff _ _ _ (by simpa using hd)
    (gm06FaceOwnerPairs_positive rows 0), gm06FaceOwnerPairs_keys]
  simp only [List.getElem?_replicate, hd, ↓reduceIte, and_true]

/-- Length of the usual face-row word encoding. -/
theorem gm06FaceCode_length (rows : List (List ℕ)) :
    (gm06EncodeRows rows).length = 1 + rows.length + rows.flatten.length := by
  have hh : (gm06EncodeRowsPayload rows).length = rows.length + rows.flatten.length := by
    induction rows with
    | nil => rfl
    | cons row rows ih =>
      simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, List.flatten_cons] at *
      omega
  simp only [gm06EncodeRows, List.length_cons, hh]
  omega

private theorem nonempty_rows_length_le {D : Type*} (rows : List (List D))
    (h : ∀ row ∈ rows, row ≠ []) : rows.length ≤ rows.flatten.length := by
  induction rows with
  | nil => exact le_rfl
  | cons row rows ih =>
    have hpos := List.length_pos_iff.mpr (h row List.mem_cons_self)
    have htail := ih (fun r hr => h r (List.mem_cons_of_mem row hr))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

/-- No repeated darts and nonempty rows give a linear word capacity. -/
theorem gm06FaceCode_capacity {n : ℕ} (rows : List (List (Fin n)))
    (hn : rows.flatten.Nodup) (h : ∀ row ∈ rows, row ≠ []) :
    (gm06EncodeRows (rows.map (List.map Fin.val))).length ≤ 1 + 2 * n := by
  have hlen : rows.flatten.length ≤ n := by simpa using hn.length_le_card
  have hrows := nonempty_rows_length_le rows h
  have hfl : (rows.map (List.map Fin.val)).flatten.length = rows.flatten.length := by
    rw [← List.map_flatten, List.length_map]
  rw [gm06FaceCode_length, List.length_map, hfl]
  omega

/-- Zero-padded buffer containing exactly the encoded completed rows. -/
def gm06FaceBuffer (cap : ℕ) (rows : List (List ℕ)) : List ℕ :=
  gm06EncodeRows rows ++ List.replicate (cap - (gm06EncodeRows rows).length) 0

/-- A sufficiently large face buffer has its allocated size. -/
theorem gm06FaceBuffer_length (cap : ℕ) (rows : List (List ℕ))
    (h : (gm06EncodeRows rows).length ≤ cap) : (gm06FaceBuffer cap rows).length = cap := by
  simp only [gm06FaceBuffer, List.length_append, List.length_replicate]
  omega

/-- Replace the new row's header and the total row count after its darts
have been appended. These are exactly the two final writes of a row. -/
theorem gm06FaceBuffer_patch (rows : List (List ℕ)) (row : List ℕ) (rem : ℕ) :
    (((gm06EncodeRows rows ++ [0] ++ row ++ List.replicate rem 0).set
      (gm06EncodeRows rows).length row.length).set 0 (rows.length + 1)) =
      gm06EncodeRows (rows ++ [row]) ++ List.replicate rem 0 := by
  rw [List.append_assoc, List.append_assoc, List.set_append_right _ _ (le_refl _)]
  simp only [Nat.sub_self, List.set_cons_zero, gm06EncodeRows,
    List.cons_append, List.set_cons_zero, List.length_append, List.length_singleton,
    gm06EncodeRowsPayload, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, gm06EncodeNatList, List.append_assoc, List.nil_append]

/-- A cyclic row in natural labels, read from a finite permutation. -/
theorem gm06OrbitTrace_nat_row {n : ℕ} (next : Equiv.Perm (Fin n)) (start : Fin n) :
    ∃ rest : List ℕ,
      (gm06OrbitTrace next start n).map Fin.val = start.val :: rest ∧
      start.val ∉ rest ∧
      List.IsChain (fun a b => (List.ofFn (fun d => (next d).val))[a]? = some b)
        (start.val :: rest ++ [start.val]) ∧ rest.length + 1 ≤ n := by
  have hcard : Fintype.card (Fin n) ≤ n := by simp
  have heq := gm06OrbitTrace_eq_iterate next start n hcard
  have hp : 0 < Function.minimalPeriod next start :=
    Function.minimalPeriod_pos_of_mem_periodicPts (next.injective.mem_periodicPts start)
  have hhead : (gm06OrbitTrace next start n).head? = some start := by
    rw [heq]
    cases hper : Function.minimalPeriod next start with
    | zero => omega
    | succ p => rfl
  obtain ⟨tail, htail⟩ : ∃ tail, gm06OrbitTrace next start n = start :: tail :=
    List.head?_eq_some_iff.mp hhead
  refine ⟨tail.map Fin.val, by simp [htail], ?_, ?_, ?_⟩
  · have hn := gm06OrbitTrace_nodup next start n hcard
    rw [htail, List.nodup_cons] at hn
    simpa only [List.mem_map, Fin.val_inj, exists_eq_right] using hn.1
  · have hc := gm06OrbitTrace_follows next start n hcard
    rw [htail] at hc
    have hm := List.isChain_map_of_isChain Fin.val
      (S := fun a b => (List.ofFn (fun d => (next d).val))[a]? = some b)
      (fun a b hab => by simp [hab]) hc
    simpa only [List.map_append, List.map_cons, List.map_nil] using hm
  · have hl := (gm06OrbitTrace_nodup next start n hcard).length_le_card
    rw [htail] at hl
    simpa only [List.length_map, List.length_cons, Fintype.card_fin] using hl

end GraphMinor.Compute
