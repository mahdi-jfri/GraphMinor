module

public import GraphMinor.Compute.GM06CutMarkFacts
public import GraphMinor.Compute.GM06FaceIncidence

/-!
# Active copied-end bits from the induced rows

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) retains
exactly the ends listed in the induced copied rotations. The origin pass
marks each such end by writing one. This file proves that the
result is exactly the dense membership table, even when a label
is written more than once. Filtering its permanent label space
therefore gives the pure sorted active-dart list.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem scatter_ones_zero_iff (labels table : List ℕ) (d : ℕ) (hd : d < table.length) :
    (gm06Scatter (labels.map (fun x => (x, 1))) table)[d]? = some 0 ↔ d ∉ labels ∧ table[d]? = some 0 := by
  induction labels generalizing table with
  | nil => simp [gm06Scatter]
  | cons x xs ih =>
    rw [List.map_cons, gm06Scatter, ih _ (by simpa using hd)]
    by_cases hx : x = d
    · subst x
      simp [List.getElem?_set_self hd]
    · simp only [List.getElem?_set_ne hx, List.mem_cons, not_or]
      constructor
      · rintro ⟨hnot, hz⟩
        exact ⟨⟨Ne.symm hx, hnot⟩, hz⟩
      · rintro ⟨⟨_, hnot⟩, hz⟩
        exact ⟨hnot, hz⟩

/-- Each in-range bit of the one-write scatter is exactly membership
in its source label list, with zero for absent labels. -/
theorem gm06CutActiveScatter_getElem? (q : ℕ) (labels : List ℕ) (d : ℕ) (hd : d < q) :
    (gm06Scatter (labels.map (fun x => (x, 1))) (List.replicate q 0))[d]? =
      some (if d ∈ labels then 1 else 0) := by
  let table := gm06Scatter (labels.map (fun x => (x, 1))) (List.replicate q 0)
  have hlen : table.length = q := by simp only [table, gm06Scatter_length, List.length_replicate]
  have hidx : d < table.length := hlen ▸ hd
  have hbits : ∀ x ∈ table, x = 0 ∨ x = 1 := by
    apply gm06Scatter_forall
    · intro p hp
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
      exact Or.inr rfl
    · intro x hx
      exact Or.inl (List.mem_replicate.mp hx).2
  have hzero : table[d]? = some 0 ↔ d ∉ labels := by
    dsimp only [table]
    rw [scatter_ones_zero_iff _ _ _ (by simpa using hd)]
    simp only [List.getElem?_replicate, hd, ↓reduceIte, and_true]
  change table[d]? = _
  by_cases hm : d ∈ labels
  · have hnotzero : table[d] ≠ 0 := by
      intro hz
      exact (hzero.mp (by rw [List.getElem?_eq_getElem hidx, hz])) hm
    have hone : table[d] = 1 := (hbits _ (List.getElem_mem hidx)).resolve_left hnotzero
    rw [List.getElem?_eq_getElem hidx, hone, ite_eq_left hm]
  · simpa only [hm, ↓reduceIte] using hzero.mpr hm

/-- Scattering one at all listed labels computes exactly the dense
membership function used for later component and face scans. -/
theorem gm06CutActiveScatter_eq (q : ℕ) (labels : List ℕ) :
    gm06Scatter (labels.map (fun x => (x, 1))) (List.replicate q 0) = gm06IncidenceBits q labels := by
  apply List.ext_getElem
  · simp only [gm06Scatter_length, List.length_replicate, gm06IncidenceBits, List.length_ofFn]
  · intro i hi hi'
    have hiq : i < q := by simpa only [gm06Scatter_length, List.length_replicate] using hi
    have he := gm06CutActiveScatter_getElem? q labels i hiq
    rw [List.getElem?_eq_getElem hi] at he
    simpa only [gm06IncidenceBits, List.getElem_ofFn] using Option.some.inj he

/-- The increasing active-dart list is precisely the range filtered
by the bitmap that the origin pass computes. -/
theorem gm06CutActiveDarts_eq_bits (m : ℕ) (rows : List (List ℕ)) :
    gm06CutActiveDarts m rows = (List.range (4 * m)).filter
      (fun d => (gm06IncidenceBits (4 * m) rows.flatten)[d]?.getD 0 == 1) := by
  apply List.filter_congr
  intro d hd
  have hb : d < 4 * m := List.mem_range.mp hd
  simp only [gm06IncidenceBits, List.getElem?_ofFn, hb, ↓reduceDIte, Option.getD_some]
  by_cases hm : d ∈ rows.flatten <;> simp only [hm, ↓reduceIte, decide_true, decide_false] <;> rfl

end GraphMinor.Compute
