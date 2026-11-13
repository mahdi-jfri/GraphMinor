module

public import GraphMinor.Compute.GM06CutOutput
public import GraphMinor.Compute.GM06CutAlongLinkageProgram
import GraphMinor.Compute.GM06CutBufferBounds

/-!
# Recovering the stored records of the computed cut

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns the
component rotations as consecutive records. The cut specification
parses those records into finite graph data. The parser equations
below also recover their actual stored prefix and common origins.
Thus the phase's record reader can use the cut output directly.
-/

@[expose] public section
namespace GraphMinor.Compute

private theorem readNatList_some {words row tail : List ℕ}
    (h : gm06ReadNatList words = some (row, tail)) :
    words = gm06EncodeNatList row ++ tail := by
  cases words with
  | nil => simp [gm06ReadNatList] at h
  | cons n words =>
    change (if n ≤ words.length then some (words.take n, words.drop n) else none) = some (row, tail) at h
    split at h
    next hn =>
      have he := Option.some.inj h
      have hr : words.take n = row := congrArg Prod.fst he
      have ht : words.drop n = tail := congrArg Prod.snd he
      rw [← hr, ← ht]
      have hl : (words.take n).length = n := by simp only [List.length_take, Nat.min_eq_left hn]
      simp only [gm06EncodeNatList, hl, List.cons_append, List.take_append_drop]
    next hn => contradiction

private theorem readRowsAux_some {count : ℕ} {words tail : List ℕ} {rows : List (List ℕ)}
    (h : gm06ReadRowsAux count words = some (rows, tail)) :
    rows.length = count ∧ words = gm06EncodeRowsPayload rows ++ tail := by
  induction count generalizing words rows tail with
  | zero =>
    have he := Option.some.inj h
    have hr : [] = rows := congrArg Prod.fst he
    have ht : words = tail := congrArg Prod.snd he
    subst rows
    exact ⟨rfl, by simpa [gm06EncodeRowsPayload] using ht⟩
  | succ count ih =>
    unfold gm06ReadRowsAux at h
    cases hfirst : gm06ReadNatList words with
    | none => simp [hfirst] at h
    | some first =>
      obtain ⟨row, rest⟩ := first
      simp only [hfirst, Option.bind_eq_bind, Option.bind_some, Prod.fst, Prod.snd] at h
      cases hrest : gm06ReadRowsAux count rest with
      | none => simp [hrest] at h
      | some result =>
        obtain ⟨rows', tail'⟩ := result
        simp only [hrest, Option.bind_eq_bind, Option.bind_some, Prod.fst, Prod.snd, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hc, hr⟩ := ih hrest
        refine ⟨by simpa only [List.length_cons] using congrArg (· + 1) hc, ?_⟩
        rw [readNatList_some hfirst, hr]
        simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc]

private theorem readRows_some {words tail : List ℕ} {rows : List (List ℕ)}
    (h : gm06ReadRows words = some (rows, tail)) : words = gm06EncodeRows rows ++ tail := by
  cases words with
  | nil => simp [gm06ReadRows] at h
  | cons count words =>
    obtain ⟨hc, hr⟩ := readRowsAux_some h
    simp only [gm06EncodeRows, List.cons_append]
    rw [hc, hr]

private theorem readComponentRotationsAux_some {count : ℕ} {words tail : List ℕ}
    {records : List (List (List ℕ))}
    (h : gm06ReadComponentRotationsAux count words = some (records, tail)) :
    records.length = count ∧ words = records.flatMap gm06EncodeRows ++ tail := by
  induction count generalizing words records tail with
  | zero =>
    have he := Option.some.inj h
    have hr : [] = records := congrArg Prod.fst he
    have ht : words = tail := congrArg Prod.snd he
    subst records
    exact ⟨rfl, by simpa using ht⟩
  | succ count ih =>
    unfold gm06ReadComponentRotationsAux at h
    cases hfirst : gm06ReadRows words with
    | none => simp [hfirst] at h
    | some first =>
      obtain ⟨rows, rest⟩ := first
      simp only [hfirst, Option.bind_eq_bind, Option.bind_some, Prod.fst, Prod.snd] at h
      cases hrest : gm06ReadComponentRotationsAux count rest with
      | none => simp [hrest] at h
      | some result =>
        obtain ⟨records', tail'⟩ := result
        simp only [hrest, Option.bind_eq_bind, Option.bind_some, Prod.fst, Prod.snd, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hc, hr⟩ := ih hrest
        refine ⟨by simpa only [List.length_cons] using congrArg (· + 1) hc, ?_⟩
        rw [readRows_some hfirst, hr]
        simp only [List.flatMap_cons, List.append_assoc]

/-- Successfully parsed component rotations occur as an actual
length-prefixed prefix of their source buffer. -/
theorem gm06ReadComponentRotations_some {words tail : List ℕ}
    {records : List (List (List ℕ))}
    (h : gm06ReadComponentRotations words = some (records, tail)) :
    words = records.length :: (records.flatMap gm06EncodeRows ++ tail) := by
  cases words with
  | nil => simp [gm06ReadComponentRotations] at h
  | cons count words =>
    obtain ⟨hc, hr⟩ := readComponentRotationsAux_some h
    rw [hc, hr]

private theorem decoded_rotations (n : ℕ) (origins active : List ℕ)
    (masks : List (List ℕ)) (rotations : List (List (List ℕ)))
    (hlen : masks.length = rotations.length) :
    ((masks.zip rotations).map (fun p => gm06DecodeCutComponentRecord n origins active p.1 p.2)).map
      GM06CutData.rotations = rotations := by
  induction masks generalizing rotations with
  | nil =>
    have hr : rotations = [] := List.eq_nil_iff_length_eq_zero.mpr hlen.symm
    simp [hr]
  | cons mask masks ih =>
    cases rotations with
    | nil => simp at hlen
    | cons rows rotations =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simpa only [List.zip_cons_cons, List.map_cons, gm06DecodeCutComponentRecord] using
        congrArg (rows :: ·) (ih rotations hlen)

/-- The cut's parsed finite result determines both the physical
rotation-record prefix and the common origin table used by every component. -/
theorem gm06CutAlongLinkageResult_records {s : State} {parts : List GM06CutData}
    (h : gm06CutAlongLinkageResult s = some parts) :
    ∃ tail, gm06CutMaterializeResult s = parts.length ::
        ((parts.map GM06CutData.rotations).flatMap gm06EncodeRows ++ tail) ∧
      ∀ part ∈ parts, part.origins = s.arrs 626 := by
  unfold gm06CutAlongLinkageResult at h
  cases hmask : gm06ReadRows (s.arrs 600) with
  | none => simp [hmask] at h
  | some maskResult =>
    obtain ⟨masks, maskTail⟩ := maskResult
    simp only [hmask, Option.bind_eq_bind, Option.bind_some, Prod.fst, Prod.snd] at h
    cases hrot : gm06ReadComponentRotations (gm06CutMaterializeResult s) with
    | none => simp [hrot] at h
    | some rotResult =>
      obtain ⟨rotations, tail⟩ := rotResult
      simp only [hrot, Option.bind_eq_bind, Option.bind_some, Prod.fst, Prod.snd] at h
      split at h
      next hlen =>
        have hparts := Option.some.inj h
        have hr := decoded_rotations (s.regs 620) (s.arrs 626) (s.arrs 628) masks rotations hlen
        rw [hparts] at hr
        have hl : parts.length = rotations.length := by
          have hh := congrArg List.length hr
          simpa only [List.length_map] using hh
        refine ⟨tail, ?_, ?_⟩
        · rw [gm06ReadComponentRotations_some hrot, hl, hr]
        · intro part hp
          rw [← hparts] at hp
          obtain ⟨p, _, rfl⟩ := List.mem_map.mp hp
          rfl
      next hlen => contradiction

/-- The actual component record prefix occurs in the physical array,
including any unused capacity after the materialized records. -/
theorem gm06CutAlongLinkageResult_array_records {s : State} {parts : List GM06CutData}
    (h : gm06CutAlongLinkageResult s = some parts) :
    ∃ tail, s.arrs 601 = parts.length ::
      ((parts.map GM06CutData.rotations).flatMap gm06EncodeRows ++ tail) := by
  obtain ⟨tail, hp, _⟩ := gm06CutAlongLinkageResult_records h
  refine ⟨tail ++ (s.arrs 601).drop (s.regs 655), ?_⟩
  have hsplit := List.take_append_drop (s.regs 655) (s.arrs 601)
  change (s.arrs 601).take (s.regs 655) = _ at hp
  rw [hp] at hsplit
  simpa only [List.cons_append, List.append_assoc] using hsplit.symm

private theorem materialize_buffer_bounds {w : ℕ} (inner : List ℕ) (s sf : State) (t : ℕ)
    (hw : 1 < 2 ^ w) (hk : inner.length < 2 ^ w) (hcode : (s.arrs 625).length < 2 ^ w)
    (hfit : 3 + inner.length * (s.arrs 625).length < 2 ^ w) (h609 : s.arrs 609 = inner)
    (he : Exec w gm06CutMaterializeProg s sf t) :
    (sf.arrs 601).length = 1 + inner.length * (s.arrs 625).length ∧
      ∀ a ∈ sf.arrs 601, a < 2 ^ w := by
  cases he with
  | @seq _ _ _ sm _ _ _ hi hl =>
    obtain ⟨si, ti, hei, _, _, hb, _, _⟩ := gm06CutMaterializeInitProg_exec inner s hw hk hcode hfit h609
    have heq := (hei.deterministic hi).1
    subst si
    have hlen : (sm.arrs 601).length = 1 + inner.length * (s.arrs 625).length := by
      rw [hb.1]
      simp only [List.length_append, List.length_singleton, List.length_replicate]
    have hwords : ∀ a ∈ sm.arrs 601, a < 2 ^ w := by
      intro a ha
      rw [hb.1] at ha
      rcases List.mem_append.mp ha with ha | ha
      · have heq : a = inner.length := by simpa only [List.mem_singleton] using ha
        exact heq ▸ hk
      · have heq := (List.mem_replicate.mp ha).2
        exact heq ▸ Nat.two_pow_pos w
    exact ⟨(gm06Exec_length_eq hl 601 (by decide)).trans hlen, hl.arrs_lt 601 hwords⟩

/-- The complete cut allocates its component records from the actual
cuff count and common rotation buffer. The final array has this exact
polynomial capacity and contains only words, regardless of old scratch. -/
theorem gm06CutAlongLinkageProg_record_bounds {w : ℕ} (rows : List (List ℕ)) (inner : List ℕ)
    (s sf : State) (t : ℕ) (hw : 2 < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h609 : s.arrs 609 = inner)
    (hrotFit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hfit : 3 + inner.length * (1 + 2 * (gm06EncodeRows rows).length) < 2 ^ w)
    (he : Exec w gm06CutAlongLinkageProg s sf t) :
    (sf.arrs 601).length = 1 + inner.length * (1 + 2 * (gm06EncodeRows rows).length) ∧
      ∀ a ∈ sf.arrs 601, a < 2 ^ w := by
  cases he with
  | seq hcuff htail =>
    have hinner := hcuff.arrs_eq_of_not_mem_writtenArrs (a := 609) (by decide)
    cases hcuff with
    | seq hsearch hmask =>
      have hphys := gm06CutSearchGraphProg_output_bounds rows _ _ _ hw h600 hrotFit hsearch
      have hkeep₁ := hmask.arrs_eq_of_not_mem_writtenArrs (a := 625) (by decide)
      cases htail with
      | seq hsize hpost =>
        have hkeep₂ := hsize.arrs_eq_of_not_mem_writtenArrs (a := 625) (by decide)
        have hinner₂ := hsize.arrs_eq_of_not_mem_writtenArrs (a := 609) (by decide)
        cases hpost with
        | seq hbits hmat =>
          have hkeep₃ := hbits.arrs_eq_of_not_mem_writtenArrs (a := 625) (by decide)
          have hbefore := (congrArg List.length (hkeep₃.trans (hkeep₂.trans hkeep₁))).trans hphys.1
          have hinner₃ := (hbits.arrs_eq_of_not_mem_writtenArrs (a := 609) (by decide)).trans
            (hinner₂.trans (hinner.trans h609))
          have hkw : inner.length < 2 ^ w := by nlinarith only [hfit]
          obtain ⟨hlen, hwords⟩ := materialize_buffer_bounds inner _ sf _ (by omega) hkw
            (by rw [hbefore]; omega) (by rw [hbefore]; exact hfit) hinner₃ hmat
          exact ⟨hlen.trans (by rw [hbefore]), hwords⟩

end GraphMinor.Compute
