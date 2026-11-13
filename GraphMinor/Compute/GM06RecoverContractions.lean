module

public import GraphMinor.Compute.GM06RestorePathWord
import GraphMinor.Compute.GM06RefreshContractedMasks
import Mathlib.Data.List.Induction

/-!
# Reversing the computed contraction history

The adaptation of VI (5.7), page 133, recovers an output linkage
through earlier reductions. Contractions record pairs of a path
index and its removed first edge. Read those pairs from the end
of the history and prepend each edge to its current output row.
The loop uses the stored record count, leaves the history fixed
and stops after exactly that many records. The output encoding
grows by one word per contraction and the time bound is polynomial.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- History pairs use two consecutive words, in the order in which
the contractions were performed. -/
@[expose] def gm06ContractionHistoryWords (records : List (ℕ × ℕ)) : List ℕ :=
  records.flatMap (fun p => [p.1, p.2])

/-- Restore the records in reverse order to the current output rows. -/
@[expose] def gm06RecoverContractionRows (records : List (ℕ × ℕ)) (rows : List (List ℕ)) :
    List (List ℕ) :=
  records.foldr (fun p rs => rs.set p.1 (p.2 :: (rs[p.1]?.getD []))) rows

/-- One recovery iteration pops the record count, reads its pair
and prepends that directed edge to its current output path. -/
@[expose] def gm06RecoverContractionBody : Cmd :=
  .seq (.assign 309 (.op .sub (.reg 309) (.const 1)))
    (.seq (.assign 295 (.read 9 (.op .mul (.const 2) (.reg 309))))
      (.seq (.assign 23 (.read 9 (.op .add (.op .mul (.const 2) (.reg 309)) (.const 1))))
        gm06RestorePathWordProg))

/-- Undo all recorded contractions, starting at the newest record. -/
@[expose] def gm06RecoverContractionsProg : Cmd :=
  .while (.op .lt (.const 0) (.reg 309)) gm06RecoverContractionBody

private theorem history_words_length (records : List (ℕ × ℕ)) :
    (gm06ContractionHistoryWords records).length = 2 * records.length := by
  induction records with
  | nil => rfl
  | cons r records ih =>
    simp only [gm06ContractionHistoryWords, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_nil] at *
    omega

private theorem history_words_append (xs ys : List (ℕ × ℕ)) :
    gm06ContractionHistoryWords (xs ++ ys) =
      gm06ContractionHistoryWords xs ++ gm06ContractionHistoryWords ys := by
  simp only [gm06ContractionHistoryWords, List.flatMap_append]

private theorem row_words_lt {w : ℕ} (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) : ∀ x ∈ rows[i], x < 2 ^ w := by
  intro x hm
  apply hx x
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨rows[i], List.getElem_mem hi, by simp [gm06EncodeNatList, hm]⟩

/-- The history loop reads every stored pair in reverse order and
computes exactly the corresponding path-row updates. The history
and other instance fields are preserved, the count becomes zero,
and the encoding grows by precisely the number of records. -/
theorem gm06RecoverContractionsProg_exec {w : ℕ} (records : List (ℕ × ℕ))
    (rows : List (List ℕ)) (tail : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : (gm06EncodeRows rows).length + records.length < 2 ^ w)
    (hhist : (gm06ContractionHistoryWords records ++ tail).length < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hr : ∀ p ∈ records, p.1 < rows.length ∧ p.2 < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows)
    (h9 : s.arrs 9 = gm06ContractionHistoryWords records ++ tail)
    (h309 : s.regs 309 = records.length) :
    ∃ s' t, Exec w gm06RecoverContractionsProg s s' t ∧
      t ≤ 3 + records.length * (400 + 300 * ((gm06EncodeRows rows).length + records.length)) ∧
      Keeps [309, 295, 23, 31, 7, 8, 9, 11, 313, 4, 323, 324, 98] [24, 27, 25, 8, 28] s s' ∧
      s'.regs 309 = 0 ∧ s'.arrs 8 = gm06EncodeRows (gm06RecoverContractionRows records rows) ∧
      (s'.arrs 8).length = (gm06EncodeRows rows).length + records.length := by
  induction records using List.reverseRecOn generalizing rows tail s with
  | nil =>
    refine ⟨s, 3, ?_, by simp, Keeps.refl _ _ s, h309, ?_, ?_⟩
    · exact .while_false (by simp [Expr.eval, h309, checkWord, BinOp.eval, BinOp.raw])
    · simpa only [gm06RecoverContractionRows, List.foldr_nil] using h8
    · simp only [h8, List.length_nil, Nat.add_zero]
  | append_singleton records p ih =>
    have hlenRec : (records ++ [p]).length = records.length + 1 := by simp
    have hp : p.1 < rows.length ∧ p.2 < 2 ^ w := hr p (by simp)
    have hpre : ∀ r ∈ records, r.1 < rows.length ∧ r.2 < 2 ^ w :=
      fun r hm => hr r (by simp [hm])
    have h9' : s.arrs 9 = (gm06ContractionHistoryWords records ++ [p.1, p.2]) ++ tail := by
      rw [h9, history_words_append]
      rfl
    have hhistLen : (gm06ContractionHistoryWords records ++ [p.1, p.2] ++ tail).length < 2 ^ w := by
      rw [history_words_append] at hhist
      exact hhist
    have hc : records.length + 1 < 2 ^ w := by
      simp only [List.length_append, List.length_cons, List.length_nil, history_words_length] at hhistLen
      omega
    have hc0 : records.length < 2 ^ w := by omega
    have hpos : 2 * records.length + 1 < (s.arrs 9).length := by
      rw [h9', List.length_append, List.length_append, history_words_length]
      simp only [List.length_cons, List.length_nil]
      omega
    have harrLen : (s.arrs 9).length < 2 ^ w := by rw [h9]; exact hhist
    have hposw : 2 * records.length + 1 < 2 ^ w := hpos.trans harrLen
    have hget0 : (s.arrs 9)[2 * records.length]? = some p.1 := by
      rw [h9', List.append_assoc, List.getElem?_append_right
        (l₁ := gm06ContractionHistoryWords records) (by rw [history_words_length])]
      rw [history_words_length]
      simp
    have hget1 : (s.arrs 9)[2 * records.length + 1]? = some p.2 := by
      rw [h9', List.append_assoc, List.getElem?_append_right
        (l₁ := gm06ContractionHistoryWords records) (by rw [history_words_length]; omega)]
      rw [history_words_length]
      simp
    have hpos0 : 2 * records.length < (s.arrs 9).length := by omega
    have hval0 : (s.arrs 9)[2 * records.length]'hpos0 = p.1 := by
      simpa only [List.getElem?_eq_getElem hpos0, Option.some.injEq] using hget0
    have hval1 : (s.arrs 9)[2 * records.length + 1]'hpos = p.2 := by
      simpa only [List.getElem?_eq_getElem hpos, Option.some.injEq] using hget1
    have hindex : p.1 < 2 ^ w := by
      have hcount := hx rows.length (by simp [gm06EncodeRows])
      exact hp.1.trans hcount
    let s₁ := s.setReg 309 records.length
    have he₁ : Exec w (.assign 309 (.op .sub (.reg 309) (.const 1))) s s₁ 4 := by
      have hh := GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg (h309.trans hlenRec) hc)
        (GraphMinor.Compute.Crossing.eval_const (show 1 < 2 ^ w by omega))
      simpa only [Nat.add_sub_cancel, Expr.cost, Nat.reduceAdd] using Exec.assign (r := 309) hh
    let s₂ := s₁.setReg 295 p.1
    have he₂ : Exec w (.assign 295 (.read 9 (.op .mul (.const 2) (.reg 309)))) s₁ s₂ 5 := by
      have hh := GraphMinor.Compute.Crossing.eval_read (a := 9) (s := s₁)
        (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
          (GraphMinor.Compute.Crossing.eval_reg (r := 309) (by simp [s₁]) hc0) (by omega))
        (by simpa [s₁] using (show 2 * records.length < (s.arrs 9).length by omega))
        (by have hh := hget0; rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hh; simpa [s₁, hh] using hindex)
      exact .assign (hh.trans (congrArg some hval0))
    let s₃ := s₂.setReg 23 p.2
    have he₃ : Exec w (.assign 23 (.read 9 (.op .add (.op .mul (.const 2) (.reg 309)) (.const 1)))) s₂ s₃ 7 := by
      have hh := GraphMinor.Compute.Crossing.eval_read (a := 9) (s := s₂)
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
            (GraphMinor.Compute.Crossing.eval_reg (r := 309) (by simp [s₂, s₁]) hc0) (by omega))
          (GraphMinor.Compute.Crossing.eval_const (show 1 < 2 ^ w by omega)) (by omega))
        (by simpa [s₂, s₁] using hpos)
        (by have hh := hget1; rw [List.getElem?_eq_getElem hpos, Option.some.injEq] at hh; simpa [s₂, s₁, hh] using hp.2)
      exact .assign (hh.trans (congrArg some hval1))
    let R := [309, 295, 23, 31, 7, 8, 9, 11, 313, 4, 323, 324, 98]
    let A := [24, 27, 25, 8, 28]
    have hk₀ : Keeps R A s s₃ :=
      (((Keeps.refl _ _ s).setReg (by simp [R]) _).setReg (by simp [R]) _).setReg (by simp [R]) _
    obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hout₄, hlen₄⟩ := gm06RestorePathWordProg_exec
      rows p.1 p.2 hp.1 s₃ (by omega) (by rw [hlenRec] at hn; omega) hx hp.2
      (by simpa [s₃, s₂, s₁] using h8) (by simp [s₃, s₂]) (by simp [s₃])
    have hk₄' : Keeps R A s s₄ := hk₀.trans hk₄ (by simp [R]) (by simp [A])
    let rows₁ := rows.set p.1 (p.2 :: rows[p.1])
    have hnewlen : (gm06EncodeRows rows₁).length = (gm06EncodeRows rows).length + 1 := by
      rw [hout₄] at hlen₄
      exact hlen₄
    have hrowlen : rows[p.1].length < (gm06EncodeRows rows).length := by
      rw [gm06EncodeRows_length]
      have hh : rows[p.1].length ≤ rows.flatten.length :=
        (List.sublist_flatten_of_mem (List.getElem_mem hp.1)).length_le
      omega
    have hcount : rows.length < (gm06EncodeRows rows).length := by rw [gm06EncodeRows_length]; omega
    have hwords₁ : ∀ x ∈ gm06EncodeRows rows₁, x < 2 ^ w := gm06EncodeRows_set_words
      rows p.1 hp.1 (p.2 :: rows[p.1]) hx
      (by intro x hm; rcases List.mem_cons.mp hm with rfl | hm; exact hp.2; exact row_words_lt rows hp.1 hx x hm)
      (by simp only [List.length_cons]; rw [hlenRec] at hn; omega)
    obtain ⟨s₅, t₅, he₅, ht₅, hk₅, hzero, hout₅, hlen₅⟩ := ih rows₁
      ([p.1, p.2] ++ tail) s₄
      (by rw [hnewlen]; rw [hlenRec] at hn; omega)
      (by simpa only [List.append_assoc] using hhistLen) hwords₁
      (by simpa only [rows₁, List.length_set] using hpre) hout₄
      (by simpa only [List.append_assoc] using (hk₄'.2 9 (by decide)).trans h9')
      (by simpa [s₃, s₂, s₁] using hk₄.1 309 (by decide))
    have hcond : (Expr.op .lt (.const 0) (.reg 309)).eval w s = some 1 := by
      have hh := GraphMinor.Compute.Crossing.eval_lt
        (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
        (GraphMinor.Compute.Crossing.eval_reg (h309.trans hlenRec) hc) (by omega)
      simpa using hh
    have heBody : Exec w gm06RecoverContractionBody s s₄ (4 + (5 + (7 + t₄))) :=
      .seq he₁ (.seq he₂ (.seq he₃ he₄))
    refine ⟨s₅, 3 + (4 + (5 + (7 + t₄))) + t₅,
      .while_true hcond (by decide) heBody he₅, ?_,
      hk₄'.trans hk₅ (by simp [R]) (by simp [A]), hzero, ?_, ?_⟩
    · rw [hnewlen] at ht₅
      rw [hlenRec]
      have hN : (gm06EncodeRows rows).length + 1 + records.length =
          (gm06EncodeRows rows).length + (records.length + 1) := by omega
      rw [hN] at ht₅
      rw [Nat.add_mul, Nat.one_mul]
      omega
    · have hget : rows[p.1]?.getD [] = rows[p.1] := by simp [List.getElem?_eq_getElem hp.1]
      simpa only [gm06RecoverContractionRows, List.foldr_append, List.foldr_cons,
        List.foldr_nil, hget, rows₁] using hout₅
    · rw [hlen₅, hnewlen, hlenRec]
      omega

end GraphMinor.Compute
