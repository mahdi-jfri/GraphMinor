module

public import GraphMinor.Compute.GM06SpliceRotations
public import GraphMinor.Compute.GM06SelectRow
public import GraphMinor.Compute.TwoPathsNorm
import GraphMinor.Compute.GM06RowPositions
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Installing a changed rotation row

The contraction in VI (5.7), page 133, changes the rotation at the
initial vertex and clears the retired vertex's row. To replace a
length-prefixed row, copy the preceding words, write the new header,
copy the new row and copy the unchanged suffix. The program locates
the old row by its ordinary input index. The proof identifies the
result with the encoding of list replacement, including empty rows.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy the words before and after a selected row around its
replacement in array 27. Registers 323 and 324 delimit the old row. -/
@[expose] def gm06ReplaceRotationRowCore : Cmd :=
  .seq (.alloc 28 (.op .add (.op .sub (.len 4) (.len 25)) (.len 27)))
    (.seq (gm06RotationSliceProg 4 28 (.reg 323) (.const 0) (.const 0))
      (.seq (.write 28 (.reg 323) (.len 27))
        (.seq (gm06RotationSliceProg 27 28 (.len 27) (.const 0)
          (.op .add (.reg 323) (.const 1)))
          (.seq (gm06RotationSliceProg 4 28 (.op .sub (.len 4) (.reg 324)) (.reg 324)
            (.op .add (.op .add (.reg 323) (.const 1)) (.len 27)))
            (copyProg 4 28)))))

/-- Copying the prefix, new header and row, and suffix replaces
precisely the selected row while preserving every other input field. -/
theorem gm06ReplaceRotationRowCore_exec {w : ℕ} (pre oldrow row tail : List ℕ)
    (s : State) (hw : 1 < 2 ^ w)
    (hn : (pre ++ oldrow.length :: oldrow ++ tail).length < 2 ^ w)
    (hn' : (pre ++ row.length :: row ++ tail).length < 2 ^ w)
    (hx : ∀ x ∈ pre ++ oldrow.length :: oldrow ++ tail, x < 2 ^ w)
    (hy : ∀ x ∈ row, x < 2 ^ w)
    (h4 : s.arrs 4 = pre ++ oldrow.length :: oldrow ++ tail)
    (h25 : s.arrs 25 = oldrow) (h27 : s.arrs 27 = row)
    (h323 : s.regs 323 = pre.length)
    (h324 : s.regs 324 = pre.length + 1 + oldrow.length) :
    ∃ s' t, Exec w gm06ReplaceRotationRowCore s s' t ∧
      t ≤ 100 + 80 * ((pre ++ oldrow.length :: oldrow ++ tail).length + row.length) ∧
      Keeps [313, 98] [4, 28] s s' ∧
      s'.arrs 4 = pre ++ row.length :: row ++ tail := by
  let xs := pre ++ oldrow.length :: oldrow ++ tail
  let out := pre ++ row.length :: row ++ tail
  change xs.length < 2 ^ w at hn
  change out.length < 2 ^ w at hn'
  change s.arrs 4 = xs at h4
  change ∀ x ∈ xs, x < 2 ^ w at hx
  have hlen : xs.length = pre.length + 1 + oldrow.length + tail.length := by
    simp only [xs, List.length_append, List.length_cons]; omega
  have hlen' : out.length = pre.length + 1 + row.length + tail.length := by
    simp only [out, List.length_append, List.length_cons]; omega
  have holdw : oldrow.length < 2 ^ w := by omega
  have hroww : row.length < 2 ^ w := by omega
  have hprew : pre.length < 2 ^ w := by omega
  have hendw : pre.length + 1 + oldrow.length < 2 ^ w := by omega
  have hnewwords : ∀ x ∈ out, x < 2 ^ w := by
    intro x hm
    have hm' : x ∈ pre ++ (row.length :: (row ++ tail)) := by
      simpa only [out, List.append_assoc, List.cons_append] using hm
    rcases List.mem_append.mp hm' with hp | hr
    · exact hx x (by simp [xs, hp])
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hroww
      · rcases List.mem_append.mp hr with hr | ht
        · exact hy x hr
        · exact hx x (by simp [xs, ht])
  let s₀ := s.setArr 28 (List.replicate out.length 0)
  have he₀ : Exec w (.alloc 28 (.op .add (.op .sub (.len 4) (.len 25)) (.len 27)))
      s s₀ (5 + out.length) := by
    have hh := GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_len h4 hn)
        (GraphMinor.Compute.Crossing.eval_len h25 holdw))
      (GraphMinor.Compute.Crossing.eval_len h27 hroww)
      (show xs.length - oldrow.length + row.length < 2 ^ w by omega)
    have heq : xs.length - oldrow.length + row.length = out.length := by omega
    change (Expr.op .add (.op .sub (.len 4) (.len 25)) (.len 27)).eval w s = some _ at hh
    rw [heq] at hh
    exact .alloc hh
  have hk₀ : Keeps [313] [28] s s₀ := (Keeps.refl _ _ s).setArr (by simp) _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06RotationSliceProg_exec
    4 28 (by decide) (.reg 323) (.const 0) (.const 0) xs [] 0 pre.length out.length s₀
    hw hn (by omega) hx (by omega) (by simpa only [List.length_nil, Nat.zero_add] using hn')
    (by simpa [s₀] using h4) (by simp [s₀])
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 323 (by decide)).trans (by simpa [s₀] using h323)) hprew)
    (fun _ _ => GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    (fun _ _ => by simp [Expr.eval, checkWord])
  have hk₁' : Keeps [313] [28] s s₁ := hk₀.trans hk₁ (by simp) (by simp)
  have htake : xs.take pre.length = pre := by
    simp only [xs, List.append_assoc]
    exact List.take_left
  have hd₁' : s₁.arrs 28 = pre ++ List.replicate (1 + row.length + tail.length) 0 := by
    have hr : out.length - pre.length = 1 + row.length + tail.length := by omega
    simpa only [List.drop_zero, htake, List.nil_append, hr] using hd₁
  let s₂ := s₁.writeArr 28 pre.length row.length
  have he₂ : Exec w (.write 28 (.reg 323) (.len 27)) s₁ s₂ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_reg ((hk₁'.1 323 (by decide)).trans h323) hprew)
      (GraphMinor.Compute.Crossing.eval_len ((hk₁'.2 27 (by decide)).trans h27) hroww)
      (by rw [hd₁']; simp only [List.length_append, List.length_replicate]; omega)
  have hk₂ : Keeps [313] [28] s s₂ := hk₁'.writeArr (by simp) _ _
  have hd₂ : s₂.arrs 28 = (pre ++ [row.length]) ++ List.replicate (row.length + tail.length) 0 := by
    simp only [s₂, State.writeArr_arrs_self, hd₁']
    rw [List.set_append_right pre.length row.length (Nat.le_refl _)]
    simp only [Nat.sub_self]
    have hr : 1 + row.length + tail.length = (row.length + tail.length) + 1 := by omega
    rw [hr, List.replicate_succ, List.set_cons_zero]
    simp only [List.append_assoc, List.singleton_append]
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06RotationSliceProg_exec
    27 28 (by decide) (.len 27) (.const 0) (.op .add (.reg 323) (.const 1))
    row (pre ++ [row.length]) 0 row.length (row.length + tail.length) s₂ hw hroww
    (by omega) hy (by omega) (by simp only [List.length_append, List.length_singleton]; omega)
    ((hk₂.2 27 (by decide)).trans h27) hd₂
    (fun st hk => GraphMinor.Compute.Crossing.eval_len
      ((hk.2 27 (by decide)).trans ((hk₂.2 27 (by decide)).trans h27)) hroww)
    (fun _ _ => GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    (fun st hk => by
      simp only [List.length_append, List.length_singleton]
      exact GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg ((hk.1 323 (by decide)).trans ((hk₂.1 323 (by decide)).trans h323)) hprew)
        (GraphMinor.Compute.Crossing.eval_const hw) (by omega))
  have hk₃' : Keeps [313] [28] s s₃ := hk₂.trans hk₃ (by simp) (by simp)
  have hd₃' : s₃.arrs 28 = (pre ++ row.length :: row) ++ List.replicate tail.length 0 := by
    simpa only [List.drop_zero, List.take_length, Nat.add_sub_cancel_left,
      List.append_assoc, List.singleton_append] using hd₃
  have hdrop : xs.drop (pre.length + 1 + oldrow.length) = tail := by
    have hh : xs = (pre ++ oldrow.length :: oldrow) ++ tail := by simp [xs, List.append_assoc]
    have hl : (pre ++ oldrow.length :: oldrow).length = pre.length + 1 + oldrow.length := by simp; omega
    rw [hh, ← hl, List.drop_left]
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm06RotationSliceProg_exec
    4 28 (by decide) (.op .sub (.len 4) (.reg 324)) (.reg 324)
    (.op .add (.op .add (.reg 323) (.const 1)) (.len 27))
    xs (pre ++ row.length :: row) (pre.length + 1 + oldrow.length) tail.length tail.length
    s₃ hw hn (by omega) hx (Nat.le_refl _) (by simp only [List.length_append, List.length_cons]; omega)
    ((hk₃'.2 4 (by decide)).trans h4) hd₃'
    (fun st hk => by
      have hh := GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_len ((hk.2 4 (by decide)).trans ((hk₃'.2 4 (by decide)).trans h4)) hn)
        (GraphMinor.Compute.Crossing.eval_reg ((hk.1 324 (by decide)).trans ((hk₃'.1 324 (by decide)).trans h324)) hendw)
      have heq : xs.length - (pre.length + 1 + oldrow.length) = tail.length := by omega
      simpa only [heq] using hh)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg
      ((hk.1 324 (by decide)).trans ((hk₃'.1 324 (by decide)).trans h324)) hendw)
    (fun st hk => by
      have heq : (pre ++ row.length :: row).length = pre.length + 1 + row.length := by simp; omega
      rw [heq]
      exact GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg ((hk.1 323 (by decide)).trans ((hk₃'.1 323 (by decide)).trans h323)) hprew)
          (GraphMinor.Compute.Crossing.eval_const hw) (by omega))
        (GraphMinor.Compute.Crossing.eval_len ((hk.2 27 (by decide)).trans ((hk₃'.2 27 (by decide)).trans h27)) hroww)
        (by omega))
  have hd₄' : s₄.arrs 28 = out := by
    simpa only [hdrop, List.take_length, Nat.sub_self, List.replicate_zero, List.append_nil,
      List.append_assoc, out] using hd₄
  have hk₄' : Keeps [313] [28] s s₄ := hk₃'.trans hk₄ (by simp) (by simp)
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, hout⟩ := copyProg_exec
    (dst := 4) (src := 28) (by decide) out s₄ hw hn' hnewwords hd₄'
  have hk : Keeps [313, 98] [4, 28] s s₄ := hk₄'.mono (by simp) (by simp)
  refine ⟨s₅, (5 + out.length) + (t₁ + (3 + (t₃ + (t₄ + t₅)))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅)))), ?_,
    hk.trans hk₅ (by simp [rI3]) (by simp), hout⟩
  simp only [Expr.cost] at ht₁ ht₃ ht₄
  change t₅ ≤ 6 + 12 * out.length at ht₅
  change _ ≤ 100 + 80 * (xs.length + row.length)
  omega

/-- Find rotation row 31, replace it by row 27 and retain the
replacement row for any following update. -/
@[expose] def gm06ReplaceRotationRowProg : Cmd :=
  .seq (gm06SelectRowProg 4 25)
    (.seq (.assign 323 (.op .sub (.op .sub (.reg 8) (.len 25)) (.const 1)))
      (.seq (.assign 324 (.reg 8)) gm06ReplaceRotationRowCore))

private theorem encoding_set_split (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length)
    (row : List ℕ) :
    gm06EncodeRows (rows.set i row) =
      (rows.length :: gm06EncodeRowsPayload (rows.take i)) ++ row.length :: row ++
        gm06EncodeRowsPayload (rows.drop (i + 1)) := by
  rw [List.set_eq_take_append_cons_drop]
  simp only [hi, ite_true, gm06EncodeRows, List.length_append, List.length_cons,
    List.length_take, Nat.min_eq_left hi.le, List.length_drop,
    gm06EncodeRowsPayload, List.flatMap_append, List.flatMap_cons, gm06EncodeNatList]
  have hh : i + (rows.length - (i + 1) + 1) = rows.length := by omega
  simp only [hh, List.cons_append, List.append_assoc]

/-- Replacing a row changes the encoding length by exactly the
change in that row's length. The row count and all headers persist. -/
theorem gm06EncodeRows_set_length (rows : List (List ℕ)) (i : ℕ)
    (hi : i < rows.length) (row : List ℕ) :
    (gm06EncodeRows (rows.set i row)).length + rows[i].length =
      (gm06EncodeRows rows).length + row.length := by
  have hold := encoding_set_split rows i hi rows[i]
  rw [List.set_getElem_self hi] at hold
  rw [encoding_set_split rows i hi row, hold]
  simp only [List.length_append, List.length_cons]
  omega

/-- A replaced row code contains only old code words, replacement
entries and the new length header. -/
theorem gm06EncodeRows_set_words {w : ℕ} (rows : List (List ℕ)) (i : ℕ)
    (hi : i < rows.length) (row : List ℕ)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hy : ∀ x ∈ row, x < 2 ^ w) (hlen : row.length < 2 ^ w) :
    ∀ x ∈ gm06EncodeRows (rows.set i row), x < 2 ^ w := by
  have hold := encoding_set_split rows i hi rows[i]
  rw [List.set_getElem_self hi] at hold
  intro x hm
  rw [encoding_set_split rows i hi row] at hm
  simp only [List.cons_append, List.append_assoc, List.mem_cons, List.mem_append] at hm
  rcases hm with hm | hm | hm | hm | hm
  · exact hx x (by rw [hold]; simp [hm])
  · exact hx x (by rw [hold]; simp [hm])
  · subst x; exact hlen
  · exact hy x hm
  · exact hx x (by rw [hold]; simp [hm])

/-- Replacing the indexed row on the RAM produces exactly the
encoded list update, for a row of any length, including zero. -/
theorem gm06ReplaceRotationRowProg_exec {w : ℕ} (rows : List (List ℕ))
    (i : ℕ) (hi : i < rows.length) (row : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hn' : (gm06EncodeRows (rows.set i row)).length < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) (hy : ∀ x ∈ row, x < 2 ^ w)
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h27 : s.arrs 27 = row) (h31 : s.regs 31 = i) :
    ∃ s' t, Exec w gm06ReplaceRotationRowProg s s' t ∧
      t ≤ 150 + 17 * i + 22 * rows[i].length + 80 * ((gm06EncodeRows rows).length + row.length) ∧
      Keeps [7, 8, 9, 11, 31, 323, 324, 313, 98] [25, 4, 28] s s' ∧
      s'.arrs 4 = gm06EncodeRows (rows.set i row) ∧ s'.arrs 27 = row := by
  let pre := rows.length :: gm06EncodeRowsPayload (rows.take i)
  let tail := gm06EncodeRowsPayload (rows.drop (i + 1))
  have hold : gm06EncodeRows rows = pre ++ rows[i].length :: rows[i] ++ tail := by
    have hh := encoding_set_split rows i hi rows[i]
    simpa only [List.set_getElem_self hi] using hh
  have hnew : gm06EncodeRows (rows.set i row) = pre ++ row.length :: row ++ tail :=
    encoding_set_split rows i hi row
  have hlen : (gm06EncodeRows rows).length = pre.length + 1 + rows[i].length + tail.length := by
    rw [hold]; simp only [List.length_append, List.length_cons]; omega
  obtain ⟨s₁, t₁, he₁, ht₁, hrow, _, hsrc, hk₁, hend⟩ :=
    gm06SelectRowProg_exec_with_end 4 25 (by decide) rows i hi s hw h4 hn hx h31
  have hend' : s₁.regs 8 = pre.length + 1 + rows[i].length := by
    simp only [pre, List.length_cons]
    omega
  have hendw : pre.length + 1 + rows[i].length < 2 ^ w := by omega
  have hroww : rows[i].length < 2 ^ w := by omega
  let s₂ := s₁.setReg 323 pre.length
  have he₂ : Exec w (.assign 323 (.op .sub (.op .sub (.reg 8) (.len 25)) (.const 1))) s₁ s₂ 6 := by
    have hh := GraphMinor.Compute.Crossing.eval_sub
      (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg hend' hendw)
        (GraphMinor.Compute.Crossing.eval_len hrow hroww)) (GraphMinor.Compute.Crossing.eval_const hw)
    have heq : pre.length + 1 + rows[i].length - rows[i].length - 1 = pre.length := by omega
    rw [heq] at hh
    exact .assign hh
  let s₃ := s₂.setReg 324 (pre.length + 1 + rows[i].length)
  have he₃ : Exec w (.assign 324 (.reg 8)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂] using hend') hendw)
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hout⟩ := gm06ReplaceRotationRowCore_exec pre rows[i] row tail s₃ hw
    (by rw [← hold]; exact hn) (by rw [← hnew]; exact hn')
    (by rw [← hold]; exact hx) hy
    (by simpa [s₃, s₂, hold] using hsrc.trans h4)
    (by simpa [s₃, s₂] using hrow)
    (by simpa [s₃, s₂] using (hk₁.2 27 (by decide)).trans h27)
    (by simp [s₃, s₂]) (by simp [s₃])
  let R := [7, 8, 9, 11, 31, 323, 324, 313, 98]
  have hk₁' : Keeps R [25, 4, 28] s s₁ := hk₁.mono (by simp [R]) (by simp)
  have hk₃ : Keeps R [25, 4, 28] s s₃ :=
    (hk₁'.setReg (by simp [R]) _).setReg (by simp [R]) _
  have hk : Keeps R [25, 4, 28] s s₄ := hk₃.trans hk₄ (by simp [R]) (by simp)
  refine ⟨s₄, t₁ + (6 + (2 + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, hk,
    hout.trans hnew.symm, (hk.2 27 (by decide)).trans h27⟩
  rw [← hold] at ht₄
  omega

end GraphMinor.Compute
