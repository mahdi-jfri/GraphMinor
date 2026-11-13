module

public import GraphMinor.Compute.GM06RowPositions
public import GraphMinor.Compute.GM06SelectRow
public import GraphMinor.Compute.GM06EraseLinkageWord
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Removing the first edge of a given path after contraction

The given paths in VI (5.7), page 133, are stored as rows with
length headers. Removing the first edge of one path erases its
first directed-edge word and decreases its header by one. The
other rows and the number of paths stay fixed. The identities
below justify those two concrete writes. The RAM program selects
the supplied row, computes its header and first-word positions from
the returned cursor, erases that word and updates the header.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

private theorem erase_next_set_header (pre tail : List ℕ) (n d n' : ℕ) :
    ((pre ++ n :: d :: tail).eraseIdx (pre.length + 1)).set pre.length n' = pre ++ n' :: tail := by
  rw [List.eraseIdx_append_of_length_le (l := pre) (k := pre.length + 1) (by omega) (n :: d :: tail)]
  simp only [Nat.add_sub_cancel_left, List.eraseIdx_cons_succ, List.eraseIdx_cons_zero]
  rw [List.set_append_right pre.length n' (Nat.le_refl _)]
  simp only [Nat.sub_self, List.set_cons_zero]

/-- Erasing a nonempty row's first word and changing its length
header gives the encoding with precisely that row shortened. -/
theorem gm06DropInitialPathEncoding_at_split (pre : List (List ℕ)) (d : ℕ) (row : List ℕ) (post : List (List ℕ)) :
    (((gm06EncodeRows (pre ++ (d :: row) :: post)).eraseIdx
      (2 + (gm06EncodeRowsPayload pre).length)).set
      (1 + (gm06EncodeRowsPayload pre).length) row.length) =
        gm06EncodeRows (pre ++ row :: post) := by
  let p := (pre.length + (post.length + 1)) :: gm06EncodeRowsPayload pre
  let tail := row ++ gm06EncodeRowsPayload post
  have hold : gm06EncodeRows (pre ++ (d :: row) :: post) = p ++ (row.length + 1) :: d :: tail := by
    simp [gm06EncodeRows, gm06EncodeRowsPayload, gm06EncodeNatList, p, tail]
  have hnew : gm06EncodeRows (pre ++ row :: post) = p ++ row.length :: tail := by
    simp [gm06EncodeRows, gm06EncodeRowsPayload, gm06EncodeNatList, p, tail]
  rw [hold, hnew]
  have hpos : p.length = 1 + (gm06EncodeRowsPayload pre).length := by
    simp only [p, List.length_cons]
    omega
  have hdel : p.length + 1 = 2 + (gm06EncodeRowsPayload pre).length := by omega
  have hh := erase_next_set_header p tail (row.length + 1) d row.length
  rw [hdel, hpos] at hh
  exact hh

/-- The first word of a nonempty indexed path row lies within its
encoded array, after the row count and the preceding row payloads. -/
theorem gm06InitialPathWord_position_lt (rows : List (List ℕ)) (i : ℕ)
    (hi : i < rows.length) (hne : 0 < rows[i].length) :
    2 + (gm06EncodeRowsPayload (rows.take i)).length < (gm06EncodeRows rows).length := by
  have hpre := gm06RowsPrefixLength_le rows (i + 1)
  rw [gm06RowsPrefixLength_succ rows hi] at hpre
  simp only [gm06EncodeRows, List.length_cons]
  omega

/-- Deleting the first edge word of the selected given path and
updating its header is exactly the encoding of the shortened row. -/
theorem gm06DropInitialPathEncoding (rows : List (List ℕ)) (i : ℕ)
    (hi : i < rows.length) (hne : 0 < rows[i].length) :
    (((gm06EncodeRows rows).eraseIdx
      (2 + (gm06EncodeRowsPayload (rows.take i)).length)).set
      (1 + (gm06EncodeRowsPayload (rows.take i)).length) (rows[i].length - 1)) =
        gm06EncodeRows (rows.set i rows[i].tail) := by
  cases hrow : rows[i] with
  | nil => simp only [hrow, List.length_nil] at hne; omega
  | cons d row =>
    have hold : rows.take i ++ (d :: row) :: rows.drop (i + 1) = rows := by
      rw [← hrow, ← List.drop_eq_getElem_cons hi]
      exact List.take_append_drop i rows
    have hnew : rows.set i rows[i].tail = rows.take i ++ row :: rows.drop (i + 1) := by
      rw [List.set_eq_take_append_cons_drop]
      simp only [hi, ite_true, hrow, List.tail_cons]
    have hh := gm06DropInitialPathEncoding_at_split (rows.take i) d row (rows.drop (i + 1))
    rw [hold, ← hnew] at hh
    simpa only [hrow, List.length_cons, Nat.add_sub_cancel] using hh

/-- Shorten path 295 by its first edge, using array 24 for the
selected row and array 27 for the deletion copy. -/
@[expose] def gm06DropInitialPathEdgeProg : Cmd :=
  .seq (.assign 31 (.reg 295))
    (.seq (gm06SelectRowProg 8 24)
      (.seq (.assign 311 (.op .sub (.op .sub (.reg 8) (.len 24)) (.const 1)))
        (.seq (.assign 310 (.op .add (.reg 311) (.const 1)))
          (.seq (.assign 312 (.op .sub (.len 24) (.const 1)))
            (.seq gm06EraseLinkageWordProg (.write 8 (.reg 311) (.reg 312)))))))

/-- The path update removes exactly its first edge word, updates
its header and lowers the linkage encoding length by one. Its
running time is linear in the encoded paths and the selected row. -/
theorem gm06DropInitialPathEdgeProg_exec {w : ℕ}
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length)
    (hne : 0 < rows[i].length) (s : State) (hw : 1 < 2 ^ w)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hx : ∀ v ∈ gm06EncodeRows rows, v < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows) (h295 : s.regs 295 = i) :
    ∃ s' t, Exec w gm06DropInitialPathEdgeProg s s' t ∧
      t ≤ 51 + 17 * i + 22 * rows[i].length + 32 * (gm06EncodeRows rows).length ∧
      Keeps [7, 8, 9, 11, 31, 311, 310, 312, 308, 98] [24, 8, 27] s s' ∧
      s'.arrs 8 = gm06EncodeRows (rows.set i rows[i].tail) ∧
      (s'.arrs 8).length + 1 = (gm06EncodeRows rows).length ∧
      s'.arrs 24 = rows[i] := by
  let h := 1 + (gm06EncodeRowsPayload (rows.take i)).length
  have hcount : rows.length < 2 ^ w := hx _ (by simp [gm06EncodeRows])
  have hiw := hi.trans hcount
  have hpre := gm06RowsPrefixLength_le rows (i + 1)
  rw [gm06RowsPrefixLength_succ rows hi] at hpre
  have hlen : (gm06EncodeRows rows).length = 1 + (gm06EncodeRowsPayload rows).length := by
    simp only [gm06EncodeRows, List.length_cons]
    omega
  have hendw : h + 1 + rows[i].length < 2 ^ w := by dsimp only [h]; omega
  have hroww : rows[i].length < 2 ^ w := by omega
  have hhw : h < 2 ^ w := by omega
  have hpos : h + 1 < (gm06EncodeRows rows).length := by
    have hh := gm06InitialPathWord_position_lt rows i hi hne
    dsimp only [h]
    omega
  let s₀ := s.setReg 31 i
  have he₀ : Exec w (.assign 31 (.reg 295)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h295 hiw)
  obtain ⟨s₁, t₁, he₁, ht₁, hrow, _, hsrc, hk₁, hend⟩ :=
    gm06SelectRowProg_exec_with_end 8 24 (by decide) rows i hi s₀ hw
      (by simpa only [s₀, State.setReg_arrs] using h8) hn hx (by simp [s₀])
  have hend' : s₁.regs 8 = h + 1 + rows[i].length := hend
  have hsrc' : s₁.arrs 8 = gm06EncodeRows rows := by
    simpa only [s₀, State.setReg_arrs, h8] using hsrc
  let R := [7, 8, 9, 11, 31, 311, 310, 312, 308, 98]
  have hk₀ : Keeps R [24] s s₀ := (Keeps.refl R [24] s).setReg (by simp [R]) _
  have hk₁' : Keeps R [24] s s₁ := hk₀.trans hk₁ (by simp [R]) (by simp)
  let s₂ := s₁.setReg 311 h
  have he₂ : Exec w (.assign 311
      (.op .sub (.op .sub (.reg 8) (.len 24)) (.const 1))) s₁ s₂ 6 := by
    have hh := GraphMinor.Compute.Crossing.eval_sub
      (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg hend' hendw)
        (GraphMinor.Compute.Crossing.eval_len hrow hroww))
      (GraphMinor.Compute.Crossing.eval_const hw)
    have heq : (h + 1 + rows[i].length - rows[i].length) - 1 = h := by omega
    rw [heq] at hh
    exact .assign hh
  let s₃ := s₂.setReg 310 (h + 1)
  have he₃ : Exec w (.assign 310 (.op .add (.reg 311) (.const 1))) s₂ s₃ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simp [s₂]) hhw)
      (GraphMinor.Compute.Crossing.eval_const hw) (hpos.trans hn))
  let s₄ := s₃.setReg 312 (rows[i].length - 1)
  have he₄ : Exec w (.assign 312 (.op .sub (.len 24) (.const 1))) s₃ s₄ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_sub
      (GraphMinor.Compute.Crossing.eval_len (by simpa [s₃, s₂] using hrow) hroww)
      (GraphMinor.Compute.Crossing.eval_const hw))
  have hk₄ : Keeps R [24] s s₄ :=
    ((hk₁'.setReg (by simp [R]) _).setReg (by simp [R]) _).setReg (by simp [R]) _
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, hdel, _, hdrop⟩ := gm06EraseLinkageWordProg_exec
    (gm06EncodeRows rows) (h + 1) s₄ hw hn hx hpos
    (by simpa only [s₄, s₃, s₂, State.setReg_arrs] using hsrc')
    (by simp [s₄, s₃])
  have hheader : s₅.regs 311 = h := by
    simpa [s₄, s₃, s₂] using hk₅.1 311 (by decide)
  have hnewlen : s₅.regs 312 = rows[i].length - 1 := by
    simpa [s₄] using hk₅.1 312 (by decide)
  let s₆ := s₅.writeArr 8 h (rows[i].length - 1)
  have he₆ : Exec w (.write 8 (.reg 311) (.reg 312)) s₅ s₆ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_reg hheader hhw)
      (GraphMinor.Compute.Crossing.eval_reg hnewlen ((Nat.sub_le _ _).trans_lt hroww))
      (by omega)
  have hk₄' : Keeps R [24, 8, 27] s s₄ := hk₄.mono (by simp [R]) (by simp)
  have hk₅' : Keeps R [24, 8, 27] s s₅ := hk₄'.trans hk₅ (by simp [R]) (by simp)
  refine ⟨s₆, 2 + (t₁ + (6 + (4 + (4 + (t₅ + 3))))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆))))),
    by omega, hk₅'.setArr (by simp) _, ?_, ?_, ?_⟩
  · have hh := gm06DropInitialPathEncoding rows i hi hne
    have hp : h + 1 = 2 + (gm06EncodeRowsPayload (rows.take i)).length := by
      dsimp only [h]; omega
    simpa only [s₆, State.writeArr_arrs_self, hdel, hp, h] using hh
  · simpa only [s₆, State.writeArr_arrs_self, List.length_set] using hdrop
  · simpa [s₆, s₄, s₃, s₂] using (hk₅.2 24 (by decide)).trans
      (show s₄.arrs 24 = rows[i] by simpa [s₄, s₃, s₂] using hrow)

end GraphMinor.Compute
