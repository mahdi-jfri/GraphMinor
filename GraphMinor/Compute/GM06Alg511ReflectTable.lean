module

public import GraphMinor.Compute.GM06Alg511ReflectRegionProg
public import GraphMinor.Compute.GM06ReplaceRotationRow
import GraphMinor.Compute.GM06RowPositions
import Mathlib.Tactic

/-!
# Reflecting a complete encoded drawing table

The orientation step of VI (5.11), page 134, transforms every supplied
rotation or region row. Read a row by its index, apply the verified
row operation, and install its result with the verified encoded-row
replacement program. Each replacement preserves its row length.
The outer loop records the already transformed prefix and leaves the
unread suffix fixed. Its quadratic bound includes all row searches
and copies. No geometric values are selected by the program.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- The two ordinary drawing-table row operations. The region case
retains the row header, while the rotation case reverses every end. -/
def gm06Alg511ReflectedTableRow (region : Bool) (m k : ℕ) (row : List ℕ) : List ℕ :=
  if region then gm06Alg511ReflectRegionRow m k row
  else row.reverse.map (gm06Alg511ReflectAugmentedDart m k)

private theorem reflected_row_length (region : Bool) (m k : ℕ) (row : List ℕ) :
    (gm06Alg511ReflectedTableRow region m k row).length = row.length := by
  cases region <;> simp [gm06Alg511ReflectedTableRow, gm06Alg511ReflectRegionRow_length]

private theorem reflected_row_words {w : ℕ} (region : Bool) (m k : ℕ) (row : List ℕ)
    (hn : 2 * (m + k + k) < 2 ^ w) (hx : ∀ x ∈ row, x < 2 ^ w)
    (hd : ∀ x ∈ (if region then row.tail else row), x < 2 * (m + k + k)) :
    ∀ x ∈ gm06Alg511ReflectedTableRow region m k row, x < 2 ^ w := by
  cases region with
  | false =>
    intro x h
    obtain ⟨d, hdrow, rfl⟩ := List.mem_map.mp h
    exact (gm06Alg511ReflectAugmentedDart_lt (hd d (List.mem_reverse.mp hdrow))).trans hn
  | true =>
    cases row with
    | nil => simp [gm06Alg511ReflectedTableRow, gm06Alg511ReflectRegionRow]
    | cons r ds =>
      intro x h
      rcases List.mem_cons.mp h with rfl | h
      · exact hx _ List.mem_cons_self
      · obtain ⟨d, hds, rfl⟩ := List.mem_map.mp h
        exact (gm06Alg511ReflectAugmentedDart_lt
          (gm06DartMate_lt (hd d (List.mem_reverse.mp hds)))).trans hn

/-- Transform the selected row from array 25 into array 27.
The rotation case also uses scratch array 26. -/
def gm06Alg511ReflectSelectedRowProg (region : Bool) : Cmd :=
  if region then gm06Alg511ReflectRegionRowProg 25 27
  else gm06Alg511ReflectRotationRowProg 25 26 27

private theorem selected_row_exec {w : ℕ} (region : Bool) (m k : ℕ)
    (row : List ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * (m + k + k) < 2 ^ w) (hlen : row.length + 1 < 2 ^ w)
    (hx : ∀ x ∈ row, x < 2 ^ w)
    (hd : ∀ x ∈ (if region then row.tail else row), x < 2 * (m + k + k))
    (h25 : s.arrs 25 = row) (h60 : s.regs 60 = m) (h52 : s.regs 52 = k) :
    ∃ s' t, Exec w (gm06Alg511ReflectSelectedRowProg region) s s' t ∧
      t ≤ 12 + 94 * row.length ∧ Keeps [20, 23, 24] [26, 27] s s' ∧
      s'.arrs 27 = gm06Alg511ReflectedTableRow region m k row := by
  cases region with
  | false =>
    exact gm06Alg511ReflectRotationRowProg_exec 25 26 27 (by decide) (by decide)
      m k row s hw hn hlen hx h25 h60 h52
  | true =>
    obtain ⟨s', t, he, ht, hk, ho⟩ := gm06Alg511ReflectRegionRowProg_exec
      25 27 (by decide) m k row s hw hn (by omega) hx hd h25 h60 h52
    exact ⟨s', t, he, by omega, hk.mono (by simp) (by simp), ho⟩

private theorem row_length_lt_code (rows : List (List ℕ)) {i : ℕ} (hi : i < rows.length) :
    rows[i].length + 1 < (gm06EncodeRows rows).length := by
  have hh := gm06RowsPrefixLength_le rows (i + 1)
  rw [gm06RowsPrefixLength_succ rows hi] at hh
  simp only [gm06EncodeRows, List.length_cons]
  omega

private theorem count_lt_code (rows : List (List ℕ)) :
    rows.length < (gm06EncodeRows rows).length := by
  have h : ∀ rs : List (List ℕ), rs.length ≤ (gm06EncodeRowsPayload rs).length := by
    intro rs
    induction rs with
    | nil => simp [gm06EncodeRowsPayload]
    | cons r rs ih => simp only [gm06EncodeRowsPayload, List.flatMap_cons, gm06EncodeNatList,
        List.length_cons, List.length_append] at *; omega
  have hh := h rows
  simp only [gm06EncodeRows, List.length_cons]
  omega

private theorem row_word_mem_code (rows : List (List ℕ)) {i x : ℕ}
    (hi : i < rows.length) (hx : x ∈ rows[i]) : x ∈ gm06EncodeRows rows := by
  apply List.mem_cons_of_mem
  apply List.mem_flatMap.mpr
  exact ⟨rows[i], List.getElem_mem hi, by simp [gm06EncodeNatList, hx]⟩

private def bodyRegs : List Reg := [31, 7, 8, 9, 11, 20, 23, 24, 323, 324, 313, 98]
private def tableArrays : List Arr := [4, 25, 26, 27, 28]

/-- Read the row indexed by counter 1401, transform it, and replace
that same encoded row. The counter survives both row searches. -/
def gm06Alg511ReflectTableStep (region : Bool) : Cmd :=
  .seq (.assign 31 (.reg 1401)) (.seq (gm06SelectRowProg 4 25)
    (.seq (gm06Alg511ReflectSelectedRowProg region)
      (.seq (.assign 31 (.reg 1401)) gm06ReplaceRotationRowProg)))

private theorem table_step_exec {w : ℕ} (region : Bool) (m k : ℕ)
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) (s : State)
    (hw : 2 < 2 ^ w) (hn : 2 * (m + k + k) < 2 ^ w)
    (hcode : (gm06EncodeRows rows).length < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hd : ∀ x ∈ (if region then rows[i].tail else rows[i]), x < 2 * (m + k + k))
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h60 : s.regs 60 = m)
    (h52 : s.regs 52 = k) (h1401 : s.regs 1401 = i) :
    ∃ s' t, Exec w (gm06Alg511ReflectTableStep region) s s' t ∧
      t ≤ 182 + 34 * i + 218 * rows[i].length + 80 * (gm06EncodeRows rows).length ∧
      Keeps bodyRegs tableArrays s s' ∧
      s'.arrs 4 = gm06EncodeRows (rows.set i (gm06Alg511ReflectedTableRow region m k rows[i])) := by
  let row := gm06Alg511ReflectedTableRow region m k rows[i]
  have hlen : row.length = rows[i].length := reflected_row_length region m k rows[i]
  have hrow : rows[i].length + 1 < 2 ^ w := (row_length_lt_code rows hi).trans hcode
  have hiw : i < 2 ^ w := (hi.trans (count_lt_code rows)).trans hcode
  have hwords : ∀ x ∈ rows[i], x < 2 ^ w := fun x hxrow => hx x (row_word_mem_code rows hi hxrow)
  have hnewwords : ∀ x ∈ row, x < 2 ^ w := reflected_row_words region m k rows[i] hn hwords hd
  have hnewlen : (gm06EncodeRows (rows.set i row)).length = (gm06EncodeRows rows).length := by
    have hh := gm06EncodeRows_set_length rows i hi row
    rw [hlen] at hh
    omega
  let s₀ := s.setReg 31 i
  have he₀ : Exec w (.assign 31 (.reg 1401)) s s₀ 2 := .assign (GraphMinor.Compute.Crossing.eval_reg h1401 hiw)
  obtain ⟨s₁, t₁, he₁, ht₁, h25, _, h4₁, hk₁, _⟩ := gm06SelectRowProg_exec_with_end
    4 25 (by decide) rows i hi s₀ (by omega) (by simpa [s₀] using h4) hcode hx (by simp [s₀])
  have h60₁ : s₁.regs 60 = m := (hk₁.1 60 (by decide)).trans (by simpa [s₀] using h60)
  have h52₁ : s₁.regs 52 = k := (hk₁.1 52 (by decide)).trans (by simpa [s₀] using h52)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h27⟩ := selected_row_exec region m k rows[i] s₁
    hw hn hrow hwords hd h25 h60₁ h52₁
  have h1401₂ : s₂.regs 1401 = i := (hk₂.1 1401 (by decide)).trans
    ((hk₁.1 1401 (by decide)).trans (by simpa [s₀] using h1401))
  let s₃ := s₂.setReg 31 i
  have he₃ : Exec w (.assign 31 (.reg 1401)) s₂ s₃ 2 := .assign (GraphMinor.Compute.Crossing.eval_reg h1401₂ hiw)
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hout, _⟩ := gm06ReplaceRotationRowProg_exec rows i hi row s₃
    (by omega) hcode (by rw [hnewlen]; exact hcode) hx hnewwords
    (by simpa [s₃] using (hk₂.2 4 (by decide)).trans (h4₁.trans (by simpa [s₀] using h4)))
    (by simpa [s₃] using h27) (by simp [s₃])
  have hk₀ : Keeps bodyRegs tableArrays s s₀ := (Keeps.refl _ _ s).setReg (by simp [bodyRegs]) _
  have hk₁' : Keeps bodyRegs tableArrays s s₁ := hk₀.trans hk₁ (by simp [bodyRegs]) (by simp [tableArrays])
  have hk₂' : Keeps bodyRegs tableArrays s s₂ := hk₁'.trans hk₂ (by simp [bodyRegs]) (by simp [tableArrays])
  have hk₃ : Keeps bodyRegs tableArrays s s₃ := hk₂'.setReg (by simp [bodyRegs]) _
  refine ⟨s₄, 2 + (t₁ + (t₂ + (2 + t₄))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))),
    ?_, hk₃.trans hk₄ (by simp [bodyRegs]) (by simp [tableArrays]), hout⟩
  rw [hlen] at ht₄
  omega

private def prefixMap (f : List ℕ → List ℕ) (rows : List (List ℕ)) (i : ℕ) : List (List ℕ) :=
  (rows.take i).map f ++ rows.drop i

private theorem prefixMap_length (f : List ℕ → List ℕ) (rows : List (List ℕ)) (i : ℕ) :
    (prefixMap f rows i).length = rows.length := by
  simp only [prefixMap, List.length_append, List.length_map, List.length_take, List.length_drop]
  omega

private theorem prefixMap_get (f : List ℕ → List ℕ) (rows : List (List ℕ)) {i : ℕ}
    (hi : i < rows.length) : (prefixMap f rows i)[i]'(by rw [prefixMap_length]; exact hi) = rows[i] := by
  have hlen : ((rows.take i).map f).length = i := by
    rw [List.length_map, List.length_take_of_le hi.le]
  unfold prefixMap
  rw [List.getElem_append_right (by rw [hlen])]
  simp only [hlen, Nat.sub_self, List.getElem_drop, Nat.add_zero]

private theorem prefixMap_step (f : List ℕ → List ℕ) (rows : List (List ℕ)) {i : ℕ}
    (hi : i < rows.length) : (prefixMap f rows i).set i (f rows[i]) = prefixMap f rows (i + 1) := by
  have hdrop : rows.drop i = rows[i] :: rows.drop (i + 1) := List.drop_eq_getElem_cons hi
  simp only [prefixMap, hdrop]
  rw [List.set_append_right _ _ (by simp)]
  simp only [List.length_map, List.length_take_of_le hi.le, Nat.sub_self, List.set_cons_zero]
  rw [List.take_succ_eq_append_getElem hi, List.map_append]
  simp only [List.map_cons, List.map_nil, List.singleton_append, List.append_assoc]

private theorem prefixMap_code_length (f : List ℕ → List ℕ) (rows : List (List ℕ))
    (hf : ∀ row, (f row).length = row.length) : ∀ i,
    (gm06EncodeRows (prefixMap f rows i)).length = (gm06EncodeRows rows).length := by
  intro i
  induction i with
  | zero => simp [prefixMap]
  | succ i ih =>
    by_cases hi : i < rows.length
    · have h := gm06EncodeRows_set_length (prefixMap f rows i) i (by rw [prefixMap_length]; exact hi) (f rows[i])
      rw [prefixMap_get f rows hi, hf, prefixMap_step f rows hi] at h
      omega
    · have hge : rows.length ≤ i := by omega
      simp only [prefixMap, List.take_of_length_le hge, List.drop_eq_nil_of_le hge, List.append_nil] at ih
      simpa only [prefixMap, List.take_of_length_le (by omega : rows.length ≤ i + 1),
        List.drop_eq_nil_of_le (by omega : rows.length ≤ i + 1), List.append_nil] using ih

/-- Reflect every row of the encoded table in array 4. The row count
and the growing transformed prefix are computed by the program. -/
def gm06Alg511ReflectTableProg (region : Bool) : Cmd :=
  .seq (.assign 1400 (.read 4 (.const 0))) (.seq (.assign 1401 (.const 0))
    (forUp 1401 (.reg 1400) (gm06Alg511ReflectTableStep region)))

/-- The full encoded table reflection has quadratic running time.
Its input consists only of the table words and the two edge counts. -/
theorem gm06Alg511ReflectTableProg_exec {w : ℕ} (region : Bool) (m k : ℕ)
    (rows : List (List ℕ)) (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * (m + k + k) < 2 ^ w) (hcode : (gm06EncodeRows rows).length < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hd : ∀ row ∈ rows, ∀ d ∈ (if region then row.tail else row), d < 2 * (m + k + k))
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h60 : s.regs 60 = m) (h52 : s.regs 52 = k) :
    ∃ s' t, Exec w (gm06Alg511ReflectTableProg region) s s' t ∧
      t ≤ 8 + rows.length * (607 + 600 * (gm06EncodeRows rows).length) ∧
      Keeps [1400, 1401, 31, 7, 8, 9, 11, 20, 23, 24, 323, 324, 313, 98]
        [4, 25, 26, 27, 28] s s' ∧
      s'.arrs 4 = gm06EncodeRows (rows.map (gm06Alg511ReflectedTableRow region m k)) := by
  let f := gm06Alg511ReflectedTableRow region m k
  let N := (gm06EncodeRows rows).length
  let R : List Reg := 1400 :: 1401 :: bodyRegs
  have hcount : rows.length < 2 ^ w := (count_lt_code rows).trans hcode
  have hN : 0 < N := by simp [N, gm06EncodeRows]
  let s₁ := s.setReg 1400 rows.length
  let s₂ := s₁.setReg 1401 0
  have hhead : (s.arrs 4)[0]'(by rw [h4]; simp [gm06EncodeRows]) = rows.length := by
    simp [h4, gm06EncodeRows]
  have hread : (Expr.read 4 (.const 0)).eval w s = some rows.length := by
    have hh := GraphMinor.Compute.Crossing.eval_read (a := 4)
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) (by rw [h4]; simp [gm06EncodeRows])
      (by rw [hhead]; exact hcount)
    simpa only [hhead] using hh
  have he₁ : Exec w (.assign 1400 (.read 4 (.const 0))) s s₁ 3 := .assign hread
  have he₂ : Exec w (.assign 1401 (.const 0)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  let Inv : ℕ → State → Prop := fun i st => Keeps R tableArrays s st ∧ st.regs 1400 = rows.length ∧
    st.regs 1401 = i ∧ st.arrs 4 = gm06EncodeRows (prefixMap f rows i) ∧
    ∀ x ∈ gm06EncodeRows (prefixMap f rows i), x < 2 ^ w
  have hstart : Inv 0 s₂ := by
    refine ⟨((Keeps.refl _ _ s).setReg (by simp [R]) _).setReg (by simp [R]) _,
      by simp [s₂, s₁], by simp [s₂], ?_, ?_⟩
    · simpa only [prefixMap, List.take_zero, List.map_nil, List.drop_zero, List.nil_append,
        s₂, s₁, State.setReg_arrs] using h4
    · simpa only [prefixMap, List.take_zero, List.map_nil, List.drop_zero, List.nil_append] using hx
  have hloop := forUp_pot Inv (fun _ => 0) rows.length (600 * (N + 1)) (r_i := 1401) (hi := .reg 1400)
    (body := gm06Alg511ReflectTableStep region) (by omega : 1 < 2 ^ w) hcount
    (fun i _ st hst => ⟨hst.2.2.1, GraphMinor.Compute.Crossing.eval_reg hst.2.1 hcount⟩)
    (fun i hi st hst => by
      let current := prefixMap f rows i
      have hic : i < current.length := by rw [prefixMap_length]; exact hi
      have hcur : current[i] = rows[i] := prefixMap_get f rows hi
      have hcurN : (gm06EncodeRows current).length = N := prefixMap_code_length f rows
        (reflected_row_length region m k) i
      obtain ⟨st', t, he, ht, hk, hout⟩ := table_step_exec region m k current i hic st hw hn
        (by rw [hcurN]; exact hcode) hst.2.2.2.2
        (by rw [hcur]; exact hd rows[i] (List.getElem_mem hi)) hst.2.2.2.1
        ((hst.1.1 60 (by simp [R, bodyRegs])).trans h60)
        ((hst.1.1 52 (by simp [R, bodyRegs])).trans h52) hst.2.2.1
      have hnext : current.set i (f current[i]) = prefixMap f rows (i + 1) := by
        rw [hcur]
        exact prefixMap_step f rows hi
      have hnextWords : ∀ x ∈ gm06EncodeRows (prefixMap f rows (i + 1)), x < 2 ^ w := by
        rw [← hnext]
        apply gm06EncodeRows_set_words current i hic (f current[i]) hst.2.2.2.2
        · rw [hcur]
          exact reflected_row_words region m k rows[i] hn
            (fun x hm => hx x (row_word_mem_code rows hi hm)) (hd rows[i] (List.getElem_mem hi))
        · rw [reflected_row_length]
          have hh := (row_length_lt_code current hic).trans (by rw [hcurN]; exact hcode)
          omega
      have hrowN : current[i].length < N := by have hh := row_length_lt_code current hic; rw [hcurN] at hh; omega
      have hiN : i < N := hi.trans (count_lt_code rows)
      refine ⟨st', t, he, ?_, ?_, (hk.1 1401 (by simp [bodyRegs])).trans hst.2.2.1⟩
      · rw [hcurN] at ht
        omega
      · refine ⟨(hst.1.trans hk (by intro r hr; exact List.mem_cons_of_mem 1400 (List.mem_cons_of_mem 1401 hr)) (by simp)).setReg (by simp [R]) _,
          ?_, by simp, ?_, hnextWords⟩
        · simpa only [State.setReg_regs_ne _ _ (by decide : 1400 ≠ 1401)] using
            (hk.1 1400 (by simp [bodyRegs])).trans hst.2.1
        · change st'.arrs 4 = gm06EncodeRows (current.set i (f current[i])) at hout
          rw [hnext] at hout
          simpa only [State.setReg_arrs] using hout)
    0 (Nat.zero_le _) s₂ hstart
  obtain ⟨s', t, he, ht, hk, _, _, hout, _⟩ := hloop
  refine ⟨s', 3 + (2 + t), .seq he₁ (.seq he₂ he), ?_, hk, ?_⟩
  · simp only [Expr.cost, Nat.sub_zero, Nat.add_zero] at ht
    rw [show 1 + 6 + 600 * (N + 1) = 607 + 600 * N by omega] at ht
    dsimp only [N] at ht
    omega
  · simpa only [prefixMap, List.take_length, List.drop_length, List.append_nil] using hout

/-- Reflecting rows retains the number of rows and every row
length, and hence the length of the whole encoded table. -/
theorem gm06Alg511ReflectedTable_code_length (region : Bool) (m k : ℕ) (rows : List (List ℕ)) :
    (gm06EncodeRows (rows.map (gm06Alg511ReflectedTableRow region m k))).length =
      (gm06EncodeRows rows).length := by
  have h := prefixMap_code_length (gm06Alg511ReflectedTableRow region m k) rows
    (reflected_row_length region m k) rows.length
  simpa only [prefixMap, List.take_length, List.drop_length, List.append_nil] using h

/-- Every word in the transformed table still fits: row lengths and
region headers are retained, while directed labels stay in range. -/
theorem gm06Alg511ReflectedTable_code_words {w : ℕ} (region : Bool) (m k : ℕ)
    (rows : List (List ℕ)) (hn : 2 * (m + k + k) < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (hd : ∀ row ∈ rows, ∀ d ∈ (if region then row.tail else row), d < 2 * (m + k + k)) :
    ∀ x ∈ gm06EncodeRows (rows.map (gm06Alg511ReflectedTableRow region m k)), x < 2 ^ w := by
  intro x hm
  rcases List.mem_cons.mp hm with hcount | hm
  · rw [List.length_map] at hcount
    exact hx x (hcount ▸ List.mem_cons_self)
  · obtain ⟨out, hout, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hout
    rcases List.mem_cons.mp hm with hlen | hm
    · rw [reflected_row_length] at hlen
      apply hx x
      apply List.mem_cons_of_mem
      exact List.mem_flatMap.mpr ⟨row, hrow, hlen ▸ List.mem_cons_self⟩
    · exact reflected_row_words region m k row hn
        (fun x hxrow => hx x (List.mem_cons_of_mem _
          (List.mem_flatMap.mpr ⟨row, hrow, List.mem_cons_of_mem _ hxrow⟩))) (hd row hrow) x hm

/-- The explicit table-scan bound is quadratic in its supplied word
length, with a fixed coefficient independent of the drawing. -/
theorem gm06Alg511ReflectTable_time_le (rows : List (List ℕ)) :
    8 + rows.length * (607 + 600 * (gm06EncodeRows rows).length) ≤
      1000 * ((gm06EncodeRows rows).length + 1) ^ 2 := by
  let N := (gm06EncodeRows rows).length
  have hlen : rows.length ≤ N := (count_lt_code rows).le
  calc
    _ ≤ 8 + N * (607 + 600 * N) := Nat.add_le_add_left (Nat.mul_le_mul_right _ hlen) _
    _ ≤ _ := by nlinarith

end GraphMinor.Compute
