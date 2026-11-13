module

public import GraphMinor.Compute.GM06PruneRotationRow
public import GraphMinor.Compute.GM06ReplaceRotationRow
import GraphMinor.Compute.GM06RefreshContractedMasks

/-!
# Pruning the complete rotation table

The deletion branches of VI (5.7), page 133, first clear activity
bits. Before another scan, remove inactive directed words from
each rotation row. The row count and all original vertex labels
stay fixed. Each selected row is filtered and replaced through the
proved row commands.

The loop invariant records a pruned prefix followed by untouched
rows. Every replacement shortens the code or leaves its length
unchanged, and preserves its word bounds. The resulting program
computes the exact table filter with a polynomial bound.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Keep the current active ends in each permanent vertex row. -/
@[expose] def gm06PrunedRotationRows (activity : List ℕ) (rows : List (List ℕ)) :
    List (List ℕ) := rows.map (List.filter (gm06KeepActiveDart activity))

/-- Prune the row indexed by the outer counter 330. -/
@[expose] def gm06PruneRotationAtRowProg : Cmd :=
  .seq (.assign 31 (.reg 330))
    (.seq (gm06SelectRowProg 4 25)
      (.seq gm06PruneRotationRowProg
        (.seq (.assign 31 (.reg 330)) gm06ReplaceRotationRowProg)))

/-- Prune every row, retaining the row count read from the original
header. The activity array 30 has already been constructed. -/
@[expose] def gm06PruneRotationsProg : Cmd :=
  .seq (.assign 339 (.read 4 (.const 0)))
    (.seq (.assign 330 (.const 0))
      (forUp 330 (.reg 339) gm06PruneRotationAtRowProg))

private theorem row_length_lt_code (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) :
    rows[i].length < (gm06EncodeRows rows).length := by
  have hh := (List.sublist_flatten_of_mem (List.getElem_mem hi)).length_le
  rw [gm06EncodeRows_length]
  omega

private theorem row_word_mem_code (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length)
    (x : ℕ) (hx : x ∈ rows[i]) : x ∈ gm06EncodeRows rows := by
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr ⟨rows[i], List.getElem_mem hi, by simp [gm06EncodeNatList, hx]⟩

/-- One indexed pruning step gives the exact row replacement,
never increases the code length, and preserves every word bound. -/
theorem gm06PruneRotationAtRowProg_exec {w : ℕ} (activity : List ℕ) (rows : List (List ℕ))
    (i : ℕ) (hi : i < rows.length) (s : State) (hw : 2 < 2 ^ w)
    (hlen : 4 * (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (haLen : activity.length < 2 ^ w) (hbits : ∀ x ∈ activity, x ≤ 1)
    (hd : ∀ d ∈ rows[i], d < 2 * activity.length)
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h30 : s.arrs 30 = activity) (h330 : s.regs 330 = i) :
    let row := rows[i].filter (gm06KeepActiveDart activity)
    ∃ s' t, Exec w gm06PruneRotationAtRowProg s s' t ∧
      t ≤ 250 + 34 * rows.length + 300 * (gm06EncodeRows rows).length ∧
      Keeps [31, 7, 8, 9, 11, 313, 323, 324, 98, 331, 332, 333, 334, 335, 336, 337]
        [25, 27, 29, 4, 28] s s' ∧ s'.regs 330 = i ∧
      s'.arrs 4 = gm06EncodeRows (rows.set i row) ∧
      (gm06EncodeRows (rows.set i row)).length ≤ (gm06EncodeRows rows).length ∧
      ∀ x ∈ gm06EncodeRows (rows.set i row), x < 2 ^ w := by
  dsimp only
  let row := rows[i].filter (gm06KeepActiveDart activity)
  have hn : (gm06EncodeRows rows).length < 2 ^ w := by omega
  have hcount : rows.length < 2 ^ w := hwords _ (by simp [gm06EncodeRows])
  have hiw : i < 2 ^ w := hi.trans hcount
  have hrow := row_length_lt_code rows i hi
  have hrowWords : ∀ x ∈ rows[i], x < 2 ^ w := fun x hx =>
    hwords x (row_word_mem_code rows i hi x hx)
  have hnewWords : ∀ x ∈ row, x < 2 ^ w := fun x hx => hrowWords x (List.mem_filter.mp hx).1
  have hfilter : row.length ≤ rows[i].length := List.length_filter_le _ _
  have hsetLen := gm06EncodeRows_set_length rows i hi row
  have hshrink : (gm06EncodeRows (rows.set i row)).length ≤ (gm06EncodeRows rows).length := by omega
  have hsetWords := gm06EncodeRows_set_words rows i hi row hwords hnewWords (by omega)
  let s₀ := s.setReg 31 i
  have he₀ : Exec w (.assign 31 (.reg 330)) s s₀ 2 := .assign
    (GraphMinor.Compute.Crossing.eval_reg h330 hiw)
  obtain ⟨s₁, t₁, he₁, ht₁, h25, _, h4same, hk₁, _⟩ := gm06SelectRowProg_exec_with_end
    4 25 (by decide) rows i hi s₀ (by omega) (by simpa [s₀] using h4) hn hwords (by simp [s₀])
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h27⟩ := gm06PruneRotationRowProg_exec activity rows[i] s₁
    hw (by omega) haLen hbits hd hrowWords h25
    ((hk₁.2 30 (by decide)).trans (by simpa [s₀] using h30))
  let R := [31, 7, 8, 9, 11, 313, 323, 324, 98, 331, 332, 333, 334, 335, 336, 337]
  let A := [25, 27, 29, 4, 28]
  have hk₀ : Keeps R A s s₀ := (Keeps.refl _ _ s).setReg (by simp [R]) _
  have hk₁' : Keeps R A s s₁ := hk₀.trans hk₁ (by simp [R]) (by simp [A])
  have hk₂' : Keeps R A s s₂ := hk₁'.trans hk₂ (by simp [R]) (by simp [A])
  have h330₂ : s₂.regs 330 = i := (hk₂'.1 330 (by decide)).trans h330
  let s₃ := s₂.setReg 31 i
  have he₃ : Exec w (.assign 31 (.reg 330)) s₂ s₃ 2 := .assign
    (GraphMinor.Compute.Crossing.eval_reg h330₂ hiw)
  have hk₃ : Keeps R A s s₃ := hk₂'.setReg (by simp [R]) _
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hout, _⟩ := gm06ReplaceRotationRowProg_exec rows i hi row s₃
    (by omega) hn (hshrink.trans_lt hn) hwords hnewWords
    (by simpa [s₃] using (hk₂.2 4 (by decide)).trans (h4same.trans (by simpa [s₀] using h4)))
    (by simpa [s₃, row] using h27) (by simp [s₃])
  have hk : Keeps R A s s₄ := hk₃.trans hk₄ (by simp [R]) (by simp [A])
  refine ⟨s₄, 2 + (t₁ + (t₂ + (2 + t₄))), .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))),
    ?_, hk, (hk.1 330 (by decide)).trans h330, hout, hshrink, hsetWords⟩
  omega

private def prunedPrefix (activity : List ℕ) (rows : List (List ℕ)) (i : ℕ) : List (List ℕ) :=
  (rows.take i).map (List.filter (gm06KeepActiveDart activity)) ++ rows.drop i

private theorem prunedPrefix_length (activity : List ℕ) (rows : List (List ℕ)) (i : ℕ) :
    (prunedPrefix activity rows i).length = rows.length := by
  simp only [prunedPrefix, List.length_append, List.length_map, List.length_take, List.length_drop]
  omega

private theorem prunedPrefix_get (activity : List ℕ) (rows : List (List ℕ)) (i : ℕ)
    (hi : i < rows.length) :
    (prunedPrefix activity rows i)[i]'(by rw [prunedPrefix_length]; exact hi) = rows[i] := by
  have hindex : i < ((rows.take i).map (List.filter (gm06KeepActiveDart activity)) ++ rows.drop i).length := by
    simp only [List.length_append, List.length_map, List.length_take, List.length_drop]
    omega
  change ((rows.take i).map (List.filter (gm06KeepActiveDart activity)) ++ rows.drop i)[i]'hindex = rows[i]
  rw [List.getElem_append_right (by simp [List.length_take, Nat.min_eq_left hi.le])]
  simp only [List.length_map, List.length_take, Nat.min_eq_left hi.le, Nat.sub_self, List.getElem_drop, Nat.add_zero]

private theorem prunedPrefix_succ (activity : List ℕ) (rows : List (List ℕ)) (i : ℕ)
    (hi : i < rows.length) :
    (prunedPrefix activity rows i).set i (rows[i].filter (gm06KeepActiveDart activity)) =
      prunedPrefix activity rows (i + 1) := by
  simp only [prunedPrefix]
  rw [List.drop_eq_getElem_cons hi]
  rw [List.set_append_right _ _ (by simp [List.length_take, Nat.min_eq_left hi.le])]
  simp only [List.length_map, List.length_take, Nat.min_eq_left hi.le, Nat.sub_self, List.set_cons_zero]
  rw [List.take_succ_eq_append_getElem hi, List.map_append, List.map_cons, List.map_nil]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The complete table command computes the pure row-wise filter,
keeps the number of rows fixed and never increases the encoded size. -/
theorem gm06PruneRotationsProg_exec {w : ℕ} (activity : List ℕ) (rows : List (List ℕ))
    (s : State) (hw : 2 < 2 ^ w) (hlen : 4 * (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (haLen : activity.length < 2 ^ w) (hbits : ∀ x ∈ activity, x ≤ 1)
    (hd : ∀ row ∈ rows, ∀ d ∈ row, d < 2 * activity.length)
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h30 : s.arrs 30 = activity) :
    ∃ s' t, Exec w gm06PruneRotationsProg s s' t ∧
      t ≤ 10 + rows.length * (260 + 34 * rows.length + 300 * (gm06EncodeRows rows).length) ∧
      Keeps [339, 330, 31, 7, 8, 9, 11, 313, 323, 324, 98, 331, 332, 333, 334, 335, 336, 337]
        [25, 27, 29, 4, 28] s s' ∧
      s'.arrs 4 = gm06EncodeRows (gm06PrunedRotationRows activity rows) ∧
      (s'.arrs 4).length ≤ (gm06EncodeRows rows).length ∧
      ∀ x ∈ s'.arrs 4, x < 2 ^ w := by
  have hn : (gm06EncodeRows rows).length < 2 ^ w := by omega
  have hcount : rows.length < 2 ^ w := hwords _ (by simp [gm06EncodeRows])
  let R := [339, 330, 31, 7, 8, 9, 11, 313, 323, 324, 98, 331, 332, 333, 334, 335, 336, 337]
  let A := [25, 27, 29, 4, 28]
  let Inv := fun i st => st.regs 330 = i ∧ st.regs 339 = rows.length ∧ Keeps R A s st ∧
    st.arrs 4 = gm06EncodeRows (prunedPrefix activity rows i) ∧
    (gm06EncodeRows (prunedPrefix activity rows i)).length ≤ (gm06EncodeRows rows).length ∧
    ∀ x ∈ gm06EncodeRows (prunedPrefix activity rows i), x < 2 ^ w
  let s₀ := s.setReg 339 rows.length
  let s₁ := s₀.setReg 330 0
  have hread : (Expr.read 4 (.const 0)).eval w s = some rows.length := by
    have hh := GraphMinor.Compute.Crossing.eval_read (a := 4)
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (by rw [h4]; simp [gm06EncodeRows])
      (by simpa only [h4, gm06EncodeRows, List.getElem_cons_zero] using hcount)
    simpa only [h4, gm06EncodeRows, List.getElem_cons_zero] using hh
  have he₀ : Exec w (.assign 339 (.read 4 (.const 0))) s s₀ 3 := .assign hread
  have he₁ : Exec w (.assign 330 (.const 0)) s₀ s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hInv : Inv 0 s₁ := by
    refine ⟨by simp [s₁], by simp [s₁, s₀],
      ((Keeps.refl _ _ s).setReg (by simp [R]) _).setReg (by simp [R]) _, ?_, ?_, ?_⟩
    · simpa only [prunedPrefix, List.take_zero, List.map_nil, List.nil_append, List.drop_zero] using
        (show s₁.arrs 4 = gm06EncodeRows rows by simpa [s₁, s₀] using h4)
    · simp [prunedPrefix]
    · simpa only [prunedPrefix, List.take_zero, List.map_nil, List.nil_append, List.drop_zero] using hwords
  obtain ⟨s₂, t₂, he₂, ht₂, hfinal⟩ := GraphMinor.Compute.Crossing.forUp_exec' Inv rows.length
    (250 + 34 * rows.length + 300 * (gm06EncodeRows rows).length)
    (r_i := 330) (hi := .reg 339) (body := gm06PruneRotationAtRowProg) (by omega) hcount
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_reg h.2.1 hcount⟩)
    (fun i hi st h => by
      obtain ⟨h330, h339, hk, hcode, hsize, hfit⟩ := h
      let current := prunedPrefix activity rows i
      have hi' : i < current.length := by rw [prunedPrefix_length]; exact hi
      have hcurrentBound : (gm06EncodeRows current).length ≤ (gm06EncodeRows rows).length := hsize
      have hstrong : 4 * (gm06EncodeRows current).length < 2 ^ w := by omega
      obtain ⟨st', t, hex, ht, hk', hiout, hout, hsmaller, hnewfit⟩ :=
        gm06PruneRotationAtRowProg_exec activity current i hi' st hw hstrong hfit haLen hbits
          (by rw [prunedPrefix_get activity rows i hi]; exact hd _ (List.getElem_mem hi)) hcode
          ((hk.2 30 (by decide)).trans h30) h330
      have hnext : current.set i (current[i].filter (gm06KeepActiveDart activity)) =
          prunedPrefix activity rows (i + 1) := by
        rw [prunedPrefix_get activity rows i hi]
        exact prunedPrefix_succ activity rows i hi
      have hk'' : Keeps R A s st' := hk.trans hk' (by simp [R]) (by simp [A])
      refine ⟨st', t, hex, ?_, ?_, hiout⟩
      · have hc : current.length = rows.length := prunedPrefix_length activity rows i
        rw [hc] at ht
        omega
      · refine ⟨by simp, ?_, hk''.setReg (by simp [R]) _, ?_, ?_, ?_⟩
        · simpa only [State.setReg_regs_ne _ _ (by decide : (339 : ℕ) ≠ 330)] using
            (hk'.1 339 (by decide)).trans h339
        · simpa only [State.setReg_arrs, hnext] using hout
        · rw [← hnext]
          exact hsmaller.trans hsize
        · simpa only [hnext] using hnewfit)
    s₁ hInv
  have hprefix : prunedPrefix activity rows rows.length = gm06PrunedRotationRows activity rows := by
    simp [prunedPrefix, gm06PrunedRotationRows]
  refine ⟨s₂, 3 + (2 + t₂), .seq he₀ (.seq he₁ he₂), ?_, hfinal.2.2.1, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₂
    have hc : 1 + 6 + (250 + 34 * rows.length + 300 * (gm06EncodeRows rows).length) ≤
        260 + 34 * rows.length + 300 * (gm06EncodeRows rows).length := by omega
    have hh := Nat.add_le_add_left (Nat.mul_le_mul_left rows.length hc) 3
    have hb := ht₂.trans hh
    omega
  · simpa only [hprefix] using hfinal.2.2.2.1
  · rw [hfinal.2.2.2.1]
    exact hfinal.2.2.2.2.1
  · rw [hfinal.2.2.2.1]
    exact hfinal.2.2.2.2.2

/-- Build the cuff-extended activity array and prune all current
rows after a deletion mask update. -/
@[expose] def gm06PruneCurrentRotationsProg : Cmd :=
  .seq gm06AugmentedActivityProg gm06PruneRotationsProg

/-- Complete mask-to-rotation pruning preserves all instance fields
except the rotation code and its local work arrays. -/
theorem gm06PruneCurrentRotationsProg_exec {w : ℕ} (mask cuff : List ℕ)
    (rows : List (List ℕ)) (s : State) (hw : 2 < 2 ^ w)
    (hlen : 4 * (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (haLen : mask.length + 2 * cuff.length < 2 ^ w) (hbits : ∀ x ∈ mask, x ≤ 1)
    (hd : ∀ row ∈ rows, ∀ d ∈ row, d < 2 * (mask.length + 2 * cuff.length))
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h12 : s.arrs 12 = mask) (h6 : s.arrs 6 = cuff) :
    ∃ s' t, Exec w gm06PruneCurrentRotationsProg s s' t ∧
      t ≤ 27 + 16 * mask.length + 30 * cuff.length +
        rows.length * (260 + 34 * rows.length + 300 * (gm06EncodeRows rows).length) ∧
      Keeps [339, 330, 31, 7, 8, 9, 11, 313, 323, 324, 98, 331, 332, 333, 334, 335, 336, 337]
        [30, 25, 27, 29, 4, 28] s s' ∧
      s'.arrs 4 = gm06EncodeRows (gm06PrunedRotationRows (gm06AugmentedActivity mask cuff.length) rows) ∧
      s'.arrs 30 = gm06AugmentedActivity mask cuff.length ∧
      (s'.arrs 4).length ≤ (gm06EncodeRows rows).length ∧
      ∀ x ∈ s'.arrs 4, x < 2 ^ w := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, h30⟩ := gm06AugmentedActivityProg_exec
    mask cuff s hw haLen hbits h12 h6
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout, hsize, hfit⟩ := gm06PruneRotationsProg_exec
    (gm06AugmentedActivity mask cuff.length) rows s₁ hw hlen hwords
    (by simpa only [gm06AugmentedActivity_length] using haLen)
    (gm06AugmentedActivity_bits mask cuff.length hbits)
    (by simpa only [gm06AugmentedActivity_length] using hd)
    ((hk₁.2 4 (by decide)).trans h4) h30
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega,
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp),
    hout, (hk₂.2 30 (by decide)).trans h30, hsize, hfit⟩

end GraphMinor.Compute
