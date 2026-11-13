module

public import GraphMinor.Compute.GM06SkipRows
public import GraphMinor.Compute.GM06ReadRow
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.GM06RowPositions

/-!
# Selecting a supplied row by its input index

Rotation and linkage rows have input-dependent indices. Start after
the row count, skip the number of rows held in register 31, then copy
the next row to a work array. This is one fixed RAM program. Its
execution proof returns the supplied row and bounds its running time.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Select the row numbered by register 31 from a coded row-list array. -/
def gm06SelectRowProg (src dst : Arr) : Cmd :=
  .seq (.assign 8 (.const 1))
    (.seq (gm06SkipRowsProg src 8 9 31) (gm06ReadRowProg src dst))

/-- The row selector returns the indexed row, preserves its source
array and records the cursor immediately after the selected row. -/
theorem gm06SelectRowProg_exec_with_end {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs src = gm06EncodeRows rows)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeRows rows, v < 2 ^ w) (hr : s.regs 31 = i) :
    ∃ s' t, Exec w (gm06SelectRowProg src dst) s s' t ∧
      t ≤ 16 + 17 * i + 22 * rows[i].length ∧ s'.arrs dst = rows[i] ∧
      s'.regs 31 = 0 ∧ s'.arrs src = s.arrs src ∧
      Keeps [7, 8, 9, 11, 31] [dst] s s' ∧
      s'.regs 8 = 1 + (gm06EncodeRowsPayload (rows.take i)).length + 1 + rows[i].length := by
  have hsplit : rows.take i ++ rows[i] :: rows.drop (i + 1) = rows := by
    rw [← List.drop_eq_getElem_cons hi]
    exact List.take_append_drop i rows
  have hpayload : gm06EncodeRowsPayload rows =
      gm06EncodeRowsPayload (rows.take i) ++ gm06EncodeNatList rows[i] ++
        gm06EncodeRowsPayload (rows.drop (i + 1)) := by
    calc
      gm06EncodeRowsPayload rows = gm06EncodeRowsPayload
          (rows.take i ++ rows[i] :: rows.drop (i + 1)) := congrArg gm06EncodeRowsPayload hsplit.symm
      _ = _ := by
        rw [gm06EncodeRowsPayload_append]
        simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc]
  have hlength : (gm06EncodeRows rows).length = 1 + (gm06EncodeRowsPayload rows).length := by
    simp [gm06EncodeRows]
    omega
  have hcount : rows.length < 2 ^ w := hwords _ (by simp [gm06EncodeRows])
  have htake : (rows.take i).length = i := List.length_take_of_le hi.le
  have hend : 1 + (gm06EncodeRowsPayload (rows.take i)).length < 2 ^ w := by
    have hh := gm06RowsPrefixLength_le rows i
    omega
  let s₀ := s.setReg 8 1
  have hs : AtStream src 1 (gm06EncodeRowsPayload (rows.take i) ++
      (gm06EncodeNatList rows[i] ++ gm06EncodeRowsPayload (rows.drop (i + 1)))) s₀ := by
    refine ⟨[rows.length], rfl, ?_⟩
    simp only [s₀, State.setReg_arrs, ha, gm06EncodeRows, hpayload, List.singleton_append,
      List.append_assoc]
  obtain ⟨s₁, t₁, he₁, ht₁, hp₁, hc₁, hs₁, har₁, hreg₁⟩ := gm06SkipRowsProg_exec 8 9 31
    (by decide) (by decide) (by decide) (rows.take i)
    (gm06EncodeNatList rows[i] ++ gm06EncodeRowsPayload (rows.drop (i + 1))) hw
    (by rw [htake]; exact hi.trans hcount) hend hs (by simp [s₀])
    (by simpa only [s₀, State.setReg_regs_ne _ _ (by decide : 31 ≠ 8), htake] using hr)
  obtain ⟨pre, hpre, harray⟩ := hs₁
  have ha₁ : s₁.arrs src = pre ++ gm06EncodeNatList rows[i] ++
      gm06EncodeRowsPayload (rows.drop (i + 1)) := by
    simpa only [List.append_assoc] using harray
  have hsrc : s₁.arrs src = s.arrs src := har₁ src
  obtain ⟨s₂, t₂, he₂, ht₂, hd₂, hcursor₂, hregs₂, har₂⟩ := gm06ReadRowProg_exec src dst hne
    pre rows[i] (gm06EncodeRowsPayload (rows.drop (i + 1))) s₁ hw ha₁
    (by simpa only [hsrc, ha] using hn) (by simpa only [hsrc, ha] using hwords)
    (hp₁.trans hpre.symm)
  refine ⟨s₂, 2 + (t₁ + t₂),
    .seq (.assign (by simp [Expr.eval, checkWord, hw])) (.seq he₁ he₂),
    ?_, hd₂, ?_, ?_, ?_, ?_⟩
  · rw [htake] at ht₁
    omega
  · exact (hregs₂ 31 (by decide) (by decide) (by decide) (by decide)).trans hc₁
  · exact (har₂ src hne).trans hsrc
  · constructor
    · intro r hr'
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr'
      obtain ⟨h7, h8, h9, h11, h31⟩ := hr'
      have hh := (hregs₂ r h7 h8 h9 h11).trans (hreg₁ r h8 h9 h31)
      simpa only [s₀, State.setReg_regs_ne _ _ h8] using hh
    · intro a ha'
      have hne' : a ≠ dst := by simpa only [List.mem_singleton] using ha'
      simpa only [s₀, State.setReg_arrs] using (har₂ a hne').trans (har₁ a)

  · simpa only [hpre] using hcursor₂

/-- The row selector returns the indexed row and preserves its source array. -/
theorem gm06SelectRowProg_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs src = gm06EncodeRows rows)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeRows rows, v < 2 ^ w) (hr : s.regs 31 = i) :
    ∃ s' t, Exec w (gm06SelectRowProg src dst) s s' t ∧
      t ≤ 16 + 17 * i + 22 * rows[i].length ∧ s'.arrs dst = rows[i] ∧
      s'.regs 31 = 0 ∧ s'.arrs src = s.arrs src ∧
      Keeps [7, 8, 9, 11, 31] [dst] s s' := by
  obtain ⟨s', t, he, ht, hd, hzero, hsrc, hframe, _⟩ :=
    gm06SelectRowProg_exec_with_end src dst hne rows i hi s hw ha hn hwords hr
  exact ⟨s', t, he, ht, hd, hzero, hsrc, hframe⟩

end GraphMinor.Compute
