module

public import GraphMinor.Compute.GM06SelectedFaceIndex
public import GraphMinor.Compute.GM06PredecessorProgram

/-!
# Reading an indexed row from the computed face code

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) uses the
face row identified by the reverse inner cuff dart's owner. The face code
is a sequence of length-prefixed rows. This file relocates the verified
row reader to that code and proves the prefix-skipping loop. The loop
computes the target row address from the stored lengths and keeps the
owner table and target dart unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the next computed face row from 607 into 600, with cursor 661. -/
def gm06ReadFaceRowProg : Cmd :=
  renameCmd gm06RotationReadRename (gm06ReadRowProg 607 600)

/-- Exact face-row reading using the reserved high register block. -/
theorem gm06ReadFaceRowProg_exec {w : ℕ} (pre row tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 607 = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs 607).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 607, x < 2 ^ w)
    (hr : s.regs 661 = pre.length) :
    ∃ sf t, Exec w gm06ReadFaceRowProg s sf t ∧
      t ≤ 13 + 22 * row.length ∧ Keeps [660, 661, 662, 664] [600] s sf ∧
      sf.arrs 600 = row ∧ sf.regs 661 = pre.length + 1 + row.length := by
  let sr := renameState gm06RotationReadRename s
  obtain ⟨sm, t, he, ht, hd, hp, hregs, harrs⟩ := gm06ReadRowProg_exec
    607 600 (by decide) pre row tail sr hw ha hn hwords hr
  have hinv : renameState gm06RotationReadRename sr = s := by
    ext x <;> simp [sr, renameState, gm06RotationReadRename_involutive x]
  refine ⟨renameState gm06RotationReadRename sm, t, ?_, ht, ⟨?_, ?_⟩, hd, hp⟩
  · rw [← hinv]
    exact exec_renameCmd gm06RotationReadRename_involutive he
  · intro r hr
    have hneq : gm06RotationReadRename r ≠ 7 ∧ gm06RotationReadRename r ≠ 8 ∧
        gm06RotationReadRename r ≠ 9 ∧ gm06RotationReadRename r ≠ 11 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      unfold gm06RotationReadRename
      split_ifs <;> omega
    change sm.regs (gm06RotationReadRename r) = s.regs r
    rw [hregs _ hneq.1 hneq.2.1 hneq.2.2.1 hneq.2.2.2]
    exact congrArg s.regs (gm06RotationReadRename_involutive r)
  · intro a ha
    have hneq : gm06RotationReadRename a ≠ 600 := by
      simp only [List.mem_singleton] at ha
      unfold gm06RotationReadRename
      split_ifs <;> omega
    change sm.arrs (gm06RotationReadRename a) = s.arrs a
    rw [harrs _ hneq]
    exact congrArg s.arrs (gm06RotationReadRename_involutive a)

/-- Skip the number of face rows in register 665, advancing cursor 661. -/
def gm06SkipFaceRowsLoop : Cmd :=
  .while (.reg 665) (.seq gm06ReadFaceRowProg (.assign 665 (.op .sub (.reg 665) (.const 1))))

/-- The skip loop advances past precisely the indicated stored rows,
with linear time in their encoded size. -/
theorem gm06SkipFaceRowsLoop_exec {w : ℕ} (rows : List (List ℕ)) (pre tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hc : rows.length < 2 ^ w)
    (ha : s.arrs 607 = pre ++ gm06EncodeRowsPayload rows ++ tail)
    (hn : (s.arrs 607).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 607, x < 2 ^ w)
    (h661 : s.regs 661 = pre.length) (h665 : s.regs 665 = rows.length) :
    ∃ sf t, Exec w gm06SkipFaceRowsLoop s sf t ∧
      t ≤ 1 + 18 * rows.length + 22 * rows.flatten.length ∧
      Keeps [660, 661, 662, 664, 665] [600] s sf ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload rows).length ∧ sf.regs 665 = 0 := by
  induction rows generalizing pre s with
  | nil =>
    exact ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg h665 (Nat.two_pow_pos w)), by simp,
      Keeps.refl _ _ _, by simpa [gm06EncodeRowsPayload] using h661, h665⟩
  | cons row rows ih =>
    simp only [List.length_cons] at hc h665
    have hsource : s.arrs 607 = pre ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload rows ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using ha
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, _, hp₁⟩ := gm06ReadFaceRowProg_exec
      pre row (gm06EncodeRowsPayload rows ++ tail) s hw hsource hn hwords h661
    have hcount : s₁.regs 665 = rows.length + 1 := (hk₁.1 665 (by decide)).trans h665
    let s₂ := s₁.setReg 665 rows.length
    have he₂ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₁ s₂ 4 :=
      .assign (by
        have he := GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg hcount hc)
          (GraphMinor.Compute.Crossing.eval_const hw)
        simpa using he)
    have hk₁₂ : Keeps [660, 661, 662, 664, 665] [600] s s₂ :=
      (hk₁.mono (by simp) (fun _ h => h)).setReg (by simp) _
    let pre' := pre ++ gm06EncodeNatList row
    have hsrc : s₂.arrs 607 = pre' ++ gm06EncodeRowsPayload rows ++ tail := by
      rw [hk₁₂.2 607 (by decide)]
      simpa only [pre', List.append_assoc] using hsource
    obtain ⟨sf, tf, hef, htf, hkf, hpf, hcf⟩ := ih pre' s₂ (by omega) hsrc
      (by rw [hk₁₂.2 607 (by decide)]; exact hn) (by rw [hk₁₂.2 607 (by decide)]; exact hwords)
      (by simpa [s₂, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp₁) (by simp [s₂])
    refine ⟨sf, 1 + (t₁ + 4) + tf, .while_true (GraphMinor.Compute.Crossing.eval_reg h665 hc)
      (Nat.succ_ne_zero _) (.seq he₁ he₂) hef, ?_, hk₁₂.trans hkf (fun _ h => h) (fun _ h => h), ?_, hcf⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf

/-- Splitting a face code at an indexed row preserves its stored boundaries. -/
theorem gm06EncodeRowsPayload_split (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length) :
    gm06EncodeRowsPayload rows = gm06EncodeRowsPayload (rows.take i) ++ gm06EncodeNatList rows[i] ++
      gm06EncodeRowsPayload (rows.drop (i + 1)) := by
  conv_lhs => rw [← List.take_append_drop i rows, List.drop_eq_getElem_cons hi]
  simp only [gm06EncodeRowsPayload, List.flatMap_append, List.flatMap_cons, List.append_assoc]

end GraphMinor.Compute
