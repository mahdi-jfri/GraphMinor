module

public import GraphMinor.Compute.GM06ReplaceRotationRow
public import GraphMinor.Compute.TwoPathsRename

/-!
# Selecting and installing the Reduction 4 linkage row

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) changes one
linkage path and keeps all others. The existing verified row selector
and row replacement commands are relocated into the finite workspace.
The selected path is read from the full encoding, and installation
returns the full updated encoding. All graph rotations are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

private theorem keeps_rename {f : ℕ → ℕ} (hf : Function.Involutive f)
    {R A : List ℕ} {s t : State} (hk : Keeps R A s t) :
    Keeps (R.map f) (A.map f) (renameState f s) (renameState f t) := by
  constructor
  · intro r hr
    change t.regs (f r) = s.regs (f r)
    apply hk.1
    intro hm
    exact hr (List.mem_map.mpr ⟨f r, hm, hf r⟩)
  · intro a ha
    change t.arrs (f a) = s.arrs (f a)
    apply hk.2
    intro hm
    exact ha (List.mem_map.mpr ⟨f a, hm, hf a⟩)

/-- Relocate all memory touched by the selector into the reserved workspace. -/
def gm06Apply4ReadRename (x : ℕ) : ℕ :=
  if x = 7 then 660
  else if x = 660 then 7
  else if x = 8 then 661
  else if x = 661 then 8
  else if x = 9 then 662
  else if x = 662 then 9
  else if x = 11 then 664
  else if x = 664 then 11
  else if x = 31 then 668
  else if x = 668 then 31 else x

/-- The finite relocation exchanges disjoint address pairs. -/
theorem gm06Apply4ReadRename_involutive : Function.Involutive gm06Apply4ReadRename := by
  intro x
  by_cases hx : x ∈ [7, 660, 8, 661, 9, 662, 11, 664, 31, 668]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    have hfixed : gm06Apply4ReadRename x = x := by simp_all [gm06Apply4ReadRename]
    rw [hfixed, hfixed]

/-- Read the selected full-linkage row into array 610. -/
def gm06ReadApply4RowProg : Cmd :=
  .seq (.assign 668 (.reg 669))
    (renameCmd gm06Apply4ReadRename (gm06SelectRowProg 600 610))

/-- The old row is computed from the full linkage encoding itself. -/
theorem gm06ReadApply4RowProg_exec {w : ℕ} (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length)
    (s : State) (hw : 1 < 2 ^ w) (hlen : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h669 : s.regs 669 = i) :
    ∃ sf t, Exec w gm06ReadApply4RowProg s sf t ∧ t ≤ 18 + 17 * i + 22 * rows[i].length ∧
      Keeps [660, 661, 662, 664, 668] [610] s sf ∧ sf.arrs 610 = rows[i] := by
  have hiw : i < 2 ^ w := hi.trans (hwords _ (by simp [gm06EncodeRows]))
  let s₀ := s.setReg 668 i
  let sr := renameState gm06Apply4ReadRename s₀
  have he₀ : Exec w (.assign 668 (.reg 669)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h669 hiw)
  obtain ⟨sm, t, he, ht, hd, _, _, hk⟩ := gm06SelectRowProg_exec 600 610 (by decide) rows i hi sr hw
    h600 hlen hwords (by simp [sr, renameState, gm06Apply4ReadRename, s₀])
  have hinv : renameState gm06Apply4ReadRename sr = s₀ := by
    ext x <;> simp only [sr, renameState_regs, renameState_arrs, gm06Apply4ReadRename_involutive x]
  have he' : Exec w (renameCmd gm06Apply4ReadRename (gm06SelectRowProg 600 610)) s₀
      (renameState gm06Apply4ReadRename sm) t := by
    simpa only [hinv] using exec_renameCmd gm06Apply4ReadRename_involutive he
  have hk' := keeps_rename gm06Apply4ReadRename_involutive hk
  have hR : [7, 8, 9, 11, 31].map gm06Apply4ReadRename = [660, 661, 662, 664, 668] := by decide
  have hA : [610].map gm06Apply4ReadRename = [610] := by decide
  rw [hR, hA, hinv] at hk'
  refine ⟨_, 2 + t, .seq he₀ he', by omega,
    ((Keeps.refl _ _ s).setReg (by simp) _).trans hk' (fun _ h => h) (fun _ h => h), ?_⟩
  exact hd

/-- Relocate all memory touched by the row installer into the reserved workspace. -/
def gm06Apply4InstallRename (x : ℕ) : ℕ :=
  if x = 7 then 660
  else if x = 660 then 7
  else if x = 8 then 661
  else if x = 661 then 8
  else if x = 9 then 662
  else if x = 662 then 9
  else if x = 11 then 664
  else if x = 664 then 11
  else if x = 31 then 668
  else if x = 668 then 31
  else if x = 323 then 665
  else if x = 665 then 323
  else if x = 324 then 666
  else if x = 666 then 324
  else if x = 313 then 667
  else if x = 667 then 313
  else if x = 98 then 659
  else if x = 659 then 98
  else if x = 4 then 600
  else if x = 600 then 4
  else if x = 27 then 637
  else if x = 637 then 27
  else if x = 25 then 601
  else if x = 601 then 25
  else if x = 28 then 602
  else if x = 602 then 28 else x

/-- The finite relocation exchanges disjoint address pairs. -/
theorem gm06Apply4InstallRename_involutive : Function.Involutive gm06Apply4InstallRename := by
  intro x
  by_cases hx : x ∈ [7, 660, 8, 661, 9, 662, 11, 664, 31, 668, 323, 665, 324, 666, 313, 667, 98, 659, 4, 600, 27, 637, 25, 601, 28, 602]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    have hfixed : gm06Apply4InstallRename x = x := by simp_all [gm06Apply4InstallRename]
    rw [hfixed, hfixed]

/-- Install the replacement row 637 in the full linkage encoding 600. -/
def gm06InstallApply4RowProg : Cmd :=
  .seq (.assign 668 (.reg 669)) (renameCmd gm06Apply4InstallRename gm06ReplaceRotationRowProg)

/-- Installation changes exactly the selected row, keeping its projected
replacement array and every other linkage row. -/
theorem gm06InstallApply4RowProg_exec {w : ℕ} (rows : List (List ℕ)) (i : ℕ) (hi : i < rows.length)
    (row : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hlen : (gm06EncodeRows rows).length < 2 ^ w)
    (hnewLen : (gm06EncodeRows (rows.set i row)).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) (hrowWords : ∀ x ∈ row, x < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h637 : s.arrs 637 = row) (h669 : s.regs 669 = i) :
    ∃ sf t, Exec w gm06InstallApply4RowProg s sf t ∧
      t ≤ 152 + 17 * i + 22 * rows[i].length + 80 * ((gm06EncodeRows rows).length + row.length) ∧
      Keeps [660, 661, 662, 664, 668, 665, 666, 667, 659] [601, 600, 602] s sf ∧
      sf.arrs 600 = gm06EncodeRows (rows.set i row) ∧ sf.arrs 637 = row := by
  have hiw : i < 2 ^ w := hi.trans (hwords _ (by simp [gm06EncodeRows]))
  let s₀ := s.setReg 668 i
  let sr := renameState gm06Apply4InstallRename s₀
  have he₀ : Exec w (.assign 668 (.reg 669)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h669 hiw)
  obtain ⟨sm, t, he, ht, hk, hd, hr⟩ := gm06ReplaceRotationRowProg_exec rows i hi row sr hw
    hlen hnewLen hwords hrowWords h600 h637 (by simp [sr, renameState, gm06Apply4InstallRename, s₀])
  have hinv : renameState gm06Apply4InstallRename sr = s₀ := by
    ext x <;> simp only [sr, renameState_regs, renameState_arrs, gm06Apply4InstallRename_involutive x]
  have he' : Exec w (renameCmd gm06Apply4InstallRename gm06ReplaceRotationRowProg) s₀
      (renameState gm06Apply4InstallRename sm) t := by
    simpa only [hinv] using exec_renameCmd gm06Apply4InstallRename_involutive he
  have hk' := keeps_rename gm06Apply4InstallRename_involutive hk
  have hR : [7, 8, 9, 11, 31, 323, 324, 313, 98].map gm06Apply4InstallRename =
      [660, 661, 662, 664, 668, 665, 666, 667, 659] := by decide
  have hA : [25, 4, 28].map gm06Apply4InstallRename = [601, 600, 602] := by decide
  rw [hR, hA, hinv] at hk'
  exact ⟨_, 2 + t, .seq he₀ he', by omega,
    ((Keeps.refl _ _ s).setReg (by simp) _).trans hk' (fun _ h => h) (fun _ h => h), hd, hr⟩

end GraphMinor.Compute
