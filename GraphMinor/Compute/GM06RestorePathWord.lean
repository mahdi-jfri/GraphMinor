module

public import GraphMinor.Compute.GM06ReplaceRotationRow
public import GraphMinor.Compute.TwoPathsRename
public import Mathlib.Logic.Equiv.Basic
import GraphMinor.Compute.GM06RowPositions
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Restoring a contracted initial edge to an output path

The linkage output of VI (5.7), page 133, is lifted through the
contractions in reverse order. A recovery record gives a path index
and its old first directed edge. Read that output row, prepend the
recorded edge and replace the row in the encoding. The replacement
command is the proved rotation-row command with addresses 4 and 8
exchanged. The procedure reads the current output paths and the
recorded word, and preserves all other rows.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- Move the row replacement from the rotation table to the
path table by exchanging addresses 4 and 8. -/
@[expose] def gm06ReplacePathRowProg : Cmd :=
  renameCmd (Equiv.swap 4 8) gm06ReplaceRotationRowProg

/-- Address renaming transfers the exact row replacement and its
bound to the path encoding, preserving the replacement row. -/
theorem gm06ReplacePathRowProg_exec {w : ℕ} (rows : List (List ℕ))
    (i : ℕ) (hi : i < rows.length) (row : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : (gm06EncodeRows rows).length < 2 ^ w)
    (hn' : (gm06EncodeRows (rows.set i row)).length < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) (hy : ∀ x ∈ row, x < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows) (h27 : s.arrs 27 = row) (h31 : s.regs 31 = i) :
    ∃ s' t, Exec w gm06ReplacePathRowProg s s' t ∧
      t ≤ 150 + 17 * i + 22 * rows[i].length + 80 * ((gm06EncodeRows rows).length + row.length) ∧
      Keeps [7, 4, 9, 11, 31, 323, 324, 313, 98] [25, 8, 28] s s' ∧
      s'.arrs 8 = gm06EncodeRows (rows.set i row) ∧ s'.arrs 27 = row := by
  let f : ℕ → ℕ := Equiv.swap 4 8
  have hf : Function.Involutive f := Equiv.swap_apply_self 4 8
  let ss := renameState f s
  obtain ⟨st, t, hex, ht, hk, hout, hrow⟩ := gm06ReplaceRotationRowProg_exec
    rows i hi row ss hw hn hn' hx hy
    (by simpa [ss, f, Equiv.swap_apply_def] using h8) (by simpa [ss, f, Equiv.swap_apply_def] using h27) (by simpa [ss, f, Equiv.swap_apply_def] using h31)
  have hss : renameState f ss = s := by
    apply State.ext
    · funext r
      change s.regs (f (f r)) = s.regs r
      rw [hf r]
    · funext a
      change s.arrs (f (f a)) = s.arrs a
      rw [hf a]
  refine ⟨renameState f st, t, ?_, ht, ⟨?_, ?_⟩, ?_, ?_⟩
  · simpa only [hss, gm06ReplacePathRowProg, f] using exec_renameCmd hf hex
  · intro r hr
    have hr' : f r ∉ [7, 8, 9, 11, 31, 323, 324, 313, 98] := by
      intro hm
      have hm' : r ∈ [7, 8, 9, 11, 31, 323, 324, 313, 98].map f :=
        List.mem_map.mpr ⟨f r, hm, hf r⟩
      exact hr (by simpa [f, Equiv.swap_apply_def] using hm')
    simpa only [renameState_regs, ss, renameState_regs, hf r] using hk.1 (f r) hr'
  · intro a ha
    have ha' : f a ∉ [25, 4, 28] := by
      intro hm
      have hm' : a ∈ [25, 4, 28].map f := List.mem_map.mpr ⟨f a, hm, hf a⟩
      exact ha (by simpa [f, Equiv.swap_apply_def] using hm')
    simpa only [renameState_arrs, ss, renameState_arrs, hf a] using hk.2 (f a) ha'
  · simpa [f, Equiv.swap_apply_def] using hout
  · simpa [f, Equiv.swap_apply_def] using hrow

/-- Prepend word 23 to output path 295, keeping all other rows. -/
@[expose] def gm06RestorePathWordProg : Cmd :=
  .seq (.assign 31 (.reg 295))
    (.seq (gm06SelectRowProg 8 24)
      (.seq (.alloc 27 (.op .add (.len 24) (.const 1)))
        (.seq (.write 27 (.const 0) (.reg 23))
          (.seq (gm06RotationSliceProg 24 27 (.len 24) (.const 0) (.const 1))
            (.seq (.assign 31 (.reg 295)) gm06ReplacePathRowProg)))))

/-- The recovery write adds precisely the recorded directed edge
to the selected current output path, increasing its encoding by
one word. It has a linear bound in the current encoded output. -/
theorem gm06RestorePathWordProg_exec {w : ℕ} (rows : List (List ℕ)) (i d : ℕ)
    (hi : i < rows.length) (s : State) (hw : 1 < 2 ^ w)
    (hn : (gm06EncodeRows rows).length + 1 < 2 ^ w)
    (hx : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) (hd : d < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows rows) (h295 : s.regs 295 = i) (h23 : s.regs 23 = d) :
    ∃ s' t, Exec w gm06RestorePathWordProg s s' t ∧
      t ≤ 300 + 34 * i + 140 * rows[i].length + 80 * (gm06EncodeRows rows).length ∧
      Keeps [31, 7, 8, 9, 11, 313, 4, 323, 324, 98] [24, 27, 25, 8, 28] s s' ∧
      s'.arrs 8 = gm06EncodeRows (rows.set i (d :: rows[i])) ∧
      (s'.arrs 8).length = (gm06EncodeRows rows).length + 1 := by
  have hN : (gm06EncodeRows rows).length < 2 ^ w := by omega
  have hcount : rows.length < 2 ^ w := hx _ (by simp [gm06EncodeRows])
  have hiw := hi.trans hcount
  have hpre := gm06RowsPrefixLength_le rows (i + 1)
  rw [gm06RowsPrefixLength_succ rows hi] at hpre
  have htotal : (gm06EncodeRows rows).length = 1 + (gm06EncodeRowsPayload rows).length := by
    simp only [gm06EncodeRows, List.length_cons]; omega
  have hrowlen : rows[i].length + 1 < 2 ^ w := by omega
  have hrowWords : ∀ x ∈ rows[i], x < 2 ^ w := by
    intro x hm
    apply hx x
    apply List.mem_cons_of_mem
    exact List.mem_flatMap.mpr ⟨rows[i], List.getElem_mem hi, by simp [gm06EncodeNatList, hm]⟩
  have hnewlen := gm06EncodeRows_set_length rows i hi (d :: rows[i])
  simp only [List.length_cons] at hnewlen
  have hnewcode : (gm06EncodeRows (rows.set i (d :: rows[i]))).length =
      (gm06EncodeRows rows).length + 1 := by omega
  let s₀ := s.setReg 31 i
  have he₀ : Exec w (.assign 31 (.reg 295)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h295 hiw)
  obtain ⟨s₁, t₁, he₁, ht₁, hrow, _, hsrc, hk₁⟩ := gm06SelectRowProg_exec
    8 24 (by decide) rows i hi s₀ hw (by simpa [s₀] using h8) hN hx (by simp [s₀])
  let R := [31, 7, 8, 9, 11, 313, 4, 323, 324, 98]
  let A := [24, 27, 25, 8, 28]
  have hk₀ : Keeps R A s s₀ := (Keeps.refl _ _ s).setReg (by simp [R]) _
  have hk₁' : Keeps R A s s₁ := hk₀.trans hk₁ (by simp [R]) (by simp [A])
  let s₂ := s₁.setArr 27 (List.replicate (rows[i].length + 1) 0)
  have he₂ : Exec w (.alloc 27 (.op .add (.len 24) (.const 1))) s₁ s₂ (3 + (rows[i].length + 1)) :=
    .alloc (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_len hrow (by omega)) (GraphMinor.Compute.Crossing.eval_const hw) hrowlen)
  have hk₂ : Keeps R A s s₂ := hk₁'.setArr (by simp [A]) _
  let s₃ := s₂.writeArr 27 0 d
  have he₃ : Exec w (.write 27 (.const 0) (.reg 23)) s₂ s₃ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_reg ((hk₂.1 23 (by decide)).trans h23) hd)
      (by simp [s₂])
  have hbuf : s₃.arrs 27 = [d] ++ List.replicate rows[i].length 0 := by
    simp [s₃, s₂, List.replicate_succ]
  have hk₃ : Keeps R A s s₃ := hk₂.writeArr (by simp [A]) _ _
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm06RotationSliceProg_exec
    24 27 (by decide) (.len 24) (.const 0) (.const 1) rows[i] [d] 0
    rows[i].length rows[i].length s₃ hw (by omega) (by omega) hrowWords (Nat.le_refl _)
    (by simp only [List.length_singleton]; omega) (by simpa [s₃, s₂] using hrow) hbuf
    (fun st hk => GraphMinor.Compute.Crossing.eval_len
      ((hk.2 24 (by decide)).trans (show s₃.arrs 24 = rows[i] by simpa [s₃, s₂] using hrow)) (by omega))
    (fun _ _ => GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    (fun _ _ => by simp [Expr.eval, checkWord, hw])
  have hd₄' : s₄.arrs 27 = d :: rows[i] := by simpa using hd₄
  have hk₄' : Keeps R A s s₄ := hk₃.trans hk₄ (by simp [R]) (by simp [A])
  let s₅ := s₄.setReg 31 i
  have he₅ : Exec w (.assign 31 (.reg 295)) s₄ s₅ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg ((hk₄'.1 295 (by decide)).trans h295) hiw)
  have hk₅ : Keeps R A s s₅ := hk₄'.setReg (by simp [R]) _
  have hsource : s₅.arrs 8 = gm06EncodeRows rows := by
    simpa [s₅, s₃, s₂, s₀] using (hk₄.2 8 (by decide)).trans
      (show s₃.arrs 8 = gm06EncodeRows rows by simpa [s₃, s₂, s₀] using hsrc.trans h8)
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, hout, _⟩ := gm06ReplacePathRowProg_exec
    rows i hi (d :: rows[i]) s₅ hw hN (by rw [hnewcode]; exact hn) hx
    (by intro x hm; rcases List.mem_cons.mp hm with rfl | hm; exact hd; exact hrowWords x hm)
    hsource (by simpa [s₅] using hd₄') (by simp [s₅])
  refine ⟨s₆, 2 + (t₁ + ((3 + (rows[i].length + 1)) + (3 + (t₄ + (2 + t₆))))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆))))), ?_,
    hk₅.trans hk₆ (by simp [R]) (by simp [A]), hout, ?_⟩
  · simp only [Expr.cost] at ht₄
    simp only [List.length_cons] at ht₆
    omega
  · rw [hout, hnewcode]

end GraphMinor.Compute
