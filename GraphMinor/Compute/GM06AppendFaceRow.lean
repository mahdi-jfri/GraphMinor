module

public import GraphMinor.Compute.GM06FaceBuffers

/-!
# Appending one discovered face row

FACE_ROWS in Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
starts a new row at an unseen dart. Reserve its length word, run the
return-to-start traversal, fill that length, and update the row count.
This file proves the exact owner table and encoded buffer after this
whole operation. The proof uses the cyclic row and space bounds of
the local situation; the outer scan supplies them from its invariant.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Prepare the current dart, row label and new row's length position. -/
def gm06FaceRowBegin : Cmd :=
  .seq (.assign 651 (.reg 652))
    (.seq (.assign 654 (.op .add (.reg 655) (.const 1)))
      (.seq (.assign 657 (.reg 656)) (.assign 656 (.op .add (.reg 656) (.const 1)))))

/-- Fill the row length, increment the row count and store the count. -/
def gm06FaceRowEnd : Cmd :=
  .seq (.write 606 (.reg 657) (.op .sub (.op .sub (.reg 656) (.reg 657)) (.const 1)))
    (.seq (.assign 655 (.op .add (.reg 655) (.const 1))) (.write 606 (.const 0) (.reg 655)))

/-- Append the complete orbit at start register 652 to the row buffer. -/
def gm06AppendFaceRowProg : Cmd :=
  .seq gm06FaceRowBegin (.seq gm06OrbitWriteProg gm06FaceRowEnd)

/-- Exact execution of one discovered face row, including its length
and the updated count. The result agrees with appending that row to
the pure list, and every visited dart gets the new row label. -/
theorem gm06AppendFaceRowProg_exec {w : ℕ}
    (successors : List ℕ) (rows : List (List ℕ)) (start : ℕ) (rest : List ℕ)
    (cap : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : successors.length < 2 ^ w) (hs : start < successors.length)
    (hd : ∀ d ∈ rest, d < successors.length) (hnot : start ∉ rest)
    (hchain : List.IsChain (fun a b => successors[a]? = some b) (start :: rest ++ [start]))
    (hroom : (gm06EncodeRows (rows ++ [start :: rest])).length ≤ cap)
    (hcap : cap < 2 ^ w)
    (h603 : s.arrs 603 = successors)
    (h605 : s.arrs 605 = gm06FaceOwners successors.length rows)
    (h606 : s.arrs 606 = gm06FaceBuffer cap rows)
    (h652 : s.regs 652 = start) (h655 : s.regs 655 = rows.length)
    (h656 : s.regs 656 = (gm06EncodeRows rows).length) :
    ∃ sf t, Exec w gm06AppendFaceRowProg s sf t ∧
      t ≤ 26 + 18 * (rest.length + 1) ∧
      Keeps [651, 654, 655, 656, 657] [605, 606] s sf ∧
      sf.arrs 605 = gm06FaceOwners successors.length (rows ++ [start :: rest]) ∧
      sf.arrs 606 = gm06FaceBuffer cap (rows ++ [start :: rest]) ∧
      sf.regs 655 = rows.length + 1 ∧
      sf.regs 656 = (gm06EncodeRows (rows ++ [start :: rest])).length := by
  let L := (gm06EncodeRows rows).length
  let row := start :: rest
  have hnewlen : (gm06EncodeRows (rows ++ [row])).length = L + 1 + row.length := by
    dsimp only [L]
    rw [gm06FaceCode_length, gm06FaceCode_length]
    simp only [List.length_append, List.length_singleton, List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.length_append]
    omega
  have hLcap : L + 1 + row.length ≤ cap := hnewlen ▸ hroom
  have hLw : L < 2 ^ w := by omega
  have hlabel : rows.length + 1 < 2 ^ w := by
    rw [gm06FaceCode_length] at hroom
    simp only [List.length_append, List.length_singleton] at hroom
    omega
  have hLp : L + 1 < 2 ^ w := by rw [hnewlen] at hroom; omega
  let s₁ := s.setReg 651 start
  let s₂ := s₁.setReg 654 (rows.length + 1)
  let s₃ := s₂.setReg 657 L
  let s₄ := s₃.setReg 656 (L + 1)
  have hb₁ : Exec w (.assign 651 (.reg 652)) s s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg h652 (hs.trans hn))
  have hb₂ : Exec w (.assign 654 (.op .add (.reg 655) (.const 1))) s₁ s₂ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁] using h655) (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) hlabel)
  have hb₃ : Exec w (.assign 657 (.reg 656)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂, s₁] using h656) hLw)
  have hb₄ : Exec w (.assign 656 (.op .add (.reg 656) (.const 1))) s₃ s₄ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₃, s₂, s₁] using h656) hLw)
      (GraphMinor.Compute.Crossing.eval_const hw) hLp)
  have he₁ : Exec w gm06FaceRowBegin s s₄ 12 := .seq hb₁ (.seq hb₂ (.seq hb₃ hb₄))
  have hk₁ : Keeps [651, 654, 655, 656, 657] [605, 606] s s₄ :=
    ((((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg
      (by simp) _).setReg (by simp) _
  let pre := gm06EncodeRows rows ++ [0]
  let rem := cap - (L + 1)
  have hrem : row.length ≤ rem := by rw [hnewlen] at hroom; dsimp only [rem]; omega
  have hbuffer : s₄.arrs 606 = pre ++ List.replicate rem 0 := by
    change s.arrs 606 = _
    rw [h606]
    have hdiff : cap - L = rem + 1 := by dsimp only [rem]; rw [hnewlen] at hroom; omega
    change gm06EncodeRows rows ++ List.replicate (cap - L) 0 = _
    rw [hdiff, List.replicate_succ]
    simp only [pre, List.append_assoc, List.singleton_append]
  obtain ⟨sm, tm, hem, htm, hkm, hdm, hbm, _, hpm⟩ := gm06OrbitWriteProg_exec
    successors (gm06FaceOwners successors.length rows) pre rest rem start (rows.length + 1)
    s₄ hw hn (gm06FaceOwners_length _ _) hs hd hnot hchain hlabel hrem
    (by simp only [pre, List.length_append, List.length_singleton]; dsimp only [rem]; omega)
    h603 h605 hbuffer (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂, s₁, h652])
    (by simp [s₄, s₃, s₂]) (by simp [s₄, pre, L])
  have hk₁m : Keeps [651, 654, 655, 656, 657] [605, 606] s sm :=
    hk₁.trans hkm (by simp) (fun _ h => h)
  have hcount : sm.regs 655 = rows.length := (hkm.1 655 (by decide)).trans (by simp [s₄, s₃, s₂, s₁, h655])
  have hheader : sm.regs 657 = L := (hkm.1 657 (by decide)).trans (by simp [s₄, s₃])
  have hpos : sm.regs 656 = L + 1 + row.length := by
    simpa [pre, L, row] using hpm
  have hposw : L + 1 + row.length < 2 ^ w := by rw [hnewlen] at hroom; omega
  have hdiff : (L + 1 + row.length) - L - 1 = row.length := by omega
  have hval : (Expr.op .sub (.op .sub (.reg 656) (.reg 657)) (.const 1)).eval w sm = some row.length := by
    have hh := GraphMinor.Compute.Crossing.eval_sub
      (GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg hpos hposw)
        (GraphMinor.Compute.Crossing.eval_reg hheader hLw)) (GraphMinor.Compute.Crossing.eval_const hw)
    simpa only [hdiff] using hh
  have hpre : pre.length = L + 1 := by simp [pre, L]
  have hbufferlen : (sm.arrs 606).length = cap := by
    rw [hbm]
    simp only [List.length_append, List.length_replicate, List.length_cons, hpre]
    dsimp only [rem]
    have hh := hroom
    rw [hnewlen] at hh
    dsimp only [row, List.length_cons] at hh
    omega
  have hcap0 : 0 < cap := by
    have hh : 0 < (gm06EncodeRows (rows ++ [row])).length := by simp [gm06EncodeRows]
    exact hh.trans_le hroom
  let se := sm.writeArr 606 L row.length
  let sc := se.setReg 655 (rows.length + 1)
  let sf := sc.writeArr 606 0 (rows.length + 1)
  have he₂ : Exec w (.write 606 (.reg 657)
      (.op .sub (.op .sub (.reg 656) (.reg 657)) (.const 1))) sm se 7 :=
    .write (GraphMinor.Compute.Crossing.eval_reg hheader hLw) hval (by rw [hbufferlen]; rw [hnewlen] at hroom; omega)
  have he₃ : Exec w (.assign 655 (.op .add (.reg 655) (.const 1))) se sc 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg hcount (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) hlabel)
  have he₄ : Exec w (.write 606 (.const 0) (.reg 655)) sc sf 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_reg (by simp [sc]) hlabel)
      (by simpa only [sc, se, State.setReg_arrs, State.writeArr, State.setArr_arrs_self,
        List.length_set, hbufferlen] using hcap0)
  refine ⟨sf, 12 + (tm + (7 + (4 + 3))), .seq he₁ (.seq hem (.seq he₂ (.seq he₃ he₄))),
    by omega, ((hk₁m.writeArr (by simp) _ _).setReg (by simp) _).writeArr (by simp) _ _,
    ?_, ?_, by simp [sf, sc], ?_⟩
  · rw [show sf.arrs 605 = sm.arrs 605 by simp [sf, sc, se, State.writeArr], hdm]
    exact (gm06FaceOwners_append _ rows row).symm
  · change ((sm.arrs 606).set L row.length).set 0 (rows.length + 1) = _
    rw [hbm]
    have hpatch := gm06FaceBuffer_patch rows row (rem - row.length)
    have hrem' : rem - row.length = cap - (gm06EncodeRows (rows ++ [row])).length := by
      rw [hnewlen]
      dsimp only [rem]
      omega
    change ((gm06EncodeRows rows ++ [0] ++ row ++ List.replicate (rem - row.length) 0).set
      L row.length).set 0 (rows.length + 1) = gm06FaceBuffer cap (rows ++ [row])
    unfold gm06FaceBuffer
    rw [← hrem']
    exact hpatch
  · change sm.regs 656 = (gm06EncodeRows (rows ++ [row])).length
    rw [hpos, hnewlen]

end GraphMinor.Compute
