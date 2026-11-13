module

public import GraphMinor.Compute.GM06CutSplitVertex
public import GraphMinor.Compute.GM06CutRowsFacts
public import GraphMinor.Compute.GM06PredecessorProgram

/-!
# Processing every original rotation into its copied rows

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) scans
original vertices in label order. This loop reads each encoded rotation,
computes both induced rows from the linkage and cuff tables, and
appends them to the output. Its invariant gives the exact encoded
copied prefix, the unread source cursor and the next original vertex.
A factor-two capacity bound covers the remaining output.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the next rotation row from source 600 into row array 611,
using source cursor 661 and preserving the cut-mark tables. -/
def gm06ReadCutRotationRowProg : Cmd :=
  renameCmd gm06RotationReadRename (gm06ReadRowProg 600 611)

/-- The relocated reader returns the exact next input rotation. -/
theorem gm06ReadCutRotationRowProg_exec {w : ℕ} (pre row tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 600 = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs 600).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 600, x < 2 ^ w)
    (hr : s.regs 661 = pre.length) :
    ∃ sf t, Exec w gm06ReadCutRotationRowProg s sf t ∧
      t ≤ 13 + 22 * row.length ∧ Keeps [660, 661, 662, 664] [611] s sf ∧
      sf.arrs 611 = row ∧ sf.regs 661 = pre.length + 1 + row.length := by
  let sr := renameState gm06RotationReadRename s
  obtain ⟨sm, t, he, ht, hd, hp, hregs, harrs⟩ := gm06ReadRowProg_exec
    600 611 (by decide) pre row tail sr hw ha hn hwords hr
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
    have hneq : gm06RotationReadRename a ≠ 611 := by
      simp only [List.mem_singleton] at ha
      unfold gm06RotationReadRename
      split_ifs <;> omega
    change sm.arrs (gm06RotationReadRename a) = s.arrs a
    rw [harrs _ hneq]
    exact congrArg s.arrs (gm06RotationReadRename_involutive a)

/-- Induced rotation slots of a suffix whose first original vertex has label base. -/
def gm06SplitRotationRowsFrom (marks : GM06CutTables) (base : ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  (rows.zipIdx base).flatMap (fun p => gm06SplitVertexRows (gm06CutPositionAt marks p.2) p.1)

/-- Starting at vertex zero gives exactly the full pure copied rotations. -/
theorem gm06SplitRotationRowsFrom_zero (marks : GM06CutTables) (rows : List (List ℕ)) :
    gm06SplitRotationRowsFrom marks 0 rows = gm06SplitRotationRows marks rows := rfl

/-- Splitting the first row precedes splitting the remaining vertex slots. -/
theorem gm06SplitRotationRowsFrom_cons (marks : GM06CutTables) (base : ℕ)
    (row : List ℕ) (rows : List (List ℕ)) :
    gm06SplitRotationRowsFrom marks base (row :: rows) =
      gm06SplitVertexRows (gm06CutPositionAt marks base) row ++ gm06SplitRotationRowsFrom marks (base + 1) rows := by
  simp only [gm06SplitRotationRowsFrom, List.zipIdx_cons, List.flatMap_cons]

/-- The encoded row payload has one header per row and one word per dart. -/
theorem gm06EncodeRowsPayload_length (rows : List (List ℕ)) :
    (gm06EncodeRowsPayload rows).length = rows.length + rows.flatten.length := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
      gm06EncodeNatList, List.length_cons, List.flatten_cons] at *
    omega

/-- One old row needs at most two headers and twice its dart entries. -/
theorem gm06SplitVertexPayload_length_le (position : Option GM06CutPosition) (row : List ℕ) :
    (gm06EncodeRowsPayload (gm06SplitVertexRows position row)).length ≤ 2 + 2 * row.length := by
  rw [gm06EncodeRowsPayload_length]
  have hslots : (gm06SplitVertexRows position row).length = 2 := by cases position <;> rfl
  rw [hslots]
  exact Nat.add_le_add_left (gm06SplitVertexRows_length_le position row) 2

/-- Read a row, emit both copies, then advance the original vertex and source-row counters. -/
def gm06CutSplitRowsLoop : Cmd :=
  .while (.reg 665)
    (.seq gm06ReadCutRotationRowProg
      (.seq gm06CutSplitVertexProg
        (.seq (.assign 666 (.op .add (.reg 666) (.const 1)))
          (.assign 665 (.op .sub (.reg 665) (.const 1))))))

/-- Scratch registers changed by the full original-row loop. -/
def gm06CutSplitRowsRegs : List ℕ := gm06CutSplitVertexRegs ++ [660, 661, 662, 664, 665, 666]

/-- The global row loop appends exactly the induced rotations in
permanent vertex-copy order. Its bound is polynomial in the original
row data and dart-label-space size. -/
theorem gm06CutSplitRowsLoop_exec {w n m base cap : ℕ}
    (marks : GM06CutTables) (rows : List (List ℕ)) (preSrc tailSrc preOut : List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hm : 4 * m < 2 ^ w)
    (hvertices : base + rows.length ≤ n) (hc : rows.length < 2 ^ w)
    (hnd : ∀ row ∈ rows, row.Nodup) (hkeys : ∀ d ∈ rows.flatten, d < 2 * m)
    (hlens : marks.incoming.length = n ∧ marks.outgoing.length = n ∧
      marks.cuffPositive.length = n ∧ marks.cuffNegative.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing)
    (h623 : s.arrs 623 = marks.cuffPositive) (h624 : s.arrs 624 = marks.cuffNegative)
    (hsrc : s.arrs 600 = preSrc ++ gm06EncodeRowsPayload rows ++ tailSrc)
    (hcode : (s.arrs 600).length < 2 ^ w) (hsrcWords : ∀ x ∈ s.arrs 600, x < 2 ^ w)
    (h647 : s.regs 647 = 2 * m) (h666 : s.regs 666 = base)
    (h661 : s.regs 661 = preSrc.length) (h665 : s.regs 665 = rows.length)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 625 655 preOut cap s)
    (hcap : 2 * rows.length + 2 * rows.flatten.length ≤ cap)
    (hfit : preOut.length + cap + 2 < 2 ^ w) :
    ∃ sf t, Exec w gm06CutSplitRowsLoop s sf t ∧
      t ≤ 1 + rows.length * (6000 + 26 * m) + 6000 * rows.flatten.length ∧
      Keeps gm06CutSplitRowsRegs [611, 614, 615, 616, 625] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 625 655
        (preOut ++ gm06EncodeRowsPayload (gm06SplitRotationRowsFrom marks base rows))
        (cap - (gm06EncodeRowsPayload (gm06SplitRotationRowsFrom marks base rows)).length) sf ∧
      sf.regs 661 = preSrc.length + (gm06EncodeRowsPayload rows).length ∧
      sf.regs 665 = 0 ∧ sf.regs 666 = base + rows.length := by
  have hw1 : 1 < 2 ^ w := by omega
  induction rows generalizing base cap preSrc preOut s with
  | nil =>
    refine ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg h665 (Nat.two_pow_pos w)),
      by simp, Keeps.refl _ _ _, ?_, ?_, h665, ?_⟩
    · simpa [gm06SplitRotationRowsFrom, gm06EncodeRowsPayload] using hbuf
    · simpa [gm06EncodeRowsPayload] using h661
    · simpa using h666
  | cons row rows ih =>
    simp only [List.length_cons] at hvertices hc h665
    simp only [List.length_cons, List.flatten_cons, List.length_append] at hcap
    have hrowSrc : s.arrs 600 = preSrc ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload rows ++ tailSrc) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using hsrc
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hp₁⟩ := gm06ReadCutRotationRowProg_exec
      preSrc row (gm06EncodeRowsPayload rows ++ tailSrc) s hw1 hrowSrc hcode hsrcWords h661
    have hb₁ : GraphMinor.Compute.Crossing.IsBuf 625 655 preOut cap s₁ :=
      ⟨(hk₁.2 625 (by decide)).trans hbuf.1, (hk₁.1 655 (by decide)).trans hbuf.2⟩
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hb₂⟩ := gm06CutSplitVertexProg_exec marks row preOut s₁
      hw hn hm (by omega)
      (hnd row List.mem_cons_self) (fun d hd => hkeys d (by simp [hd])) hlens hwords
      ((hk₁.2 620 (by decide)).trans h620) ((hk₁.2 621 (by decide)).trans h621)
      ((hk₁.2 623 (by decide)).trans h623) ((hk₁.2 624 (by decide)).trans h624)
      hd₁ ((hk₁.1 647 (by decide)).trans h647) ((hk₁.1 666 (by decide)).trans h666)
      hb₁ (by omega) hfit
    have hk₁₂ : Keeps gm06CutSplitRowsRegs [611, 614, 615, 616, 625] s s₂ :=
      (hk₁.mono (by simp [gm06CutSplitRowsRegs, gm06CutSplitVertexRegs]) (by simp)).trans hk₂
        (by simp [gm06CutSplitRowsRegs, gm06CutSplitVertexRegs]) (by simp)
    have hbase : s₂.regs 666 = base :=
      (hk₂.1 666 (by simp [gm06CutSplitVertexRegs])).trans ((hk₁.1 666 (by decide)).trans h666)
    have hcount : s₂.regs 665 = rows.length + 1 :=
      (hk₂.1 665 (by simp [gm06CutSplitVertexRegs])).trans ((hk₁.1 665 (by decide)).trans h665)
    let s₃ := s₂.setReg 666 (base + 1)
    let s₄ := s₃.setReg 665 rows.length
    have he₃ : Exec w (.assign 666 (.op .add (.reg 666) (.const 1))) s₂ s₃ 4 :=
      .assign (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg hbase (by omega))
        (GraphMinor.Compute.Crossing.eval_const hw1) (by omega))
    have he₄ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₃ s₄ 4 :=
      .assign (by simpa only [Nat.add_sub_cancel, List.length_cons] using (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₃] using hcount) hc)
        (GraphMinor.Compute.Crossing.eval_const hw1)))
    let newRows := gm06SplitVertexRows (gm06CutPositionAt marks base) row
    let newWords := gm06EncodeRowsPayload newRows
    let preSrc' := preSrc ++ gm06EncodeNatList row
    let preOut' := preOut ++ newWords
    have hnew : newWords.length ≤ 2 + 2 * row.length := gm06SplitVertexPayload_length_le _ _
    have hk₁₄ : Keeps gm06CutSplitRowsRegs [611, 614, 615, 616, 625] s s₄ :=
      ((hk₁₂.setReg (by simp [gm06CutSplitRowsRegs]) _).setReg (by simp [gm06CutSplitRowsRegs]) _)
    have hsrc' : s₄.arrs 600 = preSrc' ++ gm06EncodeRowsPayload rows ++ tailSrc := by
      rw [hk₁₄.2 600 (by decide)]
      simpa only [preSrc', List.append_assoc] using hrowSrc
    have hcursor : s₄.regs 661 = preSrc'.length := by
      have hh := (hk₂.1 661 (by simp [gm06CutSplitVertexRegs])).trans hp₁
      simpa [s₄, s₃, preSrc', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    obtain ⟨sf, tf, hef, htf, hkf, hbf, hpf, hcf, hvf⟩ := ih
      (base := base + 1) (cap := cap - newWords.length) preSrc' preOut' s₄
      (by omega) (by omega)
      (fun r hr => hnd r (List.mem_cons_of_mem row hr)) (fun d hd => hkeys d (by simp [hd]))
      ((hk₁₄.2 620 (by decide)).trans h620) ((hk₁₄.2 621 (by decide)).trans h621)
      ((hk₁₄.2 623 (by decide)).trans h623) ((hk₁₄.2 624 (by decide)).trans h624)
      hsrc' (by rw [hk₁₄.2 600 (by decide)]; exact hcode)
      (by rw [hk₁₄.2 600 (by decide)]; exact hsrcWords)
      ((hk₁₄.1 647 (by simp [gm06CutSplitRowsRegs, gm06CutSplitVertexRegs])).trans h647)
      (by simp [s₄, s₃]) hcursor (by simp [s₄]) hb₂
      (by omega)
      (by simp only [preOut', List.length_append]; omega)
    refine ⟨sf, 1 + (t₁ + (t₂ + (4 + 4))) + tf,
      .while_true (GraphMinor.Compute.Crossing.eval_reg h665 hc) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ (.seq he₃ he₄))) hef, ?_,
      hk₁₄.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, hcf, ?_⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      nlinarith only [ht₁, ht₂, htf, Nat.zero_le row.length, Nat.zero_le m]
    · simpa only [gm06SplitRotationRowsFrom_cons, gm06EncodeRowsPayload, List.flatMap_append,
        preOut', newWords, newRows, List.append_assoc, List.length_append, Nat.sub_sub] using hbf
    · simpa only [preSrc', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvf

end GraphMinor.Compute
