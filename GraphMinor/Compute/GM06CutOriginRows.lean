module

public import GraphMinor.Compute.GM06CutOriginRowProgram

/-!
# Computing origins for every copied rotation row

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) connects the
copied edge ends by their induced vertex rows. This loop reads all
computed rows, writes their vertex indices and marks active ends.
The invariant gives exactly the two accumulated scatter passes and
the next copied vertex index. It supports a zero-padded source buffer.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the next rotation row from source 625 into row array 611,
using source cursor 661 and preserving the copied-origin tables. -/
def gm06ReadCutOriginRowProg : Cmd :=
  renameCmd gm06RotationReadRename (gm06ReadRowProg 625 611)

/-- The relocated reader returns the exact next input rotation. -/
theorem gm06ReadCutOriginRowProg_exec {w : ℕ} (pre row tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 625 = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (hr : s.regs 661 = pre.length) :
    ∃ sf t, Exec w gm06ReadCutOriginRowProg s sf t ∧
      t ≤ 13 + 22 * row.length ∧ Keeps [660, 661, 662, 664] [611] s sf ∧
      sf.arrs 611 = row ∧ sf.regs 661 = pre.length + 1 + row.length := by
  let sr := renameState gm06RotationReadRename s
  obtain ⟨sm, t, he, ht, hd, hp, hregs, harrs⟩ := gm06ReadRowProg_exec
    625 611 (by decide) pre row tail sr hw ha hn hwords hr
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

/-- Origin writes for a suffix of copied vertex slots. -/
def gm06CutOriginPairsFrom (base : ℕ) (rows : List (List ℕ)) : List (ℕ × ℕ) :=
  (rows.zipIdx base).flatMap (fun p => p.1.map (fun d => (d, p.2)))

/-- Starting at copied vertex zero gives the full origin write list. -/
theorem gm06CutOriginPairsFrom_zero (rows : List (List ℕ)) :
    gm06CutOriginPairsFrom 0 rows = gm06CutOriginPairs rows := rfl

/-- One copied row precedes the origin writes of the remaining rows. -/
theorem gm06CutOriginPairsFrom_cons (base : ℕ) (row : List ℕ) (rows : List (List ℕ)) :
    gm06CutOriginPairsFrom base (row :: rows) = row.map (fun d => (d, base)) ++
      gm06CutOriginPairsFrom (base + 1) rows := by
  simp only [gm06CutOriginPairsFrom, List.zipIdx_cons, List.flatMap_cons]

/-- Read a copied row, write its ends, then advance the copied vertex index. -/
def gm06CutOriginRowsLoop : Cmd :=
  .while (.reg 665)
    (.seq gm06ReadCutOriginRowProg
      (.seq gm06CutOriginRowProg
        (.seq (.assign 666 (.op .add (.reg 666) (.const 1)))
          (.assign 665 (.op .sub (.reg 665) (.const 1))))))

/-- Registers changed while scanning all copied rows for origins. -/
def gm06CutOriginRowsRegs : List ℕ := [650, 651, 660, 661, 662, 664, 665, 666]

/-- Exact origins and active-end writes for every row, with linear
time in the encoded copied graph. The source may include unused
zero padding after its last encoded row. -/
theorem gm06CutOriginRowsLoop_exec {w q base : ℕ}
    (rows : List (List ℕ)) (pre tail origins active : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hq : q < 2 ^ w) (hbaseFit : base + rows.length < 2 ^ w)
    (hc : rows.length < 2 ^ w)
    (ha : s.arrs 625 = pre ++ gm06EncodeRowsPayload rows ++ tail)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (hkeys : ∀ d ∈ rows.flatten, d < q)
    (hlenOrg : origins.length = q) (hlenAct : active.length = q)
    (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = active)
    (h661 : s.regs 661 = pre.length) (h665 : s.regs 665 = rows.length) (h666 : s.regs 666 = base) :
    ∃ sf t, Exec w gm06CutOriginRowsLoop s sf t ∧
      t ≤ 1 + 27 * rows.length + 38 * rows.flatten.length ∧
      Keeps gm06CutOriginRowsRegs [611, 626, 627] s sf ∧
      sf.arrs 626 = gm06Scatter (gm06CutOriginPairsFrom base rows) origins ∧
      sf.arrs 627 = gm06Scatter (rows.flatten.map (fun d => (d, 1))) active ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload rows).length ∧
      sf.regs 665 = 0 ∧ sf.regs 666 = base + rows.length := by
  induction rows generalizing base pre origins active s with
  | nil =>
    exact ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg h665 (Nat.two_pow_pos w)), by simp,
      Keeps.refl _ _ _, h626, h627, by simpa [gm06EncodeRowsPayload] using h661, h665, by simpa using h666⟩
  | cons row rows ih =>
    simp only [List.length_cons] at hbaseFit hc h665
    have hrowSrc : s.arrs 625 = pre ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload rows ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using ha
    have hlen : (s.arrs 625).length = pre.length + (1 + row.length) +
        (gm06EncodeRowsPayload rows).length + tail.length := by
      rw [hrowSrc]
      simp [gm06EncodeNatList, List.length_append]
      omega
    have hrow : row.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hp₁⟩ := gm06ReadCutOriginRowProg_exec
      pre row (gm06EncodeRowsPayload rows ++ tail) s hw hrowSrc hcode hwords h661
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, ho₂, ha₂⟩ := gm06CutOriginRowProg_exec row origins active s₁
      hw hq (by omega) hrow (fun d hd => hkeys d (by simp [hd])) hlenOrg hlenAct hd₁
      ((hk₁.2 626 (by decide)).trans h626) ((hk₁.2 627 (by decide)).trans h627)
      ((hk₁.1 666 (by decide)).trans h666)
    have hk₁₂ : Keeps gm06CutOriginRowsRegs [611, 626, 627] s s₂ :=
      (hk₁.mono (by simp [gm06CutOriginRowsRegs]) (by simp)).trans hk₂
        (by simp [gm06CutOriginRowsRegs]) (by simp)
    have hbase : s₂.regs 666 = base := (hk₂.1 666 (by decide)).trans ((hk₁.1 666 (by decide)).trans h666)
    have hcount : s₂.regs 665 = rows.length + 1 := (hk₂.1 665 (by decide)).trans ((hk₁.1 665 (by decide)).trans h665)
    let s₃ := s₂.setReg 666 (base + 1)
    let s₄ := s₃.setReg 665 rows.length
    have he₃ : Exec w (.assign 666 (.op .add (.reg 666) (.const 1))) s₂ s₃ 4 :=
      .assign (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg hbase (by omega))
        (GraphMinor.Compute.Crossing.eval_const hw) (by omega))
    have he₄ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₃ s₄ 4 :=
      .assign (by simpa only [Nat.add_sub_cancel] using (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₃] using hcount) hc)
        (GraphMinor.Compute.Crossing.eval_const hw)))
    let origins' := gm06Scatter (row.map (fun d => (d, base))) origins
    let active' := gm06Scatter (row.map (fun d => (d, 1))) active
    let pre' := pre ++ gm06EncodeNatList row
    have hk₁₄ : Keeps gm06CutOriginRowsRegs [611, 626, 627] s s₄ :=
      (hk₁₂.setReg (by simp [gm06CutOriginRowsRegs]) _).setReg (by simp [gm06CutOriginRowsRegs]) _
    have hsrc' : s₄.arrs 625 = pre' ++ gm06EncodeRowsPayload rows ++ tail := by
      rw [hk₁₄.2 625 (by decide)]
      simpa only [pre', List.append_assoc] using hrowSrc
    have hcursor : s₄.regs 661 = pre'.length := by
      have hh := (hk₂.1 661 (by decide)).trans hp₁
      simpa [s₄, s₃, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    obtain ⟨sf, tf, hef, htf, hkf, hof, haf, hpf, hcf, hvf⟩ := ih
      (base := base + 1) pre' origins' active' s₄ (by omega) (by omega)
      hsrc' (by rw [hk₁₄.2 625 (by decide)]; exact hcode)
      (by rw [hk₁₄.2 625 (by decide)]; exact hwords)
      (fun d hd => hkeys d (by simp [hd]))
      (by simpa [origins', gm06Scatter_length] using hlenOrg)
      (by simpa [active', gm06Scatter_length] using hlenAct) ho₂ ha₂
      hcursor (by simp [s₄]) (by simp [s₄, s₃])
    refine ⟨sf, 1 + (t₁ + (t₂ + (4 + 4))) + tf,
      .while_true (GraphMinor.Compute.Crossing.eval_reg h665 hc) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ (.seq he₃ he₄))) hef, ?_,
      hk₁₄.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, ?_, hcf, ?_⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [gm06CutOriginPairsFrom_cons, gm06Scatter_append, origins'] using hof
    · simpa only [List.flatten_cons, List.map_append, gm06Scatter_append, active'] using haf
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvf

end GraphMinor.Compute
