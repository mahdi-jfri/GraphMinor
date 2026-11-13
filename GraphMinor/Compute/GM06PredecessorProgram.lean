module

public import GraphMinor.Compute.GM06PredecessorRowProgram
public import GraphMinor.Compute.GM06ReadRow
public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.TwoPathsRename
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The complete RAM predecessor pass

The first pass of FACE_ROWS in Section 5 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) reads all length-prefixed rotation rows. It initializes a
table on the permanent dart-label space, then writes each row's cyclic predecessors. Its source
contains the rotations, not a predecessor table. The proof composes the row reader and the
cyclic row scan and counts each encoded entry once.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Consecutive scatter passes equal their concatenated pair pass. -/
theorem gm06Scatter_append (xs ys : List (ℕ × ℕ)) (table : List ℕ) :
    gm06Scatter (xs ++ ys) table = gm06Scatter ys (gm06Scatter xs table) := by
  induction xs generalizing table with
  | nil => rfl
  | cons p ps ih => exact ih (table.set p.1 p.2)

/-- Move the row reader's registers 7--11 to 660--664. -/
def gm06RotationReadRename (x : ℕ) : ℕ :=
  if 7 ≤ x ∧ x < 12 then x + 653
  else if 660 ≤ x ∧ x < 665 then x - 653 else x

/-- The row-reader memory relocation is its own inverse. -/
theorem gm06RotationReadRename_involutive : Function.Involutive gm06RotationReadRename := by
  intro x
  unfold gm06RotationReadRename
  split_ifs <;> omega

/-- Read the next rotation from source 600 into row array 601,
using source cursor 661 and preserving the predecessor array. -/
def gm06ReadRotationRowProg : Cmd :=
  renameCmd gm06RotationReadRename (gm06ReadRowProg 600 601)

/-- The relocated reader returns the exact next input rotation. -/
theorem gm06ReadRotationRowProg_exec {w : ℕ} (pre row tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 600 = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs 600).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 600, x < 2 ^ w)
    (hr : s.regs 661 = pre.length) :
    ∃ sf t, Exec w gm06ReadRotationRowProg s sf t ∧
      t ≤ 13 + 22 * row.length ∧ Keeps [660, 661, 662, 664] [601] s sf ∧
      sf.arrs 601 = row ∧ sf.regs 661 = pre.length + 1 + row.length := by
  let sr := renameState gm06RotationReadRename s
  obtain ⟨sm, t, he, ht, hd, hp, hregs, harrs⟩ := gm06ReadRowProg_exec
    600 601 (by decide) pre row tail sr hw ha hn hwords hr
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
    have hneq : gm06RotationReadRename a ≠ 601 := by
      simp only [List.mem_singleton] at ha
      unfold gm06RotationReadRename
      split_ifs <;> omega
    change sm.arrs (gm06RotationReadRename a) = s.arrs a
    rw [harrs _ hneq]
    exact congrArg s.arrs (gm06RotationReadRename_involutive a)

/-- Scratch registers changed by the complete predecessor pass. -/
def gm06PredecessorRegs : List ℕ := [650, 651, 652, 660, 661, 662, 664, 665]

/-- Read and scatter the remaining rotation rows. -/
def gm06PredecessorRowsLoop : Cmd :=
  .while (.reg 665)
    (.seq gm06ReadRotationRowProg
      (.seq (gm06PredecessorRowProg 601 602)
        (.assign 665 (.op .sub (.reg 665) (.const 1)))))

/-- The rotation-row loop computes the concatenated predecessor-pair
scatter, with a linear bound in the number of rows and darts. -/
theorem gm06PredecessorRowsLoop_exec {w : ℕ}
    (rows : List (List ℕ)) (pre tail table : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : table.length < 2 ^ w)
    (hc : rows.length < 2 ^ w)
    (ha : s.arrs 600 = pre ++ gm06EncodeRowsPayload rows ++ tail)
    (hcode : (s.arrs 600).length < 2 ^ w)
    (hwords : ∀ x ∈ s.arrs 600, x < 2 ^ w)
    (hkeys : ∀ d ∈ rows.flatten, d < table.length)
    (hp : s.regs 661 = pre.length) (hr : s.regs 665 = rows.length)
    (htab : s.arrs 602 = table) :
    ∃ sf t, Exec w gm06PredecessorRowsLoop s sf t ∧
      t ≤ 1 + 29 * rows.length + 37 * rows.flatten.length ∧
      Keeps gm06PredecessorRegs [601, 602] s sf ∧
      sf.arrs 602 = gm06Scatter (rows.flatMap gm06RotationPredecessorPairs) table ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload rows).length ∧ sf.regs 665 = 0 := by
  induction rows generalizing pre table s with
  | nil =>
    exact ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg hr (Nat.two_pow_pos w)),
      by simp, Keeps.refl _ _ _, htab, by simpa [gm06EncodeRowsPayload] using hp, hr⟩
  | cons row rows ih =>
    have hrowSrc : s.arrs 600 = pre ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload rows ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using ha
    have hlen : (s.arrs 600).length = pre.length + (1 + row.length) +
        (gm06EncodeRowsPayload rows).length + tail.length := by
      rw [hrowSrc]
      simp [gm06EncodeNatList, List.length_append]
      omega
    have hrow : row.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hp₁⟩ :=
      gm06ReadRotationRowProg_exec pre row (gm06EncodeRowsPayload rows ++ tail) s hw
        hrowSrc hcode hwords hp
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06PredecessorRowProg_exec 601 602
      (by decide) row table s₁ hw hrow hn
      (fun d hd => hkeys d (by simp [hd])) hd₁ ((hk₁.2 602 (by decide)).trans htab)
    have hk₁₂ : Keeps gm06PredecessorRegs [601, 602] s s₂ :=
      (hk₁.mono (by simp [gm06PredecessorRegs]) (by simp)).trans hk₂
        (by simp [gm06PredecessorRegs]) (by simp)
    have hcount : s₂.regs 665 = rows.length + 1 :=
      (hk₂.1 665 (by decide)).trans ((hk₁.1 665 (by decide)).trans hr)
    let s₃ := s₂.setReg 665 rows.length
    have he₃ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₂ s₃ 4 :=
      .assign (by simpa using (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg hcount hc) (GraphMinor.Compute.Crossing.eval_const hw)))
    let table' := gm06Scatter (gm06RotationPredecessorPairs row) table
    let pre' := pre ++ gm06EncodeNatList row
    have htablen : table'.length = table.length := gm06Scatter_length _ _
    have hsource : s₃.arrs 600 = pre' ++ gm06EncodeRowsPayload rows ++ tail := by
      rw [show s₃.arrs 600 = s.arrs 600 from hk₁₂.2 600 (by decide)]
      simpa only [pre', List.append_assoc] using hrowSrc
    have hcursor : s₃.regs 661 = pre'.length := by
      have hh := (hk₂.1 661 (by decide)).trans hp₁
      simpa [s₃, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    obtain ⟨sf, tf, hef, htf, hkf, hdf, hpf, hrf⟩ := ih pre' table' s₃
      (htablen ▸ hn) (by simpa only [List.length_cons] using Nat.lt_of_succ_lt hc)
      hsource (by simpa only [s₃, State.setReg_arrs, hk₁₂.2 600 (by decide)] using hcode)
      (by simpa only [s₃, State.setReg_arrs, hk₁₂.2 600 (by decide)] using hwords)
      (fun d hd => htablen ▸ hkeys d (by simp [hd])) hcursor (by simp [s₃]) hd₂
    refine ⟨sf, 1 + (t₁ + (t₂ + 4)) + tf,
      .while_true (GraphMinor.Compute.Crossing.eval_reg hr hc) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ he₃)) hef, ?_,
      (hk₁₂.setReg (by simp [gm06PredecessorRegs]) _).trans hkf (fun _ h => h) (fun _ h => h),
      ?_, ?_, hrf⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [List.flatMap_cons, gm06Scatter_append, table'] using hdf
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf

/-- Compute the predecessor table from encoded rotation rows in 600,
with its label-space size in register 648. The answer is in 602. -/
def gm06PredecessorsProg : Cmd :=
  .seq (gm13TabulateProg 650 (.reg 648) (.reg 650) 602)
    (.seq (.assign 661 (.const 1))
      (.seq (.assign 665 (.read 600 (.const 0))) gm06PredecessorRowsLoop))

/-- The complete predecessor pass computes the exact pure table,
with a linear bound in its label space and encoded input length. -/
theorem gm06PredecessorsProg_exec {w n : ℕ} (rows : List (List ℕ)) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hkeys : ∀ d ∈ rows.flatten, d < n)
    (ha : s.arrs 600 = gm06EncodeRows rows)
    (hcode : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) (hsize : s.regs 648 = n) :
    ∃ sf t, Exec w gm06PredecessorsProg s sf t ∧
      t ≤ 12 + 13 * n + 29 * rows.length + 37 * rows.flatten.length ∧
      Keeps gm06PredecessorRegs [601, 602] s sf ∧
      sf.arrs 602 = gm06RotationPredecessors n rows := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm13TabulateProg_exec 650 (.reg 648) (.reg 650)
    602 (List.range n) s hw (by simpa using hn)
    (fun st hk => by simpa only [List.length_range] using
      (GraphMinor.Compute.Crossing.eval_reg ((hk.1 648 (by decide)).trans hsize) hn))
    (fun st i hi _ hidx => by
      have hi' : i < n := by simpa using hi
      simpa only [List.getElem_range] using GraphMinor.Compute.Crossing.eval_reg hidx (hi'.trans hn))
  let s₂ := s₁.setReg 661 1
  let s₃ := s₂.setReg 665 rows.length
  have he₂ : Exec w (.assign 661 (.const 1)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have hsrc : s₂.arrs 600 = gm06EncodeRows rows := by
    exact (hk₁.2 600 (by decide)).trans ha
  have hcw : rows.length < 2 ^ w := hwords _ (by simp [gm06EncodeRows])
  have he₃ : Exec w (.assign 665 (.read 600 (.const 0))) s₂ s₃ 3 :=
    .assign (by
      have hi : 0 < (s₂.arrs 600).length := by simp [hsrc, gm06EncodeRows]
      have hget : (s₂.arrs 600)[0]'hi = rows.length := by simp [hsrc, gm06EncodeRows]
      have he := GraphMinor.Compute.Crossing.eval_read (a := 600)
        (GraphMinor.Compute.Crossing.eval_const (c := 0) (Nat.two_pow_pos w)) hi
        (by rw [hget]; exact hcw)
      simpa only [hget] using he)
  have hk₁₃ : Keeps gm06PredecessorRegs [601, 602] s s₃ :=
    ((hk₁.mono (by simp [gm06PredecessorRegs]) (by simp)).setReg
      (by simp [gm06PredecessorRegs]) _).setReg (by simp [gm06PredecessorRegs]) _
  obtain ⟨sf, tf, hef, htf, hkf, hdf, _, _⟩ := gm06PredecessorRowsLoop_exec
    rows [rows.length] [] (List.range n) s₃ hw (by simpa using hn) hcw
    (by simpa only [s₃, State.setReg_arrs, gm06EncodeRows, List.singleton_append, List.append_nil] using hsrc)
    (by simpa [s₃, hsrc] using hcode) (by simpa [s₃, hsrc] using hwords)
    (by simpa using hkeys) (by simp [s₃, s₂]) (by simp [s₃]) hd₁
  refine ⟨sf, t₁ + (2 + (3 + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    hk₁₃.trans hkf (fun _ h => h) (fun _ h => h), hdf⟩
  simp only [Expr.cost, List.length_range] at ht₁
  omega

end GraphMinor.Compute
