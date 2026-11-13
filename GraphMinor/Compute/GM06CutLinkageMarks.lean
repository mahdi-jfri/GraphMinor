module

public import GraphMinor.Compute.GM06CutPathMarks
public import GraphMinor.Compute.GM06PredecessorProgram

/-!
# Reading and marking every linkage path

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) computes path
positions from the linkage itself. The program reads each encoded
path row and runs the paired endpoint scan. The two accumulating
arrays contain exactly the incoming and outgoing path-end writes
from the processed rows. Both the encoded linkage and its original
origin table are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the next linkage row from source 608 into row array 611,
using source cursor 661 and preserving the path-mark tables. -/
def gm06ReadLinkageRowProg : Cmd :=
  renameCmd gm06RotationReadRename (gm06ReadRowProg 608 611)

/-- The relocated reader returns the exact next input path. -/
theorem gm06ReadLinkageRowProg_exec {w : ℕ} (pre row tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 608 = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs 608).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 608, x < 2 ^ w)
    (hr : s.regs 661 = pre.length) :
    ∃ sf t, Exec w gm06ReadLinkageRowProg s sf t ∧
      t ≤ 13 + 22 * row.length ∧ Keeps [660, 661, 662, 664] [611] s sf ∧
      sf.arrs 611 = row ∧ sf.regs 661 = pre.length + 1 + row.length := by
  let sr := renameState gm06RotationReadRename s
  obtain ⟨sm, t, he, ht, hd, hp, hregs, harrs⟩ := gm06ReadRowProg_exec
    608 611 (by decide) pre row tail sr hw ha hn hwords hr
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

/-- Scratch registers used while reading and marking all paths. -/
def gm06CutLinkageRegs : List ℕ := [650, 651, 652, 660, 661, 662, 664, 665]

/-- Read each remaining linkage row and mark its two directed ends. -/
def gm06CutLinkageMarksLoop : Cmd :=
  .while (.reg 665)
    (.seq gm06ReadLinkageRowProg
      (.seq gm06CutPathMarkRowProg
        (.assign 665 (.op .sub (.reg 665) (.const 1)))))

/-- Every processed path contributes exactly its two endpoint scatters.
The loop has a linear bound in the encoded path length. -/
theorem gm06CutLinkageMarksLoop_exec {w n m : ℕ}
    (paths : List (List ℕ)) (pre tail origins incoming outgoing : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hc : paths.length < 2 ^ w)
    (ha : s.arrs 608 = pre ++ gm06EncodeRowsPayload paths ++ tail)
    (hcode : (s.arrs 608).length < 2 ^ w)
    (hwords : ∀ x ∈ s.arrs 608, x < 2 ^ w)
    (horig : origins.length = 2 * m) (hv : ∀ v ∈ origins, v < n)
    (hkeys : ∀ d ∈ paths.flatten, d < 2 * m)
    (hin : incoming.length = n) (hout : outgoing.length = n)
    (hp : s.regs 661 = pre.length) (hr : s.regs 665 = paths.length)
    (h601 : s.arrs 601 = origins) (h620 : s.arrs 620 = incoming)
    (h621 : s.arrs 621 = outgoing) :
    ∃ sf t, Exec w gm06CutLinkageMarksLoop s sf t ∧
      t ≤ 1 + 23 * paths.length + 56 * paths.flatten.length ∧
      Keeps gm06CutLinkageRegs [611, 620, 621] s sf ∧
      sf.arrs 620 = gm06Scatter (gm06CutPathEndPairs origins paths.flatten true) incoming ∧
      sf.arrs 621 = gm06Scatter (gm06CutPathEndPairs origins paths.flatten false) outgoing ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload paths).length ∧ sf.regs 665 = 0 := by
  have hw1 : 1 < 2 ^ w := by omega
  induction paths generalizing pre incoming outgoing s with
  | nil =>
    exact ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg hr (Nat.two_pow_pos w)),
      by simp, Keeps.refl _ _ _, h620, h621,
      by simpa [gm06EncodeRowsPayload] using hp, hr⟩
  | cons row paths ih =>
    have hrowSrc : s.arrs 608 = pre ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload paths ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using ha
    have hlen : (s.arrs 608).length = pre.length + (1 + row.length) +
        (gm06EncodeRowsPayload paths).length + tail.length := by
      rw [hrowSrc]
      simp [gm06EncodeNatList, List.length_append]
      omega
    have hrow : row.length < 2 ^ w := by omega
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hp₁⟩ :=
      gm06ReadLinkageRowProg_exec pre row (gm06EncodeRowsPayload paths ++ tail) s hw1
        hrowSrc hcode hwords hp
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂, ho₂⟩ := gm06CutPathMarkRowProg_exec
      origins row incoming outgoing s₁ hw hn hm hrow horig hin hout
      (fun d hd => hkeys d (by simp [hd])) hv
      ((hk₁.2 601 (by decide)).trans h601) hd₁
      ((hk₁.2 620 (by decide)).trans h620) ((hk₁.2 621 (by decide)).trans h621)
    have hk₁₂ : Keeps gm06CutLinkageRegs [611, 620, 621] s s₂ :=
      (hk₁.mono (by simp [gm06CutLinkageRegs]) (by simp)).trans hk₂
        (by simp [gm06CutLinkageRegs]) (by simp)
    have hcount : s₂.regs 665 = paths.length + 1 :=
      (hk₂.1 665 (by decide)).trans ((hk₁.1 665 (by decide)).trans hr)
    let s₃ := s₂.setReg 665 paths.length
    have he₃ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₂ s₃ 4 :=
      .assign (by simpa using (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg hcount hc) (GraphMinor.Compute.Crossing.eval_const hw1)))
    let incoming' := gm06Scatter (gm06CutPathEndPairs origins row true) incoming
    let outgoing' := gm06Scatter (gm06CutPathEndPairs origins row false) outgoing
    let pre' := pre ++ gm06EncodeNatList row
    have hin' : incoming'.length = n := (gm06Scatter_length _ _).trans hin
    have hout' : outgoing'.length = n := (gm06Scatter_length _ _).trans hout
    have hsource : s₃.arrs 608 = pre' ++ gm06EncodeRowsPayload paths ++ tail := by
      rw [show s₃.arrs 608 = s.arrs 608 from hk₁₂.2 608 (by decide)]
      simpa only [pre', List.append_assoc] using hrowSrc
    have hcursor : s₃.regs 661 = pre'.length := by
      have hh := (hk₂.1 661 (by decide)).trans hp₁
      simpa [s₃, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    obtain ⟨sf, tf, hef, htf, hkf, hdf, hof, hpf, hrf⟩ := ih pre' incoming' outgoing' s₃
      (by simpa only [List.length_cons] using Nat.lt_of_succ_lt hc)
      hsource (by simpa only [s₃, State.setReg_arrs, hk₁₂.2 608 (by decide)] using hcode)
      (by simpa only [s₃, State.setReg_arrs, hk₁₂.2 608 (by decide)] using hwords)
      (fun d hd => hkeys d (by simp [hd])) hin' hout' hcursor (by simp [s₃])
      ((hk₁₂.2 601 (by decide)).trans h601) hd₂ ho₂
    refine ⟨sf, 1 + (t₁ + (t₂ + 4)) + tf,
      .while_true (GraphMinor.Compute.Crossing.eval_reg hr hc) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ he₃)) hef, ?_,
      (hk₁₂.setReg (by simp [gm06CutLinkageRegs]) _).trans hkf (fun _ h => h) (fun _ h => h),
      ?_, ?_, ?_, hrf⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [List.flatten_cons, gm06CutPathEndPairs, List.map_append,
        gm06Scatter_append, incoming'] using hdf
    · simpa only [List.flatten_cons, gm06CutPathEndPairs, List.map_append,
        gm06Scatter_append, outgoing'] using hof
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf

end GraphMinor.Compute
