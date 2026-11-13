module

public import GraphMinor.Compute.GM06CutComponentAppend

/-!
# Materializing every cuff component's induced rotations

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns the
finite cut components with their induced vertex orders. This loop
reads each computed membership row from array 600, saves its source
cursor, and scans the common cut rotations to append the component's
full rotation record. Restoring the saved cursor resumes the next
membership row. The output is the exact sequence of induced records.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read a component membership row from 600 into mask array 630. -/
def gm06ReadCutComponentMaskProg : Cmd :=
  renameCmd gm06RotationReadRename (gm06ReadRowProg 600 630)

/-- Exact relocated membership-row reading with the original source cursor. -/
theorem gm06ReadCutComponentMaskProg_exec {w : ℕ} (pre row tail : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 600 = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs 600).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 600, x < 2 ^ w)
    (hr : s.regs 661 = pre.length) :
    ∃ sf t, Exec w gm06ReadCutComponentMaskProg s sf t ∧
      t ≤ 13 + 22 * row.length ∧ Keeps [660, 661, 662, 664] [630] s sf ∧
      sf.arrs 630 = row ∧ sf.regs 661 = pre.length + 1 + row.length := by
  let sr := renameState gm06RotationReadRename s
  obtain ⟨sm, t, he, ht, hd, hp, hregs, harrs⟩ := gm06ReadRowProg_exec
    600 630 (by decide) pre row tail sr hw ha hn hwords hr
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
    have hneq : gm06RotationReadRename a ≠ 630 := by
      simp only [List.mem_singleton] at ha
      unfold gm06RotationReadRename
      split_ifs <;> omega
    change sm.arrs (gm06RotationReadRename a) = s.arrs a
    rw [harrs _ hneq]
    exact congrArg s.arrs (gm06RotationReadRename_involutive a)

/-- Exact sequence of induced rotation records for explicit component masks. -/
def gm06CutMaterializedPayload (n : ℕ) (data : GM06CutData) (masks : List (List ℕ)) : List ℕ :=
  masks.flatMap (fun bits => gm06EncodeRows (gm06CutMaterializedRows n data bits))

/-- A single component record fits inside the common graph's row encoding. -/
theorem gm06CutMaterializedRows_code_length_le (n : ℕ) (data : GM06CutData) (bits : List ℕ) :
    (gm06EncodeRows (gm06CutMaterializedRows n data bits)).length ≤
      1 + data.rotations.length + data.rotations.flatten.length := by
  have h := gm06CutComponentRotations_payload_length_le data.origins data.activeDarts
    (gm06CutBitVertices n bits) data.rotations
  change (gm06EncodeRowsPayload (gm06CutMaterializedRows n data bits)).length ≤
    data.rotations.length + data.rotations.flatten.length at h
  simp only [gm06EncodeRows, List.length_cons]
  omega

/-- Total component rotation storage is bounded by the mask count
multiplied by one complete common-graph record. -/
theorem gm06CutMaterializedPayload_length_le (n : ℕ) (data : GM06CutData) (masks : List (List ℕ)) :
    (gm06CutMaterializedPayload n data masks).length ≤ masks.length *
      (1 + data.rotations.length + data.rotations.flatten.length) := by
  induction masks with
  | nil => simp [gm06CutMaterializedPayload]
  | cons bits masks ih =>
    have h := gm06CutMaterializedRows_code_length_le n data bits
    simp only [gm06CutMaterializedPayload, List.flatMap_cons, List.length_append, List.length_cons,
      Nat.add_mul, Nat.one_mul]
    change (masks.flatMap _).length ≤ _ at ih
    omega

/-- Read one mask, preserve its next cursor, append its induced
rotation record, restore the cursor and advance the remaining count. -/
def gm06CutMaterializeLoop : Cmd :=
  .while (.reg 668)
    (.seq gm06ReadCutComponentMaskProg
      (.seq (.assign 659 (.reg 661))
        (.seq gm06CutComponentAppendProg
          (.seq (.assign 661 (.reg 659)) (.assign 668 (.op .sub (.reg 668) (.const 1)))))))

/-- Registers used by all induced component-rotation records. -/
def gm06CutMaterializeRegs : List ℕ := gm06CutComponentRotationsRegs ++ [659, 668]

/-- Exact materialization of every component mask. Only numerical
sizes and zero/one membership encoding are required of the masks. -/
theorem gm06CutMaterializeLoop_exec {w n m cap : ℕ} (data : GM06CutData)
    (masks : List (List ℕ)) (pre tail padding output : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hlen : data.rotations.length = n) (horgLen : data.origins.length = 2 * m)
    (hvalues : ∀ v ∈ data.origins, v < n) (hkeys : ∀ d ∈ data.rotations.flatten, d < 2 * m)
    (hmaskLen : ∀ mask ∈ masks, mask.length = n)
    (hmaskBits : ∀ mask ∈ masks, ∀ x ∈ mask, x = 0 ∨ x = 1)
    (hcap : masks.length * (1 + n + data.rotations.flatten.length) ≤ cap)
    (hfit : output.length + cap + 2 < 2 ^ w) (hc : masks.length < 2 ^ w)
    (h600 : s.arrs 600 = pre ++ gm06EncodeRowsPayload masks ++ tail)
    (hcode600 : (s.arrs 600).length < 2 ^ w) (hwords600 : ∀ x ∈ s.arrs 600, x < 2 ^ w)
    (h625 : s.arrs 625 = gm06EncodeRows data.rotations ++ padding)
    (hcode625 : (s.arrs 625).length < 2 ^ w) (hwords625 : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = data.origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) data.activeDarts)
    (h620 : s.regs 620 = n) (h661 : s.regs 661 = pre.length) (h668 : s.regs 668 = masks.length)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 601 655 output cap s) :
    ∃ sf t, Exec w gm06CutMaterializeLoop s sf t ∧
      t ≤ 1 + masks.length * (40 + 2200 * n + 2200 * data.rotations.flatten.length) ∧
      Keeps gm06CutMaterializeRegs [601, 611, 615, 616, 630] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 601 655 (output ++ gm06CutMaterializedPayload n data masks)
        (cap - (gm06CutMaterializedPayload n data masks).length) sf ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload masks).length ∧ sf.regs 668 = 0 := by
  induction masks generalizing cap pre output s with
  | nil =>
    refine ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg h668 (Nat.two_pow_pos w)), by simp,
      Keeps.refl _ _ _, ?_, by simpa [gm06EncodeRowsPayload] using h661, h668⟩
    simpa [gm06CutMaterializedPayload] using hbuf
  | cons bits masks ih =>
    simp only [List.length_cons] at hc h668 hcap
    have hbLen := hmaskLen bits List.mem_cons_self
    have hbBits := hmaskBits bits List.mem_cons_self
    have hsource : s.arrs 600 = pre ++ gm06EncodeNatList bits ++ (gm06EncodeRowsPayload masks ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using h600
    have hcursorFit : pre.length + 1 + bits.length < 2 ^ w := by
      have hl : (s.arrs 600).length = pre.length + (1 + bits.length) +
          (gm06EncodeRowsPayload masks).length + tail.length := by
        rw [hsource]
        simp [gm06EncodeNatList, List.length_append]
        omega
      omega
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hp₁⟩ := gm06ReadCutComponentMaskProg_exec
      pre bits (gm06EncodeRowsPayload masks ++ tail) s (by omega) hsource hcode600 hwords600 h661
    let s₂ := s₁.setReg 659 (pre.length + 1 + bits.length)
    have he₂ : Exec w (.assign 659 (.reg 661)) s₁ s₂ 2 :=
      .assign (GraphMinor.Compute.Crossing.eval_reg hp₁ hcursorFit)
    have hk₁₂ : Keeps gm06CutMaterializeRegs [601, 611, 615, 616, 630] s s₂ :=
      (hk₁.mono (by simp [gm06CutMaterializeRegs, gm06CutComponentRotationsRegs]) (by simp)).setReg
        (by simp [gm06CutMaterializeRegs]) _
    have hcapHead : 1 + n + data.rotations.flatten.length ≤ cap := by
      simp only [Nat.add_mul, Nat.one_mul] at hcap
      omega
    have hmask : s₂.arrs 630 = gm06IncidenceBits n (gm06CutBitVertices n bits) := by
      change s₁.arrs 630 = _
      rw [hd₁, gm06CutBitVertices_incidence bits hbLen hbBits]
    obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hb₃⟩ := gm06CutComponentAppendProg_exec data
      (gm06CutBitVertices n bits) output padding s₂ hw hn hm hlen horgLen hvalues hkeys hcapHead hfit
      ((hk₁₂.2 625 (by decide)).trans h625)
      (by rw [hk₁₂.2 625 (by decide)]; exact hcode625)
      (by rw [hk₁₂.2 625 (by decide)]; exact hwords625)
      ((hk₁₂.2 626 (by decide)).trans h626) ((hk₁₂.2 627 (by decide)).trans h627) hmask
      ((hk₁₂.1 620 (by simp [gm06CutMaterializeRegs, gm06CutComponentRotationsRegs])).trans h620)
      ⟨(hk₁.2 601 (by decide)).trans hbuf.1, (hk₁.1 655 (by decide)).trans hbuf.2⟩
    have hsave : s₃.regs 659 = pre.length + 1 + bits.length :=
      (hk₃.1 659 (by decide)).trans (by simp [s₂])
    have hcount : s₃.regs 668 = masks.length + 1 :=
      (hk₃.1 668 (by decide)).trans (by simpa [s₂] using (hk₁.1 668 (by decide)).trans h668)
    let s₄ := s₃.setReg 661 (pre.length + 1 + bits.length)
    let s₅ := s₄.setReg 668 masks.length
    have he₄ : Exec w (.assign 661 (.reg 659)) s₃ s₄ 2 := .assign (GraphMinor.Compute.Crossing.eval_reg hsave hcursorFit)
    have he₅ : Exec w (.assign 668 (.op .sub (.reg 668) (.const 1))) s₄ s₅ 4 :=
      .assign (by
        have he := GraphMinor.Compute.Crossing.eval_sub
          (GraphMinor.Compute.Crossing.eval_reg (r := 668) (s := s₄) (by simpa [s₄] using hcount) hc)
          (GraphMinor.Compute.Crossing.eval_const (c := 1) (by omega))
        simpa using he)
    have hk₁₅ : Keeps gm06CutMaterializeRegs [601, 611, 615, 616, 630] s s₅ :=
      ((hk₁₂.trans hk₃ (by simp [gm06CutMaterializeRegs, gm06CutComponentRotationsRegs]) (by simp)).setReg
        (by simp [gm06CutMaterializeRegs, gm06CutComponentRotationsRegs]) _).setReg (by simp [gm06CutMaterializeRegs]) _
    let record := gm06EncodeRows (gm06CutMaterializedRows n data bits)
    have hrecord : record.length ≤ 1 + n + data.rotations.flatten.length := by
      simpa only [hlen] using gm06CutMaterializedRows_code_length_le n data bits
    let pre' := pre ++ gm06EncodeNatList bits
    let output' := output ++ record
    have hsrc' : s₅.arrs 600 = pre' ++ gm06EncodeRowsPayload masks ++ tail := by
      rw [hk₁₅.2 600 (by decide)]
      simpa only [pre', List.append_assoc] using hsource
    obtain ⟨sf, tf, hef, htf, hkf, hbf, hpf, hcf⟩ := ih
      (cap := cap - record.length) pre' output' s₅
      (fun mask hm => hmaskLen mask (List.mem_cons_of_mem _ hm))
      (fun mask hm => hmaskBits mask (List.mem_cons_of_mem _ hm))
      (by simp only [Nat.add_mul, Nat.one_mul] at hcap; omega)
      (by simp only [output', List.length_append]; omega) (by omega) hsrc'
      (by rw [hk₁₅.2 600 (by decide)]; exact hcode600)
      (by rw [hk₁₅.2 600 (by decide)]; exact hwords600)
      ((hk₁₅.2 625 (by decide)).trans h625)
      (by rw [hk₁₅.2 625 (by decide)]; exact hcode625)
      (by rw [hk₁₅.2 625 (by decide)]; exact hwords625)
      ((hk₁₅.2 626 (by decide)).trans h626) ((hk₁₅.2 627 (by decide)).trans h627)
      ((hk₁₅.1 620 (by simp [gm06CutMaterializeRegs, gm06CutComponentRotationsRegs])).trans h620)
      (by simp [s₅, s₄, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm])
      (by simp [s₅])
      (by simpa [s₅, s₄, output', record, gm06CutMaterializedRows, GraphMinor.Compute.Crossing.IsBuf] using hb₃)
    refine ⟨sf, 1 + (t₁ + (2 + (t₃ + (2 + 4)))) + tf,
      .while_true (GraphMinor.Compute.Crossing.eval_reg h668 hc) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅)))) hef, ?_,
      hk₁₅.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, hcf⟩
    · rw [hbLen] at ht₁
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · simpa only [gm06CutMaterializedPayload, List.flatMap_cons, output', record,
        List.append_assoc, List.length_append, Nat.sub_sub] using hbf
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf

end GraphMinor.Compute
