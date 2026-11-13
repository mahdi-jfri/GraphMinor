module

public import GraphMinor.Compute.GM06CutComponentFilter
public import GraphMinor.Compute.GM06CutOriginRows
public import GraphMinor.Compute.CrossingOpsReplEnc

/-!
# Materializing all rotations of one cut component

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) retains the
induced order of the ends assigned to each copied vertex. This loop
reads every stored cut rotation, filters it using the computed
component vertex bits, and appends the exact length-prefixed result.
Its invariant tracks both source and output prefixes, while preserving
the component bits and all common graph data.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Exact list of induced rotations for an explicitly selected vertex list. -/
def gm06CutComponentRotations (origins active vertices : List ℕ) (rows : List (List ℕ)) : List (List ℕ) :=
  rows.map (gm06CutComponentRotation origins active vertices)

/-- Filtering preserves the number of permanent rotation slots. -/
theorem gm06CutComponentRotations_length (origins active vertices : List ℕ) (rows : List (List ℕ)) :
    (gm06CutComponentRotations origins active vertices rows).length = rows.length := by simp only [gm06CutComponentRotations, List.length_map]

/-- An induced rotation payload fits inside its original payload. -/
theorem gm06CutComponentRotations_payload_length_le (origins active vertices : List ℕ) (rows : List (List ℕ)) :
    (gm06EncodeRowsPayload (gm06CutComponentRotations origins active vertices rows)).length ≤
      rows.length + rows.flatten.length := by
  induction rows with
  | nil => simp [gm06CutComponentRotations, gm06EncodeRowsPayload]
  | cons row rows ih =>
    have hrow : (gm06CutComponentRotation origins active vertices row).length ≤ row.length := List.length_filter_le _ _
    simp only [gm06CutComponentRotations, List.map_cons, gm06EncodeRowsPayload, List.flatMap_cons,
      List.length_append, gm06EncodeNatList, List.length_cons, List.flatten_cons]
    change (gm06EncodeRowsPayload (gm06CutComponentRotations origins active vertices rows)).length ≤ _ at ih
    simp only [gm06CutComponentRotations, gm06EncodeRowsPayload] at ih
    omega

/-- Read, filter and append all remaining copied rotations of a component. -/
def gm06CutComponentRotationsLoop : Cmd :=
  .while (.reg 665)
    (.seq gm06ReadCutOriginRowProg
      (.seq gm06CutComponentFilterProg
        (.seq (GraphMinor.Compute.Crossing.emitFieldProg 616 601 651)
          (.assign 665 (.op .sub (.reg 665) (.const 1))))))

/-- Registers changed by the induced-rotation materialization loop. -/
def gm06CutComponentRotationsRegs : List ℕ := [650, 651, 652, 653, 654, 655, 656, 657, 660, 661, 662, 664, 665]

/-- Exact physical output for all induced rotations. Retained rows
are computed from component bits, not passed as an additional input. -/
theorem gm06CutComponentRotationsLoop_exec {w n m cap : ℕ} (origins active vertices : List ℕ)
    (rows : List (List ℕ)) (pre tail output : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w) (hc : rows.length < 2 ^ w)
    (horgLen : origins.length = 2 * m) (hvalues : ∀ v ∈ origins, v < n)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * m)
    (hcap : rows.length + rows.flatten.length ≤ cap) (hfit : output.length + cap + 2 < 2 ^ w)
    (h625 : s.arrs 625 = pre ++ gm06EncodeRowsPayload rows ++ tail)
    (hcode : (s.arrs 625).length < 2 ^ w) (hwords : ∀ x ∈ s.arrs 625, x < 2 ^ w)
    (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = gm06IncidenceBits (2 * m) active)
    (h630 : s.arrs 630 = gm06IncidenceBits n vertices)
    (h661 : s.regs 661 = pre.length) (h665 : s.regs 665 = rows.length)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 601 655 output cap s) :
    let payload := gm06EncodeRowsPayload (gm06CutComponentRotations origins active vertices rows)
    ∃ sf t, Exec w gm06CutComponentRotationsLoop s sf t ∧
      t ≤ 1 + 2100 * rows.length + 2100 * rows.flatten.length ∧
      Keeps gm06CutComponentRotationsRegs [601, 611, 615, 616] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 601 655 (output ++ payload) (cap - payload.length) sf ∧
      sf.regs 661 = pre.length + (gm06EncodeRowsPayload rows).length ∧ sf.regs 665 = 0 := by
  induction rows generalizing cap pre output s with
  | nil =>
    refine ⟨s, 1, .while_false (GraphMinor.Compute.Crossing.eval_reg h665 (Nat.two_pow_pos w)), by simp,
      Keeps.refl _ _ _, ?_, by simpa [gm06EncodeRowsPayload] using h661, h665⟩
    simpa [gm06CutComponentRotations, gm06EncodeRowsPayload] using hbuf
  | cons row rows ih =>
    simp only [List.length_cons] at hc h665
    simp only [List.length_cons, List.flatten_cons, List.length_append] at hcap
    have hrowSrc : s.arrs 625 = pre ++ gm06EncodeNatList row ++ (gm06EncodeRowsPayload rows ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using h625
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hp₁⟩ := gm06ReadCutOriginRowProg_exec
      pre row (gm06EncodeRowsPayload rows ++ tail) s (by omega) hrowSrc hcode hwords h661
    obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06CutComponentFilterProg_exec
      origins active vertices row s₁ hw hn hm (by omega) horgLen (fun d hd => hkeys d (by simp [hd])) hvalues hd₁
      ((hk₁.2 626 (by decide)).trans h626) ((hk₁.2 627 (by decide)).trans h627) ((hk₁.2 630 (by decide)).trans h630)
    let out := gm06CutComponentRotation origins active vertices row
    have houtlen : out.length ≤ row.length := List.length_filter_le _ _
    have hrowBound : (gm06CutComponentRotation origins active vertices row).length ≤ row.length := houtlen
    have houtwords : ∀ d ∈ out, d < 2 ^ w := fun d hd => (hkeys d (by
      apply List.mem_flatten.mpr; exact ⟨row, List.mem_cons_self, (List.mem_filter.mp hd).1⟩)).trans hm
    have hb₂ : GraphMinor.Compute.Crossing.IsBuf 601 655 output cap s₂ :=
      ⟨(hk₂.2 601 (by decide)).trans ((hk₁.2 601 (by decide)).trans hbuf.1),
        (hk₂.1 655 (by decide)).trans ((hk₁.1 655 (by decide)).trans hbuf.2)⟩
    obtain ⟨s₃, t₃, he₃, ht₃, hb₃, ha₃, hr₃⟩ := GraphMinor.Compute.Crossing.emitFieldProg_exec
      616 601 651 (by decide) hd₂ hb₂ (by omega) houtwords hfit
    have hk₃ : Keeps [654, 655, 656, 657] [601] s₂ s₃ := by
      constructor
      · intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
        exact hr₃ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
      · intro a ha
        exact ha₃ a (by simpa using ha)
    have hk₁₃ : Keeps gm06CutComponentRotationsRegs [601, 611, 615, 616] s s₃ :=
      ((hk₁.mono (by simp [gm06CutComponentRotationsRegs]) (by simp)).trans hk₂
        (by simp [gm06CutComponentRotationsRegs]) (by simp)).trans hk₃
          (by simp [gm06CutComponentRotationsRegs]) (by simp)
    have hcount : s₃.regs 665 = rows.length + 1 := (hk₃.1 665 (by decide)).trans ((hk₂.1 665 (by decide)).trans ((hk₁.1 665 (by decide)).trans h665))
    let s₄ := s₃.setReg 665 rows.length
    have he₄ : Exec w (.assign 665 (.op .sub (.reg 665) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        have he := GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_reg hcount hc)
          (GraphMinor.Compute.Crossing.eval_const (c := 1) (by omega))
        simpa using he)
    have hk₁₄ : Keeps gm06CutComponentRotationsRegs [601, 611, 615, 616] s s₄ :=
      hk₁₃.setReg (by simp [gm06CutComponentRotationsRegs]) _
    let pre' := pre ++ gm06EncodeNatList row
    let output' := output ++ gm06EncodeNatList out
    have hsource : s₄.arrs 625 = pre' ++ gm06EncodeRowsPayload rows ++ tail := by
      rw [hk₁₄.2 625 (by decide)]
      simpa only [pre', List.append_assoc] using hrowSrc
    have hp₄ : s₄.regs 661 = pre'.length := by
      have hp := (hk₃.1 661 (by decide)).trans ((hk₂.1 661 (by decide)).trans hp₁)
      simpa [s₄, pre', gm06EncodeNatList, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    obtain ⟨sf, tf, hef, htf, hkf, hbf, hpf, hcf⟩ := ih
      (cap := cap - (out.length + 1)) pre' output' s₄ (by omega) (fun d hd => hkeys d (by simp [hd]))
      (by omega) (by simp only [output', gm06EncodeNatList, List.length_append, List.length_cons]; omega)
      hsource (by rw [hk₁₄.2 625 (by decide)]; exact hcode)
      (by rw [hk₁₄.2 625 (by decide)]; exact hwords)
      ((hk₁₄.2 626 (by decide)).trans h626) ((hk₁₄.2 627 (by decide)).trans h627)
      ((hk₁₄.2 630 (by decide)).trans h630) hp₄ (by simp [s₄])
      (by simpa [s₄, output', out, GraphMinor.Compute.Crossing.IsBuf, gm06EncodeNatList] using hb₃)
    refine ⟨sf, 1 + (t₁ + (t₂ + (t₃ + 4))) + tf,
      .while_true (GraphMinor.Compute.Crossing.eval_reg h665 hc) (Nat.succ_ne_zero _)
        (.seq he₁ (.seq he₂ (.seq he₃ he₄))) hef, ?_,
      hk₁₄.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, hcf⟩
    · simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega
    · simpa only [gm06CutComponentRotations, List.map_cons, gm06EncodeRowsPayload, List.flatMap_cons,
        output', out, List.append_assoc, List.length_append, gm06EncodeNatList, List.length_cons, Nat.sub_sub,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hbf
    · simpa only [pre', gm06EncodeRowsPayload, List.flatMap_cons, List.length_append,
        gm06EncodeNatList, List.length_cons, Nat.add_assoc] using hpf

end GraphMinor.Compute
