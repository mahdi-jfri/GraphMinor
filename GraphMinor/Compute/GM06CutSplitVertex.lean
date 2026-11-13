module

public import GraphMinor.Compute.GM06CutEmitRow

/-!
# Emitting both induced rotations of one original vertex

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) processes an
original rotation by computing its local cut position, then forming
the left and right induced rows. This program reads the computed
path and cuff tables itself, prepares all interval positions once,
and emits the two rows in permanent copy-label order. The exact
buffer invariant is the encoded pure split-vertex output.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Registers changed by preparing and emitting both copied rows. -/
def gm06CutSplitVertexRegs : List ℕ :=
  [650, 651, 652, 653, 654, 655, 656, 657, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677]

/-- Prepare the local cut data and emit the left row followed by the right row. -/
def gm06CutSplitVertexProg : Cmd :=
  .seq gm06CutPrepareRowProg
    (.seq (.assign 656 (.const 0))
      (.seq gm06CutEmitRowProg (.seq (.assign 656 (.const 1)) gm06CutEmitRowProg)))

private theorem metadata_after_emission (position : Option GM06CutPosition) (row : List ℕ)
    (s sf : State) (hk : Keeps [650, 651, 652, 653, 654, 655, 656, 657] [615, 616, 625] s sf)
    (hm : ∀ pair ∈ gm06CutRowMetadata position row, s.regs pair.1 = pair.2) :
    ∀ pair ∈ gm06CutRowMetadata position row, sf.regs pair.1 = pair.2 := by
  intro pair hp
  have hkey := gm06CutRowMetadata_key position row pair hp
  have hnot : pair.1 ∉ [650, 651, 652, 653, 654, 655, 656, 657] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkey ⊢
    omega
  exact (hk.1 pair.1 hnot).trans (hm pair hp)

/-- Each processed vertex appends exactly its two copied rotation
rows. No decoded case, side table or output row is an input. -/
theorem gm06CutSplitVertexProg_exec {w n m v cap : ℕ}
    (marks : GM06CutTables) (row pre : List ℕ) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hm : 4 * m < 2 ^ w)
    (hv : v < n) (hnd : row.Nodup) (hkeys : ∀ d ∈ row, d < 2 * m)
    (hlens : marks.incoming.length = n ∧ marks.outgoing.length = n ∧
      marks.cuffPositive.length = n ∧ marks.cuffNegative.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing)
    (h623 : s.arrs 623 = marks.cuffPositive) (h624 : s.arrs 624 = marks.cuffNegative)
    (h611 : s.arrs 611 = row) (h647 : s.regs 647 = 2 * m) (h666 : s.regs 666 = v)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 625 655 pre cap s)
    (hcap : 2 + 2 * row.length ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w) :
    ∃ sf t, Exec w gm06CutSplitVertexProg s sf t ∧
      t ≤ 5000 * (row.length + 1) + 26 * m ∧
      Keeps gm06CutSplitVertexRegs [614, 615, 616, 625] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 625 655
        (pre ++ gm06EncodeRowsPayload (gm06SplitVertexRows (gm06CutPositionAt marks v) row))
        (cap - (gm06EncodeRowsPayload (gm06SplitVertexRows (gm06CutPositionAt marks v) row)).length) sf := by
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hl : row.length < 2 ^ w := by omega
  let p := gm06CutPositionAt marks v
  let left := gm06CutSelectedRow p row true
  let right := gm06CutSelectedRow p row false
  have hleftlen : left.length ≤ row.length := gm06CutSelectedRow_length_le _ _ _
  have hrightlen : right.length ≤ row.length := gm06CutSelectedRow_length_le _ _ _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hki, hpos, hfirst, hlast⟩ := gm06CutPrepareRowProg_exec
    marks row s hw2 hn (by omega) hl hv hnd hkeys hlens hwords h620 h621 h623 h624 h611 h647 h666
  have hmeta₁ := gm06CutPrepared_metadata marks v row s s₁ hki hfirst hlast
  have hmetaWords := gm06CutRowMetadata_words marks v row hw2 hl hwords
  let s₂ := s₁.setReg 656 0
  have he₂ : Exec w (.assign 656 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hm₂ : ∀ pair ∈ gm06CutRowMetadata p row, s₂.regs pair.1 = pair.2 := by
    apply metadata_after_emission p row s₁ s₂
      ((Keeps.refl _ _ s₁).setReg (by simp) _) hmeta₁
  have hb₂ : GraphMinor.Compute.Crossing.IsBuf 625 655 pre cap s₂ :=
    ⟨(hk₁.2 625 (by decide)).trans hbuf.1,
      by simpa only [s₂, State.setReg_regs_ne _ _ (by decide : 655 ≠ 656)] using
        (hk₁.1 655 (by simp [gm06CutPrepareRowRegs])).trans hbuf.2⟩
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hb₃⟩ := gm06CutEmitRowProg_exec p row pre true s₂ hw hm hnd hkeys
    ((hk₁.2 611 (by decide)).trans h611) hpos (by simp [s₂]) hm₂ hmetaWords hb₂ (by omega) hfit
  let s₄ := s₃.setReg 656 1
  have he₄ : Exec w (.assign 656 (.const 1)) s₃ s₄ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const hw1)
  have hm₄ : ∀ pair ∈ gm06CutRowMetadata p row, s₄.regs pair.1 = pair.2 :=
    metadata_after_emission p row s₂ s₄ (hk₃.setReg (by simp) _) hm₂
  have hlenField : (gm06EncodeNatList left).length = left.length + 1 := by simp [gm06EncodeNatList]
  have hb₄ : GraphMinor.Compute.Crossing.IsBuf 625 655
      (pre ++ gm06EncodeNatList left) (cap - (left.length + 1)) s₄ := by
    exact ⟨hb₃.1, by simpa only [s₄, State.setReg_regs_ne _ _ (by decide : 655 ≠ 656)] using hb₃.2⟩
  obtain ⟨sf, tf, hef, htf, hkf, hbf⟩ := gm06CutEmitRowProg_exec p row
    (pre ++ gm06EncodeNatList left) false s₄ hw hm hnd hkeys
    ((hk₃.2 611 (by decide)).trans ((hk₁.2 611 (by decide)).trans h611))
    ((hk₃.2 614 (by decide)).trans hpos) (by simp [s₄]) hm₄ hmetaWords hb₄ (by omega)
    (by simp only [List.length_append, hlenField]; omega)
  have hk₁₂ : Keeps gm06CutSplitVertexRegs [614, 615, 616, 625] s s₂ :=
    (hk₁.mono (by simp [gm06CutSplitVertexRegs, gm06CutPrepareRowRegs]) (by simp)).setReg
      (by simp [gm06CutSplitVertexRegs]) _
  have hk₁₄ : Keeps gm06CutSplitVertexRegs [614, 615, 616, 625] s s₄ :=
    (hk₁₂.trans hk₃ (by simp [gm06CutSplitVertexRegs]) (by simp)).setReg
      (by simp [gm06CutSplitVertexRegs]) _
  refine ⟨sf, t₁ + (2 + (t₃ + (2 + tf))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef))), by omega,
    hk₁₄.trans hkf (by simp [gm06CutSplitVertexRegs]) (by simp), ?_⟩
  simpa only [gm06SplitVertexRows_eq_selected, gm06EncodeRowsPayload, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.length_append, hlenField,
    gm06EncodeNatList, List.length_cons, Nat.sub_sub, List.append_assoc, p, left, right,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbf

end GraphMinor.Compute
