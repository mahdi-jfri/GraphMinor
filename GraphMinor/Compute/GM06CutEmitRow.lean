module

public import GraphMinor.Compute.GM06CutRowMetadata
public import GraphMinor.Compute.CrossingOpsReplEnc

/-!
# Emitting one computed cut rotation

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns the
induced rotation rows in copy-label order. This command computes a selected
row and appends its length and darts to the global row buffer. The
buffer invariant identifies its exact prefix and remaining capacity.
All computed local fields and source arrays remain available for
emitting the other copy of the same vertex.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Select the current copied row and append its length-prefixed
encoding to output buffer 625, using global cursor register 655. -/
def gm06CutEmitRowProg : Cmd :=
  .seq gm06CutSelectRowProg (GraphMinor.Compute.Crossing.emitFieldProg 616 625 651)

/-- The emitted field is exactly the prescribed induced row. The
local scan and serialization both take linear time in the old row. -/
theorem gm06CutEmitRowProg_exec {w m cap : ℕ}
    (position : Option GM06CutPosition) (row pre : List ℕ) (left : Bool) (s : State)
    (hw : 4 < 2 ^ w) (hm : 4 * m < 2 ^ w)
    (hnd : row.Nodup) (hkeys : ∀ d ∈ row, d < 2 * m)
    (h611 : s.arrs 611 = row) (h614 : s.arrs 614 = gm06RowPositions (2 * m) row)
    (h656 : s.regs 656 = (!left).toNat)
    (hmeta : ∀ pair ∈ gm06CutRowMetadata position row, s.regs pair.1 = pair.2)
    (hword : ∀ pair ∈ gm06CutRowMetadata position row, pair.2 < 2 ^ w)
    (hbuf : GraphMinor.Compute.Crossing.IsBuf 625 655 pre cap s)
    (hcap : row.length + 1 ≤ cap) (hfit : pre.length + cap + 2 < 2 ^ w) :
    ∃ sf t, Exec w gm06CutEmitRowProg s sf t ∧ t ≤ 2100 * (row.length + 1) ∧
      Keeps [650, 651, 652, 653, 654, 655, 656, 657] [615, 616, 625] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 625 655
        (pre ++ gm06EncodeNatList (gm06CutSelectedRow position row left))
        (cap - ((gm06CutSelectedRow position row left).length + 1)) sf := by
  let out := gm06CutSelectedRow position row left
  have houtlen := gm06CutSelectedRow_length_le position row left
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06CutSelectRowProg_exec_metadata
    position row left s hw hm (by omega) hnd hkeys h611 h614 h656 hmeta hword
  have hb₁ : GraphMinor.Compute.Crossing.IsBuf 625 655 pre cap s₁ :=
    ⟨(hk₁.2 625 (by decide)).trans hbuf.1, (hk₁.1 655 (by decide)).trans hbuf.2⟩
  have houtwords : ∀ x ∈ out, x < 2 ^ w := by
    intro x hx
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
    exact (gm06CutOutputDart_lt position left (hkeys _ (List.mem_filter.mp hd).1)).trans hm
  obtain ⟨sf, tf, hef, htf, hbf, haf, hrf⟩ := GraphMinor.Compute.Crossing.emitFieldProg_exec
    616 625 651 (by decide) hd₁ hb₁ (by omega) houtwords hfit
  have hkf : Keeps [654, 655, 656, 657] [625] s₁ sf := by
    constructor
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
      exact hrf r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    · intro A hA
      exact haf A (by simpa using hA)
  refine ⟨sf, t₁ + tf, .seq he₁ hef, by omega,
    (hk₁.mono (by simp) (by simp)).trans hkf (by simp) (by simp), ?_⟩
  simpa only [gm06EncodeNatList] using hbf

end GraphMinor.Compute
