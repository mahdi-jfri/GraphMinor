module

public import GraphMinor.Compute.GM06PuncturedEdgeMark
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading an active edge for the punctured component search

For Reduction 2 in VI (5.7), page 133, keep the original edge
indices while deleted edges are masked out. Read the two endpoint
positions for the current edge and its activity bit, then run the
punctured matrix step. The arrays holding the instance are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Read edge 136 and mark its adjacency away from removed vertex 135. -/
def gm06PuncturedEdgeReadProg (ends active : Arr) : Cmd :=
  .seq (.assign 132 (.read ends (.op .mul (.reg 136) (.const 2))))
    (.seq (.assign 133 (.read ends (.op .add (.op .mul (.reg 136) (.const 2)) (.const 1))))
      (.seq (.assign 134 (.read active (.reg 136))) gm06PuncturedEdgeMarkProg))

/-- One indexed edge read produces exactly the active punctured row
marks in constant time, preserving all arrays except the matrix. -/
theorem gm06PuncturedEdgeReadProg_exec {w n : ℕ} (ends active : Arr)
    (xs mask : List ℕ) (i : ℕ) (hi : i < mask.length) (e : Fin n × Fin n) (cut : Fin n)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hlen : xs.length = 2 * mask.length) (hm : xs.length < 2 ^ w)
    (hbits : ∀ b ∈ mask, b ≤ 1)
    (hfirst : xs[2 * i]'(by omega) = e.1.val)
    (hsecond : xs[2 * i + 1]'(by omega) = e.2.val)
    {s : State} (ha : s.arrs ends = xs) (hb : s.arrs active = mask)
    (hindex : s.regs 136 = i) (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val)
    (hcap : (s.arrs 28).length = n * n) :
    ∃ s' t, Exec w (gm06PuncturedEdgeReadProg ends active) s s' t ∧ t ≤ 41 ∧
      Keeps [132, 133, 134] [28] s s' ∧
      s'.arrs 28 = (gm06PuncturedEdgeRows e mask[i] cut).foldl (gm06MatrixMarkRow n) (s.arrs 28) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hiw : i < 2 ^ w := by omega
  have h2i : 2 * i < xs.length := by omega
  have h2i1 : 2 * i + 1 < xs.length := by omega
  have haddr : (Expr.op .mul (.reg 136) (.const 2)).eval w s = some (2 * i) := by
    simpa only [Nat.mul_comm] using eval_mul (eval_reg hindex hiw) (eval_const hw)
      (by omega : i * 2 < 2 ^ w)
  have hreadA : (Expr.read ends (.op .mul (.reg 136) (.const 2))).eval w s = some e.1.val := by
    have hh := eval_read (a := ends) haddr (by simpa only [ha] using h2i)
      (by simpa only [ha, hfirst] using e.1.isLt.trans hn)
    simpa only [ha, hfirst] using hh
  let s₁ := s.setReg 132 e.1.val
  have he₁ : Exec w (.assign 132 (.read ends (.op .mul (.reg 136) (.const 2)))) s s₁ 5 :=
    .assign hreadA
  have haddr₁ : (Expr.op .mul (.reg 136) (.const 2)).eval w s₁ = some (2 * i) := by
    simpa [s₁, Expr.eval] using haddr
  have haddrB := eval_add haddr₁ (eval_const hw1) (h2i1.trans hm)
  have hreadB : (Expr.read ends (.op .add (.op .mul (.reg 136) (.const 2)) (.const 1))).eval w s₁ = some e.2.val := by
    have hh := eval_read (a := ends) haddrB (by simpa only [s₁, State.setReg_arrs, ha] using h2i1)
      (by simpa only [s₁, State.setReg_arrs, ha, hsecond] using e.2.isLt.trans hn)
    simpa only [s₁, State.setReg_arrs, ha, hsecond] using hh
  let s₂ := s₁.setReg 133 e.2.val
  have he₂ : Exec w (.assign 133 (.read ends
      (.op .add (.op .mul (.reg 136) (.const 2)) (.const 1)))) s₁ s₂ 7 := .assign hreadB
  have hbval : mask[i] ≤ 1 := hbits _ (List.getElem_mem hi)
  have hreadM : (Expr.read active (.reg 136)).eval w s₂ = some mask[i] := by
    have hh := eval_read (a := active) (eval_reg (s := s₂) (r := 136) (by simpa [s₂, s₁] using hindex) hiw)
      (by simpa [s₂, s₁, hb] using hi)
      (by simpa [s₂, s₁, hb] using hbval.trans_lt hw1)
    simpa [s₂, s₁, hb] using hh
  let s₃ := s₂.setReg 134 mask[i]
  have he₃ : Exec w (.assign 134 (.read active (.reg 136))) s₂ s₃ 3 := .assign hreadM
  obtain ⟨s', t, he₄, ht, hmat, _, _⟩ := gm06PuncturedEdgeMarkProg_exec (s := s₃) e mask[i] cut
    hw1 hn hsquare hbval (by simpa [s₃, s₂, s₁] using hN) (by simp [s₃, s₂, s₁])
    (by simp [s₃, s₂]) (by simp [s₃]) (by simpa [s₃, s₂, s₁] using hcut) hcap
  have hex : Exec w (gm06PuncturedEdgeReadProg ends active) s s' (5 + (7 + (3 + t))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨s', _, hex, by omega, ⟨?_, ?_⟩, hmat⟩
  · intro r hr
    apply hex.regs_eq_of_not_mem_writtenRegs
    simpa [gm06PuncturedEdgeReadProg, gm06PuncturedEdgeMarkProg, gm06VertexEdgeMarkProg,
      Cmd.writtenRegs, and_comm, and_left_comm, and_assoc] using hr
  · intro a ha28
    apply hex.arrs_eq_of_not_mem_writtenArrs
    simpa [gm06PuncturedEdgeReadProg, gm06PuncturedEdgeMarkProg, gm06VertexEdgeMarkProg,
      Cmd.writtenArrs] using ha28

end GraphMinor.Compute
