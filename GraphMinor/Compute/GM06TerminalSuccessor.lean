module

public import GraphMinor.Compute.GM06CylinderDegree
import GraphMinor.GM06.Section5TerminalFeasibility
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The terminal RAM decision in VI (5.7)

After all reductions have been excluded, scan the initial valencies
and return one exactly when none is one. The proved terminal criterion
identifies this bit with feasibility of the next winding. This file
verifies the decision branch, with a quadratic scan bound and the
ordinary finite graph and cuff interpretation as its input conditions.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Surface GraphMinor.GM06

/-- Decide the next winding in an unreduced instance by its initial valencies. -/
def gm06TerminalSuccessorProg : Cmd :=
  .seq gm06SuccessorDegreeScanProg (.assign outReg (.op .eq (.reg 27) (.const 0)))

/-- The terminal RAM branch returns precisely the next-winding feasibility bit. -/
theorem gm06TerminalSuccessorProg_exec {w k : ℕ} {θ : ℝ}
    (x : GM06SuccessorInput) (G : Drawing ClosedCylinder)
    (rep : GM06SuccessorGraphRep x G.toGraph)
    (hlen : x.innerCuff.length = k) (label : Fin k → Fin x.vertexCount)
    (hlabels : ∀ i : Fin k,
      x.innerCuff[i.val]'(by rw [hlen]; exact i.isLt) = (label i).val)
    (hpoints : ∀ i : Fin k, (rep.vertex (label i)).val = cylinderM1Point k i)
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L)
    (s : State) (hw : 1 < 2 ^ w) (ha : s.arrs 0 = gm06EncodeSuccessorInput x)
    (hn : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeSuccessorInput x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06TerminalSuccessorProg s s' t ∧
      t ≤ 14 + 22 * (gm06EncodeSuccessorInput x).length +
        x.innerCuff.length * (24 + 14 * x.endpoints.length) ∧ s'.arrs 0 = s.arrs 0 ∧
      (s'.regs outReg = 1 ↔ IsThetaFeasible k G (θ + 1 / (k : ℝ))) ∧
      (s'.regs outReg = 0 ∨ s'.regs outReg = 1) := by
  obtain ⟨s₁, t, he, ht, hs, hd⟩ := gm06SuccessorDegreeScanProg_exec_on_cylinder
    x G rep hlen label hlabels hpoints s hw ha hn hwords
  have hcrit := isThetaFeasible_next_iff_no_initial_valency_one L hG hθ hno
  have hflag : s₁.regs 27 = 0 ∨ s₁.regs 27 = 1 := hd.imp And.left And.left
  have hgood : s₁.regs 27 = 0 ↔ IsThetaFeasible k G (θ + 1 / (k : ℝ)) := by
    constructor
    · intro hz
      rcases hd with h | h
      · exact hcrit.mpr h.2
      · have hh : (0 : ℕ) = 1 := hz.symm.trans h.1
        exact False.elim (by cases hh)
    · intro hf
      rcases hd with h | h
      · exact h.1
      · obtain ⟨_, i, _, hi⟩ := h
        exact False.elim (hcrit.mp hf i hi)
  have hfit : s₁.regs 27 < 2 ^ w := by
    rcases hflag with h | h
    · rw [h]; exact Nat.two_pow_pos w
    · rw [h]; exact hw
  let result := if s₁.regs 27 = 0 then 1 else 0
  let s₂ := s₁.setReg outReg result
  have heval : (Expr.op .eq (.reg 27) (.const 0)).eval w s₁ = some result :=
    GraphMinor.Compute.Crossing.eval_eq
      (GraphMinor.Compute.Crossing.eval_reg rfl hfit)
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hw
  refine ⟨s₂, t + 4, .seq he (.assign heval), by omega, ?_, ?_, ?_⟩
  · simpa only [s₂, State.setReg_arrs] using hs
  · have hh : s₂.regs outReg = 1 ↔ s₁.regs 27 = 0 := by simp [s₂, result]
    exact hh.trans hgood
  · simp only [s₂, State.setReg_regs_self]
    dsimp only [result]
    split <;> simp

end GraphMinor.Compute
