module

public import GraphMinor.Compute.PlanarityRamLayout

/-!
# Two-lowpoint insertion on the Word RAM

Part I, Section 1 of the planarity note inserts a depth into the least two
values. The program uses registers 47 and 48 for the pair and register 49
for the inserted depth. The first branch saves the old least value before
replacing it. All branches have a constant execution bound.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- The `INSERT` control flow of Part I, Section 1. -/
def insertLowProg : Cmd :=
  .ite (.op .lt (.reg 49) (.reg 47))
    (.seq (.assign 48 (.reg 47)) (.assign 47 (.reg 49)))
    (.ite (.op .lt (.reg 47) (.reg 49))
      (.ite (.op .lt (.reg 49) (.reg 48)) (.assign 48 (.reg 49)) .skip)
      .skip)

/-- The state updates made by `INSERT`. -/
def insertLowState (s : State) : State :=
  if s.regs 49 < s.regs 47 then (s.setReg 48 (s.regs 47)).setReg 47 (s.regs 49)
  else if s.regs 47 < s.regs 49 ∧ s.regs 49 < s.regs 48 then
    s.setReg 48 (s.regs 49)
  else s

private theorem eval_lt_regs (s : State) (w a b : ℕ)
    (ha : s.regs a < 2 ^ w) (hb : s.regs b < 2 ^ w) (hw : 1 < 2 ^ w) :
    (Expr.op .lt (.reg a) (.reg b)).eval w s =
      some (if s.regs a < s.regs b then 1 else 0) := by
  simp only [Expr.eval, checkWord_of_lt ha, checkWord_of_lt hb, BinOp.eval, BinOp.raw]
  split <;> apply checkWord_of_lt <;> omega

/-- `INSERT` terminates in at most eleven steps when its three inputs and
Boolean comparison results fit in a word. No ordering assumption on the
input pair is needed. -/
theorem insertLowProg_exec (w : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hlo : s.regs 47 < 2 ^ w)
    (hhi : s.regs 48 < 2 ^ w) (hk : s.regs 49 < 2 ^ w) :
    ∃ t, Exec w insertLowProg s (insertLowState s) t ∧ t ≤ 11 := by
  have hkl := eval_lt_regs s w 49 47 hk hlo hw
  have hlk := eval_lt_regs s w 47 49 hlo hk hw
  have hkh := eval_lt_regs s w 49 48 hk hhi hw
  by_cases h₁ : s.regs 49 < s.regs 47
  · simp only [h₁, ↓reduceIte] at hkl
    refine ⟨7, ?_, by omega⟩
    simp only [insertLowProg, insertLowState, h₁, ↓reduceIte]
    apply Exec.ite_true (t := 4) hkl (by decide)
    apply Exec.seq (t₁ := 2) (t₂ := 2)
    · exact Exec.assign (e := .reg 47) (checkWord_of_lt hlo)
    · apply Exec.assign (e := .reg 49)
      simpa [Expr.eval, State.setReg] using checkWord_of_lt hk
  · simp only [h₁, ↓reduceIte] at hkl
    by_cases h₂ : s.regs 47 < s.regs 49
    · simp only [h₂, ↓reduceIte] at hlk
      by_cases h₃ : s.regs 49 < s.regs 48
      · simp only [h₃, ↓reduceIte] at hkh
        refine ⟨11, ?_, by omega⟩
        simp only [insertLowProg, insertLowState, h₁, h₂, h₃, ↓reduceIte, and_self]
        exact Exec.ite_false hkl (Exec.ite_true hlk (by decide)
          (Exec.ite_true hkh (by decide) (Exec.assign (e := .reg 49) (checkWord_of_lt hk))))
      · simp only [h₃, ↓reduceIte] at hkh
        refine ⟨10, ?_, by omega⟩
        simp only [insertLowProg, insertLowState, h₁, h₂, h₃, ↓reduceIte, and_false]
        exact Exec.ite_false hkl (Exec.ite_true hlk (by decide)
          (Exec.ite_false hkh (Exec.skip s)))
    · simp only [h₂, ↓reduceIte] at hlk
      refine ⟨7, ?_, by omega⟩
      simp only [insertLowProg, insertLowState, h₁, h₂, ↓reduceIte, false_and]
      exact Exec.ite_false hkl (Exec.ite_false hlk (Exec.skip s))

/-- The two output registers are precisely the functional insertion result. -/
theorem insertLowState_pair (s : State) :
    LRPlanarity.LowPair.mk ((insertLowState s).regs 47) ((insertLowState s).regs 48) =
      LRPlanarity.insertLow ⟨s.regs 47, s.regs 48⟩ (s.regs 49) := by
  unfold insertLowState LRPlanarity.insertLow
  split
  · simp_all [State.setReg]
  · split <;> simp_all [State.setReg]

/-- Insertion changes only the two pair registers. -/
theorem insertLowState_regs (s : State) (r : ℕ) (hlo : r ≠ 47) (hhi : r ≠ 48) :
    (insertLowState s).regs r = s.regs r := by
  unfold insertLowState
  split
  · simp_all [State.setReg]
  · split <;> simp_all [State.setReg]

/-- Insertion preserves every array. -/
theorem insertLowState_arrs (s : State) : (insertLowState s).arrs = s.arrs := by
  unfold insertLowState
  split
  · rfl
  · split <;> rfl

end GraphMinor.Compute.PlanarityRam
