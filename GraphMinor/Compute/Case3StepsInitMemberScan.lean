module

public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Initializing the member scan

Count the full directed edges and allocate a single buffer for the member
records. The allocation is linear in the ambient vertex count and compact
edge count. Initialize the wall flag, used length, record count, and scan
index while retaining all routing tables.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Allocate the record buffer and initialize the member scan counters. -/
def case3InitMemberScanProg : Cmd :=
  .seq (sumEdgeMultProg 3 108)
    (.seq (.alloc 57 (.op .mul (.const 24)
      (.op .add (.op .add (.len 2) (.reg 110)) (.const 1))))
      (.seq (.assign 0 (.const 0)) (.seq (.assign 1 (.const 0))
        (.seq (.assign 2 (.const 0)) (.assign 54 (.const 0))))))

/-- The initial record buffer has the capacity from the summed record
bound, and all four counters start at zero. -/
theorem case3InitMemberScanProg_exec {w n N : ℕ} (D : MultiDigraph n)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w)
    (hcapacity : 24 * (N + D.numEdges + 1) < 2 ^ w)
    {s : State} (hD : s.arrs 3 = D.enc) (hrank : (s.arrs 2).length = N) :
    ∃ s' t, Exec w case3InitMemberScanProg s s' t ∧
      t ≤ 22 * D.numActivePairs + 24 * (N + D.numEdges + 1) + 30 ∧
      s'.arrs 57 = List.replicate (24 * (N + D.numEdges + 1)) 0 ∧
      s'.regs 0 = 0 ∧ s'.regs 1 = 0 ∧ s'.regs 2 = 0 ∧ s'.regs 54 = 0 ∧
      (∀ a, a ≠ 57 → s'.arrs a = s.arrs a) ∧
      (∀ r < 108, r ≠ 54 → r ≠ 0 → r ≠ 1 → r ≠ 2 → s'.regs r = s.regs r) := by
  have he : D.numEdges < 2 ^ w := by omega
  have hN : N < 2 ^ w := by omega
  have hsum : N + D.numEdges < 2 ^ w := by omega
  have hsum1 : N + D.numEdges + 1 < 2 ^ w := by omega
  have h24 : 24 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h0 := Nat.two_pow_pos w
  obtain ⟨s₁, t₁, hex₁, ht₁, _, _, he₁, harr₁, hreg₁⟩ :=
    sumEdgeMultProg_exec D 3 108 hw hn hA he hD
  change s₁.regs 110 = D.numEdges at he₁
  let cap := 24 * (N + D.numEdges + 1)
  let s₂ := s₁.setArr 57 (List.replicate cap 0)
  have hex₂ : Exec w (.alloc 57 (.op .mul (.const 24)
      (.op .add (.op .add (.len 2) (.reg 110)) (.const 1)))) s₁ s₂ (7 + cap) :=
    .alloc (by simp only [Expr.eval, checkWord, harr₁ 2, hrank, he₁, hN, he, hsum, hsum1,
      h24, h1, BinOp.eval, BinOp.raw, hcapacity, cap, ↓reduceIte])
  let s₃ := s₂.setReg 0 0
  let s₄ := s₃.setReg 1 0
  let s₅ := s₄.setReg 2 0
  let s₆ := s₅.setReg 54 0
  have hex₃ : Exec w (.assign 0 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hex₄ : Exec w (.assign 1 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hex₅ : Exec w (.assign 2 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hex₆ : Exec w (.assign 54 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  refine ⟨s₆, t₁ + ((7 + cap) + (2 + (2 + (2 + 2)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), by dsimp only [cap]; omega,
    rfl, ?_, ?_, ?_, State.setReg_regs_self .., ?_, ?_⟩
  · simp only [s₆, s₅, s₄, s₃, State.setReg_regs_ne _ _ (show (0 : Reg) ≠ 54 by decide),
      State.setReg_regs_ne _ _ (show (0 : Reg) ≠ 2 by decide),
      State.setReg_regs_ne _ _ (show (0 : Reg) ≠ 1 by decide), State.setReg_regs_self]
  · simp only [s₆, s₅, s₄, State.setReg_regs_ne _ _ (show (1 : Reg) ≠ 54 by decide),
      State.setReg_regs_ne _ _ (show (1 : Reg) ≠ 2 by decide), State.setReg_regs_self]
  · simp only [s₆, s₅, State.setReg_regs_ne _ _ (show (2 : Reg) ≠ 54 by decide), State.setReg_regs_self]
  · intro a ha
    exact (State.setArr_arrs_ne s₁ _ ha).trans (harr₁ a)
  · intro r hr h54 h70 h71 h72
    simp only [s₆, s₅, s₄, s₃, s₂, State.setReg_regs_ne _ _ h54,
      State.setReg_regs_ne _ _ h72, State.setReg_regs_ne _ _ h71,
      State.setReg_regs_ne _ _ h70, State.setArr_regs, hreg₁ r hr]

end GraphMinor.Compute
