module

public import GraphMinor.Compute.GM06CutAdjacencyRows
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Initializing the cut graph's adjacency arrays

The component searches of Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) use one adjacency row per permanent copied vertex slot. This
program allocates two offset tables and a quadratic entries buffer from the runtime vertex count. It
starts the rotation reader past the row-count header and starts the entries buffer at zero.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Allocate CSR storage using the vertex count in register 620. -/
def gm06CutAdjacencyInitProg : Cmd :=
  .seq (.alloc 620 (.reg 620))
    (.seq (.alloc 621 (.reg 620))
      (.seq (.alloc 622 (.op .mul (.reg 620) (.reg 620)))
        (.seq (.assign 655 (.const 0))
          (.seq (.assign 661 (.const 1))
            (.seq (.assign 665 (.reg 620)) (.assign 666 (.const 0)))))))

/-- The initialized offsets, buffer and cursors are exact. All graph
sources and the runtime vertex count survive. -/
theorem gm06CutAdjacencyInitProg_exec {w n : ℕ} (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hfit : n * n < 2 ^ w) (h620 : s.regs 620 = n) :
    ∃ sf t, Exec w gm06CutAdjacencyInitProg s sf t ∧ t = 13 + 2 * n + n * n ∧
      Keeps [655, 661, 665, 666] [620, 621, 622] s sf ∧
      sf.arrs 620 = List.replicate n 0 ∧ sf.arrs 621 = List.replicate n 0 ∧
      GraphMinor.Compute.Crossing.IsBuf 622 655 [] (n * n) sf ∧
      sf.regs 661 = 1 ∧ sf.regs 665 = n ∧ sf.regs 666 = 0 := by
  let s₁ := s.setArr 620 (List.replicate n 0)
  let s₂ := s₁.setArr 621 (List.replicate n 0)
  let s₃ := s₂.setArr 622 (List.replicate (n * n) 0)
  let s₄ := s₃.setReg 655 0
  let s₅ := s₄.setReg 661 1
  let s₆ := s₅.setReg 665 n
  let sf := s₆.setReg 666 0
  have he₁ : Exec w (.alloc 620 (.reg 620)) s s₁ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg h620 hn)
  have he₂ : Exec w (.alloc 621 (.reg 620)) s₁ s₂ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg h620 hn)
  have he₃ : Exec w (.alloc 622 (.op .mul (.reg 620) (.reg 620))) s₂ s₃ (3 + n * n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_reg h620 hn)
      (GraphMinor.Compute.Crossing.eval_reg h620 hn) hfit)
  have he₄ : Exec w (.assign 655 (.const 0)) s₃ s₄ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₅ : Exec w (.assign 661 (.const 1)) s₄ s₅ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const hw)
  have he₆ : Exec w (.assign 665 (.reg 620)) s₅ s₆ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₅, s₄, s₃, s₂, s₁] using h620) hn)
  have he₇ : Exec w (.assign 666 (.const 0)) s₆ sf 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk : Keeps [655, 661, 665, 666] [620, 621, 622] s sf :=
    (((((((Keeps.refl _ _ s).setArr (by simp) _).setArr (by simp) _).setArr (by simp) _).setReg
      (by simp) _).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
  refine ⟨sf, (1 + n) + ((1 + n) + ((3 + n * n) + (2 + (2 + (2 + 2))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇))))), by omega, hk, ?_⟩
  simp [sf, s₆, s₅, s₄, s₃, s₂, s₁, GraphMinor.Compute.Crossing.IsBuf]

end GraphMinor.Compute
