module

public import GraphMinor.Compute.GM02InjectedVertexPrefix
public import GraphMinor.Compute.Basic
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Initializing the injected-vertex buffer

Allocate one header word and one word per host vertex. Write the fixed
pattern vertex count, set the scan counter to zero, and point the output
position past the header. The decoded choices remain in their registers.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Allocate and initialize the host-order vertex scan. -/
@[expose] def gm02InitInjectedVerticesProg (p : ℕ) : Cmd :=
  .seq (.alloc 29 (.op .add (.reg 40) (.const 1)))
    (.seq (.write 29 (.const 0) (.const p))
      (.seq (.assign 194 (.const 0)) (.assign 195 (.const 1))))

/-- Initialization supplies the exact empty vertex prefix without changing the decoded choices. -/
theorem gm02InitInjectedVerticesProg_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State) (hrn : s.regs 40 = G.n)
    (hw : 1 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hp : H.n < 2 ^ W) :
    ∃ s', Exec W (gm02InitInjectedVerticesProg H.n) s s' (G.n + 11) ∧
      s'.arrs 29 = gm02InjectedVertexBuffer G H f 0 ∧
      s'.regs 194 = 0 ∧ s'.regs 195 = 1 ∧
      (∀ a, a ≠ 29 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 194 → r ≠ 195 → s'.regs r = s.regs r) := by
  let s₀ := s.setArr 29 (List.replicate (G.n + 1) 0)
  have he₀ : Exec W (.alloc 29 (.op .add (.reg 40) (.const 1))) s s₀ (G.n + 4) := by
    convert Exec.alloc (a := 29) (eval_add (eval_reg hrn (by omega)) (eval_const hw) hn) using 1 <;> first | rfl | (simp only [Expr.cost]; omega)
  let s₁ := s₀.writeArr 29 0 H.n
  have he₁ : Exec W (.write 29 (.const 0) (.const H.n)) s₀ s₁ 3 :=
    .write (eval_const (by omega)) (eval_const hp) (by simp [s₀])
  let s₂ := s₁.setReg 194 0
  let s₃ := s₂.setReg 195 1
  have he₂ : Exec W (.assign 194 (.const 0)) s₁ s₂ 2 := .assign (eval_const (by omega))
  have he₃ : Exec W (.assign 195 (.const 1)) s₂ s₃ 2 := .assign (eval_const hw)
  refine ⟨s₃, ?_, ?_, ?_, State.setReg_regs_self .., ?_, ?_⟩
  · convert Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃)) using 1 <;> first | rfl | (simp only [Expr.cost]; omega)
  · simp [s₃, s₂, s₁, s₀, gm02InjectedVertexBuffer, gm02InjectedVertexWords,
      gm02InjectedVertexPrefix, List.replicate_succ]
  · exact State.setReg_regs_ne s₂ 1 (by decide) |>.trans (State.setReg_regs_self ..)
  · intro a ha
    exact (State.writeArr_arrs_ne s₀ 0 H.n ha).trans (State.setArr_arrs_ne s _ ha)
  · intro r hr194 hr195
    exact (State.setReg_regs_ne s₂ 1 hr195).trans (State.setReg_regs_ne s₁ 0 hr194)

end GraphMinor.Compute
