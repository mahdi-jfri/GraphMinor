module

public import GraphMinor.Compute.GM02TerminalPrefix
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Initializing the active terminal buffer

Save the terminal vertex offset, allocate one count header plus two
words per supplied pattern edge, and initialize the scan index, used
word position, and active pair count. The initial buffer is precisely
the empty terminal-prefix invariant.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Allocate the terminal buffer and initialize its offset and scan counters. -/
@[expose] def gm02InitTerminalBufferProg : Cmd :=
  .seq (.assign 73 (.op .add (.reg 10) (.reg 11)))
    (.seq (.assign 77 (.op .add (.const 1) (.op .mul (.const 2) (.reg 15))))
      (.seq (.alloc 26 (.reg 77))
        (.seq (.assign 74 (.const 0)) (.seq (.assign 75 (.const 1)) (.assign 76 (.const 0))))))

/-- The terminal buffer initializer executes in linear allocation time with exact metadata and frames. -/
theorem gm02InitTerminalBufferProg_exec {w K : ℕ} (x : GM02TopologicalInput) (hflags : List ℕ)
    (hK : x.edges.length ≤ K) (s : State) (hn : s.regs 10 = x.G.n)
    (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hcap : 1 + 2 * x.edges.length < 2 ^ w) :
    ∃ s', Exec w gm02InitTerminalBufferProg s s' (18 + 2 * x.edges.length) ∧
      s'.arrs 26 = gm02TerminalBuffer x hflags K hK 0 ∧
      s'.regs 73 = x.G.n + x.G.edges.length ∧ s'.regs 74 = 0 ∧
      s'.regs 75 = 1 ∧ s'.regs 76 = 0 ∧
      (∀ a, a ≠ 26 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ∉ [73, 74, 75, 76, 77] → s'.regs r = s.regs r) := by
  let base := x.G.n + x.G.edges.length
  let cap := 1 + 2 * x.edges.length
  have hnw : x.G.n < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hmw : x.G.edges.length < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hbw : base < 2 ^ w := by dsimp only [base]; unfold gm02FullPortSize at hN; omega
  have hfw : x.edges.length < 2 ^ w := by omega
  have h2fw : 2 * x.edges.length < 2 ^ w := by omega
  let s₀ := s.setReg 73 base
  have he₀ : Exec w (.assign 73 (.op .add (.reg 10) (.reg 11))) s s₀ 4 :=
    .assign (eval_add (eval_reg hn hnw) (eval_reg hm hmw) hbw)
  let s₁ := s₀.setReg 77 cap
  have he₁ : Exec w (.assign 77 (.op .add (.const 1) (.op .mul (.const 2) (.reg 15)))) s₀ s₁ 6 :=
    .assign (eval_add (eval_const (by omega))
      (eval_mul (eval_const hw) (eval_reg ((State.setReg_regs_ne s base (by decide : (15 : Reg) ≠ 73)).trans hf) hfw) h2fw) hcap)
  let s₂ := s₁.setArr 26 (List.replicate cap 0)
  have he₂ : Exec w (.alloc 26 (.reg 77)) s₁ s₂ (1 + cap) :=
    .alloc (eval_reg (State.setReg_regs_self ..) hcap)
  let s₃ := s₂.setReg 74 0
  let s₄ := s₃.setReg 75 1
  let s₅ := s₄.setReg 76 0
  have he₃ : Exec w (.assign 74 (.const 0)) s₂ s₃ 2 := .assign (eval_const (by omega))
  have he₄ : Exec w (.assign 75 (.const 1)) s₃ s₄ 2 := .assign (eval_const (by omega))
  have he₅ : Exec w (.assign 76 (.const 0)) s₄ s₅ 2 := .assign (eval_const (by omega))
  have hex := Exec.seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))))
  refine ⟨s₅, ?_, ?_, ?_, ?_, ?_, State.setReg_regs_self .., ?_, ?_⟩
  · convert hex using 1 <;> first | rfl | (dsimp only [cap]; omega)
  · change List.replicate cap 0 = _
    simp only [gm02TerminalBuffer, gm02TerminalWords, gm02TerminalPrefix_zero,
      List.length_nil, Nat.sub_zero, flatEdges, List.flatMap_nil, List.append_nil]
    rw [show cap = 2 * x.edges.length + 1 by dsimp only [cap]; omega, List.replicate_succ]
    rfl
  · simp [s₅, s₄, s₃, s₂, s₁, s₀, base]
  · simp [s₅, s₄, s₃]
  · simp [s₅, s₄]
  · intro a ha26
    exact State.setArr_arrs_ne s₁ _ ha26
  · intro r hrnot
    have hne (a : ℕ) (ha : a ∈ [73, 74, 75, 76, 77]) : r ≠ a := fun h => hrnot (h.symm ▸ ha)
    simp only [s₅, s₄, s₃, s₂, s₁, s₀, State.setReg_regs_ne _ _ (hne 76 (by decide)),
      State.setReg_regs_ne _ _ (hne 75 (by decide)), State.setReg_regs_ne _ _ (hne 74 (by decide)),
      State.setArr_regs, State.setReg_regs_ne _ _ (hne 77 (by decide)), State.setReg_regs_ne _ _ (hne 73 (by decide))]

end GraphMinor.Compute
