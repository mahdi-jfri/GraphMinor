module

public import GraphMinor.Compute.GM02TopologicalDecisionExec
public import GraphMinor.Compute.GM02TopologicalWordBounds
public import GraphMinor.Compute.Algorithm33Multigraph
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Calling II (4.6) while retaining the outer injection search

Run the complete labelled-containment program in shifted working
memory. The caller's host array, candidate code, and decoded pattern
vertices remain available. Copy only the three-way result back into
register 89. The original execution budget and correctness are retained.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Call the complete labelled program above the caller's arrays and decoded vertex slots. -/
@[expose] noncomputable def gm02ShiftedTopologicalCallProg (K q p : ℕ) : Cmd :=
  .seq ((gm02TopologicalDecisionProg K q).shift 1000 (1000 + p))
    (.assign 89 (.reg (outReg + (1000 + p))))

/-- The shifted labelled test preserves caller memory and returns its exact three alternatives. -/
theorem gm02ShiftedTopologicalCallProg_exec {W K : ℕ} (q p : ℕ)
    (x : GM02TopologicalInput) (w : ℤ) (s : State) (hK : x.edges.length ≤ K)
    (hq : max w.toNat 2 + 2 * K < q)
    (hsrc : s.arrs (inArr + 1000) = x.enc) (hw : 3 < 2 ^ W)
    (hword : wordSize (gm02TopologicalWordCoefficient q K) (gm02TopologicalSize x) ≤ W) :
    ∃ s' t, Exec W (gm02ShiftedTopologicalCallProg K q p) s s' t ∧
      t ≤ gm02TopologicalBudget q x K + 2 ∧
      ((s'.regs 89 = 1 ∧ TopologicallyContains x.G.graph x.H) ∨
        (s'.regs 89 = 0 ∧ ¬TopologicallyContains x.G.graph x.H) ∨
        (s'.regs 89 = 2 ∧ w < (treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges : ℕ))) ∧
      (∀ a, a < 1000 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 1000 + p → r ≠ 89 → s'.regs r = s.regs r) := by
  obtain ⟨hw₀, hs₀, he₀, hN₀, hm₀, hp₀, hj₀, hr₀⟩ := gm02Topological_wordBounds q K x
  obtain ⟨sub, t, he, ht, hc⟩ := gm02TopologicalDecisionProg_exec x
    (s.unshift 1000 (1000 + p)) hK w q hq hsrc hw₀ hs₀ he₀ hN₀ hm₀ hp₀ hj₀ hr₀
  have heW := Exec.mono_wordSize hword he
  let s₀ := s.applyShifted 1000 (1000 + p) sub
  have heshift : Exec W ((gm02TopologicalDecisionProg K q).shift 1000 (1000 + p)) s s₀ t :=
    Exec.shift_from 1000 (1000 + p) heW
  have hflag : sub.regs outReg ≤ 2 := by
    rcases hc with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
  let s₁ := s₀.setReg 89 (sub.regs outReg)
  have hreg : s₀.regs (outReg + (1000 + p)) = sub.regs outReg := State.applyShifted_regs_add ..
  have heret : Exec W (.assign 89 (.reg (outReg + (1000 + p)))) s₀ s₁ 2 :=
    .assign (eval_reg hreg (hflag.trans_lt (by omega)))
  refine ⟨s₁, t + 2, .seq heshift heret, Nat.add_le_add_right ht 2, ?_, ?_, ?_⟩
  · have hret : s₁.regs 89 = sub.regs outReg := State.setReg_regs_self ..
    rcases hc with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
    · exact Or.inl ⟨hret.trans hf, hp⟩
    · exact Or.inr (Or.inl ⟨hret.trans hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hret.trans hf, hp⟩)
  · intro a ha
    exact State.applyShifted_arrs_lt 1000 (1000 + p) s sub ha
  · intro r hr hr89
    exact (State.setReg_regs_ne s₀ (sub.regs outReg) hr89).trans
      (State.applyShifted_regs_lt 1000 (1000 + p) s sub hr)

end GraphMinor.Compute
