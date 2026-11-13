module

public import GraphMinor.Compute.GM02Algorithm47
public import GraphMinor.Compute.Algorithm33Multigraph
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Calling the complete injection-search program in shifted memory

The finite pattern scan of II (4.9) needs its original host array after
each test. Run the complete proved (4.7) program above that array and
copy only its answer back into register 89. Its polynomial time bound
and three alternatives are retained.
-/

public section
namespace GraphMinor.Compute
open Graph GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- The recursive threshold used by a fixed-pattern injection search. -/
@[expose] def gm02PatternWidthParameter (J : GM02EdgeListInput) (w : ℤ) : ℕ :=
  max w.toNat 2 + 2 * J.edges.length + 1

/-- Call the complete injection-search program and return its flag in register 89. -/
@[expose] noncomputable def gm02ShiftedInjectionCallProg (J : GM02EdgeListInput) (w : ℤ) : Cmd :=
  .seq ((gm02InjectionDecisionProg J (gm02PatternWidthParameter J w)).shift 1000 1000)
    (.assign 89 (.reg (outReg + 1000)))

/-- The shifted call retains exact correctness, polynomial time, and the caller's low arrays. -/
theorem gm02ShiftedInjectionCallProg_exec {W : ℕ} (J : GM02EdgeListInput) (w : ℤ)
    (G : GM02EdgeListInput) (s : State) (hsrc : s.arrs (inArr + 1000) = G.enc)
    (hw : 3 < 2 ^ W)
    (hword : wordSize (gm02InjectionWordCoefficient (gm02PatternWidthParameter J w) J) G.size ≤ W) :
    ∃ s' t, Exec W (gm02ShiftedInjectionCallProg J w) s s' t ∧
      t ≤ gm02InjectionPolynomialCoefficient (gm02PatternWidthParameter J w) J *
        (G.size + 1) ^ gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J + 2 ∧
      ((s'.regs 89 = 1 ∧ ∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L)) ∨
        (s'.regs 89 = 0 ∧ ¬∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L)) ∨
        (s'.regs 89 = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))) ∧
      (∀ a, a < 1000 → s'.arrs a = s.arrs a) := by
  let q := gm02PatternWidthParameter J w
  obtain ⟨hw₀, hn₀, hm₀, hc₀, hl₀, hp₀, hr₀⟩ := gm02Injection_wordBounds q G J
  obtain ⟨sub, t, he, ht, hout⟩ := gm02InjectionDecisionProg_exec q G J w
    (s.unshift 1000 1000) (Nat.lt_succ_self _) hw₀ hn₀ hm₀ hc₀ hl₀ hp₀ hr₀ hsrc
  have heW := Exec.mono_wordSize hword he
  let s₀ := s.applyShifted 1000 1000 sub
  have he₀ : Exec W ((gm02InjectionDecisionProg J q).shift 1000 1000) s s₀ t :=
    Exec.shift_from 1000 1000 heW
  have hflag : sub.regs outReg ≤ 2 := by
    rcases hout with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
  let s₁ := s₀.setReg 89 (sub.regs outReg)
  have hreg : s₀.regs (outReg + 1000) = sub.regs outReg := State.applyShifted_regs_add ..
  have he₁ : Exec W (.assign 89 (.reg (outReg + 1000))) s₀ s₁ 2 :=
    .assign (eval_reg hreg (hflag.trans_lt (by omega)))
  refine ⟨s₁, t + 2, .seq he₀ he₁, Nat.add_le_add_right (ht.trans (gm02InjectionBudget_polynomial q G J)) 2, ?_, ?_⟩
  · have hret : s₁.regs 89 = sub.regs outReg := State.setReg_regs_self ..
    rcases hout with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
    · exact Or.inl ⟨hret.trans hf, hp⟩
    · exact Or.inr (Or.inl ⟨hret.trans hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hret.trans hf, hp⟩)
  · intro a ha
    exact State.applyShifted_arrs_lt 1000 1000 s sub ha

end GraphMinor.Compute
