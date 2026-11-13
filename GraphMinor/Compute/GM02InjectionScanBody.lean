module

public import GraphMinor.Compute.GM02TestInjectionCode
public import GraphMinor.Compute.GM02AccumulateCodeFlag
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Retaining the next injection test's answer

While the outer accumulator is zero, test the next candidate and retain
a positive containment or width report. Once an answer is retained,
leave the state unchanged. The empty case records exact coded exclusion
when the candidate returns zero.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Test the next injection only while the accumulator has no positive answer. -/
@[expose] noncomputable def gm02InjectionScanBody (H : GM02EdgeListInput) (q : ℕ) : Cmd :=
  .ite (.op .eq (.reg 192) (.const 0))
    (.seq (gm02TestInjectionCodeProg H q) gm02AccumulateCodeFlagProg) .skip

/-- The empty-accumulator branch tests and retains precisely one candidate's answer. -/
theorem gm02InjectionScanBody_empty_exec {W code : ℕ} (q : ℕ) (G H : GM02EdgeListInput)
    (w : ℤ) (s : State) (hq : max w.toNat 2 + 2 * H.edges.length < q)
    (hw : 3 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hmG : G.edges.length < 2 ^ W)
    (hcap : 1 + 2 * H.edges.length < 2 ^ W) (hlen : gm02InjectedInputLength G H < 2 ^ W)
    (hpow : (G.n + 1) ^ H.n < 2 ^ W) (hcode : code < (G.n + 1) ^ H.n)
    (hword : wordSize (gm02TopologicalWordCoefficient q H.edges.length) (G.size + H.size) ≤ W)
    (hG : s.arrs inArr = G.enc) (hrn : s.regs 40 = G.n) (hrcode : s.regs 190 = code)
    (hzero : s.regs 192 = 0) :
    ∃ s' t, Exec W (gm02InjectionScanBody H q) s s' t ∧
      t ≤ gm02InjectionCodeBudget q G H + 8 ∧
      ((s'.regs 192 = 1 ∧ ∃ hv : gm02InjectionCodeValid G.n H.n code,
        TopologicallyContains G.graph (gm02InjectedPattern G H (gm02InjectionOfCode G.n H.n code hv)).H) ∨
        (s'.regs 192 = 0 ∧ ∀ hv : gm02InjectionCodeValid G.n H.n code,
          ¬TopologicallyContains G.graph (gm02InjectedPattern G H (gm02InjectionOfCode G.n H.n code hv)).H) ∨
        (s'.regs 192 = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))) ∧
      (∀ a, a < 1000 → a ≠ 29 → a ≠ 30 → a ≠ 31 → a ≠ 32 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 193 → (r < 83 ∨ 89 < r) → r ≠ 192 → s'.regs r = s.regs r) := by
  obtain ⟨s₀, t₀, he₀, ht₀, hc, ha₀, hr₀⟩ := gm02TestInjectionCodeProg_exec q G H w s
    hq hw hn hmG hcap hlen hpow hcode hword hG hrn hrcode
  have hflag : s₀.regs 89 ≤ 2 := by
    rcases hc with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
  have hzero₀ : s₀.regs 192 = 0 := (hr₀ 192 (by decide) (Or.inr (by decide))).trans hzero
  obtain ⟨s₁, t₁, he₁, ht₁, hret, ha₁, hr₁⟩ := gm02AccumulateCodeFlagProg_exec s₀ rfl hflag hzero₀ hw
  have hg : (Expr.op .eq (.reg 192) (.const 0)).eval W s = some 1 :=
    eval_eq (eval_reg hzero (by omega)) (eval_const (by omega)) (by omega)
  refine ⟨s₁, 3 + (t₀ + t₁), .ite_true hg (by decide) (.seq he₀ he₁), by omega, ?_, ?_, ?_⟩
  · rcases hc with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
    · exact Or.inl ⟨hret.trans hf, hp⟩
    · exact Or.inr (Or.inl ⟨hret.trans hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hret.trans hf, hp⟩)
  · intro a ha h29 h30 h31 h32 h33
    exact (congrFun ha₁ a).trans (ha₀ a ha h29 h30 h31 h32 h33)
  · intro r hr hshape hr192
    exact (hr₁ r hr192).trans (hr₀ r hr hshape)

end GraphMinor.Compute
