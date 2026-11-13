module

public import GraphMinor.Compute.GM02TestPortCode
public import GraphMinor.Compute.GM02AccumulateCodeFlag
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Testing the next code while the accumulator is empty

If no answer has yet been retained, execute the complete raw-code test
and accumulate its flag. Otherwise leave the state unchanged. The empty
case below proves the actual three-way answer in the accumulator and
retains the outer code and limit registers for the counted scan.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Test and accumulate one code only while no positive answer has been retained. -/
@[expose] noncomputable def gm02PortCodeScanBody (K q : ℕ) : Cmd :=
  .ite (.op .eq (.reg 192) (.const 0))
    (.seq (gm02TestPortCodeProg K q) gm02AccumulateCodeFlagProg) .skip

/-- The empty-accumulator branch executes the full candidate test and retains its exact answer. -/
theorem gm02PortCodeScanBody_empty_exec {W K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (w : ℤ) (q : ℕ)
    (hq : max w.toNat 2 + 2 * K < q)
    (hsrc : s.arrs inArr = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card) (hcode : s.regs 190 = code)
    (hw : 3 < 2 ^ W) (hN : gm02FullPortSize x K < 2 ^ W) (henc : x.enc.length < 2 ^ W)
    (hmw : x.G.edges.length + 1 < 2 ^ W) (hcw : code < 2 ^ W)
    (hpow : (x.G.edges.length + 1) ^ (2 * K) < 2 ^ W)
    (hjoin : 3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ W)
    (hword : wordSize (gm02RecursiveWordConstant q) (gm02FullPortSize x K) ≤ W)
    (hzero : s.regs 192 = 0) :
    ∃ s' t, Exec W (gm02PortCodeScanBody K q) s s' t ∧ t ≤ gm02PortCodeBudget q x K + 8 ∧
      ((s'.regs 192 = 1 ∧ ∃ hv : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code),
          (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).A.Feasible
            (Graph.ofSimpleGraph (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).G)) ∨
       (s'.regs 192 = 0 ∧ ∀ hv : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code),
          ¬(gm02NumericTerminatedInput x gflags hflags code K hK edge hv).A.Feasible
            (Graph.ofSimpleGraph (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).G)) ∨
       (s'.regs 192 = 2 ∧ w < treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges)) ∧
      (∀ a, a < 1000 → a ≠ 23 → a ≠ 24 → a ≠ 25 → a ≠ 26 → a ≠ 27 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r, (r < 32 ∨ 89 < r) → r < 200 → r ≠ 192 → s'.regs r = s.regs r) := by
  obtain ⟨s₀, t₀, he₀, ht₀, hcorrect, ha₀, hr₀⟩ :=
    gm02TestPortCodeProg_exec x s gflags hflags hK edge w q hq hsrc hG hGlen hGbits hH hHlen hHbits hmask
      hn hm hf hoff hcode hw hN henc hmw hcw hpow hjoin hword
  have hflag : s₀.regs 89 ≤ 2 := by
    rcases hcorrect with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
  have hzero₀ : s₀.regs 192 = 0 := (hr₀ 192 (Or.inr (by decide)) (by decide)).trans hzero
  obtain ⟨s₁, t₁, he₁, ht₁, hret, ha₁, hr₁⟩ :=
    gm02AccumulateCodeFlagProg_exec s₀ rfl hflag hzero₀ hw
  have hg : (Expr.op .eq (.reg 192) (.const 0)).eval W s = some 1 :=
    eval_eq (eval_reg hzero (by omega)) (eval_const (by omega)) (by omega)
  refine ⟨s₁, 3 + (t₀ + t₁), .ite_true hg (by decide) (.seq he₀ he₁), ?_, ?_, ?_, ?_⟩
  · calc
      3 + (t₀ + t₁) ≤ 3 + (gm02PortCodeBudget q x K + 5) :=
        Nat.add_le_add_left (Nat.add_le_add ht₀ ht₁) 3
      _ = gm02PortCodeBudget q x K + 8 := by omega
  · rcases hcorrect with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
    · exact Or.inl ⟨hret.trans hf, hp⟩
    · exact Or.inr (Or.inl ⟨hret.trans hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hret.trans hf, hp⟩)
  · intro a ha1000 h23 h24 h25 h26 h27 h28
    exact (congrFun ha₁ a).trans (ha₀ a ha1000 h23 h24 h25 h26 h27 h28)
  · intro r hrange hr200 hr192
    exact (hr₁ r hr192).trans (hr₀ r hrange hr200)

end GraphMinor.Compute
