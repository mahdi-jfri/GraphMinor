module

public import GraphMinor.Compute.GM02DecodeAndValidate
public import GraphMinor.Compute.GM02TestValidPortCode
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Testing an arbitrary candidate code

Decode and validate the candidate from the original graph input. Reject
invalid choices directly. For a valid choice, construct and execute the
actual split path test. A zero flag says no proof of validity can give a
feasible numeric instance, while flags one and two carry feasibility or
the justified original-host width report.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 GraphMinor.Compute.Crossing Classical

/-- Validate the code in register 190 and execute its split test only when valid. -/
@[expose] noncomputable def gm02TestPortCodeProg (K q : ℕ) : Cmd :=
  .seq (gm02DecodeAndValidateProg inArr K)
    (.ite (.reg 51) (gm02TestValidPortCodeProg inArr K q) (.assign 89 (.const 0)))

/-- A uniform construction-and-test budget for every raw candidate code. -/
@[expose] noncomputable def gm02PortCodeBudget (q : ℕ) (x : GM02TopologicalInput) (K : ℕ) : ℕ :=
  13 + (2 * K) * (12 + 4 * (2 * K)) + 139 * x.edges.length + gm02PortCandidateBudget q x K

private theorem decode_frame {r : ℕ} (h : r < 32 ∨ 89 < r) :
    r ≠ 32 ∧ r ≠ 40 ∧ (r < 42 ∨ 51 < r) ∧ r ≠ 89 := by omega

private theorem combine_code_time (a b td tv : ℕ) (hd : td ≤ a) (hv : tv ≤ b) :
    td + (1 + tv) ≤ a + 1 + b := by omega

private theorem candidate_budget_ge_two (q : ℕ) (x : GM02TopologicalInput) (K : ℕ) :
    2 ≤ gm02PortCandidateBudget q x K := by
  unfold gm02PortCandidateBudget
  omega

/-- Every candidate is tested by the actual decoder, validator, constructor, and path program. -/
theorem gm02TestPortCodeProg_exec {W K code : ℕ} (x : GM02TopologicalInput) (s : State)
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
    (hword : wordSize (gm02RecursiveWordConstant q) (gm02FullPortSize x K) ≤ W) :
    ∃ s' t, Exec W (gm02TestPortCodeProg K q) s s' t ∧ t ≤ gm02PortCodeBudget q x K ∧
      ((s'.regs 89 = 1 ∧ ∃ hv : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code),
          (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).A.Feasible
            (Graph.ofSimpleGraph (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).G)) ∨
       (s'.regs 89 = 0 ∧ ∀ hv : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code),
          ¬(gm02NumericTerminatedInput x gflags hflags code K hK edge hv).A.Feasible
            (Graph.ofSimpleGraph (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).G)) ∨
       (s'.regs 89 = 2 ∧ w < treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges)) ∧
      (∀ a, a < 1000 → a ≠ 23 → a ≠ 24 → a ≠ 25 → a ≠ 26 → a ≠ 27 → a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ r, (r < 32 ∨ 89 < r) → r < 200 → s'.regs r = s.regs r) := by
  have hnw : x.G.n < 2 ^ W := by unfold gm02FullPortSize at hN; omega
  have hKw : 2 * K < 2 ^ W := by unfold gm02FullPortSize at hN; omega
  obtain ⟨s₀, td, hed, htd, hvalidbit, hdigits, had, hrd⟩ :=
    gm02DecodeAndValidateProg_exec x s inArr gflags hflags (by decide) hK hsrc hG hGlen hGbits hH hHlen hHbits
      hoff hm hf hcode (by omega) hnw hKw hmw hcw hpow henc
  have hlow (r : ℕ) (hr : r < 32) : s₀.regs r = s.regs r :=
    hrd r (Nat.ne_of_lt hr) (Nat.ne_of_lt (hr.trans (by decide))) (Or.inl (hr.trans (by decide)))
      (Or.inl (hr.trans (by decide)))
  by_cases hv : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code)
  · have hg : (Expr.reg 51).eval W s₀ = some 1 :=
      eval_reg (by simpa only [hv, ite_true] using hvalidbit) (by omega)
    obtain ⟨s₁, tv, hev, htv, hcorrect, hav, hrv⟩ :=
      gm02TestValidPortCodeProg_exec x s₀ inArr gflags hflags (by decide) hK edge hv w q hq
        ((had inArr (by decide)).trans hsrc) ((had 20 (by decide)).trans hG) hGlen hGbits
        ((had 21 (by decide)).trans hH) hHlen hHbits ((had 22 (by decide)).trans hmask) hdigits
        ((hlow 10 (by decide)).trans hn) ((hlow 11 (by decide)).trans hm) ((hlow 15 (by decide)).trans hf)
        hw hN henc hjoin hword
    refine ⟨s₁, td + (1 + tv), .seq hed (.ite_true hg (by decide) hev), ?_, ?_, ?_, ?_⟩
    · have ht := combine_code_time _ _ _ _ htd htv
      simpa only [gm02PortCodeBudget] using (show td + (1 + tv) ≤
        13 + 2 * K * (12 + 4 * (2 * K)) + 139 * x.edges.length + gm02PortCandidateBudget q x K by omega)
    · rcases hcorrect with ⟨hf, hp⟩ | ⟨hf, hp⟩ | h
      · exact Or.inl ⟨hf, hv, hp⟩
      · exact Or.inr (Or.inl ⟨hf, fun _ => hp⟩)
      · exact Or.inr (Or.inr h)
    · intro a ha1000 h23 h24 h25 h26 h27 h28
      exact (hav a ha1000 h24 h25 h26 h27 h28).trans (had a h23)
    · intro r hrange hr200
      obtain ⟨h32, h40, hfilter, _⟩ := decode_frame hrange
      exact (hrv r hrange (hr200.trans_le (by decide : 200 ≤ 290))).trans
        (hrd r h32 h40 hfilter (Or.inl hr200))
  · have hg : (Expr.reg 51).eval W s₀ = some 0 :=
      eval_reg (by simpa only [hv, ite_false] using hvalidbit) (by omega)
    let s₁ := s₀.setReg 89 0
    have he₁ : Exec W (.assign 89 (.const 0)) s₀ s₁ 2 := .assign (eval_const (by omega))
    refine ⟨s₁, td + 3, .seq hed (.ite_false hg he₁), ?_, ?_, ?_, ?_⟩
    · have hbudget := candidate_budget_ge_two q x K
      dsimp only [gm02PortCodeBudget]
      omega
    · exact Or.inr (Or.inl ⟨State.setReg_regs_self .., fun hv' => False.elim (hv hv')⟩)
    · intro a _ h23 _ _ _ _ _
      exact had a h23
    · intro r hrange hr200
      obtain ⟨h32, h40, hfilter, h89⟩ := decode_frame hrange
      exact (State.setReg_regs_ne s₀ 0 h89).trans (hrd r h32 h40 hfilter (Or.inl hr200))

end GraphMinor.Compute
