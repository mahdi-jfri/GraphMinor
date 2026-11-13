module

public import GraphMinor.Compute.GM02EliminateBranchLoops
public import GraphMinor.Compute.GM02InitPortCodeScan
public import GraphMinor.Compute.GM02PortCodeScan

/-!
# Complete execution of the topological containment decision program

Perform the paper's branch-loop eliminations, initialize the fixed code
range, and run the complete proved numeric split scan. Copy its answer
to the ordinary output register. The preprocessing equivalence transfers
the active containment answer back to the original graph pair. Only
numerical word bounds remain to be supplied from the original input size.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 GraphMinor.Compute.Crossing Classical

/-- The complete plain-input program for II (4.6). -/
@[expose] noncomputable def gm02TopologicalDecisionProg (K q : ℕ) : Cmd :=
  .seq gm02EliminateBranchLoopsProg
    (.seq (gm02InitPortCodeScanProg K)
      (.seq (gm02PortCodeScanProg K q) (.assign outReg (.reg 192))))

/-- The explicit root execution budget before bounding it by a fixed polynomial. -/
@[expose] noncomputable def gm02TopologicalBudget (q : ℕ) (x : GM02TopologicalInput) (K : ℕ) : ℕ :=
  120 * (gm02TopologicalSize x + 1) ^ 2 + 13 + 8 * K +
    (x.G.edges.length + 1) ^ (2 * K) * (gm02PortCodeBudget q x K + 15)

/-- The complete program returns the three printed alternatives from plain input and numerical word bounds. -/
theorem gm02TopologicalDecisionProg_exec {W K : ℕ} (x : GM02TopologicalInput) (s : State)
    (hK : x.edges.length ≤ K) (w : ℤ) (q : ℕ) (hq : max w.toNat 2 + 2 * K < q)
    (hsrc : s.arrs inArr = x.enc) (hw : 3 < 2 ^ W)
    (hsize : gm02TopologicalSize x < 2 ^ W) (henc : x.enc.length < 2 ^ W)
    (hN : gm02FullPortSize x K < 2 ^ W) (hmw : x.G.edges.length + 1 < 2 ^ W)
    (hpow : (x.G.edges.length + 1) ^ (2 * K) < 2 ^ W)
    (hjoin : 3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ W)
    (hword : wordSize (gm02RecursiveWordConstant q) (gm02FullPortSize x K) ≤ W) :
    ∃ s' t, Exec W (gm02TopologicalDecisionProg K q) s s' t ∧
      t ≤ gm02TopologicalBudget q x K ∧ x.correct w s' := by
  obtain ⟨s₀, t₀, he₀, ht₀, hsrc₀, hmask₀, h10, h11, _, _, _, h15, h16, hG₀,
      hHlen₀, hHbits₀, hTopo₀, hNoLoop₀, _⟩ :=
    gm02EliminateBranchLoopsProg_exec x s hsrc (by omega) hsize henc
  have hGlen : (s₀.arrs 20).length = x.G.edges.length := by
    rw [hG₀]
    exact gm02HostLoopFlags_length x _
  have hGbits : ∀ b ∈ s₀.arrs 20, b ≤ 1 := by
    rw [hG₀]
    exact gm02HostLoopFlags_bits x _
  let : Fintype E(gm02ActiveGraph x.H (s₀.arrs 21)) :=
    (gm02ActivePattern_finite_edges x (s₀.arrs 21)).fintype
  let edge : Fin (Fintype.card E(gm02ActiveGraph x.H (s₀.arrs 21))) ≃ E(gm02ActiveGraph x.H (s₀.arrs 21)) :=
    (Fintype.equivFin _).symm
  obtain ⟨s₁, he₁, hzero₁, hlimit₁, hacc₁, ha₁, hr₁⟩ :=
    gm02InitPortCodeScanProg_exec s₀ h11 (by omega) hmw hpow
  obtain ⟨s₂, t₂, he₂, ht₂, hcorrect⟩ := gm02PortCodeScanProg_exec x s₁ (s₀.arrs 20) (s₀.arrs 21) hK edge w q hq
    hNoLoop₀ ((congrFun ha₁ inArr).trans hsrc₀) (congrFun ha₁ 20) hGlen hGbits
    (congrFun ha₁ 21) hHlen₀ hHbits₀ ((congrFun ha₁ 22).trans hmask₀)
    ((hr₁ 10 (by decide)).trans h10) ((hr₁ 11 (by decide)).trans h11)
    ((hr₁ 15 (by decide)).trans h15) ((hr₁ 16 (by decide)).trans h16)
    hzero₁ hlimit₁ hacc₁ hw hN henc hmw hpow hjoin hword
  have hflag : s₂.regs 192 ≤ 2 := by
    rcases hcorrect with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
  let s₃ := s₂.setReg outReg (s₂.regs 192)
  have he₃ : Exec W (.assign outReg (.reg 192)) s₂ s₃ 2 := .assign (eval_reg rfl (by omega))
  refine ⟨s₃, t₀ + ((8 + 8 * K) + (t₂ + 2)), .seq he₀ (.seq he₁ (.seq he₂ he₃)), ?_, ?_⟩
  · dsimp only [gm02TopologicalBudget]
    omega
  · have hret : s₃.regs outReg = s₂.regs 192 := State.setReg_regs_self ..
    rcases hcorrect with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
    · exact Or.inl ⟨hret.trans hf, hTopo₀.2 hp⟩
    · exact Or.inr (Or.inl ⟨hret.trans hf, fun h => hp (hTopo₀.1 h)⟩)
    · exact Or.inr (Or.inr ⟨hret.trans hf, hp⟩)

end GraphMinor.Compute
