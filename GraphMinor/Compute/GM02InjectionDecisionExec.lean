module

public import GraphMinor.Compute.GM02InitInjectionScan
public import GraphMinor.Compute.GM02InjectionScan
public import GraphMinor.Compute.GM02IsomorphicTopologicalInput
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Complete plain-host execution for II (4.7)

Initialize the injection range from the input graph, run the complete
candidate scan, and copy its retained answer to the standard output.
The only input words are the original host count and edge list.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- The complete injection-search program reading just the host graph encoding. -/
@[expose] noncomputable def gm02InjectionDecisionProg (H : GM02EdgeListInput) (q : ℕ) : Cmd :=
  .seq (gm02InitInjectionScanProg H.n)
    (.seq (gm02InjectionScanProg H q) (.assign outReg (.reg 192)))

/-- The complete execution budget before bounding it by a fixed polynomial. -/
@[expose] noncomputable def gm02InjectionBudget (q : ℕ) (G H : GM02EdgeListInput) : ℕ :=
  14 + 4 * H.n + (G.n + 1) ^ H.n * (gm02InjectionCodeBudget q G H + 15)

/-- The full plain-host program decides the three printed alternatives from numerical word bounds. -/
theorem gm02InjectionDecisionProg_exec {W : ℕ} (q : ℕ) (G H : GM02EdgeListInput)
    (w : ℤ) (s : State) (hq : max w.toNat 2 + 2 * H.edges.length < q)
    (hw : 3 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hmG : G.edges.length < 2 ^ W)
    (hcap : 1 + 2 * H.edges.length < 2 ^ W) (hlen : gm02InjectedInputLength G H < 2 ^ W)
    (hpow : (G.n + 1) ^ H.n < 2 ^ W)
    (hword : wordSize (gm02TopologicalWordCoefficient q H.edges.length) (G.size + H.size) ≤ W)
    (hsrc : s.arrs inArr = G.enc) :
    ∃ s' t, Exec W (gm02InjectionDecisionProg H q) s s' t ∧
      t ≤ gm02InjectionBudget q G H ∧ gm02IsomorphicTopologicalCorrect H.graph w G s' := by
  obtain ⟨s₀, he₀, hz₀, hl₀, ha₀, hn₀, harr₀⟩ :=
    gm02InitInjectionScanProg_exec G H.n s hsrc (by omega) hn hpow
  obtain ⟨s₁, t₁, he₁, ht₁, hc⟩ := gm02InjectionScanProg_exec q G H w s₀ hq hw hn hmG hcap hlen
    hpow hword ((congrFun harr₀ inArr).trans hsrc) hn₀ hz₀ hl₀ ha₀
  have hflag : s₁.regs 192 ≤ 2 := by
    rcases hc with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
  let s₂ := s₁.setReg outReg (s₁.regs 192)
  have he₂ : Exec W (.assign outReg (.reg 192)) s₁ s₂ 2 := .assign (eval_reg rfl (by omega))
  refine ⟨s₂, (9 + 4 * H.n) + (t₁ + 2), .seq he₀ (.seq he₁ he₂), ?_, ?_⟩
  · unfold gm02InjectionBudget
    omega
  · have hret : s₂.regs outReg = s₁.regs 192 := State.setReg_regs_self ..
    rcases hc with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
    · exact Or.inl ⟨hret.trans hf, hp⟩
    · exact Or.inr (Or.inl ⟨hret.trans hf, hp⟩)
    · exact Or.inr (Or.inr ⟨hret.trans hf, hp⟩)

end GraphMinor.Compute
