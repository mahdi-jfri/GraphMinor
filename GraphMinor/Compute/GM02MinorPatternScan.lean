module

public import GraphMinor.Compute.GM02PatternListBounds
public import GraphMinor.Compute.GM02AnyPattern
import GraphMinor.Compute.GM02RecursiveWordSize
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Polynomial execution of the finite minor-pattern scan

Test the fixed family in order using the complete proved (4.7) calls.
The common word coefficient covers every call, and the common exponent
and summed coefficients cover the finite sequential execution. Copy
the retained flag into the standard output register.
-/

public section
namespace GraphMinor.Compute
open Graph GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Test a fixed finite pattern family and return its answer in the standard output register. -/
@[expose] noncomputable def gm02MinorPatternScanProg (ps : List GM02EdgeListInput) (w : ℤ) : Cmd :=
  .seq (gm02AnyPatternProg (fun J => gm02PatternCallProg J w) ps) (.assign outReg (.reg 89))

/-- The finite pattern scan computes the three alternatives in polynomial time from the original host encoding. -/
theorem gm02MinorPatternScan_computes (ps : List GM02EdgeListInput) (w : ℤ) :
    ComputesRelInTime GM02EdgeListInput.size (fun G s => s.arrs inArr = G.enc)
      (fun G s =>
        (s.regs outReg = 1 ∧ ∃ J ∈ ps, ∃ L : Graph ℕ ℕ,
          TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L)) ∨
        (s.regs outReg = 0 ∧ ¬∃ J ∈ ps, ∃ L : Graph ℕ ℕ,
          TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L)) ∨
        (s.regs outReg = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ)))
      (gm02MinorPatternScanProg ps w) (fun n => (n + 1) ^ gm02PatternListExponent ps w) := by
  refine ⟨gm02PatternListCoefficient ps w, gm02PatternListWordCoefficient ps w, ?_, ?_, ?_⟩
  · unfold gm02PatternListCoefficient
    omega
  · unfold gm02PatternListWordCoefficient
    omega
  · intro G s hsrc
    let W := wordSize (gm02PatternListWordCoefficient ps w) G.size
    have hw : 3 < 2 ^ W := by
      have hc : 3 + 0 + 1 ≤ gm02PatternListWordCoefficient ps w := by
        unfold gm02PatternListWordCoefficient
        omega
      simpa only [pow_zero, Nat.mul_one] using
        (gm02FixedPolynomialWordBound (D := 3) (d := 0) (n := G.size) hc (w := W) le_rfl)
    let B : GM02EdgeListInput → ℕ := fun J => gm02PatternCallCoefficient J w *
      (G.size + 1) ^ gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J
    let F : GM02EdgeListInput → Prop := fun J => ∃ L : Graph ℕ ℕ,
      TopologicallyContains G.graph L ∧ Nonempty (Iso J.graph L)
    let Q := w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ)
    obtain ⟨s₀, t₀, he₀, ht₀, _, hc₀⟩ := gm02AnyPatternProg_exec
      (fun J => gm02PatternCallProg J w) B F Q ps inArr G.enc hw
      (fun J hJ st hs => gm02PatternCallProg_exec J w G st hs
        (wordSize_mono_left (gm02PatternList_word_le ps w J hJ) G.size)) s hsrc
    have hflag : s₀.regs 89 ≤ 2 := by
      rcases hc₀ with ⟨hf, _⟩ | ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
    let s₁ := s₀.setReg outReg (s₀.regs 89)
    have he₁ : Exec W (.assign outReg (.reg 89)) s₀ s₁ 2 := .assign (eval_reg rfl (by omega))
    refine ⟨s₁, t₀ + 2, .seq he₀ he₁, ?_, ?_⟩
    · have hsum := gm02PatternList_time_le ps w G.size
      have htime : t₀ + 2 ≤ (ps.map (fun J => B J + 2)).sum + 4 := by omega
      exact htime.trans hsum
    · have hret : s₁.regs outReg = s₀.regs 89 := State.setReg_regs_self ..
      rcases hc₀ with ⟨hf, hp⟩ | ⟨hf, hn⟩ | ⟨hf, hq⟩
      · exact Or.inl ⟨hret.trans hf, hp⟩
      · refine Or.inr (Or.inl ⟨hret.trans hf, ?_⟩)
        rintro ⟨J, hJ, hcontains⟩
        exact hn J hJ hcontains
      · exact Or.inr (Or.inr ⟨hret.trans hf, hq⟩)

end GraphMinor.Compute
