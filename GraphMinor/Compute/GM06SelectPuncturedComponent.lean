module

public import GraphMinor.Compute.GM06PuncturedFindSpec
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Preparing the chosen component for deletion

The source search for Reduction 2 in VI (5.7), page 133, keeps its
first successful source, but later queries can overwrite component
marks. Recompute the chosen component before changing the drawing.
If no source was found, every live source meets a protected vertex.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Find a disjoint live component and leave precisely its marks in array 33. -/
def gm06SelectPuncturedComponentProg (ends active guarded live : Arr) : Cmd :=
  .seq (gm06FindPuncturedComponentProg ends active guarded live)
    (.ite (.reg 113)
      (.seq (.assign 187 (.reg 114))
        (.seq (gm06PuncturedComponentProg ends active)
          (.seq (.assign 114 (.reg 187)) (.assign 113 (.const 1))))) .skip)

/-- The component selector either excludes every eligible live source
or returns its chosen live source with its exact component marks. -/
theorem gm06SelectPuncturedComponentProg_exec {w n : ℕ} (ends active guarded live : Arr)
    (he28 : ends < 28) (ha28 : active < 28) (hp28 : guarded < 28) (hl28 : live < 28)
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (Q A : Finset (Fin n))
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs ends = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs active = tagged.map Prod.snd) (hQ : s.arrs guarded = gm02VertexBits Q)
    (hA : s.arrs live = gm02VertexBits A) (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w (gm06SelectPuncturedComponentProg ends active guarded live) s s' t ∧
      t ≤ 64 + n * (53 * (n * n) + 64 * n + 48 * tagged.length + 78) +
        53 * (n * n) + 47 * n + 48 * tagged.length ∧
      (∀ a : ℕ, a < 28 → s'.arrs a = s.arrs a) ∧ s'.regs 100 = n ∧ s'.regs 135 = cut.val ∧
      ((s'.regs 113 = 0 ∧ ∀ source ∈ A,
          (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card ≠ 0) ∨
        ∃ source : Fin n, s'.regs 113 = 1 ∧ s'.regs 114 = source.val ∧ source ∈ A ∧
          (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0 ∧
          s'.arrs 33 = gm06VertexReachData (gm06PuncturedGraphData tagged cut) source) := by
  classical
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hf₁, ha₁, hN₁, hcut₁⟩ :=
    gm06FindPuncturedComponentProg_exec ends active guarded live he28 ha28 hp28 hl28
      tagged cut Q A hw hn hsquare hm hbits ha hb hQ hA hN hcut
  rcases gm06PuncturedSourceCandidates_fold_spec tagged cut Q A with ⟨hnone, hnoneSpec⟩ |
      ⟨source, hsome, hsourceA, hzero⟩
  · rw [hnone] at hf₁
    have hflag : s₁.regs 113 = 0 := by simpa [gm06SingletonRegs] using hf₁.1
    refine ⟨s₁, t₁ + 2, .seq he₁ (.ite_false (eval_reg hflag (Nat.two_pow_pos w)) (.skip s₁)),
      by omega, ha₁, hN₁, hcut₁, Or.inl ⟨hflag, hnoneSpec⟩⟩
  · rw [hsome] at hf₁
    have hflag : s₁.regs 113 = 1 := by simpa [gm06SingletonRegs] using hf₁.1
    have hchosen : s₁.regs 114 = source.val := hf₁.2 _ rfl
    let s₂ := s₁.setReg 187 source.val
    have he₂ : Exec w (.assign 187 (.reg 114)) s₁ s₂ 2 :=
      .assign (eval_reg hchosen (source.isLt.trans hn))
    obtain ⟨s₃, t₃, he₃, ht₃, hreach₃, ha₃, hN₃, hcut₃, hsource₃⟩ :=
      gm06PuncturedComponentProg_exec (s := s₂) ends active he28 ha28 tagged cut source hw hn hsquare hm hbits
        ((ha₁ ends he28).trans ha) ((ha₁ active ha28).trans hb)
        (by simpa [s₂] using hN₁) (by simpa [s₂] using hcut₁) (by simp [s₂])
    let s₄ := s₃.setReg 114 source.val
    let s₅ := s₄.setReg 113 1
    have he₄ : Exec w (.assign 114 (.reg 187)) s₃ s₄ 2 :=
      .assign (eval_reg hsource₃ (source.isLt.trans hn))
    have he₅ : Exec w (.assign 113 (.const 1)) s₄ s₅ 2 := .assign (eval_const hw1)
    refine ⟨s₅, t₁ + (1 + (2 + (t₃ + (2 + 2)))),
      .seq he₁ (.ite_true (eval_reg hflag hw1) (by decide)
        (.seq he₂ (.seq he₃ (.seq he₄ he₅)))), by omega, ?_, ?_, ?_, Or.inr ?_⟩
    · intro a ha'
      exact (ha₃ a ha').trans (ha₁ a ha')
    · simpa [s₅, s₄] using hN₃
    · simpa [s₅, s₄] using hcut₃
    · exact ⟨source, by simp [s₅], by simp [s₅, s₄], hsourceA, hzero, hreach₃⟩

end GraphMinor.Compute
