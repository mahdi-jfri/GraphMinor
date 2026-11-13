module

public import GraphMinor.Compute.GM02DecodeInjection
public import GraphMinor.Compute.GM02TestValidInjection
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Testing an arbitrary integer candidate for II (4.7)

Decode and check the candidate vertex choices. Invalid choices return
zero immediately. Valid choices construct an ordinary labelled input
and run the complete proved program of (4.6). The returned zero bit
rules out every valid interpretation of that candidate code.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Decode, validate, and test one integer candidate. -/
@[expose] noncomputable def gm02TestInjectionCodeProg (H : GM02EdgeListInput) (q : ℕ) : Cmd :=
  .seq (gm02DecodeInjectionProg H.n)
    (.ite (.reg 193) (gm02TestValidInjectionProg H q) (.assign 89 (.const 0)))

/-- A budget independent of the particular code covers decoding, validation, and the labelled test. -/
@[expose] noncomputable def gm02InjectionCodeBudget (q : ℕ) (G H : GM02EdgeListInput) : ℕ :=
  5 + H.n * (8 + 4 * H.n) + (gm02InjectionValidExpr H.n).cost + gm02InjectionCandidateBudget q G H

private theorem frame_bounds {p : ℕ} (r : ℕ) (hlt : r < 193) :
    r ≠ 193 ∧ (r < 200 ∨ 200 + p ≤ r) := by omega

private theorem shape_ne (r : ℕ) (h : r < 83 ∨ 89 < r) : r ≠ 89 := by omega

/-- One raw code returns exact coded containment, coded exclusion, or a host-width report. -/
theorem gm02TestInjectionCodeProg_exec {W code : ℕ} (q : ℕ) (G H : GM02EdgeListInput)
    (w : ℤ) (s : State) (hq : max w.toNat 2 + 2 * H.edges.length < q)
    (hw : 3 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hmG : G.edges.length < 2 ^ W)
    (hcap : 1 + 2 * H.edges.length < 2 ^ W) (hlen : gm02InjectedInputLength G H < 2 ^ W)
    (hpow : (G.n + 1) ^ H.n < 2 ^ W) (hcode : code < (G.n + 1) ^ H.n)
    (hword : wordSize (gm02TopologicalWordCoefficient q H.edges.length) (G.size + H.size) ≤ W)
    (hG : s.arrs inArr = G.enc) (hrn : s.regs 40 = G.n) (hrcode : s.regs 190 = code) :
    ∃ s' t, Exec W (gm02TestInjectionCodeProg H q) s s' t ∧
      t ≤ gm02InjectionCodeBudget q G H ∧
      ((s'.regs 89 = 1 ∧ ∃ hv : gm02InjectionCodeValid G.n H.n code,
        TopologicallyContains G.graph (gm02InjectedPattern G H (gm02InjectionOfCode G.n H.n code hv)).H) ∨
        (s'.regs 89 = 0 ∧ ∀ hv : gm02InjectionCodeValid G.n H.n code,
          ¬TopologicallyContains G.graph (gm02InjectedPattern G H (gm02InjectionOfCode G.n H.n code hv)).H) ∨
        (s'.regs 89 = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))) ∧
      (∀ a, a < 1000 → a ≠ 29 → a ≠ 30 → a ≠ 31 → a ≠ 32 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 193 → (r < 83 ∨ 89 < r) → s'.regs r = s.regs r) := by
  obtain ⟨s₀, t₀, he₀, ht₀, hv₀, hslots, ha₀, hr₀⟩ := gm02DecodeInjectionProg_exec H.n s
    hrn hrcode (by omega) hn (hcode.trans hpow) hpow
  have hreg (r : ℕ) (hr : r < 193) : s₀.regs r = s.regs r := by
    obtain ⟨hne, hout⟩ := frame_bounds r hr (p := H.n)
    exact hr₀ r hne hout
  by_cases hv : gm02InjectionCodeValid G.n H.n code
  · have hflag : s₀.regs 193 = 1 := by simpa only [ite_eq_left hv] using hv₀
    let f := gm02InjectionOfCode G.n H.n code hv
    obtain ⟨s₁, t₁, he₁, ht₁, hc, ha₁, hr₁⟩ := gm02TestValidInjectionProg_exec q G H f w s₀
      hq hw hn hmG hcap hlen hword ((congrFun ha₀ inArr).trans hG)
      ((hreg 40 (by decide)).trans hrn) hslots
    refine ⟨s₁, t₀ + (1 + t₁), .seq he₀ (.ite_true (eval_reg hflag (by omega : 1 < 2 ^ W)) (by decide) he₁),
      ?_, ?_, ?_, ?_⟩
    · unfold gm02InjectionCodeBudget
      omega
    · rcases hc with ⟨hf, ht⟩ | ⟨hf, ht⟩ | hc
      · exact Or.inl ⟨hf, hv, ht⟩
      · exact Or.inr (Or.inl ⟨hf, fun _ => ht⟩)
      · exact Or.inr (Or.inr hc)
    · intro a ha h29 h30 h31 h32 h33
      exact (ha₁ a ha h29 h30 h31 h32 h33).trans (congrFun ha₀ a)
    · intro r hr hshape
      exact (hr₁ r (hr.trans (by decide)) hshape).trans (hreg r hr)
  · have hflag : s₀.regs 193 = 0 := by simpa only [ite_eq_right hv] using hv₀
    let s₁ := s₀.setReg 89 0
    have he₁ : Exec W (.assign 89 (.const 0)) s₀ s₁ 2 := .assign (eval_const (by omega))
    refine ⟨s₁, t₀ + (1 + 2), .seq he₀ (.ite_false (eval_reg hflag (by omega : 0 < 2 ^ W)) he₁),
      ?_, Or.inr (Or.inl ⟨State.setReg_regs_self .., fun h => (hv h).elim⟩), ?_, ?_⟩
    · unfold gm02InjectionCodeBudget
      omega
    · intro a _ _ _ _ _ _
      exact congrFun ha₀ a
    · intro r hr hshape
      have hne : r ≠ 89 := shape_ne r hshape
      exact (State.setReg_regs_ne s₀ 0 hne).trans (hreg r hr)

end GraphMinor.Compute
