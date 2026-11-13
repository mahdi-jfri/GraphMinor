module

public import GraphMinor.Compute.GM06DeleteInitialLoop
public import GraphMinor.Compute.GM06DiscardPuncturedComponent

/-!
# The two Reduction 2 tests at one initial vertex

First search for a loop at the selected initial vertex. If one is
found, clear that edge. Otherwise search the punctured graph for
a live component disjoint from the linkage and discard it when
found. The result code is zero on failure, one for a loop deletion,
and two for a component deletion. These are the two cases of the
separation test in VI (5.7), page 133.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Apply one Reduction 2 mask update at vertex 135, returning its kind in 294. -/
def gm06Reduction2AtVertexProg : Cmd :=
  .seq gm06DeleteInitialLoopProg
    (.ite (.reg 289) (.assign 294 (.const 1))
      (.seq gm06DiscardPuncturedComponentProg
        (.assign 294 (.op .mul (.const 2) (.reg 113)))))

/-- The local Reduction 2 scan either excludes both finite tests,
clears an active attachment loop, or removes an eligible live component. -/
theorem gm06Reduction2AtVertexProg_exec {w n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (Q A : Finset (Fin n))
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hm : 2 * tagged.length < 2 ^ w) (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    {s : State}
    (ha : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs 12 = tagged.map Prod.snd) (hQ : s.arrs 17 = gm02VertexBits Q)
    (hA : s.arrs 14 = gm02VertexBits A) (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w gm06Reduction2AtVertexProg s s' t ∧
      t ≤ 126 + n * (53 * (n * n) + 64 * n + 48 * tagged.length + 78) +
        53 * (n * n) + 93 * n + 129 * tagged.length ∧
      (∀ a : ℕ, a < 28 → a ≠ 12 → a ≠ 14 → a ≠ 15 → a ≠ 16 → a ≠ 22 → a ≠ 23 →
        s'.arrs a = s.arrs a) ∧ s'.regs 100 = n ∧ s'.regs 135 = cut.val ∧
      ((s'.regs 294 = 0 ∧ s'.arrs 14 = gm02VertexBits A ∧ s'.arrs 12 = tagged.map Prod.snd ∧
          (∀ source ∈ A,
            (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card ≠ 0) ∧
          ∀ j : Fin tagged.length, ¬ (tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut)) ∨
        (s'.regs 294 = 1 ∧ s'.arrs 14 = gm02VertexBits A ∧
          ∃ j : Fin tagged.length, tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut ∧
            s'.arrs 12 = (tagged.map Prod.snd).set j.val 0 ∧
            (s'.arrs 12).count 1 + 1 = (tagged.map Prod.snd).count 1) ∨
        (s'.regs 294 = 2 ∧ ∃ source : Fin n, source ∈ A ∧
          (Q ∩ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card = 0 ∧
          s'.arrs 14 = gm02VertexBits (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
          s'.arrs 12 = gm06InducedEdgeBits tagged
            (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source) ∧
          (A \ reachSet (gm06PuncturedGraphData tagged cut).vertexGraph source).card < A.card)) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout₁⟩ := gm06DeleteInitialLoopProg_exec tagged cut s hw hn hm hbits ha hb hN hcut
  have hN₁ : s₁.regs 100 = n := (hk₁.1 100 (by decide)).trans hN
  have hcut₁ : s₁.regs 135 = cut.val := (hk₁.1 135 (by decide)).trans hcut
  have hA₁ : s₁.arrs 14 = gm02VertexBits A := (hk₁.2 14 (by decide)).trans hA
  rcases hout₁ with ⟨hflag, hb₁, hloops⟩ | ⟨j, hflag, _, hactive, hu, hv, hb₁, hprogress⟩
  · obtain ⟨s₂, t₂, he₂, ht₂, ha₂, hN₂, hcut₂, hout₂⟩ := gm06DiscardPuncturedComponentProg_exec
      tagged cut Q A hw hn hsquare hm hbits ((hk₁.2 3 (by decide)).trans ha) hb₁
      ((hk₁.2 17 (by decide)).trans hQ) hA₁ hN₁ hcut₁
    rcases hout₂ with ⟨hfound, hA₂, hb₂, hnone⟩ | ⟨source, hfound, _, hsource, hzero, hA₂, hb₂, hprogress⟩
    · let s₃ := s₂.setReg 294 0
      have he₃ : Exec w (.assign 294 (.op .mul (.const 2) (.reg 113))) s₂ s₃ 4 :=
        .assign (by simpa using GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw) (GraphMinor.Compute.Crossing.eval_reg hfound (Nat.two_pow_pos w)) (Nat.two_pow_pos w))
      refine ⟨s₃, t₁ + (1 + (t₂ + 4)), .seq he₁ (.ite_false (GraphMinor.Compute.Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.seq he₂ he₃)),
        by omega, ?_, by simpa [s₃] using hN₂, by simpa [s₃] using hcut₂, Or.inl ?_⟩
      · intro a ha' h12 h14 h15 h16 h22 h23
        exact (ha₂ a ha' h12 h14 h15 h16).trans (hk₁.2 a (by simp [h12, h22, h23]))
      · exact ⟨by simp [s₃], hA₂, hb₂, hnone, hloops⟩
    · let s₃ := s₂.setReg 294 2
      have he₃ : Exec w (.assign 294 (.op .mul (.const 2) (.reg 113))) s₂ s₃ 4 :=
        .assign (by simpa using GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw) (GraphMinor.Compute.Crossing.eval_reg hfound hw1) hw)
      refine ⟨s₃, t₁ + (1 + (t₂ + 4)), .seq he₁ (.ite_false (GraphMinor.Compute.Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.seq he₂ he₃)),
        by omega, ?_, by simpa [s₃] using hN₂, by simpa [s₃] using hcut₂, Or.inr (Or.inr ?_)⟩
      · intro a ha' h12 h14 h15 h16 h22 h23
        exact (ha₂ a ha' h12 h14 h15 h16).trans (hk₁.2 a (by simp [h12, h22, h23]))
      · exact ⟨by simp [s₃], source, hsource, hzero, hA₂, hb₂, hprogress⟩
  · let s₂ := s₁.setReg 294 1
    have he₂ : Exec w (.assign 294 (.const 1)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw1)
    refine ⟨s₂, t₁ + (1 + 2), .seq he₁ (.ite_true (GraphMinor.Compute.Crossing.eval_reg hflag hw1) (by decide) he₂),
      by omega, ?_, by simpa [s₂] using hN₁, by simpa [s₂] using hcut₁, Or.inr (Or.inl ?_)⟩
    · intro a _ h12 _ _ _ h22 h23
      exact hk₁.2 a (by simp [h12, h22, h23])
    · exact ⟨by simp [s₂], hA₁, j, hactive, hu, hv, hb₁, hprogress⟩

end GraphMinor.Compute
