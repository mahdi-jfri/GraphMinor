module

public import GraphMinor.Compute.GM06FindInitialLoop
import GraphMinor.Compute.GM06DeleteSectorEdge

/-!
# Clearing a computed initial loop

The loop finder identifies an active edge having both ends at the
selected initial vertex. Clear its activity bit and report success.
The live vertex set stays fixed and the active edge count falls by
one. If there is no loop, preserve the activity array and report failure.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Clear a found initial loop, with success in 289 and its original index in 288. -/
def gm06DeleteInitialLoopProg : Cmd :=
  .seq gm06FindInitialLoopProg
    (.seq (.assign 289 (.const 0))
      (.ite (.op .lt (.reg 288) (.len 12))
        (.seq (.write 12 (.reg 288) (.const 0)) (.assign 289 (.const 1))) .skip))

/-- The loop deletion either excludes all initial loops or clears one
active loop and strictly reduces the number of active edges. -/
theorem gm06DeleteInitialLoopProg_exec {w n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (cut : Fin n) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * tagged.length < 2 ^ w)
    (hbits : ∀ p ∈ tagged, p.2 ≤ 1)
    (ha : s.arrs 3 = gm06EndpointWords (tagged.map fun p => (p.1.1.val, p.1.2.val)))
    (hb : s.arrs 12 = tagged.map Prod.snd)
    (hN : s.regs 100 = n) (hcut : s.regs 135 = cut.val) :
    ∃ s' t, Exec w gm06DeleteInitialLoopProg s s' t ∧
      t ≤ 31 + 15 * n + 41 * tagged.length ∧
      Keeps [180, 181, 286, 287, 288, 289] [12, 22, 23] s s' ∧
      ((s'.regs 289 = 0 ∧ s'.arrs 12 = tagged.map Prod.snd ∧ ∀ j : Fin tagged.length,
          ¬ (tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut)) ∨
        ∃ j : Fin tagged.length, s'.regs 289 = 1 ∧ s'.regs 288 = j.val ∧
          tagged[j].2 = 1 ∧ tagged[j].1.1 = cut ∧ tagged[j].1.2 = cut ∧
          s'.arrs 12 = (tagged.map Prod.snd).set j.val 0 ∧
          (s'.arrs 12).count 1 + 1 = (tagged.map Prod.snd).count 1) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : tagged.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout₁⟩ := gm06FindInitialLoopProg_exec tagged cut s hw hn hm hbits ha hb hN hcut
  let regs := [180, 181, 286, 287, 288, 289]
  let arrays := [12, 22, 23]
  have hk₁' : Keeps regs arrays s s₁ := hk₁.mono (by simp [regs]) (by simp [arrays])
  let s₂ := s₁.setReg 289 0
  have he₂ : Exec w (.assign 289 (.const 0)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk₂ : Keeps regs arrays s s₂ := hk₁'.setReg (by simp [regs]) _
  have hb₂ : s₂.arrs 12 = tagged.map Prod.snd := (hk₁.2 12 (by decide)).trans hb
  have hlen : (tagged.map Prod.snd).length = tagged.length := List.length_map _
  rcases hout₁ with ⟨hnone, hexclude⟩ | ⟨j, hchosen, hactive, hu, hv⟩
  · have hpos : s₂.regs 288 = tagged.length := by simpa [s₂] using hnone
    have hc := eval_lt (eval_reg hpos hmw) (GraphMinor.Compute.Crossing.eval_len hb₂ (hlen ▸ hmw)) hw1
    have hbranch : Exec w (.ite (.op .lt (.reg 288) (.len 12))
        (.seq (.write 12 (.reg 288) (.const 0)) (.assign 289 (.const 1))) .skip) s₂ s₂ 4 :=
      .ite_false (by simpa only [hlen, lt_self_iff_false, ite_false] using hc) (.skip s₂)
    exact ⟨s₂, t₁ + (2 + 4), .seq he₁ (.seq he₂ hbranch), by omega, hk₂,
      Or.inl ⟨by simp [s₂], hb₂, hexclude⟩⟩
  · have hpos : s₂.regs 288 = j.val := by simpa [s₂] using hchosen
    let s₃ := s₂.writeArr 12 j.val 0
    let s₄ := s₃.setReg 289 1
    have he₃ : Exec w (.write 12 (.reg 288) (.const 0)) s₂ s₃ 3 :=
      .write (eval_reg hpos (j.isLt.trans hmw)) (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
        (by simpa only [hb₂, List.length_map] using j.isLt)
    have he₄ : Exec w (.assign 289 (.const 1)) s₃ s₄ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw1)
    have hc := eval_lt (eval_reg hpos (j.isLt.trans hmw)) (GraphMinor.Compute.Crossing.eval_len hb₂ (hlen ▸ hmw)) hw1
    have hbranch : Exec w (.ite (.op .lt (.reg 288) (.len 12))
        (.seq (.write 12 (.reg 288) (.const 0)) (.assign 289 (.const 1))) .skip) s₂ s₄ 8 :=
      .ite_true (by simpa only [hlen, j.isLt, ite_true] using hc) (by decide) (.seq he₃ he₄)
    have hk₄ : Keeps regs arrays s s₄ :=
      (hk₂.writeArr (by simp [arrays]) _ _).setReg (by simp [regs]) _
    have harr : s₄.arrs 12 = (tagged.map Prod.snd).set j.val 0 := by simp only [s₄, State.setReg_arrs, s₃, State.writeArr_arrs_self, hb₂]
    refine ⟨s₄, t₁ + (2 + 8), .seq he₁ (.seq he₂ hbranch), by omega, hk₄,
      Or.inr ⟨j, by simp [s₄], by simpa [s₄, s₃] using hpos, hactive, hu, hv, harr, ?_⟩⟩
    rw [harr]
    apply gm06ActiveCount_after_delete _ _ (by simpa only [List.length_map] using j.isLt)
    simpa using hactive

end GraphMinor.Compute
