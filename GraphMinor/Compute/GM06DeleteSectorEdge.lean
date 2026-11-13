module

public import GraphMinor.Compute.GM06FindSectorEdge

/-!
# Deleting a selected sector edge in the RAM workspace

Search the active edge labels for the chosen directed sector. If an
edge is found, clear its activity bit and report the change in register
60. Otherwise preserve the activity array and report zero. A successful
update decreases the number of active edges by exactly one.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Clearing an active bit decreases the number of active edges by one. -/
theorem gm06ActiveCount_after_delete (mask : List ℕ) (e : ℕ) (he : e < mask.length)
    (hactive : mask[e] = 1) : (mask.set e 0).count 1 + 1 = mask.count 1 := by
  have hmem : 1 ∈ mask := hactive ▸ List.getElem_mem he
  have hpos : 0 < mask.count 1 := List.count_pos_iff.mpr hmem
  rw [List.count_set he]
  simpa [hactive] using Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)

/-- Clear one selected sector edge, with a change flag in register 60. -/
def gm06DeleteSectorEdgeProg (rot active : Arr) : Cmd :=
  .seq (gm06FindSectorEdgeProg rot active)
    (.seq (.assign 60 (.const 0))
      (.ite (.op .lt (.reg 55) (.len active))
        (.seq (.write active (.reg 55) (.const 0)) (.assign 60 (.const 1))) .skip))

private theorem deleteSectorEdge_keeps {w rot active t : ℕ} {s s' : State}
    (he : Exec w (gm06DeleteSectorEdgeProg rot active) s s' t) :
    Keeps [53, 55, 38, 50, 40, 41, 42, 43, 54, 60] [active] s s' := by
  constructor
  · intro j hj
    apply he.regs_eq_of_not_mem_writtenRegs
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
    simp only [gm06DeleteSectorEdgeProg, gm06FindSectorEdgeProg, gm06ActiveEdgeSectorProg,
      gm06EitherEndSectorProg, gm06OptionalRotationSectorProg, gm06RotationSectorProg,
      gm06FindLabelProg, gm06BetweenProg, forUp, Cmd.writtenRegs, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, not_or, or_false]
    tauto
  · intro a ha
    apply he.arrs_eq_of_not_mem_writtenArrs
    simpa [gm06DeleteSectorEdgeProg, gm06FindSectorEdgeProg, gm06ActiveEdgeSectorProg,
      gm06EitherEndSectorProg, gm06OptionalRotationSectorProg, gm06RotationSectorProg,
      gm06FindLabelProg, gm06BetweenProg, forUp, Cmd.writtenArrs] using ha

/-- A sector deletion either excludes all eligible edges or makes one strict decrease. -/
theorem gm06DeleteSectorEdgeProg_exec {w : ℕ} (rot active : ℕ) (xs mask : List ℕ)
    (p q : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hm : 2 * mask.length < 2 ^ w)
    (hbits : ∀ b ∈ mask, b ≤ 1) (ha : s.arrs rot = xs) (hb : s.arrs active = mask)
    (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) :
    ∃ s' t, Exec w (gm06DeleteSectorEdgeProg rot active) s s' t ∧
      t ≤ 17 + mask.length * (120 + 104 * xs.length) ∧
      Keeps [53, 55, 38, 50, 40, 41, 42, 43, 54, 60] [active] s s' ∧
      ((s'.regs 60 = 0 ∧ s'.arrs active = mask ∧ ∀ e (he : e < mask.length),
        ¬(mask[e] = 1 ∧ (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
          gm06RotationSectorFlag xs p q (2 * e + 1) = 1))) ∨
        (s'.regs 60 = 1 ∧ ∃ (e : ℕ) (he : e < mask.length),
          s'.regs 55 = e ∧ s'.arrs active = mask.set e 0 ∧ mask[e] = 1 ∧
            (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
              gm06RotationSectorFlag xs p q (2 * e + 1) = 1) ∧
            (s'.arrs active).count 1 + 1 = mask.count 1)) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : mask.length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd⟩ := gm06FindSectorEdgeProg_exec rot active xs mask p q
    s hw hn hx hnd hp hq hm hbits ha hb h36 h37
  let s₂ := s₁.setReg 60 0
  have he₂ : Exec w (.assign 60 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hb₂ : s₂.arrs active = mask := by
    simpa only [s₂, State.setReg_arrs] using (hk₁.2 active (by simp)).trans hb
  rcases hd with hnone | ⟨e, he, hpos, hact, hsector⟩
  · have hpos : s₂.regs 55 = mask.length := by simpa [s₂] using hnone.1
    have hc := GraphMinor.Compute.Crossing.eval_lt
      (GraphMinor.Compute.Crossing.eval_reg hpos hmw)
      (GraphMinor.Compute.Crossing.eval_len hb₂ hmw) hw1
    have hbranch : Exec w (.ite (.op .lt (.reg 55) (.len active))
        (.seq (.write active (.reg 55) (.const 0)) (.assign 60 (.const 1))) .skip) s₂ s₂ 4 :=
      .ite_false (by simpa using hc) (.skip s₂)
    have hex : Exec w (gm06DeleteSectorEdgeProg rot active) s s₂ (t₁ + (2 + 4)) :=
      .seq he₁ (.seq he₂ hbranch)
    exact ⟨s₂, _, hex, by omega, deleteSectorEdge_keeps hex,
      Or.inl ⟨by simp [s₂], hb₂, hnone.2⟩⟩
  · have hpos₂ : s₂.regs 55 = e := by simpa [s₂] using hpos
    let s₃ := s₂.writeArr active e 0
    have he₃ : Exec w (.write active (.reg 55) (.const 0)) s₂ s₃ 3 :=
      .write (GraphMinor.Compute.Crossing.eval_reg hpos₂ (he.trans hmw))
        (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
        (by simpa only [hb₂] using he)
    let s₄ := s₃.setReg 60 1
    have he₄ : Exec w (.assign 60 (.const 1)) s₃ s₄ 2 :=
      .assign (GraphMinor.Compute.Crossing.eval_const hw1)
    have hc := GraphMinor.Compute.Crossing.eval_lt
      (GraphMinor.Compute.Crossing.eval_reg hpos₂ (he.trans hmw))
      (GraphMinor.Compute.Crossing.eval_len hb₂ hmw) hw1
    have hbranch : Exec w (.ite (.op .lt (.reg 55) (.len active))
        (.seq (.write active (.reg 55) (.const 0)) (.assign 60 (.const 1))) .skip) s₂ s₄ 8 :=
      .ite_true (by simpa only [he, ite_true] using hc) (by decide) (.seq he₃ he₄)
    have hex : Exec w (gm06DeleteSectorEdgeProg rot active) s s₄ (t₁ + (2 + 8)) :=
      .seq he₁ (.seq he₂ hbranch)
    have harr : s₄.arrs active = mask.set e 0 := by
      simp only [s₄, State.setReg_arrs, s₃, State.writeArr_arrs_self, hb₂]
    refine ⟨s₄, _, hex, by omega, deleteSectorEdge_keeps hex,
      Or.inr ⟨by simp [s₄], e, he, ?_, harr, hact, hsector, ?_⟩⟩
    · simpa only [s₄, State.setReg_regs_ne _ _ (by decide : 55 ≠ 60), s₃,
        State.writeArr_regs] using hpos₂
    · rw [harr]
      exact gm06ActiveCount_after_delete mask e he hact

end GraphMinor.Compute
