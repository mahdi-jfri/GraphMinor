module

public import GraphMinor.Compute.GM06RotationSector
public import GraphMinor.Compute.GM06SectorMarkers

/-!
# A RAM program calibrating a rotation sector

For VI (5.7), page 133, registers 36 and 37 hold the two boundary
markers and register 39 holds the outside cuff marker. Test that
marker with the row sector program. If it lies inside, swap the
two boundary registers. Later edge tests can then use the same
sector scan with either orientation of the input rotation row.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Calibrate the boundary registers against the outside label in register 39. -/
def gm06CalibrateSectorProg (rot : Arr) : Cmd :=
  .seq (.assign 38 (.reg 39))
    (.seq (gm06RotationSectorProg rot)
      (.ite (.reg 43)
        (.seq (.assign 59 (.reg 36))
          (.seq (.assign 36 (.reg 37)) (.assign 37 (.reg 59)))) .skip))

/-- The calibration command selects the finite calibrated markers
in linear time and preserves all drawing arrays. -/
theorem gm06CalibrateSectorProg_exec {w : ℕ} (rot : ℕ) (xs : List ℕ)
    (p q c : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hc : c ∈ xs)
    (ha : s.arrs rot = xs) (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h39 : s.regs 39 = c) :
    ∃ s' t, Exec w (gm06CalibrateSectorProg rot) s s' t ∧
      t ≤ 44 + 39 * xs.length ∧ Keeps [36, 37, 38, 50, 40, 41, 42, 43, 59] [] s s' ∧
      s'.regs 36 = (gm06SectorMarkers xs p q c).1 ∧
      s'.regs 37 = (gm06SectorMarkers xs p q c).2 := by
  have hw1 : 1 < 2 ^ w := by omega
  have hpw : p < 2 ^ w := hx p hp
  have hqw : q < 2 ^ w := hx q hq
  let s₀ := s.setReg 38 c
  have he₀ : Exec w (.assign 38 (.reg 39)) s s₀ 2 := .assign (eval_reg h39 (hx c hc))
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hflag⟩ := gm06RotationSectorProg_exec rot xs p q c s₀ hw hn hx hnd
    hp hq hc (by simpa [s₀] using ha) (by simpa [s₀] using h36)
    (by simpa [s₀] using h37) (by simp [s₀])
  have hp₁ : s₁.regs 36 = p := by simpa [s₀] using (hk₁.1 36 (by decide)).trans h36
  have hq₁ : s₁.regs 37 = q := by simpa [s₀] using (hk₁.1 37 (by decide)).trans h37
  have hframe {s' : State} {t : ℕ} (he : Exec w (gm06CalibrateSectorProg rot) s s' t) :
      Keeps [36, 37, 38, 50, 40, 41, 42, 43, 59] [] s s' := by
    constructor
    · intro j hj
      apply he.regs_eq_of_not_mem_writtenRegs
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hj
      simp only [gm06CalibrateSectorProg, gm06RotationSectorProg, gm06FindLabelProg, gm06BetweenProg,
        forUp, Cmd.writtenRegs, Finset.mem_union, Finset.mem_singleton, Finset.notMem_empty,
        or_false, not_or]
      tauto
    · intro a _
      apply he.arrs_eq_of_not_mem_writtenArrs
      simp [gm06CalibrateSectorProg, gm06RotationSectorProg, gm06FindLabelProg, gm06BetweenProg,
        forUp, Cmd.writtenArrs]
  by_cases hb : GM06DrawingData.cyclicBetween (xs.idxOf p) (xs.idxOf q) (xs.idxOf c) = true
  · have hflag₁ : s₁.regs 43 = 1 := by simpa only [hb, ite_true] using hflag
    let s₂ := s₁.setReg 59 p
    let s₃ := s₂.setReg 36 q
    let s₄ := s₃.setReg 37 p
    have he₂ : Exec w (.assign 59 (.reg 36)) s₁ s₂ 2 := .assign (eval_reg hp₁ hpw)
    have he₃ : Exec w (.assign 36 (.reg 37)) s₂ s₃ 2 :=
      .assign (eval_reg (by simpa [s₂] using hq₁) hqw)
    have he₄ : Exec w (.assign 37 (.reg 59)) s₃ s₄ 2 :=
      .assign (eval_reg (by simp [s₃, s₂]) hpw)
    have heSwap : Exec w (.seq (.assign 59 (.reg 36))
        (.seq (.assign 36 (.reg 37)) (.assign 37 (.reg 59)))) s₁ s₄ 6 := .seq he₂ (.seq he₃ he₄)
    have heBranch : Exec w (.ite (.reg 43)
        (.seq (.assign 59 (.reg 36)) (.seq (.assign 36 (.reg 37)) (.assign 37 (.reg 59)))) .skip) s₁ s₄ 7 := by
      simpa only [Expr.cost] using Exec.ite_true (cond := .reg 43) (eval_reg hflag₁ hw1)
        (by decide : 1 ≠ 0) heSwap
    have he : Exec w (gm06CalibrateSectorProg rot) s s₄ (2 + (t₁ + 7)) :=
      .seq he₀ (.seq he₁ heBranch)
    refine ⟨s₄, _, he, by omega, hframe he, ?_, ?_⟩
    · simp [s₄, s₃, gm06SectorMarkers, hb]
    · simp [s₄, gm06SectorMarkers, hb]
  · have hflag₀ : s₁.regs 43 = 0 := by simpa [hb] using hflag
    have heBranch : Exec w (.ite (.reg 43)
        (.seq (.assign 59 (.reg 36)) (.seq (.assign 36 (.reg 37)) (.assign 37 (.reg 59)))) .skip) s₁ s₁ 2 := by
      simpa only [Expr.cost] using Exec.ite_false (cond := .reg 43)
        (eval_reg hflag₀ (Nat.two_pow_pos w)) (Exec.skip (s := s₁))
    have he : Exec w (gm06CalibrateSectorProg rot) s s₁ (2 + (t₁ + 2)) :=
      .seq he₀ (.seq he₁ heBranch)
    refine ⟨s₁, _, he, by omega, hframe he, ?_, ?_⟩
    · simpa [gm06SectorMarkers, hb] using hp₁
    · simpa [gm06SectorMarkers, hb] using hq₁

end GraphMinor.Compute
