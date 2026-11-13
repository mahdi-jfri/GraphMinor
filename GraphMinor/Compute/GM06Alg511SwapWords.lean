module

public import GraphMinor.Compute.Basic
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Changing the signs of the current and target winding words

For VI (5.11), page 134, orientation reversal negates both winding
values. Swap each numerator's two magnitude parts, using a scratch
register. Restore the positive target denominator from its saved word
and record that the reflected orientation was chosen.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Exchange two word registers through a distinct scratch register. -/
def gm06Alg511SwapWordsProg (a b tmp : Reg) : Cmd :=
  .seq (.assign tmp (.reg a)) (.seq (.assign a (.reg b)) (.assign b (.reg tmp)))

/-- Exchanging two supplied words takes six steps and preserves all
other registers and every array. -/
theorem gm06Alg511SwapWordsProg_exec {w : ℕ} (a b tmp : Reg)
    (hab : a ≠ b) (hta : tmp ≠ a) (htb : tmp ≠ b) (s : State)
    (ha : s.regs a < 2 ^ w) (hb : s.regs b < 2 ^ w) :
    ∃ s', Exec w (gm06Alg511SwapWordsProg a b tmp) s s' 6 ∧
      s'.regs a = s.regs b ∧ s'.regs b = s.regs a ∧ Keeps [a, b, tmp] [] s s' := by
  let s₁ := s.setReg tmp (s.regs a)
  let s₂ := s₁.setReg a (s.regs b)
  let s₃ := s₂.setReg b (s.regs a)
  have he₁ : Exec w (.assign tmp (.reg a)) s s₁ 2 := .assign (Crossing.eval_reg rfl ha)
  have he₂ : Exec w (.assign a (.reg b)) s₁ s₂ 2 :=
    .assign (Crossing.eval_reg (by simp [s₁, htb.symm]) hb)
  have he₃ : Exec w (.assign b (.reg tmp)) s₂ s₃ 2 :=
    .assign (Crossing.eval_reg (by simp [s₂, s₁, hta]) ha)
  refine ⟨s₃, .seq he₁ (.seq he₂ he₃), by simp [s₃, s₂, hab], by simp [s₃],
    (((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _⟩

/-- Negate current numerator 54/55 and target numerator 62/63,
restore target denominator 64 from 66 and set orientation flag 57. -/
def gm06Alg511FlipScalarsProg : Cmd :=
  .seq (gm06Alg511SwapWordsProg 54 55 58)
    (.seq (gm06Alg511SwapWordsProg 62 63 58)
      (.seq (.assign 64 (.reg 66)) (.assign 57 (.const 1))))

/-- The reflected scalar values are the negatives of the old values,
with the same saved positive denominator and an explicit mode bit. -/
theorem gm06Alg511FlipScalarsProg_exec {w : ℕ} (s : State) (hw : 1 < 2 ^ w)
    (hp : s.regs 54 < 2 ^ w) (hq : s.regs 55 < 2 ^ w)
    (ha : s.regs 62 < 2 ^ w) (hb : s.regs 63 < 2 ^ w) (hd : s.regs 66 < 2 ^ w) :
    ∃ s', Exec w gm06Alg511FlipScalarsProg s s' 16 ∧
      s'.regs 54 = s.regs 55 ∧ s'.regs 55 = s.regs 54 ∧
      s'.regs 62 = s.regs 63 ∧ s'.regs 63 = s.regs 62 ∧
      s'.regs 64 = s.regs 66 ∧ s'.regs 57 = 1 ∧
      Keeps [54, 55, 58, 62, 63, 64, 57] [] s s' := by
  obtain ⟨s₁, he₁, hp₁, hq₁, hk₁⟩ := gm06Alg511SwapWordsProg_exec
    54 55 58 (by decide) (by decide) (by decide) s hp hq
  have ha₁ : s₁.regs 62 = s.regs 62 := hk₁.1 62 (by decide)
  have hb₁ : s₁.regs 63 = s.regs 63 := hk₁.1 63 (by decide)
  obtain ⟨s₂, he₂, ha₂, hb₂, hk₂⟩ := gm06Alg511SwapWordsProg_exec
    62 63 58 (by decide) (by decide) (by decide) s₁ (ha₁ ▸ ha) (hb₁ ▸ hb)
  have hden : s₂.regs 66 = s.regs 66 :=
    (hk₂.1 66 (by decide)).trans (hk₁.1 66 (by decide))
  let s₃ := s₂.setReg 64 (s.regs 66)
  let s₄ := s₃.setReg 57 1
  have he₃ : Exec w (.assign 64 (.reg 66)) s₂ s₃ 2 := .assign (Crossing.eval_reg hden hd)
  have he₄ : Exec w (.assign 57 (.const 1)) s₃ s₄ 2 := .assign (Crossing.eval_const hw)
  have hk₁' : Keeps [54, 55, 58, 62, 63, 64, 57] [] s s₁ := hk₁.mono (by simp) (by simp)
  have hk₂' := hk₁'.trans hk₂ (by simp) (by simp)
  refine ⟨s₄, .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, ?_, ?_, ?_,
    by simp [s₄, s₃], by simp [s₄], (hk₂'.setReg (by simp) _).setReg (by simp) _⟩
  · simpa only [s₄, s₃, State.setReg_regs_ne _ _ (by decide : 54 ≠ 57),
      State.setReg_regs_ne _ _ (by decide : 54 ≠ 64)] using (hk₂.1 54 (by decide)).trans hp₁
  · simpa only [s₄, s₃, State.setReg_regs_ne _ _ (by decide : 55 ≠ 57),
      State.setReg_regs_ne _ _ (by decide : 55 ≠ 64)] using (hk₂.1 55 (by decide)).trans hq₁
  · simpa [s₄, s₃] using ha₂.trans hb₁
  · simpa [s₄, s₃] using hb₂.trans ha₁

/-- Keep the original orientation, restore the target denominator
and set orientation flag zero. -/
def gm06Alg511KeepScalarsProg : Cmd :=
  .seq (.assign 64 (.reg 66)) (.assign 57 (.const 0))

/-- Retaining scalar signs takes four steps and preserves all arrays. -/
theorem gm06Alg511KeepScalarsProg_exec {w : ℕ} (s : State) (hd : s.regs 66 < 2 ^ w) :
    ∃ s', Exec w gm06Alg511KeepScalarsProg s s' 4 ∧
      s'.regs 64 = s.regs 66 ∧ s'.regs 57 = 0 ∧ Keeps [64, 57] [] s s' := by
  let s₁ := s.setReg 64 (s.regs 66)
  let s₂ := s₁.setReg 57 0
  refine ⟨s₂, .seq (.assign (Crossing.eval_reg rfl hd))
    (.assign (Crossing.eval_const (Nat.two_pow_pos w))), by simp [s₂, s₁], by simp [s₂],
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _⟩

end GraphMinor.Compute
