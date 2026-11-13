module

public import GraphMinor.Compute.GM06EitherEndSector

/-!
# Sector queries restricted to active edges

Deleted edges retain their original directed labels but have a zero
activity flag. Read the activity bit before testing the two directed
ends. The resulting flag selects exactly active edges with an end in
the chosen rotation sector, without changing the arrays.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Test an edge's two directed ends only when its activity flag is one. -/
def gm06ActiveEdgeSectorProg (rot active : Arr) : Cmd :=
  .ite (.op .eq (.read active (.reg 53)) (.const 1))
    (gm06EitherEndSectorProg rot) (.assign 43 (.const 0))

/-- The active-edge query computes exactly the activity-and-sector condition. -/
theorem gm06ActiveEdgeSectorProg_exec {w : ℕ} (rot active : ℕ) (xs mask : List ℕ)
    (p q e : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (he : e < mask.length)
    (hm : 2 * mask.length < 2 ^ w) (hbits : ∀ b ∈ mask, b ≤ 1)
    (ha : s.arrs rot = xs) (hb : s.arrs active = mask)
    (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) (h53 : s.regs 53 = e) :
    ∃ s' t, Exec w (gm06ActiveEdgeSectorProg rot active) s s' t ∧
      t ≤ 108 + 104 * xs.length ∧ Keeps [38, 50, 40, 41, 42, 43, 54] [] s s' ∧
      (s'.regs 43 = 1 ↔ mask[e] = 1 ∧
        (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
          gm06RotationSectorFlag xs p q (2 * e + 1) = 1)) ∧
      (s'.regs 43 = 0 ∨ s'.regs 43 = 1) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hew : e < 2 ^ w := by omega
  have hread := GraphMinor.Compute.Crossing.eval_read (a := active)
    (GraphMinor.Compute.Crossing.eval_reg h53 hew)
    (by simpa only [hb] using he)
    (by simpa only [hb] using (hbits mask[e] (List.getElem_mem he)).trans_lt hw1)
  simp only [hb] at hread
  have hc := GraphMinor.Compute.Crossing.eval_eq hread
    (GraphMinor.Compute.Crossing.eval_const hw1) hw1
  by_cases hact : mask[e] = 1
  · obtain ⟨s', t, he', ht, hk, hf, hbit⟩ := gm06EitherEndSectorProg_exec rot xs
      p q e mask.length s hw hn hx hnd hp hq he hm ha h36 h37 h53
    refine ⟨s', 4 + t, .ite_true (by simpa only [hact, ite_true] using hc) (by decide) he',
      by omega, hk, ?_, hbit⟩
    simpa only [hact, true_and] using hf
  · let s' := s.setReg 43 0
    have he' : Exec w (.assign 43 (.const 0)) s s' 2 :=
      .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
    refine ⟨s', 6, .ite_false (by simpa only [hact, ite_false] using hc) he', by omega,
      (Keeps.refl _ _ s).setReg (by simp) _, ?_, ?_⟩
    · simp [s', hact]
    · simp [s']

end GraphMinor.Compute
