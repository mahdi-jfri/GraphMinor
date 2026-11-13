module

public import GraphMinor.Compute.Algorithm77Prog
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Passing the selected dart prefix to the signed accumulator

The edge-selection phase of VI (5.11), page 134, stores darts in a
capacity-sized buffer. Copy only its proved prefix to array 12, whose
length is the iteration count used by the signed accumulator. The
copy preserves the signed turn words in array 11.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Materialize the dart prefix of buffer 13, length register 49,
in the signed accumulator's array 12. -/
def gm06Alg511CopyDartsProg : Cmd :=
  .seq (.assign 8 (.const 0))
    (.seq (.assign 9 (.reg 49)) (copySliceToArrCmd 13 12))

/-- Copying a proved dart prefix takes linear time and preserves all
other arrays and every register outside the copy's scratch set. -/
theorem gm06Alg511CopyDartsProg_exec {w : ℕ} (cap : ℕ) (darts : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w)
    (hbuf : IsBufPrefix s 13 49 cap darts)
    (hwords : ∀ d ∈ darts, d < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511CopyDartsProg s s' t ∧
      t ≤ 10 + 22 * darts.length ∧ s'.arrs 12 = darts ∧
      Keeps [7, 8, 9, 11] [12] s s' := by
  let s₁ := s.setReg 8 0
  let s₂ := s₁.setReg 9 darts.length
  have he₁ : Exec w (.assign 8 (.const 0)) s s₁ 2 :=
    .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 9 (.reg 49)) s₁ s₂ 2 :=
    .assign (Crossing.eval_reg (by simpa [s₁] using hbuf.2.1) (hbuf.2.2.1.trans_lt hcap))
  obtain ⟨s₃, t₃, he₃, ht₃, hout, _, hregs, harrs⟩ :=
    copySliceToArrCmd_exec 13 12 (by decide) darts 0 (s := s₂) hw
      (by simpa [s₂, s₁, hbuf.1] using hcap)
      (by simpa [s₂, s₁, hbuf.1] using hbuf.2.2.1)
      (fun j hj => by simpa [s₂, s₁] using hbuf.2.2.2 j hj)
      hwords (by simp [s₂, s₁]) (by simp [s₂])
  refine ⟨s₃, 2 + (2 + t₃), .seq he₁ (.seq he₂ he₃), by omega, hout, ?_⟩
  constructor
  · intro r hr
    have h7 : r ≠ 7 := by simp only [List.mem_cons] at hr; tauto
    have h8 : r ≠ 8 := by simp only [List.mem_cons] at hr; tauto
    have h9 : r ≠ 9 := by simp only [List.mem_cons] at hr; tauto
    have h11 : r ≠ 11 := by simp only [List.mem_cons] at hr; tauto
    rw [hregs r h7 h8 h9 h11]
    simp [s₂, s₁, h8, h9]
  · intro a ha
    simpa [s₂, s₁] using harrs a (by simpa using ha)

end GraphMinor.Compute
