module

public import GraphMinor.GM06.Alg34LoopStartExec
public import GraphMinor.GM06.Alg34CrossFree
import GraphMinor.Compute.GM06Alg34DriverControlFrames
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Correct execution of the complete disc program

The first scan either rejects a crossing division or establishes the
geometric condition required by the reduction loop. Initialize that
loop from the supplied arrays, execute it to termination, and copy its
saved Boolean to the output register. All scratch contents are arbitrary.
-/

public section
namespace GraphMinor.Compute
open GM06
universe u

/-- Exact full-program correctness for every represented disc instance,
with the sum of initialization, scan, and loop time bounds. -/
theorem gm06Alg34Prog_exec {X : GM06GapInput} {I : DiscDivInstance.{u}}
    (h : GM06GapInputRep X I.G I.Δ) {s : State}
    (hin : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    let Q := X.drawing.size + X.discGapWords.length
    ∃ b s' t, Exec (wordSize 256 Q) gm06Alg34Prog s s' t ∧
      t ≤ 452 * (Q + 2) ^ 4 + (Q + 2) ^ 16 + 50 +
        (gm06RoundBound Q + 1) * (3 * (Q + 2) ^ 2) ∧
      s'.regs 0 = (if b then 1 else 0) ∧ (I.IsFeasibleInst ↔ b = true) := by
  let Q := X.drawing.size + X.discGapWords.length
  have hB := gm06LoopBounds_initial X Q (show X.drawing.size ≤ Q from Nat.le_add_right _ _)
  have hsize := gm06LoopBounds_size hB
  obtain ⟨L, hL⟩ := h.drawing.exists_cuff_list I.hDisc
  obtain ⟨s₁, t₁, he₁, ht₁, hflag, hi₁⟩ := gm06CheckCrossFreeProg_exec X.drawing hL
    (h.drawing.cuff_nodup L (by simp [hL])) (h.drawing.division_isDivision I.hΔ)
    (c := 21) (by decide) hin
  have he₁' := he₁.mono_wordSize (gm06Uniform_wordSize Q _ hsize)
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  have hscan : t₁ ≤ 452 * (Q + 2) ^ 4 := ht₁.trans (Nat.mul_le_mul_left 452
    (Nat.pow_le_pow_left (show X.drawing.size + 1 ≤ Q + 2 by dsimp only [Q]; omega) 4))
  let b₀ := X.drawing.crossFree
  let s₂ := s₁.setReg 9001 (if b₀ then 1 else 0)
  have hflag' : s₁.regs 0 = (if b₀ then 1 else 0) := hflag
  have hfit : (if b₀ then 1 else 0) < 2 ^ wordSize 256 Q := by cases b₀ <;> simp_all
  have he₂ : Exec (wordSize 256 Q) (.assign 9001 (.reg 0)) s₁ s₂ 2 :=
    .assign (Crossing.eval_reg hflag' hfit)
  have hg₂ : s₂.arrs 47 = X.discGapWords :=
    (gm06CheckCrossFree_gap_frame he₁).trans hgap
  have hreg₂ : s₂.regs 9001 = (if b₀ then 1 else 0) := rfl
  cases hcf : X.drawing.crossFree with
  | false =>
    have hr : s₂.regs 9001 = 0 := by simpa only [b₀, hcf, Bool.false_eq_true, ↓reduceIte] using hreg₂
    let s₃ := s₂.setReg 0 0
    have he₃ : Exec (wordSize 256 Q) (.assign 0 (.reg 9001)) s₂ s₃ 2 :=
      .assign (Crossing.eval_reg hr (Nat.two_pow_pos _))
    have hno : ¬ I.IsFeasibleInst := by
      intro hf
      have hh := (alg34_rep_crossFree_iff h.drawing).mpr (isCrossFree_of_isFeasible I.hDisc hf)
      rw [hcf] at hh
      cases hh
    refine ⟨false, s₃, t₁ + (2 + (2 + 2)), .seq he₁' (.seq he₂
      (.seq (.ite_false (Crossing.eval_reg hr (Nat.two_pow_pos _)) (.skip s₂)) he₃)), ?_, rfl, ?_⟩
    · change t₁ + (2 + (2 + 2)) ≤ 452 * (Q + 2) ^ 4 + (Q + 2) ^ 16 + 50 + _
      omega
    · simp only [Bool.false_eq_true, iff_false]; exact hno
  | true =>
    have hr : s₂.regs 9001 = 1 := by simpa only [b₀, hcf, ↓reduceIte] using hreg₂
    have hX : gm06LoopInstance.{u} X :=
      ⟨I, ⟨h⟩, (alg34_rep_crossFree_iff h.drawing).mp hcf⟩
    obtain ⟨b, s₃, t₃, he₃, ht₃, hb, hf⟩ := gm06Driver_start X hX
      (show s₂.arrs 0 = X.drawing.words from hi₁) hg₂
    have hbfit : (if b then 1 else 0) < 2 ^ wordSize 256 Q := by cases b <;> simp_all
    let s₄ := s₃.setReg 0 (if b then 1 else 0)
    have he₄ : Exec (wordSize 256 Q) (.assign 0 (.reg 9001)) s₃ s₄ 2 :=
      .assign (Crossing.eval_reg hb hbfit)
    refine ⟨b, s₄, t₁ + (2 + ((1 + t₃) + 2)), .seq he₁' (.seq he₂
      (.seq (.ite_true (Crossing.eval_reg hr hw) (by decide) he₃) he₄)), ?_, rfl,
      (h.drawing.feasible_iff I.hΔ).trans hf⟩
    change t₃ ≤ (Q + 2) ^ 16 + 43 + (gm06RoundBound Q + 1) * (3 * (Q + 2) ^ 2) at ht₃
    change t₁ + (2 + ((1 + t₃) + 2)) ≤ 452 * (Q + 2) ^ 4 + (Q + 2) ^ 16 + 50 +
      (gm06RoundBound Q + 1) * (3 * (Q + 2) ^ 2)
    omega

end GraphMinor.Compute
