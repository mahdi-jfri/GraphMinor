module

public import GraphMinor.Compute.GM06Alg34DualGapClassSelect
public import GraphMinor.Compute.GM06Alg34DualGapRowProg
public import GraphMinor.Compute.GM06Alg34DualSelectedField
import Mathlib.Tactic.Ring

/-!
# Writing one computed dual division block

Compute the no-crossing row of the selected source gap, select its
region labels and write them as one length-prefixed block. The source
comes from a plain gap index register. All other input arrays and the
canonical root mask stay available for the division scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Write the complete dual division block of source gap register 7600. -/
def gm06DualGapClassRecordProg : Cmd :=
  .seq (.assign 120 (.reg 7600)) (.seq gm06GapRowProg
    (.seq gm06DualGapClassSelectProg gm06DualSelectedFieldProg))

private theorem class_record_budget (k : ℕ) :
    2 + (300 * (k + 1) ^ 3 + (100 * (k + 1) + 40 * (k + 1))) ≤ 500 * (k + 1) ^ 3 := by
  ring_nf
  omega

/-- The selected source's exact mapped dual class is appended as one
block, in cubic time in the cuff length. -/
theorem gm06DualGapClassRecordProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (hLN : L.Nodup) (hDiv : GM06.IsDivision x.divisionSet)
    (g : Fin L.length → Fin x.regions.length) (i : Fin L.length)
    {pre : List ℕ} {s : State} (hw : 2 < 2 ^ w) (hspan : L.length + 2 < 2 ^ w)
    (hdouble : 2 * L.length + 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hd : x.division.length < 2 ^ w) (hrw : x.regions.length < 2 ^ w)
    (hL : s.arrs 2 = L.map Fin.val)
    (hD : s.arrs 3 = gm06DivisionIds x.raw.division (List.replicate x.n 0))
    (hbound : s.regs 105 = L.length) (hi : s.regs 7600 = i.val)
    (hregions : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hsource : s.arrs 53 = List.range L.length)
    (hbuf : IsPrefixBuffer 55 pre (1 + (gm06DualGapClassWords x L g i).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + 1 + (gm06DualGapClassWords x L g i).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualGapClassRecordProg s s' t ∧ t ≤ 500 * (L.length + 1) ^ 3 ∧
      IsPrefixBuffer 55 (pre ++ GM06DrawingData.listWords (gm06DualGapClassWords x L g i)) cap s' ∧
      s'.regs 7804 = (pre ++ GM06DrawingData.listWords (gm06DualGapClassWords x L g i)).length ∧
      (∀ A : ℕ, A ≠ 43 → A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q < 7820 → q < 120 ∨ 126 ≤ q → q ≠ 0 →
        q < 7601 ∨ 7605 < q → q ≠ 7804 → s'.regs q = s.regs q) := by
  have hk : L.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  let s₀ := s.setReg 120 i.val
  have he₀ : Exec w (.assign 120 (.reg 7600)) s s₀ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg hi (i.isLt.trans hk))
  obtain ⟨s₁, t₁, he₁, ht₁, hrow₁, ha₁, hg₁⟩ :=
    gm06GapRowProg_exec (s := s₀) x L hLN hDiv i hw hk hdouble hn hd hL hD hbound (by simp [s₀])
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hc₂, ha₂, hg₂⟩ :=
    gm06DualGapClassSelectProg_exec x L g i hw1 hspan hrw hrow₁
      ((ha₁ 47 (by decide)).trans hregions) ((ha₁ 53 (by decide)).trans hsource)
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, _, ha₃, hg₃⟩ :=
    gm06DualSelectedFieldProg_exec (gm06DualGapClassWords x L g i) hw1
      (fun y hy => (gm06DualGapClassWords_lt x L g i hy).trans hrw) hfit hb₂ hc₂
      (hbuf.of_arr_eq ((ha₂ 55 (by decide)).trans (ha₁ 55 (by decide))))
      ((hg₂ 7804 (Or.inr (by decide))).trans
        ((hg₁ 7804 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hpos))
  have hl := gm06DualGapClassWords_length_le x L g i
  have hfield := Nat.mul_le_mul_left 40 (Nat.add_le_add_right hl 1)
  refine ⟨s₃, 2 + (t₁ + (t₂ + t₃)), .seq he₀ (.seq he₁ (.seq he₂ he₃)),
    (show 2 + (t₁ + (t₂ + t₃)) ≤
      2 + (300 * (L.length + 1) ^ 3 + (100 * (L.length + 1) + 40 * (L.length + 1))) by omega).trans
        (class_record_budget L.length), hb₃, hp₃, ?_, ?_⟩
  · intro A h43 h54 h55 h56
    exact (ha₃ A h55 h56).trans ((ha₂ A h54).trans (ha₁ A h43))
  · intro q hq hrange h0 houter h7804
    have h120 : q ≠ 120 := by omega
    exact (hg₃ q hq h7804).trans ((hg₂ q houter).trans
      ((hg₁ q h0 (by omega) (by omega) (by omega) (by omega) (by omega)).trans
        (State.setReg_regs_ne _ _ h120)))

end GraphMinor.Compute
