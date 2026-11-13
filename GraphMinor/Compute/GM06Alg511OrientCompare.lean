module

public import GraphMinor.Compute.GM06Alg511OrientBranch
public import GraphMinor.Compute.GM06Alg511CompareWinding
import Mathlib.Tactic

/-!
# Comparing and choosing the initial orientation

For VI (5.11), page 134, compare the computed current winding with
the supplied target and execute the corresponding orientation branch.
The resulting current value is at most the resulting target. Its
finite cuff and signed-turn tables describe exactly the chosen
orientation. The comparison bit is produced by the program itself.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Rational value of the current signed winding numerator and path count. -/
noncomputable def gm06Alg511CurrentValue (s : State) : ℝ :=
  ((s.regs 54 : ℝ) - (s.regs 55 : ℝ)) / s.regs 52

/-- Rational value of the normalized signed target and saved denominator. -/
noncomputable def gm06Alg511TargetValue (s : State) : ℝ :=
  ((s.regs 62 : ℝ) - (s.regs 63 : ℝ)) / s.regs 66

/-- Compare the winding values, then choose and record the orientation. -/
def gm06Alg511OrientCompareProg : Cmd :=
  .seq gm06Alg511CompareWindingProg gm06Alg511OrientBranchProg

private theorem pair_value (p q k : ℕ) (flip : Bool) :
    (((if flip then q else p : ℕ) : ℝ) - ((if flip then p else q : ℕ) : ℝ)) / k =
      if flip then -(((p : ℝ) - q) / k) else ((p : ℝ) - q) / k := by
  cases flip with
  | false => rfl
  | true =>
    change ((q : ℝ) - p) / k = -(((p : ℝ) - q) / k)
    ring

private theorem chosen_values_le (u v : ℝ) (flip : Bool) (h : flip = true ↔ v < u) :
    (if flip then -u else u) ≤ if flip then -v else v := by
  cases flip with
  | false =>
    have hn : ¬ v < u := fun hv => Bool.false_ne_true (h.mpr hv)
    exact le_of_not_gt hn
  | true =>
    exact neg_le_neg (le_of_lt (h.mp rfl))

/-- The comparison-and-orientation program computes its own mode
bit, puts the current winding below the target, and outputs exactly
the drawing tables and scalar signs for that orientation. -/
theorem gm06Alg511OrientCompareProg_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G)
    (hlen : x.edgeTurns.length = rep.pairs.length) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (helen : 2 * x.edgeTurns.length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511TurnWords x.edgeTurns, v + 1 < 2 ^ w)
    (hi : x.drawing.innerCuff.length < 2 ^ w) (ho : x.drawing.outerCuff.length < 2 ^ w)
    (hiwords : ∀ v ∈ x.drawing.innerCuff, v < 2 ^ w)
    (howords : ∀ v ∈ x.drawing.outerCuff, v < 2 ^ w)
    (hind : x.drawing.innerCuff.Nodup) (hond : x.drawing.outerCuff.Nodup)
    (hends : s.arrs 3 = x.drawing.endpoints)
    (hturns : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hinner : s.arrs 1004 = x.drawing.innerCuff) (houter : s.arrs 1006 = x.drawing.outerCuff)
    (hN : s.regs 41 = x.drawing.vertexCount)
    (hp : s.regs 54 < 2 ^ w) (hq : s.regs 55 < 2 ^ w)
    (ha : s.regs 62 < 2 ^ w) (hb : s.regs 63 < 2 ^ w)
    (hkfit : s.regs 52 < 2 ^ w) (hd : s.regs 66 < 2 ^ w)
    (hkpos : 0 < s.regs 52) (hdpos : 0 < s.regs 66) (hden : s.regs 64 = s.regs 66)
    (hleft : s.regs 55 * s.regs 66 + s.regs 62 * s.regs 52 < 2 ^ w)
    (hright : s.regs 54 * s.regs 66 + s.regs 63 * s.regs 52 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (flip : Bool), Exec w gm06Alg511OrientCompareProg s s' t ∧
      t ≤ 57 + x.drawing.vertexCount *
        (41 + 13 * x.drawing.innerCuff.length + 13 * x.drawing.outerCuff.length) +
        78 * x.edgeTurns.length + 16 * x.drawing.innerCuff.length + 16 * x.drawing.outerCuff.length ∧
      Keeps [56, 77, 20, 64, 65, 54, 55, 58, 62, 63, 57] [1200, 1201, 1210, 1211] s s' ∧
      s'.arrs 1201 = gm06Alg511TurnWords (if flip then x.reflected else x).edgeTurns ∧
      s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
      s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
      s'.regs 57 = (if flip then 1 else 0) ∧ (flip = true ↔ gm06Alg511TargetValue s < gm06Alg511CurrentValue s) ∧
      gm06Alg511CurrentValue s' = (if flip then -gm06Alg511CurrentValue s else gm06Alg511CurrentValue s) ∧
      gm06Alg511TargetValue s' = (if flip then -gm06Alg511TargetValue s else gm06Alg511TargetValue s) ∧
      gm06Alg511CurrentValue s' ≤ gm06Alg511TargetValue s' ∧ s'.regs 64 = s'.regs 66 := by
  obtain ⟨s₁, he₁, hbit, hcmp, hk₁⟩ := gm06Alg511CompareWindingProg_exec
    (s.regs 54) (s.regs 55) (s.regs 62) (s.regs 63) (s.regs 52) (s.regs 66) s
    (by omega) hkpos hdpos hp hq ha hb hkfit hd hleft hright rfl rfl rfl rfl rfl hden
  change s₁.regs 56 = 1 ↔ gm06Alg511TargetValue s < gm06Alg511CurrentValue s at hcmp
  let flip := s₁.regs 56 == 1
  have hflag : s₁.regs 56 = if flip then 1 else 0 := by
    rcases hbit with hzero | hone
    · simp [flip, hzero]
    · simp [flip, hone]
  have hchosen : flip = true ↔ gm06Alg511TargetValue s < gm06Alg511CurrentValue s := by
    simpa only [flip, beq_iff_eq] using hcmp
  have hp₁ : s₁.regs 54 = s.regs 54 := hk₁.1 54 (by decide)
  have hq₁ : s₁.regs 55 = s.regs 55 := hk₁.1 55 (by decide)
  have ha₁ : s₁.regs 62 = s.regs 62 := hk₁.1 62 (by decide)
  have hb₁ : s₁.regs 63 = s.regs 63 := hk₁.1 63 (by decide)
  have hd₁ : s₁.regs 66 = s.regs 66 := hk₁.1 66 (by decide)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hnewturns, hnewinner, hnewouter, hP, hQ, hA, hB, hD, hmode⟩ :=
    gm06Alg511OrientBranchProg_exec x rep hlen flip s₁ hw hn helen hwords hi ho hiwords howords
      hind hond ((hk₁.2 3 (by simp)).trans hends) ((hk₁.2 11 (by simp)).trans hturns)
      ((hk₁.2 1004 (by simp)).trans hinner) ((hk₁.2 1006 (by simp)).trans houter)
      ((hk₁.1 41 (by decide)).trans hN)
      (hp₁ ▸ hp) (hq₁ ▸ hq) (ha₁ ▸ ha) (hb₁ ▸ hb) (hd₁ ▸ hd) hflag
  have hK : s₂.regs 52 = s.regs 52 := (hk₂.1 52 (by decide)).trans (hk₁.1 52 (by decide))
  have hden₂ : s₂.regs 66 = s.regs 66 := (hk₂.1 66 (by decide)).trans hd₁
  have hcurrent : gm06Alg511CurrentValue s₂ =
      if flip then -gm06Alg511CurrentValue s else gm06Alg511CurrentValue s := by
    dsimp only [gm06Alg511CurrentValue]
    rw [hP, hQ, hK, hp₁, hq₁]
    exact pair_value _ _ _ flip
  have htarget : gm06Alg511TargetValue s₂ =
      if flip then -gm06Alg511TargetValue s else gm06Alg511TargetValue s := by
    dsimp only [gm06Alg511TargetValue]
    rw [hA, hB, hden₂, ha₁, hb₁]
    exact pair_value _ _ _ flip
  have hk₁' : Keeps [56, 77, 20, 64, 65, 54, 55, 58, 62, 63, 57] [1200, 1201, 1210, 1211] s s₁ :=
    hk₁.mono (by simp) (by simp)
  refine ⟨s₂, 16 + t₂, flip, .seq he₁ he₂, by omega,
    hk₁'.trans hk₂ (by simp) (by simp), hnewturns, hnewinner, hnewouter,
    hmode, hchosen, hcurrent, htarget, ?_, ?_⟩
  · rw [hcurrent, htarget]
    exact chosen_values_le _ _ flip hchosen
  · exact (hD.trans hd₁).trans hden₂.symm

end GraphMinor.Compute
