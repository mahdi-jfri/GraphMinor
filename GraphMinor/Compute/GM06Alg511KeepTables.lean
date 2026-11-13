module

public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06Alg511SwapWords
public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511TurnWords
import Mathlib.Tactic

/-!
# Retaining the original orientation in the common output tables

For VI (5.11), page 134, when the initial winding is already at most
the target, keep the original drawing. Copy its signed turn and cuff
rows to the same output locations used by the reflected branch.
Restore the saved target denominator and record orientation zero.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy original turn and cuff rows to common orientation outputs,
then retain the scalar signs and set orientation flag zero. -/
def gm06Alg511KeepTablesProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 11 1201)
    (.seq (gm06Alg511CopyRowProg 1004 1210)
      (.seq (gm06Alg511CopyRowProg 1006 1211) gm06Alg511KeepScalarsProg))

/-- The original-orientation branch preserves the represented drawing
and scalar signs while presenting its data in common output arrays. -/
theorem gm06Alg511KeepTablesProg_exec {w : ℕ} (x : GM06Alg511WindingInput) (s : State)
    (hw : 1 < 2 ^ w) (helen : 2 * x.edgeTurns.length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511TurnWords x.edgeTurns, v < 2 ^ w)
    (hi : x.drawing.innerCuff.length < 2 ^ w) (ho : x.drawing.outerCuff.length < 2 ^ w)
    (hiwords : ∀ v ∈ x.drawing.innerCuff, v < 2 ^ w)
    (howords : ∀ v ∈ x.drawing.outerCuff, v < 2 ^ w)
    (hturns : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hinner : s.arrs 1004 = x.drawing.innerCuff) (houter : s.arrs 1006 = x.drawing.outerCuff)
    (hden : s.regs 66 < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511KeepTablesProg s s' t ∧
      t ≤ 22 + 24 * x.edgeTurns.length +
        12 * x.drawing.innerCuff.length + 12 * x.drawing.outerCuff.length ∧
      Keeps [20, 64, 57] [1201, 1210, 1211] s s' ∧
      s'.arrs 1201 = gm06Alg511TurnWords x.edgeTurns ∧
      s'.arrs 1210 = x.drawing.innerCuff ∧ s'.arrs 1211 = x.drawing.outerCuff ∧
      s'.regs 64 = s.regs 66 ∧ s'.regs 57 = 0 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hnewturns⟩ := gm06Alg511CopyRowProg_exec
    11 1201 (by decide) (gm06Alg511TurnWords x.edgeTurns) s hw
    (by simpa only [gm06Alg511TurnWords_length] using helen) hwords hturns
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hnewinner⟩ := gm06Alg511CopyRowProg_exec
    1004 1210 (by decide) x.drawing.innerCuff s₁ hw hi hiwords
    ((hk₁.2 1004 (by decide)).trans hinner)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hnewouter⟩ := gm06Alg511CopyRowProg_exec
    1006 1211 (by decide) x.drawing.outerCuff s₂ hw ho howords
    ((hk₂.2 1006 (by decide)).trans ((hk₁.2 1006 (by decide)).trans houter))
  have hd₃ : s₃.regs 66 = s.regs 66 :=
    (hk₃.1 66 (by decide)).trans ((hk₂.1 66 (by decide)).trans (hk₁.1 66 (by decide)))
  obtain ⟨s₄, he₄, hden₄, hmode, hk₄⟩ := gm06Alg511KeepScalarsProg_exec s₃ (hd₃ ▸ hden)
  have hk₁' : Keeps [20, 64, 57] [1201, 1210, 1211] s s₁ := hk₁.mono (by simp) (by simp)
  have hk₂' := hk₁'.trans hk₂ (by simp) (by simp)
  have hk₃' := hk₂'.trans hk₃ (by simp) (by simp)
  have hk₄' := hk₃'.trans hk₄ (by simp) (by simp)
  refine ⟨s₄, t₁ + (t₂ + (t₃ + 4)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_,
    hk₄', ?_, ?_, ?_, hden₄.trans hd₃, hmode⟩
  · rw [gm06Alg511TurnWords_length] at ht₁
    omega
  · rw [hk₄.2 1201 (by simp), hk₃.2 1201 (by decide), hk₂.2 1201 (by decide), hnewturns]
  · rw [hk₄.2 1210 (by simp), hk₃.2 1210 (by decide), hnewinner]
  · rw [hk₄.2 1211 (by simp), hnewouter]

end GraphMinor.Compute
