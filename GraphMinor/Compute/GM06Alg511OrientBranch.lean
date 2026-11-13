module

public import GraphMinor.Compute.GM06Alg511FlipTables
public import GraphMinor.Compute.GM06Alg511KeepTables
import Mathlib.Tactic

/-!
# Executing the conditional orientation choice

For VI (5.11), page 134, use the computed comparison bit to choose
between the reflected and original drawing tables. Both branches
write common output arrays. The scalar numerator pairs are swapped
exactly in the reflected branch, and the mode bit records the choice.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Choose the reflected branch when comparison bit 56 is nonzero. -/
def gm06Alg511OrientBranchProg : Cmd :=
  .ite (.reg 56) gm06Alg511FlipTablesProg gm06Alg511KeepTablesProg

/-- The actual conditional program writes exactly the chosen finite
drawing tables and the corresponding scalar signs. -/
theorem gm06Alg511OrientBranchProg_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {α β : Type*} {G : Graph α β}
    (rep : GM06SuccessorGraphRep (x.drawing.withLinkage []) G)
    (hlen : x.edgeTurns.length = rep.pairs.length) (flip : Bool) (s : State)
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
    (ha : s.regs 62 < 2 ^ w) (hb : s.regs 63 < 2 ^ w) (hd : s.regs 66 < 2 ^ w)
    (hflag : s.regs 56 = if flip then 1 else 0) :
    ∃ s' t, Exec w gm06Alg511OrientBranchProg s s' t ∧
      t ≤ 41 + x.drawing.vertexCount *
        (41 + 13 * x.drawing.innerCuff.length + 13 * x.drawing.outerCuff.length) +
        78 * x.edgeTurns.length + 16 * x.drawing.innerCuff.length + 16 * x.drawing.outerCuff.length ∧
      Keeps [77, 20, 64, 65, 54, 55, 58, 62, 63, 57] [1200, 1201, 1210, 1211] s s' ∧
      s'.arrs 1201 = gm06Alg511TurnWords (if flip then x.reflected else x).edgeTurns ∧
      s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
      s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
      s'.regs 54 = (if flip then s.regs 55 else s.regs 54) ∧
      s'.regs 55 = (if flip then s.regs 54 else s.regs 55) ∧
      s'.regs 62 = (if flip then s.regs 63 else s.regs 62) ∧
      s'.regs 63 = (if flip then s.regs 62 else s.regs 63) ∧
      s'.regs 64 = s.regs 66 ∧ s'.regs 57 = (if flip then 1 else 0) := by
  cases flip with
  | false =>
    obtain ⟨s', t, he, ht, hk, hnewturns, hnewinner, hnewouter, hden, hmode⟩ :=
      gm06Alg511KeepTablesProg_exec x s (by omega) helen
        (fun v hv => (Nat.le_add_right _ _).trans_lt (hwords v hv)) hi ho hiwords howords
        hturns hinner houter hd
    refine ⟨s', 1 + t, .ite_false (Crossing.eval_reg hflag (Nat.two_pow_pos w)) he,
      by omega, hk.mono (by simp) (by simp), hnewturns, hnewinner, hnewouter,
      hk.1 54 (by decide), hk.1 55 (by decide), hk.1 62 (by decide), hk.1 63 (by decide), hden, hmode⟩
  | true =>
    obtain ⟨s', t, he, ht, hk, hnewturns, hnewinner, hnewouter, hP, hQ, hA, hB, hden, hmode⟩ :=
      gm06Alg511FlipTablesProg_exec x rep hlen s hw hn helen hwords hi ho hiwords howords
        hind hond hends hturns hinner houter hN hp hq ha hb hd
    have hf : s.regs 56 = 1 := by simpa using hflag
    refine ⟨s', 1 + t, .ite_true (Crossing.eval_reg hf (by omega)) (by decide) he,
      by omega, hk, hnewturns, hnewinner, hnewouter, hP, hQ, hA, hB, hden, hmode⟩

end GraphMinor.Compute
