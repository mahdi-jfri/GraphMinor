module

public import GraphMinor.Compute.GM06Alg511ReflectionTables
public import GraphMinor.Compute.GM06Alg511SwapWords
import Mathlib.Tactic

/-!
# The reflected orientation branch

For VI (5.11), page 134, compute the reflected signed edge and cuff
tables, negate the current and target winding numerators, and restore
the saved target denominator. The scalar sign changes preserve their
magnitudes. Every original graph and flow array remains available.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Build reflected drawing tables and change both winding signs. -/
def gm06Alg511FlipTablesProg : Cmd :=
  .seq gm06Alg511ReflectionTablesProg gm06Alg511FlipScalarsProg

/-- The reflected branch returns exactly the finite reflected tables
and negated scalar pairs, with a polynomial time bound. -/
theorem gm06Alg511FlipTablesProg_exec {w : ℕ} (x : GM06Alg511WindingInput)
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
    (ha : s.regs 62 < 2 ^ w) (hb : s.regs 63 < 2 ^ w) (hd : s.regs 66 < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511FlipTablesProg s s' t ∧
      t ≤ 40 + x.drawing.vertexCount *
        (41 + 13 * x.drawing.innerCuff.length + 13 * x.drawing.outerCuff.length) +
        78 * x.edgeTurns.length + 16 * x.drawing.innerCuff.length + 16 * x.drawing.outerCuff.length ∧
      Keeps [77, 20, 64, 65, 54, 55, 58, 62, 63, 57] [1200, 1201, 1210, 1211] s s' ∧
      s'.arrs 1201 = gm06Alg511TurnWords x.reflected.edgeTurns ∧
      s'.arrs 1210 = x.reflected.drawing.innerCuff ∧ s'.arrs 1211 = x.reflected.drawing.outerCuff ∧
      s'.regs 54 = s.regs 55 ∧ s'.regs 55 = s.regs 54 ∧
      s'.regs 62 = s.regs 63 ∧ s'.regs 63 = s.regs 62 ∧
      s'.regs 64 = s.regs 66 ∧ s'.regs 57 = 1 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hnewturns, hnewinner, hnewouter⟩ :=
    gm06Alg511ReflectionTablesProg_exec x rep hlen s hw hn helen hwords hi ho hiwords howords
      hind hond hends hturns hinner houter hN
  have hp₁ : s₁.regs 54 = s.regs 54 := hk₁.1 54 (by decide)
  have hq₁ : s₁.regs 55 = s.regs 55 := hk₁.1 55 (by decide)
  have ha₁ : s₁.regs 62 = s.regs 62 := hk₁.1 62 (by decide)
  have hb₁ : s₁.regs 63 = s.regs 63 := hk₁.1 63 (by decide)
  have hd₁ : s₁.regs 66 = s.regs 66 := hk₁.1 66 (by decide)
  obtain ⟨s₂, he₂, hP, hQ, hA, hB, hD, hmode, hk₂⟩ := gm06Alg511FlipScalarsProg_exec s₁
    (by omega) (hp₁ ▸ hp) (hq₁ ▸ hq) (ha₁ ▸ ha) (hb₁ ▸ hb) (hd₁ ▸ hd)
  have hk₁' : Keeps [77, 20, 64, 65, 54, 55, 58, 62, 63, 57] [1200, 1201, 1210, 1211] s s₁ :=
    hk₁.mono (by simp) (by simp)
  refine ⟨s₂, t₁ + 16, .seq he₁ he₂, by omega, hk₁'.trans hk₂ (by simp) (by simp),
    (hk₂.2 1201 (by simp)).trans hnewturns, (hk₂.2 1210 (by simp)).trans hnewinner,
    (hk₂.2 1211 (by simp)).trans hnewouter,
    hP.trans hq₁, hQ.trans hp₁, hA.trans hb₁, hB.trans ha₁, hD.trans hd₁, hmode⟩

end GraphMinor.Compute
