module

public import GraphMinor.Compute.GM06Alg511ReflectTurnsProg
public import GraphMinor.Compute.GM06Alg511ReflectCuff
import Mathlib.Tactic

/-!
# Computing the reflected cuff and turn tables

For VI (5.11), page 134, compute the vertex reference corrections,
use them to reflect the signed edge words, and reverse the prescribed
cuff indexing. The outputs are exactly the corresponding fields of
the proved finite reflected input. The original graph and flow arrays
remain available for the orientation branch.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Build reflected signed words 1201 and cuff rows 1210/1211,
using correction scratch array 1200. -/
def gm06Alg511ReflectionTablesProg : Cmd :=
  .seq gm06Alg511OffsetProg (.seq gm06Alg511ReflectTurnsProg
    (.seq (gm06Alg511ReflectCuffProg 1004 1210) (gm06Alg511ReflectCuffProg 1006 1211)))

/-- The computed reflected tables agree with the plain finite
reflection map, with an explicit polynomial running time. -/
theorem gm06Alg511ReflectionTablesProg_exec {w : ℕ} (x : GM06Alg511WindingInput)
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
    (hN : s.regs 41 = x.drawing.vertexCount) :
    ∃ s' t, Exec w gm06Alg511ReflectionTablesProg s s' t ∧
      t ≤ 24 + x.drawing.vertexCount *
        (41 + 13 * x.drawing.innerCuff.length + 13 * x.drawing.outerCuff.length) +
        78 * x.edgeTurns.length + 16 * x.drawing.innerCuff.length + 16 * x.drawing.outerCuff.length ∧
      Keeps [77, 20, 64, 65] [1200, 1201, 1210, 1211] s s' ∧
      s'.arrs 1201 = gm06Alg511TurnWords x.reflected.edgeTurns ∧
      s'.arrs 1210 = x.reflected.drawing.innerCuff ∧ s'.arrs 1211 = x.reflected.drawing.outerCuff := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hoffsets⟩ := gm06Alg511OffsetProg_exec x.drawing s hw hn
    hi ho hiwords howords hind hond hinner houter hN
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hnewturns⟩ := gm06Alg511ReflectTurnsProg_exec x rep hlen s₁
    hw hn helen hwords ((hk₁.2 3 (by decide)).trans hends)
    ((hk₁.2 11 (by decide)).trans hturns) hoffsets
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hnewinner⟩ := gm06Alg511ReflectCuffProg_exec
    1004 1210 (by decide) x.drawing.innerCuff s₂ (by omega) hi hiwords
    ((hk₂.2 1004 (by decide)).trans ((hk₁.2 1004 (by decide)).trans hinner))
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hnewouter⟩ := gm06Alg511ReflectCuffProg_exec
    1006 1211 (by decide) x.drawing.outerCuff s₃ (by omega) ho howords
    ((hk₃.2 1006 (by decide)).trans ((hk₂.2 1006 (by decide)).trans ((hk₁.2 1006 (by decide)).trans houter)))
  have hk₁' : Keeps [77, 20, 64, 65] [1200, 1201, 1210, 1211] s s₁ :=
    hk₁.mono (by simp) (by simp)
  have hk₂' := hk₁'.trans hk₂ (by simp) (by simp)
  have hk₃' := hk₂'.trans hk₃ (by simp) (by simp)
  have hk₄' := hk₃'.trans hk₄ (by simp) (by simp)
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), by omega,
    hk₄', ?_, ?_, hnewouter⟩
  · rw [hk₄.2 1201 (by decide), hk₃.2 1201 (by decide), hnewturns]
  · rw [hk₄.2 1210 (by decide)]
    exact hnewinner

end GraphMinor.Compute
