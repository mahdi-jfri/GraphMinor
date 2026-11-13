module

public import GraphMinor.Compute.GM06Alg511OrientCompare
public import GraphMinor.GM06.Alg511ReflectedInputRep
import GraphMinor.GM06.Section5ReflectionLinkage
import Mathlib.Data.List.FinRange
import Mathlib.Tactic

/-!
# Geometric correctness of the executed orientation choice

For VI (5.11), page 134, the initial winding and target are already
represented in the scalar registers. Execute the comparison and the
conditional cuff/turn-table update. The chosen drawing has a proved
input interpretation, the updated current winding is feasible there,
and it is at most the updated target. The target's answer agrees
with the original drawing by the proved geometric reflection.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The RAM orientation choice has the exact geometric meaning used
in VI (5.11): its current winding remains feasible and lies below the
target in the selected orientation. The initial feasibility and target
identities are the local postconditions of the preceding phases. -/
theorem alg511_orientation_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (helen : 2 * x.edgeTurns.length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511TurnWords x.edgeTurns, v + 1 < 2 ^ w)
    (hends : s.arrs 3 = x.drawing.endpoints)
    (hturns : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hinner : s.arrs 1004 = x.drawing.innerCuff) (houter : s.arrs 1006 = x.drawing.outerCuff)
    (hN : s.regs 41 = x.drawing.vertexCount) (hK : s.regs 52 = x.drawing.pathCount)
    (hp : s.regs 54 < 2 ^ w) (hq : s.regs 55 < 2 ^ w)
    (ha : s.regs 62 < 2 ^ w) (hb : s.regs 63 < 2 ^ w) (hd : s.regs 66 < 2 ^ w)
    (hdpos : 0 < s.regs 66) (hden : s.regs 64 = s.regs 66)
    (hleft : s.regs 55 * s.regs 66 + s.regs 62 * s.regs 52 < 2 ^ w)
    (hright : s.regs 54 * s.regs 66 + s.regs 63 * s.regs 52 < 2 ^ w)
    (hcurrent : IsThetaFeasible x.drawing.pathCount G (gm06Alg511CurrentValue s))
    (htarget : gm06Alg511TargetValue s = x.drawing.target) :
    ∃ (s' : State) (t : ℕ) (flip : Bool), Exec w gm06Alg511OrientCompareProg s s' t ∧
      t ≤ 57 + x.drawing.vertexCount * (41 + 26 * x.drawing.pathCount) +
        78 * x.edgeTurns.length + 32 * x.drawing.pathCount ∧
      TwoPaths.Keeps [56, 77, 20, 64, 65, 54, 55, 58, 62, 63, 57] [1200, 1201, 1210, 1211] s s' ∧
      s'.arrs 1201 = gm06Alg511TurnWords (if flip then x.reflected else x).edgeTurns ∧
      s'.arrs 1210 = (if flip then x.reflected else x).drawing.innerCuff ∧
      s'.arrs 1211 = (if flip then x.reflected else x).drawing.outerCuff ∧
      s'.regs 57 = (if flip then 1 else 0) ∧ s'.regs 52 = x.drawing.pathCount ∧
      Nonempty (GM06Alg511GraphTurnRep (if flip then x.reflected else x)
        (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)) ∧
      IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
        (if flip then section5ReflectedDrawing x.drawing.pathCount G else G) (gm06Alg511CurrentValue s') ∧
      gm06Alg511TargetValue s' = (if flip then x.reflected else x).drawing.target ∧
      gm06Alg511CurrentValue s' ≤ gm06Alg511TargetValue s' ∧
      (IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
        (if flip then section5ReflectedDrawing x.drawing.pathCount G else G) (gm06Alg511TargetValue s') ↔
          IsThetaFeasible x.drawing.pathCount G x.drawing.target) := by
  have hiLen : x.drawing.innerCuff.length = x.drawing.pathCount := by rw [rep.inner, List.length_ofFn]
  have hoLen : x.drawing.outerCuff.length = x.drawing.pathCount := by rw [rep.outer, List.length_ofFn]
  have hkfit : x.drawing.pathCount < 2 ^ w := (rep.pathCount_le_vertexCount hk).trans_lt hn
  have hiwords : ∀ v ∈ x.drawing.innerCuff, v < 2 ^ w := by
    intro v hv
    rw [rep.inner] at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.source i).isLt.trans hn
  have howords : ∀ v ∈ x.drawing.outerCuff, v < 2 ^ w := by
    intro v hv
    rw [rep.outer] at hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact (rep.target i).isLt.trans hn
  have hind : x.drawing.innerCuff.Nodup := by
    rw [rep.inner]
    exact List.nodup_ofFn_ofInjective (Fin.val_injective.comp (rep.source_injective hk))
  have hond : x.drawing.outerCuff.Nodup := by
    rw [rep.outer]
    exact List.nodup_ofFn_ofInjective (Fin.val_injective.comp (rep.target_injective hk))
  obtain ⟨_, _, _, _, hturnlen, _⟩ := rep.turns
  obtain ⟨s', t, flip, he, ht, hkeep, hnewturns, hnewinner, hnewouter, hmode, _, hcur, htar, hle, _⟩ :=
    gm06Alg511OrientCompareProg_exec x rep.graph hturnlen s hw hn helen hwords
      (hiLen ▸ hkfit) (hoLen ▸ hkfit) hiwords howords hind hond hends hturns hinner houter hN
      hp hq ha hb (hK ▸ hkfit) hd (hK ▸ hk) hdpos hden hleft hright
  have hrepresentation : Nonempty (GM06Alg511GraphTurnRep (if flip then x.reflected else x)
      (if flip then section5ReflectedDrawing x.drawing.pathCount G else G)) := by
    cases flip with
    | false => exact ⟨rep⟩
    | true => exact ⟨alg511ReflectedInputRep rep hk⟩
  have hfeasible : IsThetaFeasible (if flip then x.reflected else x).drawing.pathCount
      (if flip then section5ReflectedDrawing x.drawing.pathCount G else G) (gm06Alg511CurrentValue s') := by
    cases flip with
    | false => rw [hcur]; exact hcurrent
    | true => rw [hcur]; exact isThetaFeasible_reflected_of_feasible hk hcurrent
  have htarget' : gm06Alg511TargetValue s' = (if flip then x.reflected else x).drawing.target := by
    cases flip with
    | false => rw [htar]; exact htarget
    | true => rw [htar, htarget]; exact (alg511_reflected_target x).symm
  refine ⟨s', t, flip, he, ?_, hkeep, hnewturns, hnewinner, hnewouter, hmode,
    (hkeep.1 52 (by decide)).trans hK, hrepresentation, hfeasible, htarget', hle, ?_⟩
  · rw [hiLen, hoLen] at ht
    nlinarith only [ht]
  · rw [htarget']
    cases flip with
    | false => rfl
    | true => exact alg511_reflected_target_feasible_iff hk

end GraphMinor.GM06
