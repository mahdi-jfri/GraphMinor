module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Winding

/-!
# Joining the two parts of a helix

The curves in the base case of VI (5.3) meet a vertex only at their join.
Reparametrization puts that contact at time one half. Compatible angular
lifts show that their winding numbers add.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface
/-- Joining a curve with a single terminal vertex contact to one with
a single initial vertex contact gives one vertex contact, at the join. -/
theorem concatenated_vertex_hits {G : Drawing ClosedCylinder} {x v y : ClosedCylinder}
    (p : Path x v) (q : Path v y)
    (hp : ∀ t : unitInterval, p t ∈ G.V ↔ t = 1)
    (hq : ∀ t : unitInterval, q t ∈ G.V ↔ t = 0) :
    (curveVertexHits G (p.trans q).toContinuousMap).Finite ∧
      curveL G (p.trans q).toContinuousMap = 1 := by
  let mid : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have hset : curveVertexHits G (p.trans q).toContinuousMap = {mid} := by
    ext t
    change (p.trans q) t ∈ G.V ↔ t ∈ ({mid} : Set unitInterval)
    rw [Path.trans_apply]
    split_ifs with ht
    · rw [hp, mem_singleton_iff]
      constructor
      · intro hh
        apply Subtype.ext
        have he := congrArg Subtype.val hh
        change 2 * (t : ℝ) = 1 at he
        change (t : ℝ) = 1 / 2
        linarith only [he]
      · intro hh
        apply Subtype.ext
        change 2 * (t : ℝ) = 1
        have he := congrArg Subtype.val hh
        change (t : ℝ) = 1 / 2 at he
        linarith only [he]
    · rw [hq, mem_singleton_iff]
      constructor
      · intro hh
        have he := congrArg Subtype.val hh
        change 2 * (t : ℝ) - 1 = 0 at he
        have ht' : 1 / 2 < (t : ℝ) := lt_of_not_ge ht
        exact False.elim ((by linarith only [he, ht'] : False))
      · intro hh
        have he := congrArg Subtype.val hh
        change (t : ℝ) = 1 / 2 at he
        exact False.elim (ht he.le)
  exact ⟨hset ▸ finite_singleton mid, by rw [curveL, hset, ncard_singleton]⟩
end GraphMinor.GM06
namespace GraphMinor.GM06
open Set GraphMinor.Surface Real
/-- The angular displacements of concatenated cylinder paths add. -/
theorem windingNumber_path_trans {x v y : ClosedCylinder} (p : Path x v) (q : Path v y) :
    windingNumber (p.trans q).toContinuousMap =
      windingNumber p.toContinuousMap + windingNumber q.toContinuousMap := by
  let a := cylinderAngleLift p.toContinuousMap
  let b := cylinderAngleLift q.toContinuousMap
  let c : C(unitInterval, ℝ) := b + ContinuousMap.const _ (a 1 - b 0)
  let pa : Path (a 0) (a 1) := ⟨a, rfl, rfl⟩
  let pb : Path (a 1) (c 1) := ⟨c, by change b 0 + (a 1 - b 0) = a 1; ring, rfl⟩
  have hshift : Circle.exp (a 1 - b 0) = 1 := by
    rw [Circle.exp_sub, exp_cylinderAngleLift, exp_cylinderAngleLift]
    change (p 1).1.2 / (q 0).1.2 = 1
    rw [Path.target, Path.source, div_self']
  have hc (t : unitInterval) : Circle.exp (c t) = (q t).1.2 := by
    change Circle.exp (b t + (a 1 - b 0)) = _
    rw [Circle.exp_add, hshift, mul_one, exp_cylinderAngleLift]
    rfl
  have hangle (t : unitInterval) :
      Circle.exp ((pa.trans pb) t) = ((p.trans q) t).1.2 := by
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with ht
    · exact exp_cylinderAngleLift _ _
    · exact hc _
  rw [windingNumber_eq_of_exp_lift (pa.trans pb).toContinuousMap hangle]
  change (((pa.trans pb) 1) - ((pa.trans pb) 0)) / (2 * π) = _
  rw [Path.target, Path.source]
  change (b 1 + (a 1 - b 0) - a 0) / (2 * π) =
    (a 1 - a 0) / (2 * π) + (b 1 - b 0) / (2 * π)
  ring
end GraphMinor.GM06
