module

public import GraphMinor.Compute.GM06Alg511ReflectedInput
public import GraphMinor.GM06.Alg511CuffIndices
import Mathlib.Tactic

/-!
# Integer reference corrections at reflected cuff vertices

In VI (5.11), page 134, reflected reference angles at nonzero
prescribed indices need one whole turn to return to the prescribed
range. The finite correction bit recognizes exactly those labels.
The two cuff lists are disjoint because their actual radii differ.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

private theorem mem_tail_ofFn_iff {k : ℕ} (f : Fin k → ℕ)
    (hf : Function.Injective f) (i : Fin k) :
    f i ∈ (List.ofFn f).tail ↔ i.val ≠ 0 := by
  cases k with
  | zero => exact Fin.elim0 i
  | succ n =>
    rw [List.ofFn_succ, List.tail_cons, List.mem_ofFn]
    constructor
    · rintro ⟨j, hj⟩ hi
      have hh := congrArg Fin.val (hf hj)
      simp only [Fin.val_succ, hi] at hh
      omega
    · intro hi
      refine ⟨⟨i.val - 1, by omega⟩, ?_⟩
      apply congrArg f
      apply Fin.ext
      dsimp
      omega

/-- Inner and outer cuff labels are distinct, since their actual
points have radii one and two. -/
theorem GM06Alg511GraphTurnRep.source_ne_target {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (i j : Fin x.drawing.pathCount) : rep.source i ≠ rep.target j := by
  intro he
  have hp : cylinderM1Point x.drawing.pathCount i = cylinderM2Point x.drawing.pathCount j := by
    rw [← rep.source_point i, ← rep.target_point j, he]
  have hr := congrArg cylinderRadius hp
  norm_num [cylinderM1Point, cylinderM2Point] at hr

/-- At an inner prescribed point, the computed correction bit is
one exactly when its prescribed index is nonzero. -/
theorem alg511_cuffOffset_source {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount)
    (i : Fin x.drawing.pathCount) :
    gm06Alg511CuffOffset x.drawing (rep.source i).val = if i.val = 0 then 0 else 1 := by
  have hinner : (rep.source i).val ∈ x.drawing.innerCuff.tail ↔ i.val ≠ 0 := by
    rw [rep.inner]
    exact mem_tail_ofFn_iff _ (Fin.val_injective.comp (rep.source_injective hk)) i
  have houter : (rep.source i).val ∉ x.drawing.outerCuff.tail := by
    intro hm
    have hh := List.mem_of_mem_tail hm
    rw [rep.outer] at hh
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hh
    exact rep.source_ne_target i j (Fin.ext hj.symm)
  simp only [gm06Alg511CuffOffset, hinner, houter, or_false]
  split_ifs <;> simp_all

/-- At an outer prescribed point, the computed correction bit is
one exactly when its prescribed index is nonzero. -/
theorem alg511_cuffOffset_target {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G) (hk : 0 < x.drawing.pathCount)
    (j : Fin x.drawing.pathCount) :
    gm06Alg511CuffOffset x.drawing (rep.target j).val = if j.val = 0 then 0 else 1 := by
  have houter : (rep.target j).val ∈ x.drawing.outerCuff.tail ↔ j.val ≠ 0 := by
    rw [rep.outer]
    exact mem_tail_ofFn_iff _ (Fin.val_injective.comp (rep.target_injective hk)) j
  have hinner : (rep.target j).val ∉ x.drawing.innerCuff.tail := by
    intro hm
    have hh := List.mem_of_mem_tail hm
    rw [rep.inner] at hh
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hh
    exact rep.source_ne_target i j (Fin.ext hi)
  simp only [gm06Alg511CuffOffset, hinner, houter, false_or]
  split_ifs <;> simp_all

end GraphMinor.GM06
