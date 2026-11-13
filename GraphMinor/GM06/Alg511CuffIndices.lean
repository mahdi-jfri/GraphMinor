module

public import GraphMinor.GM06.Alg511InputRep
public import GraphMinor.Compute.GM06Alg511FinishIndex
public import GraphMinor.Compute.GM06Alg511Flow
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Reading prescribed cuff indices from geometric input labels

The endpoint term in the winding formula of VI (5.11), page 134,
uses the indices of the prescribed cuff points. Distinct prescribed
outer points have distinct supplied vertex labels. Thus the verified
label scan returns their actual indices without a certificate in the
input.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Every finite flow source is a prescribed inner cuff label. -/
theorem GM06Alg511GraphTurnRep.flowA_exists_source {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (a : Fin x.drawing.vertexCount) (ha : a ∈ x.drawing.flowInput.A) :
    ∃ i, rep.source i = a := by
  have hm := (Finset.mem_filter.mp ha).2
  change a.val ∈ x.drawing.innerCuff at hm
  rw [rep.inner] at hm
  obtain ⟨i, hi⟩ := List.mem_ofFn.mp hm
  exact ⟨i, Fin.ext hi⟩

/-- Every finite flow target is a prescribed outer cuff label. -/
theorem GM06Alg511GraphTurnRep.flowB_exists_target {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (b : Fin x.drawing.vertexCount) (hb : b ∈ x.drawing.flowInput.B) :
    ∃ j, rep.target j = b := by
  have hm := (Finset.mem_filter.mp hb).2
  change b.val ∈ x.drawing.outerCuff at hm
  rw [rep.outer] at hm
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
  exact ⟨j, Fin.ext hj⟩

/-- Prescribed outer cuff points give distinct supplied labels. -/
theorem GM06Alg511GraphTurnRep.target_injective {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) : Function.Injective rep.target := by
  intro i j hij
  apply cylinderM1Point_injective hk
  have hp : cylinderM2Point x.drawing.pathCount i = cylinderM2Point x.drawing.pathCount j := by
    rw [← rep.target_point i, ← rep.target_point j, hij]
  apply Subtype.ext
  have hangle := congrArg (fun p : ClosedCylinder => p.val.2) hp
  simpa only [cylinderM1Point, cylinderM2Point, cylinderPoint] using
    congrArg (fun z => ((1 : ℝ), z)) hangle

/-- On the actual supplied outer cuff row, the RAM scan returns the
index of any saved prescribed target vertex. -/
theorem alg511_finishIndex_exec {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (j : Fin x.drawing.pathCount) (s : State)
    (hw : 1 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (harr : s.arrs 1006 = x.drawing.outerCuff)
    (hfinish : s.regs 45 = (rep.target j).val) :
    ∃ s' t, Exec w gm06Alg511FinishIndexProg s s' t ∧
      t ≤ 7 + 13 * x.drawing.pathCount ∧
      TwoPaths.Keeps [20, 46] [] s s' ∧ s'.regs 46 = j.val := by
  apply gm06Alg511FinishIndexProg_exec rep.target (rep.target_injective hk) j s hw hn
    ((rep.pathCount_le_vertexCount hk).trans_lt hn)
  · exact harr.trans rep.outer
  · exact hfinish

end GraphMinor.GM06
