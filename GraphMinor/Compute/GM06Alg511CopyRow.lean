module

public import GraphMinor.Compute.TwoPathsRotate
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Copying ordinary drawing rows for the retained orientation

The orientation branch of VI (5.11), page 134, presents the same
output table locations in either orientation. When no reflection is
needed, copy the original signed turns and cuff rows into those
locations. This file verifies the plain row-copy loop.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Copy a complete row to a distinct scratch array, using counter 20. -/
def gm06Alg511CopyRowProg (src dst : Arr) : Cmd :=
  mapProg 20 (.len src) dst src (.reg 20)

/-- A complete row is copied exactly in linear time, with every
other array and every other register preserved. -/
theorem gm06Alg511CopyRowProg_exec {w : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (xs : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hwords : ∀ v ∈ xs, v < 2 ^ w)
    (ha : s.arrs src = xs) :
    ∃ s' t, Exec w (gm06Alg511CopyRowProg src dst) s s' t ∧
      t ≤ 6 + 12 * xs.length ∧ Keeps [20] [dst] s s' ∧ s'.arrs dst = xs := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := mapProg_exec
    20 (.len src) dst src (.reg 20) hne.symm xs.length id xs s hw hn
    (fun st h => Crossing.eval_len ((h.2 src (by simpa using hne)).trans ha) hn)
    (fun st i _ hi hilt => Crossing.eval_reg hi (hilt.trans hn))
    (fun i hi => hi) hwords ha
  refine ⟨s', t, he, ?_, hk, ?_⟩
  · norm_num [Expr.cost] at ht
    simpa only [Nat.mul_comm] using ht
  · simpa only [id_eq, map_getD_self] using hout

end GraphMinor.Compute
