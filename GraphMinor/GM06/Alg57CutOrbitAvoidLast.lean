module

public import GraphMinor.GM06.Alg57CutEquations
import GraphMinor.Compute.GM06CutAdjacencyMath
import GraphMinor.Compute.GM06FaceRowsProgram

/-!
# The selected cut orbit avoids block ends

The outer boundary orbits of a cut consist of darts whose reverse
starts a local block. VI (5.7), page 133, selects a different orbit.
The finite permutation argument for projection also shows that it
never contains a last end of a block.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute

/-- A cut face starting away from the boundary orbits never visits
a last dart of a local cut block. -/
theorem cut_face_iterate_not_last (marks : GM06CutTables) (rows : List (List ℕ))
    (hn : rows.flatten.Nodup)
    (hok : ∀ v row p, rows[v]? = some row → gm06CutPositionAt marks v = some p → CutBlockOK p row)
    (hfit : CutFits marks rows)
    (hmate : ∀ d ∈ (gm06SplitRotationRows marks rows).flatten,
      gm06DartMate d ∈ (gm06SplitRotationRows marks rows).flatten)
    {c : ℕ} (hc : c ∈ (gm06SplitRotationRows marks rows).flatten)
    (hcF : gm06DartMate c ∉ cutFirstDarts marks rows) (n : ℕ) :
    (dartMatePerm.trans (gm06RotationPermutation
      (gm06SplitRotationRows marks rows)).symm)^[n] c ∉ cutLastDarts marks rows := by
  classical
  have hnd := gm06SplitRotationRows_nodup marks rows hn
  have hh := cut_orbit_projection
    (gm06RotationPermutation (gm06SplitRotationRows marks rows)) dartMatePerm
    (gm06RotationPermutation rows) dartMatePerm gm06UncutDart
    (gm06SplitRotationRows marks rows).flatten.toFinset
    (cutFirstDarts marks rows) (cutLastDarts marks rows)
    (fun d hd => List.mem_toFinset.mpr
      (gm06RotationPermutation_symm_mem _ hnd d (List.mem_toFinset.mp hd)))
    (fun d hd => List.mem_toFinset.mpr (by simpa only [dartMatePerm_apply] using hmate d (List.mem_toFinset.mp hd)))
    (fun d => by simpa only [dartMatePerm_apply] using gm06UncutDart_mate d)
    (fun d hd hdF => cut_C1 marks rows hn hok (List.mem_toFinset.mp hd) hdF)
    (fun d _ hdF => cut_C2 marks rows hn hok hdF)
    (fun d _ hdL => by simpa only [dartMatePerm_apply] using cut_C3 marks rows hok hfit hdL)
    (List.mem_toFinset.mpr hc) (by simpa only [dartMatePerm_apply] using hcF) n
  intro hl
  apply hh.2.1
  simpa only [dartMatePerm_apply] using cut_C3 marks rows hok hfit hl

end GraphMinor.GM06
