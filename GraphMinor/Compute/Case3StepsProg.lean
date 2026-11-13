module

public import GraphMinor.Compute.Case3StepsCoreGroupingProg
public import GraphMinor.Compute.Case3StepsPrepareInteriorProg
public import GraphMinor.Compute.Case3StepsAllMembersProg
public import GraphMinor.Compute.Case3StepsFinishBlockProg
public import GraphMinor.Compute.Case3StepsWriteOutputAProg
public import GraphMinor.Compute.Case3StepsPublishArrays

/-!
# The program for steps (5) through (7)

Compute the compass division, prepare the perimeter test, and run both
member scans. A wall result copies its four private buffers to the caller.
Otherwise copy the original wall and deletion bitset into private storage,
finish the case (iii) block, and copy its raw and tagged forms out. The
caller tag is written only after all output buffers have been copied.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Publish the wall result in the four prescribed caller arrays. -/
def case3PublishWallProg (a_out a_bd a_wall a_A_enc a_base r_tag r_base : ℕ) : Cmd :=
  .seq (case3PublishArraysProg
    [(a_base + 55, a_out), (a_base + 56, a_bd),
      (a_base + 46, a_wall), (a_base + 54, a_A_enc)] r_base)
    (.assign r_tag (.const 1))

/-- Finish and publish the two arrays of the case (iii) block. -/
def case3FinishOutputAProg {h : ℕ} (h2 : 2 ≤ h)
    (a_W a_X a_out a_wall a_base r_tag r_base : ℕ) : Cmd :=
  .seq (copyArrLoopProg a_W (a_base + 59) (r_base + 132) (r_base + 133))
    (.seq (copyArrLoopProg a_X (a_base + 61) (r_base + 132) (r_base + 133))
      (.seq ((case3FinishBlockProg h2).shift a_base r_base)
        (.seq (case3WriteOutputAProg.shift a_base r_base)
          (.seq (case3PublishArraysProg [(a_base + 63, a_out), (a_base + 62, a_wall)] r_base)
            (.assign r_tag (.const 0))))))

/-- The complete RAM program of XIII (9.9), steps (5) through (7), with
both output alternatives and all caller storage indices explicit. -/
def case3StepsProg {h : ℕ} (h2 : 2 ≤ h) (h' : ℕ) (shiloachProg P72 : Cmd)
    (a_G a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base : ℕ) : Cmd :=
  .seq (case3CoreGroupingProg h2 shiloachProg a_G a_VK a_W a_base r_base)
    (.seq (case3PrepareInteriorProg h2 a_W a_VK a_base r_base)
      (.seq ((case3AllMembersProg h' P72).shift a_base r_base)
        (.ite (.reg r_base)
          (case3PublishWallProg a_out a_bd a_wall a_A_enc a_base r_tag r_base)
          (case3FinishOutputAProg h2 a_W a_X a_out a_wall a_base r_tag r_base))))

end GraphMinor.Compute
