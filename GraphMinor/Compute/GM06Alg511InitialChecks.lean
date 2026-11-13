module

public import GraphMinor.Compute.GM06Alg511SearchInput
public import GraphMinor.Compute.GM06Alg511TargetRead
public import GraphMinor.Compute.GM06Alg511FlowFlag

/-!
# The first two checks of VI (5.11)

Load the plain finite input, test that the requested winding lies on
the one-over-k grid, and run maximum flow only if this test passes.
The result in register zero says whether both (5.10)(i) and (ii) hold.
The maximum-flow phase also leaves a path or separator certificate.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Perform the integrality test before the initial linkage search,
as in VI (5.11), page 134. -/
def gm06Alg511InitialChecksProg : Cmd :=
  .seq gm06Alg511LoadSearchProg
    (.seq gm06Alg511ReadTargetProg (.ite (.reg 0) gm06Alg511FlowFlagProg .skip))

end GraphMinor.Compute
