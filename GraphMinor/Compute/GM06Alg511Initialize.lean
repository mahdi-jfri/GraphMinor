module

public import GraphMinor.Compute.GM06Alg511InitialChecks
public import GraphMinor.Compute.GM06Alg511StoredInitialOrientation

/-!
# Initial checks and the first oriented linkage

VI (5.11), page 134, tests integrality and linkage existence first.
If both pass, store all selected linkage edges, compute the winding
and reverse orientation when needed. Register 90 records whether
initialization succeeded. The successor loop must still decide the
target when the initial winding is strictly smaller.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Run the two initial checks, then construct and orient the full
initial linkage only in the successful branch. -/
def gm06Alg511InitializeProg : Cmd :=
  .seq gm06Alg511InitialChecksProg
    (.ite (.reg 0)
      (.seq gm06Alg511StoredInitialOrientationProg (.assign 90 (.const 1)))
      (.assign 90 (.const 0)))

end GraphMinor.Compute
