module

public import GraphMinor.Compute.GM06Alg511StoredWinding
public import GraphMinor.Compute.GM06Alg511ReadNormalTarget
public import GraphMinor.Compute.GM06Alg511OrientCompare

/-!
# Initial orientation with all linkage edges retained

For VI (5.11), page 134, store the full linkage from raw maximum
flow, compute its winding numerator, load the supplied target and
choose the orientation. The flow words and all selected linkage
edges remain available for the successor phase.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Find and store all initial linkage edges, compute the winding,
and orient that same linkage below the supplied target. -/
def gm06Alg511StoredInitialOrientationProg : Cmd :=
  .seq gm06Alg511StoredNumeratorProg
    (.seq gm06Alg511ReadNormalTargetProg gm06Alg511OrientCompareProg)

end GraphMinor.Compute
