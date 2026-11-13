module

public import GraphMinor.Compute.GM06Alg511Numerator
public import GraphMinor.Compute.GM06Alg511ReadNormalTarget
public import GraphMinor.Compute.GM06Alg511OrientCompare

/-!
# The initial winding and orientation program

For VI (5.11), page 134, start with the successful raw maximum-flow
output and the retained drawing. Compute the initial winding, read
the supplied target with positive denominator, then compare and choose
the orientation. Every path, table, scalar value and comparison bit
used by the orientation phase is produced by these commands.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute the initial winding and execute the target orientation choice. -/
def gm06Alg511InitialOrientationProg : Cmd :=
  .seq gm06Alg511NumeratorProg (.seq gm06Alg511ReadNormalTargetProg gm06Alg511OrientCompareProg)

end GraphMinor.Compute
