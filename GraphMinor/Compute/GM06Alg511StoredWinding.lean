module

public import GraphMinor.Compute.GM06Alg511LinkageEdges
public import GraphMinor.Compute.GM06Alg511WindingSetup
public import GraphMinor.Compute.GM06Alg511ScaledWinding
public import GraphMinor.Compute.GM06Alg511TraceChosenTurn

/-!
# Storing the initial linkage before computing its winding

The initial phase of VI (5.11), page 134, first fixes every path
edge using the raw maximum-flow successors. It then traverses the
first source, sums its stored edge turns, and finds its outer cuff
index. The full edge choices remain in array 1300 for later use.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Store every linkage edge, compute one path's turn, and locate
its endpoint in the prescribed outer cuff row. -/
def gm06Alg511StoredWindingProg : Cmd :=
  .seq gm06Alg511LinkageEdgesProg
    (.seq gm06Alg511TraceChosenTurnProg gm06Alg511FinishIndexProg)

/-- Prepare every scratch table from retained drawing words before
storing the full linkage and computing its winding. -/
def gm06Alg511StoredInitialWindingProg : Cmd :=
  .seq gm06Alg511WindingSetupProg gm06Alg511StoredWindingProg

/-- Compute the stored linkage and place its signed winding
numerator in registers 54/55 over the path count in register 52. -/
def gm06Alg511StoredNumeratorProg : Cmd :=
  .seq gm06Alg511StoredInitialWindingProg gm06Alg511ScaledWindingProg

end GraphMinor.Compute
