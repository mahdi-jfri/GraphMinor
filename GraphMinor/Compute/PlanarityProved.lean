module

public import GraphMinor.Compute.SpecsPlanarity
import GraphMinor.Compute.PlanarityRam
import GraphMinor.Compute.PlanarityRamSolveMain
import GraphMinor.LRPlanarity.Assembly
import GraphMinor.LRPlanarity.Search
import GraphMinor.LRPlanarity.Solver
import GraphMinor.LRPlanarity.Alignment
import GraphMinor.LRPlanarity.Sufficiency
import GraphMinor.LRPlanarity.ContourSigned
import GraphMinor.LRPlanarity.ContourFork
import GraphMinor.LRPlanarity.Necessity

/-! The planarity test follows by composing the proved RAM solver, search,
constraint solver, alignment, and geometric implications. -/

public section
namespace GraphMinor.Compute
open LRPlanarity

/-- The RAM implementation uses the proved solver phase. -/
theorem lrPlanarityRamStatement_proved : LRPlanarityRamStatement :=
  lrPlanarityRamStatement_of PlanarityRam.solveRamClaim_proved

/-- The planarity test combines the proved execution and geometric results. -/
theorem planarityTestStatement_closed : PlanarityTestStatement :=
  planarityTestStatement_of lrPlanarityRamStatement_proved searchStatement solverStatement
    weakAlignment_proved (sufficiencyStatement_of signedContour_proved)
    (necessityStatement_of contourFork_proved)

end GraphMinor.Compute
