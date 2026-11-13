module

public import GraphMinor.Compute.DPStatement
public import GraphMinor.Compute.CitedPlanarity
public import GraphMinor.Compute.Algorithm99Case3Claim
public import GraphMinor.Compute.CrossingTopLift
import GraphMinor.Compute.CrossingTop
public import GraphMinor.LRPlanarity.Statements
import GraphMinor.Compute.CrossingClassProg
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
import GraphMinor.Compute.CrossingLiftProg
import GraphMinor.Compute.Case3StepsClaim

/-!
# Assemble the planarity test and the disjoint paths algorithm

The planarity note supplies the search, solver, alignment, drawing, and RAM proofs.
Necessity closes the planarity test. The crossing extractor then supplies the
replacement for Shiloach in the main result of Graph Minors XIII (page 65), which the paper does
not number.
-/

public section

namespace GraphMinor.Compute

open GraphMinor.LRPlanarity GraphMinor.Compute.Crossing

/-- Assemble the planarity test from the planarity note. The remaining hypothesis
is `NecessityStatement`. -/
theorem planarityTestStatement_of_necessity (hNec : NecessityStatement) :
    PlanarityTestStatement :=
  planarityTestStatement_of
    (lrPlanarityRamStatement_of PlanarityRam.solveRamClaim_proved)
    searchStatement solverStatement weakAlignment_proved
    (sufficiencyStatement_of signedContour_proved) hNec

/-- The main result of Graph Minors XIII (page 65), from the crossing extractor note and the
planarity note. The remaining hypotheses are necessity (`NecessityStatement`), steps 5 to 7 of (9.9)
(`Case3StepsClaim`), and history lifting (`LiftRecHistProgClaim`). -/
theorem disjointPathsStatement_of_remaining (hNec : NecessityStatement)
    (hC3 : Case3StepsClaim) (hLift : LiftRecHistProgClaim) : DisjointPathsStatement :=
  disjointPathsStatement_of_planarity (planarityTestStatement_of_necessity hNec)
    hC3 classifyProgClaim_proved hLift

/-- The linear-time planarity test of the planarity note, with no hypotheses. Necessity is
`necessityStatement_of contourFork_proved`. -/
theorem planarityTestStatement_proved : PlanarityTestStatement :=
  planarityTestStatement_of_necessity (necessityStatement_of contourFork_proved)

/-- The main result of Graph Minors XIII (page 65), from the crossing extractor note and the
planarity note. The remaining hypotheses are steps 5 to 7 of (9.9) (`Case3StepsClaim`) and history
lifting (`LiftRecHistProgClaim`). -/
theorem disjointPathsStatement_of_case3_lift (hC3 : Case3StepsClaim)
    (hLift : LiftRecHistProgClaim) : DisjointPathsStatement :=
  disjointPathsStatement_of_planarity planarityTestStatement_proved hC3 classifyProgClaim_proved hLift

/-- The main result of Graph Minors XIII (page 65), from the crossing extractor note and the
planarity note. The one remaining hypothesis is `Case3StepsClaim`, steps 5 to 7 of (9.9). -/
theorem disjointPathsStatement_of_case3 (hC3 : Case3StepsClaim) : DisjointPathsStatement :=
  disjointPathsStatement_of_case3_lift hC3 liftRecHistProgClaim_proved

/-- The main result of Graph Minors XIII (page 65): for every fixed number of terminal pairs, the
disjoint paths problem is decided in time $O(v^3)$, with no hypotheses. Shiloach's algorithm is
replaced by the crossing extractor note, and its planarity test is proved from the planarity note.
-/
theorem disjointPathsStatement_proved : DisjointPathsStatement :=
  disjointPathsStatement_of_case3 case3StepsClaim_proved

end GraphMinor.Compute
