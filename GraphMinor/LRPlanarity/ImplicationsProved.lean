module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.Sufficiency
import GraphMinor.LRPlanarity.Necessity
import GraphMinor.LRPlanarity.ContourSigned
import GraphMinor.LRPlanarity.ContourFork

/-! The geometric implications for the planarity test use the proved signed
contour and contour-to-fork comparison. -/

public section
namespace GraphMinor.LRPlanarity

/-- Part IV, Sections 1 to 5: the proved signed contour gives geometric sufficiency. -/
theorem sufficiencyStatement_of_proved : SufficiencyStatement :=
  sufficiencyStatement_of signedContour_proved

/-- Part IV, opening and Section 7: the proved contour comparison gives necessity. -/
theorem necessityStatement_of_proved : NecessityStatement :=
  necessityStatement_of contourFork_proved

end GraphMinor.LRPlanarity
