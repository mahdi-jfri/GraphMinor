module

public import GraphMinor.Compute.CrossingClass
public import GraphMinor.Compute.CrossingClassBridgeProved

/-! The classification program of Section 6 uses the proved `BridgeCross` program of Section 5. -/

public section
namespace GraphMinor.Compute.Crossing

/-- The linear-time `Classify` program of Section 6, from the proved `BridgeCross` program. -/
theorem classifyProgClaim_proved : ClassifyProgClaim :=
  classifyProgClaim_of

end GraphMinor.Compute.Crossing
