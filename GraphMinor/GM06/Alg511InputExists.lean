module

public import GraphMinor.GM06.Alg511InputRep
public import GraphMinor.Compute.GM06Alg511Target
public import GraphMinor.Compute.GM06Alg511SearchInput
import GraphMinor.GM06.Alg511GraphInputExists

/-!
# Coverage and array determination for graph and winding data

Every Section 5 drawing admits finite graph labels, ordered prescribed
cuff labels and normalized integer edge turns. The target integer pair
is retained unchanged. These are existence witnesses in Prop, not an
encoder selecting geometric facts by choice. Equal supplied word arrays
then describe the same feasibility question, by serializer injectivity
and the proved finite feasibility characterization.

This relation covers the graph, cuffs and winding. Rotation and region
rows still require the separate successor-input interpretation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- Every actual Section 5 drawing admits finite graph, ordered cuff
and normalized turn data, with the requested integer target pair. -/
theorem alg511_exists_graph_turn_input (k : ℕ) (G : Drawing ClosedCylinder)
    (hG : IsCylinderSection5Drawing k G) (numerator denominator : ℤ) :
    ∃ x : GM06Alg511WindingInput,
      x.drawing.pathCount = k ∧ x.drawing.numerator = numerator ∧
      x.drawing.denominator = denominator ∧ Nonempty (GM06Alg511GraphTurnRep x G) := by
  obtain ⟨x, rep, hcount, hnum, hden, _, _, source, hsource, _, hinner,
    target, htarget, houter⟩ := alg511_exists_graph_cuff_input k G hG numerator denominator
  subst k
  obtain ⟨turns, hturns⟩ := alg511_exists_normalized_turns hG.1 rep
  exact ⟨⟨x, turns⟩, rfl, hnum, hden, ⟨{
    graph := rep
    source := source
    target := target
    inner := hinner
    outer := houter
    source_point := hsource
    target_point := htarget
    turns := hturns }⟩⟩

/-- Equal finite winding arrays determine the same target feasibility,
for every two actual drawings representing those arrays. -/
theorem alg511_windingWords_feasible_iff {x y : GM06Alg511WindingInput}
    {G H : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (rep' : GM06Alg511GraphTurnRep y H) (hk : 0 < x.drawing.pathCount)
    (hwords : gm06Alg511WindingWords x = gm06Alg511WindingWords y) :
    IsThetaFeasible x.drawing.pathCount G x.drawing.target ↔
      IsThetaFeasible y.drawing.pathCount H y.drawing.target := by
  have hxy := gm06Alg511WindingWords_injective hwords
  subst y
  exact rep.feasible_iff rep' hk x.drawing.target

/-- The full plain input array used by the initial RAM phase determines
its target feasibility, independently of its actual drawing realization. -/
theorem alg511_searchWords_feasible_iff {x y : GM06Alg511WindingInput}
    {G H : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (rep' : GM06Alg511GraphTurnRep y H) (hk : 0 < x.drawing.pathCount)
    (hwords : gm06Alg511SearchWords x = gm06Alg511SearchWords y) :
    IsThetaFeasible x.drawing.pathCount G x.drawing.target ↔
      IsThetaFeasible y.drawing.pathCount H y.drawing.target := by
  have hxy := gm06Alg511SearchWords_injective hwords
  subst y
  exact rep.feasible_iff rep' hk x.drawing.target

end GraphMinor.GM06
