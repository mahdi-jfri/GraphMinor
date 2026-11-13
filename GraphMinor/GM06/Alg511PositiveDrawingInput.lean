module

public import GraphMinor.GM06.Alg511InputExists
public import GraphMinor.GM06.Alg57InputRep
import GraphMinor.GM06.Alg57PathEncoding

/-!
# Linkage-free input with positively oriented cuff rotations

The revised input to VI (5.7) reads the original graph, rotations
with both cuffs and the ordered cuff vertices. It reads no region
rows. The input for VI (5.11), page 134, uses those same fields,
adds the integer target pair and the normalized signed edge turns,
and supplies no linkage. Positively oriented polar charts now
interpret its rotations in the fixed plane orientation.

Supply positive rows using the successor input construction while
retaining all original graph and turn labels. The unused region
field of the older decision-input serializer is empty. Every
intended instance has this input, and its supplied words determine
feasibility. Attaching computed path rows gives exactly the new
successor input relation.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The linkage-free input read by the decision procedure, with
positive rotations of both cuff families and no region data.
All fields are ordinary interpretations of supplied drawing data. -/
structure GM06Alg511PositiveDrawingRep (x : GM06Alg511WindingInput) (G : Drawing ClosedCylinder) where
  graphTurn : GM06Alg511GraphTurnRep x G
  denominator_ne_zero : x.drawing.denominator ≠ 0
  regions_empty : x.drawing.regionBoundaries = []
  rotations : GM06SuccessorRotationRep x.drawing.pathCount (x.drawing.withLinkage []) graphTurn.graph

/-- Supply positively oriented cuff rotations while retaining the
original endpoint, cuff, target and normalized-turn data. The unused
region field is empty. No linkage is supplied or selected. -/
theorem alg511_add_positive_drawing_geometry
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G)
    (hG : IsCylinderSection5Drawing x.drawing.pathCount G)
    (hden : x.drawing.denominator ≠ 0) :
    ∃ y : GM06Alg511WindingInput, Nonempty (GM06Alg511PositiveDrawingRep y G) ∧
      y.drawing.pathCount = x.drawing.pathCount ∧
      y.drawing.numerator = x.drawing.numerator ∧ y.drawing.denominator = x.drawing.denominator ∧
      y.drawing.vertexCount = x.drawing.vertexCount ∧ y.drawing.endpoints = x.drawing.endpoints ∧
      y.drawing.innerCuff = x.drawing.innerCuff ∧ y.drawing.outerCuff = x.drawing.outerCuff ∧
      y.edgeTurns = x.edgeTurns := by
  obtain ⟨rows, hrows⟩ := exists_successor_rotation_rows hG rep.graph
  let y : GM06Alg511WindingInput := {
    drawing := {x.drawing with rotations := rows, regionBoundaries := []}
    edgeTurns := x.edgeTurns }
  let graph : GM06SuccessorGraphRep (y.drawing.withLinkage []) G.toGraph := {
    vertex := rep.graph.vertex
    pairs := rep.graph.pairs
    endpoints := rep.graph.endpoints
    edge := rep.graph.edge
    link := rep.graph.link }
  let graphTurn : GM06Alg511GraphTurnRep y G := {
    graph := graph
    source := rep.source
    target := rep.target
    inner := rep.inner
    outer := rep.outer
    source_point := rep.source_point
    target_point := rep.target_point
    turns := rep.turns }
  have hy : GM06Alg511PositiveDrawingRep y G := {
    graphTurn := graphTurn
    denominator_ne_zero := hden
    regions_empty := rfl
    rotations := hrows }
  exact ⟨y, ⟨hy⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every intended instance of VI (5.11) has the positive,
region-free drawing data read by the new successor procedure,
with exactly the requested integer numerator and denominator. -/
theorem alg511_exists_positive_drawing_input (k : ℕ) (G : Drawing ClosedCylinder)
    (hG : IsCylinderSection5Drawing k G) (numerator denominator : ℤ)
    (hden : denominator ≠ 0) :
    ∃ x : GM06Alg511WindingInput,
      x.drawing.pathCount = k ∧ x.drawing.numerator = numerator ∧
      x.drawing.denominator = denominator ∧ Nonempty (GM06Alg511PositiveDrawingRep x G) := by
  obtain ⟨x, hk, hnum, hdenom, ⟨rep⟩⟩ := alg511_exists_graph_turn_input k G hG numerator denominator
  obtain ⟨y, hy, hyk, hynum, hyden, _⟩ := alg511_add_positive_drawing_geometry rep
    (hk.symm ▸ hG) (hdenom.symm ▸ hden)
  exact ⟨y, hyk.trans hk, hynum.trans hnum, hyden.trans hdenom, hy⟩

/-- The positive finite drawing input determines feasibility
independently of which actual drawing realizes its supplied words. -/
theorem alg511_positive_drawing_words_feasible_iff {x y : GM06Alg511WindingInput}
    {G H : Drawing ClosedCylinder} (rep : GM06Alg511PositiveDrawingRep x G)
    (rep' : GM06Alg511PositiveDrawingRep y H) (hk : 0 < x.drawing.pathCount)
    (hwords : gm06Alg511SearchWords x = gm06Alg511SearchWords y) :
    IsThetaFeasible x.drawing.pathCount G x.drawing.target ↔
      IsThetaFeasible y.drawing.pathCount H y.drawing.target :=
  alg511_searchWords_feasible_iff rep.graphTurn rep'.graphTurn hk hwords

/-- Attaching computed ordinary-dart rows to the linkage-free input
gives the precise successor input relation. All original labels and
positive rotation witnesses are retained directly. -/
@[expose] noncomputable def GM06Alg511PositiveDrawingRep.withLinkage
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511PositiveDrawingRep x G)
    (L : CylinderLinkage x.drawing.pathCount G) (rows : List (List ℕ))
    (hrows : GM06LinkageRowsEncoding L rep.graphTurn.graph.initialTagged
      rep.graphTurn.graph.vertexLabels rep.graphTurn.graph.edgeLabels rows) :
    GM06SuccessorInputRep (x.drawing.withLinkage rows) G L where
  graph := {
    vertex := rep.graphTurn.graph.vertex
    pairs := rep.graphTurn.graph.pairs
    endpoints := rep.graphTurn.graph.endpoints
    edge := rep.graphTurn.graph.edge
    link := rep.graphTurn.graph.link }
  source := rep.graphTurn.source
  target := rep.graphTurn.target
  inner := rep.graphTurn.inner
  outer := rep.graphTurn.outer
  source_point := rep.graphTurn.source_point
  target_point := rep.graphTurn.target_point
  linkage := hrows
  rotations := rep.rotations

end GraphMinor.GM06
