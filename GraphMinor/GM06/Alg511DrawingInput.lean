module

public import GraphMinor.GM06.Alg511InputExists
public import GraphMinor.GM06.Alg511CuffRotations
public import GraphMinor.GM06.Alg511BoundaryRows
import GraphMinor.GM06.Alg511FiniteRegions
import GraphMinor.GM11.PerimeterPull
import Mathlib.Tactic

/-!
# Coverage of the full drawing input of VI (5.11)

Supply the original graph, ordered cuffs, integer target pair and
normalized edge turns. The rotation rows use the original edge
labels followed by the prescribed inner and outer cuff labels.
The region rows follow the actual region-side collars in order,
with a region label at the start of every boundary component.

All vertex, edge, region and component correspondences are actual
bijections in the input relation. Drawing maps and charts witness
that relation and are not read by the program. Every Section 5
instance with a nonzero target denominator admits this input, and
equal supplied words determine the same feasibility question.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- Geometric interpretation of the supplied rotations and ordered
region rows, with the fixed directed cuff labels of the successor
procedure. The auxiliary cuff drawing retains exactly the old vertices. -/
@[expose] def Alg511DrawingGeometryRep (k : ℕ) (x : GM06SuccessorInput) (boundaries : List (List ℕ))
    {G : Drawing ClosedCylinder} (rep : GM06SuccessorGraphRep x G.toGraph) : Prop :=
  ∃ (F : Drawing ClosedCylinder)
    (edge : Fin (rep.pairs.length + (k + k)) ≃ (cylinderSphereDrawing F).E)
    (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane),
    G.IsSubdrawing F ∧ F.U = G.U ∪ bd ClosedCylinder ∧ F.V = G.V ∧
    EdgePar (cylinderSphereDrawing F) γ ∧
    (∀ j : Fin rep.pairs.length,
      (edge (j.castAdd (k + k))).val = cylinderToSphere '' (rep.edge j).val) ∧
    (∀ i : Fin k,
      (edge ((i.castAdd k).natAdd rep.pairs.length)).val =
        cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) ∧
    (∀ i : Fin k,
      (edge ((i.natAdd k).natAdd rep.pairs.length)).val =
        cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) ∧
    (∀ j : Fin rep.pairs.length,
      γ (cylinderToSphere '' (rep.edge j).val) 0 =
        cylinderToSphere (rep.vertex rep.pairs[j.val].1).val ∧
      γ (cylinderToSphere '' (rep.edge j).val) 1 =
        cylinderToSphere (rep.vertex rep.pairs[j.val].2).val) ∧
    (∀ i : Fin k, ∀ t : I,
      γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (initialCuffGapCurve k i t)) ∧
    (∀ i : Fin k, ∀ t : I,
      γ (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (alg511OuterCuffGapCurve k i t)) ∧
    x.rotations.length = x.vertexCount ∧
    (∀ v : Fin x.vertexCount,
      Alg511CuffRotationRowRep edge γ (cylinderToSphere (rep.vertex v).val)
        (x.rotations.getD v.val [])) ∧
    ∃ (r : ℕ) (region : Fin r ≃ G.R) (sphereRegion : Fin r → (cylinderSphereDrawing F).R),
      (∀ i, (sphereRegion i).val = cylinderToSphere '' ((region i).val \ bd ClosedCylinder)) ∧
      Alg511RegionRowsRep (cylinderSphereDrawing F) edge γ sphereRegion boundaries

/-- The complete linkage-free drawing input, including the ordinary
geometric interpretation of rotations and region boundaries and a
valid integer pair for its rational target. -/
structure GM06Alg511DrawingRep (x : GM06Alg511WindingInput) (G : Drawing ClosedCylinder) where
  graphTurn : GM06Alg511GraphTurnRep x G
  denominator_ne_zero : x.drawing.denominator ≠ 0
  geometry : Alg511DrawingGeometryRep x.drawing.pathCount (x.drawing.withLinkage []) x.drawing.regionBoundaries graphTurn.graph

/-- The graph, cuff and turn data extend to complete drawing data by
supplying all geometric rotation and boundary rows. The integer target
pair and the original graph data are retained. -/
theorem alg511_add_drawing_geometry
    {x : GM06Alg511WindingInput} {G : Drawing ClosedCylinder}
    (rep : GM06Alg511GraphTurnRep x G)
    (hG : IsCylinderSection5Drawing x.drawing.pathCount G)
    (hden : x.drawing.denominator ≠ 0) :
    ∃ y : GM06Alg511WindingInput, Nonempty (GM06Alg511DrawingRep y G) ∧
      y.drawing.pathCount = x.drawing.pathCount ∧
      y.drawing.numerator = x.drawing.numerator ∧
      y.drawing.denominator = x.drawing.denominator ∧
      y.drawing.vertexCount = x.drawing.vertexCount ∧
      y.drawing.endpoints = x.drawing.endpoints ∧ y.edgeTurns = x.edgeTurns := by
  classical
  obtain ⟨F, edge, γ, rotations, hGF, hFU, hFV, hγ, hedgeG, hedgeI, hedgeO,
    hends, hγI, hγO, hrotlen, hrot⟩ :=
    alg511_exists_augmented_rotation_rows hG (x.drawing.withLinkage []) rep.graph
  obtain ⟨r, ⟨region⟩⟩ := alg511_exists_region_labels hG
  let sphereRegion : Fin r → (cylinderSphereDrawing F).R := fun i =>
    ⟨cylinderToSphere '' ((region i).val \ bd ClosedCylinder),
      image_region_sdiff_boundary_mem_sphere_regions hFU (region i).property⟩
  have hS := GM11.IsSphere.isClosedSurface
    (show IsSphere (OnePoint EuclideanPlane) from ⟨Homeomorph.refl _⟩)
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  obtain ⟨boundaries, hboundaries, _⟩ := alg511_exists_region_rows hS.1
    ⟨Homeomorph.refl _⟩ (cylinderSphereDrawing F) edge hγ sphereRegion
  let y : GM06Alg511WindingInput := {
    drawing := {x.drawing with rotations := rotations, regionBoundaries := boundaries}
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
  have hgeometry : Alg511DrawingGeometryRep y.drawing.pathCount
      (y.drawing.withLinkage []) y.drawing.regionBoundaries graphTurn.graph := by
    exact ⟨F, edge, γ, hGF, hFU, hFV, hγ, hedgeG, hedgeI, hedgeO, hends, hγI, hγO,
      hrotlen, hrot, r, region, sphereRegion, fun _ => rfl, hboundaries⟩
  exact ⟨y, ⟨⟨graphTurn, hden, hgeometry⟩⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every intended instance of VI (5.11), page 134, has a full plain
finite input. Vertex, edge, cuff, region and boundary correspondences
are interpretation witnesses, and no linkage is supplied. -/
theorem alg511_exists_drawing_input (k : ℕ) (G : Drawing ClosedCylinder)
    (hG : IsCylinderSection5Drawing k G) (numerator denominator : ℤ)
    (hden : denominator ≠ 0) :
    ∃ x : GM06Alg511WindingInput,
      x.drawing.pathCount = k ∧ x.drawing.numerator = numerator ∧
      x.drawing.denominator = denominator ∧ Nonempty (GM06Alg511DrawingRep x G) := by
  obtain ⟨x, hk, hnum, hdenom, ⟨rep⟩⟩ := alg511_exists_graph_turn_input k G hG numerator denominator
  have hGx : IsCylinderSection5Drawing x.drawing.pathCount G := hk.symm ▸ hG
  have hdenx : x.drawing.denominator ≠ 0 := hdenom.symm ▸ hden
  obtain ⟨y, hy, hyk, hynum, hyden, _⟩ := alg511_add_drawing_geometry rep hGx hdenx
  exact ⟨y, hyk.trans hk, hynum.trans hnum, hyden.trans hdenom, hy⟩

/-- Equal supplied full input words describe the same feasibility
question, for every two actual drawings realizing those words. -/
theorem alg511_drawing_searchWords_feasible_iff {x y : GM06Alg511WindingInput}
    {G H : Drawing ClosedCylinder} (rep : GM06Alg511DrawingRep x G)
    (rep' : GM06Alg511DrawingRep y H) (hk : 0 < x.drawing.pathCount)
    (hwords : gm06Alg511SearchWords x = gm06Alg511SearchWords y) :
    IsThetaFeasible x.drawing.pathCount G x.drawing.target ↔
      IsThetaFeasible y.drawing.pathCount H y.drawing.target :=
  alg511_searchWords_feasible_iff rep.graphTurn rep'.graphTurn hk hwords

end GraphMinor.GM06
