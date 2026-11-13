module

public import GraphMinor.Compute.GM06Alg511ChosenEdges
public import GraphMinor.GM06.Alg511InputRep
public import GraphMinor.GM06.Alg511LinkageOfWalks
public import GraphMinor.GM06.Alg511LabelTransfer
import GraphMinor.GM06.Alg511CuffIndices
import GraphMinor.GM06.Alg511PathStarts
import Mathlib.Tactic

/-!
# The full linkage determined by computed edge choices

In VI (5.11), page 134, maximum flow first finds a linkage. Interpret
its vertex traces using the edge-choice array produced by the edge
scans. All finite paths retain those labels, and all actual paths
retain their vertex supports and signed turns. Their disjointness
therefore gives an actual linkage with exactly these path drawings.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- The successful flow output and computed directed edge choices
represent a full actual linkage, retaining every selected path. -/
theorem alg511_linkage_of_chosen_edges (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (out choices : List ℕ)
    (hsys : IsValidPathSystem x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B
      (decUsed x.drawing.vertexCount out) (decPred x.drawing.vertexCount out)
      (decSucc x.drawing.vertexCount out))
    (hcount : (pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out)).card = x.drawing.pathCount)
    (hchoices : ∀ u : Fin x.drawing.vertexCount,
      let d := choices.getD u.val x.drawing.endpoints.length
      if decSucc x.drawing.vertexCount out u < x.drawing.vertexCount then
        d < x.drawing.endpoints.length ∧ x.drawing.endpoints.getD d 0 = u.val ∧
          x.drawing.endpoints.getD (gm06DartMate d) 0 = decSucc x.drawing.vertexCount out u
      else d = x.drawing.endpoints.length) :
    ∃ (W : ∀ i : Fin x.drawing.pathCount,
        GraphWalk (gm06Alg511LabelGraph rep.graph.pairs) (rep.source i)
          (traceWalk hsys x.drawing.vertexCount (rep.source i)).1)
      (actual : ∀ i : Fin x.drawing.pathCount,
        GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val
          (rep.graph.vertex (traceWalk hsys x.drawing.vertexCount (rep.source i)).1).val)
      (L : CylinderLinkage x.drawing.pathCount G),
      (∀ i, (W i).support = (traceWalk hsys x.drawing.vertexCount (rep.source i)).2.support ∧
        (W i).IsSimple ∧ gm06Alg511LabelWalkDarts rep.graph.pairs (W i) =
          gm06Alg511ChosenDarts x.drawing choices
            (traceWalk hsys x.drawing.vertexCount (rep.source i)).2.support) ∧
      (∀ i, (actual i).support = (W i).support.map (fun v => (rep.graph.vertex v).val) ∧
        alg511InterpretedWalkTurn rep.graph x.edgeTurns (actual i) =
          gm06Alg511LabelWalkTurn rep.graph.pairs x.edgeTurns (W i) ∧
        (actual i).edges = (W i).edges.map (fun e => (rep.graph.edge e).val)) ∧
      (∀ i, L.pathDrawing i = walkDrawing G (actual i) ∧
        ParametrizesSet (L.curve i) (walkDrawing G (actual i)).U
          (rep.graph.vertex (rep.source i)).val
          (rep.graph.vertex (traceWalk hsys x.drawing.vertexCount (rep.source i)).1).val) := by
  classical
  have hstarts := alg511_pathStarts_eq_cuff x.drawing hk rep.graph rep.source
    rep.flowA_exists_source rep.source_point rep.inner_mem_iff hsys hcount
  have hu : ∀ i, rep.source i ∈ pathStarts (decUsed x.drawing.vertexCount out)
      (decPred x.drawing.vertexCount out) := by
    intro i
    rw [hstarts]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [rep.inner]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  let Q : Fin x.drawing.pathCount → ABWalk (n := x.drawing.vertexCount)
      x.drawing.flowGraph x.drawing.flowInput.A x.drawing.flowInput.B :=
    fun i => abWalkOfStart hsys (rep.source i) (hu i)
  have hfinite : ∀ i, ∃ W : GraphWalk (gm06Alg511LabelGraph rep.graph.pairs)
      (rep.source i) (Q i).finish,
      W.support = (Q i).walk.support ∧ W.IsSimple ∧
        gm06Alg511LabelWalkDarts rep.graph.pairs W =
          gm06Alg511ChosenDarts x.drawing choices (Q i).walk.support := by
    intro i
    exact gm06Alg511ChosenEdges_exists_walk x.drawing rep.graph out choices hsys hchoices
      (rep.source i) (hu i)
  choose W hsupport hs hdarts using hfinite
  choose actual hactualSupport hactualEdges hactualTurn using fun i =>
    alg511_exists_actual_walk_of_labelWalk_edges rep.graph x.edgeTurns (W i)
  have hinj : Function.Injective (fun v => (rep.graph.vertex v).val) :=
    Subtype.val_injective.comp rep.graph.vertex.injective
  have hactualSimple : ∀ i, (actual i).IsSimple := by
    intro i
    change (actual i).support.Nodup
    rw [hactualSupport i]
    exact (hs i).map hinj
  have hdisjoint : ∀ i j, i ≠ j → ∀ v,
      v ∈ (actual i).support → v ∈ (actual j).support → False := by
    intro i j hij v hvi hvj
    rw [hactualSupport i] at hvi
    rw [hactualSupport j] at hvj
    obtain ⟨a, ha, hav⟩ := List.mem_map.mp hvi
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp hvj
    have hab : a = b := hinj (hav.trans hbv.symm)
    rw [hsupport i] at ha
    rw [hsupport j] at hb
    exact abWalkOfStart_disjoint hsys (hu i) (hu j)
      (fun heq => hij (rep.source_injective hk heq)) ha (hab ▸ hb)
  have hsource : ∀ i, (rep.graph.vertex (Q i).start).val =
      cylinderM1Point x.drawing.pathCount i := rep.source_point
  have htarget : ∀ i, (rep.graph.vertex (Q i).finish).val ∈
      cylinderM2 x.drawing.pathCount := by
    intro i
    apply (rep.outer_mem_iff (Q i).finish).mp
    exact (Finset.mem_filter.mp (Q i).finish_mem).2
  obtain ⟨L, hL⟩ := alg511_linkage_of_actual_walks G
    (fun i => (rep.graph.vertex (Q i).start).val)
    (fun i => (rep.graph.vertex (Q i).finish).val) actual hsource htarget
    hactualSimple hdisjoint
  exact ⟨W, actual, L, fun i => ⟨hsupport i, hs i, hdarts i⟩,
    fun i => ⟨hactualSupport i, hactualTurn i, hactualEdges i⟩, hL⟩

end GraphMinor.GM06
