module

public import GraphMinor.Compute.GM06Alg511PathTurn
public import GraphMinor.GM06.Alg511InputRep
public import GraphMinor.GM06.Alg511WalkWinding
import GraphMinor.GM06.Alg511LabelTransfer
import Mathlib.Tactic

/-!
# Geometric meaning of the computed path turn

The RAM path-turn phase of VI (5.11), page 134, selects actual edge
labels and sums their signed words. Transfer its output walk through
the supplied label bijections. The normalized edge-turn formula then
identifies the computed register difference with the winding of every
parametrization of that actual path, after adding its cuff endpoint
indices.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11

/-- The computed signed turn determines the scaled geometric winding
of the selected initial path at any prescribed outer cuff endpoint. -/
theorem alg511_computed_path_winding {w : ℕ} (x : GM06Alg511WindingInput)
    {G : Drawing ClosedCylinder} (rep : GM06Alg511GraphTurnRep x G)
    (hk : 0 < x.drawing.pathCount) (i : Fin x.drawing.pathCount)
    (tail : List (Fin x.drawing.vertexCount))
    (hnd : (rep.source i :: tail).Nodup)
    (hadj : ∀ r (hr : r + 1 < (rep.source i :: tail).length),
      x.drawing.flowGraph.Adj (rep.source i :: tail)[r] (rep.source i :: tail)[r + 1])
    (s : State) (hw : 2 < 2 ^ w) (hn : x.drawing.vertexCount < 2 ^ w)
    (hsquare : x.drawing.vertexCount * x.drawing.vertexCount < 2 ^ w)
    (hends : x.drawing.endpoints.length < 2 ^ w)
    (hproduct : x.drawing.vertexCount * (gm06Alg511TurnWords x.edgeTurns).sum < 2 ^ w)
    (hkeys : s.arrs 1100 = gm06Alg511DartKeys x.drawing)
    (hwords : s.arrs 11 = gm06Alg511TurnWords x.edgeTurns)
    (hN : s.regs 41 = x.drawing.vertexCount)
    (hvertices : IsBufPrefix s 12 42 x.drawing.vertexCount
      ((rep.source i :: tail).map Fin.val)) :
    ∃ s' t, Exec w gm06Alg511PathTurnProg s s' t ∧
      t ≤ 29 + x.drawing.vertexCount * (89 + 13 * x.drawing.endpoints.length) ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      ∃ (b : Fin x.drawing.vertexCount)
        (W : GraphWalk G.toGraph (rep.graph.vertex (rep.source i)).val (rep.graph.vertex b).val),
        W.support = (rep.source i :: tail).map (fun v => (rep.graph.vertex v).val) ∧
        W.IsSimple ∧
        ∀ (j : Fin x.drawing.pathCount), (rep.graph.vertex b).val = cylinderM2Point x.drawing.pathCount j →
          ∀ (f : Curve ClosedCylinder), ParametrizesSet f (walkDrawing G W).U
            (rep.graph.vertex (rep.source i)).val (rep.graph.vertex b).val →
            (x.drawing.pathCount : ℝ) * windingNumber f =
              (((x.drawing.pathCount : ℤ) * ((s'.regs 21 : ℤ) - (s'.regs 22 : ℤ)) +
                (j.val : ℤ) - (i.val : ℤ) : ℤ) : ℝ) := by
  obtain ⟨reference, _, _, _, hturnlen, _⟩ := rep.turns
  obtain ⟨s', t, he, ht, harr, b, W, hsupport, hsimple, hturn⟩ :=
    gm06Alg511PathTurnProg_exec x.drawing rep.graph x.edgeTurns hturnlen
      (rep.source i) tail hnd hadj s hw hn hsquare hends hproduct hkeys hwords hN hvertices
  obtain ⟨W', hsupport', hturn'⟩ := alg511_exists_actual_walk_of_labelWalk rep.graph x.edgeTurns W
  have hinj : Function.Injective (fun v => (rep.graph.vertex v).val) :=
    Subtype.val_injective.comp rep.graph.vertex.injective
  have hs' : W'.IsSimple := by
    change W'.support.Nodup
    rw [hsupport']
    exact hsimple.map hinj
  refine ⟨s', t, he, ht, harr, b, W', by rw [hsupport', hsupport], hs', ?_⟩
  intro j hj f hf
  obtain ⟨angle, hM1, hM2, hwinding⟩ :=
    alg511_normalized_walk_winding rep.graph x.edgeTurns rep.turns
  have h := hwinding W' hs' f hf
  rw [congrArg angle (rep.source_point i), congrArg angle hj, hM1, hM2] at h
  have hscaled := alg511_scaled_winding_of_relative_turn hk i j f
    (alg511InterpretedWalkTurn rep.graph x.edgeTurns W')
    (alg511_relative_curveTurn_iff.mpr h)
  rw [hturn', ← hturn] at hscaled
  exact hscaled

end GraphMinor.GM06
