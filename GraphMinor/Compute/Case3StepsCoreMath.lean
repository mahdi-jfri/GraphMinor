module

public import GraphMinor.Compute.Case3StepsInputProg
public import GraphMinor.Compute.Case3StepsDivision

/-!
# Validity and size of the compact compass input

Flatness excludes the cross output of (8.6). The compact multigraph and the
compact simple compass have the same simple edges, so the size bound already
proved for the compass society applies to the program's input as well.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Flatness rules out a cross in the society input written by the program. -/
theorem case3CompactSocietyInput_noCross {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (hflat : W.IsFlatWall h2) :
    ¬ HasCrossInSociety (case3CompactSocietyInput D W h2 he hW).G
      (case3CompactSocietyInput D W h2 he hW).omega := by
  change ¬ HasCrossInSociety (case3CompactCompassMultigraph D W).toSimpleGraph
    (List.ofFn (compactCorner W h2 he))
  rw [case3CompactCompassMultigraph_toSimpleGraph]
  exact not_hasCrossInSociety_case3Alg81Input D W h2 he hW hflat

/-- Replacing the compact graph by the compact multigraph's underlying simple
graph does not change the (8.6) size parameter. -/
theorem case3CompactSocietyInput_size_eq {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    alg81Size (case3CompactSocietyInput D W h2 he hW) =
      alg81Size (case3Alg81Input D W h2 he hW) := by
  have hE : (case3CompactCompassMultigraph D W).toSimpleGraph.edgeFinset =
      (compactCompassGraph D W).edgeFinset := by
    apply Finset.coe_inj.mp
    rw [SimpleGraph.coe_edgeFinset, SimpleGraph.coe_edgeFinset,
      case3CompactCompassMultigraph_toSimpleGraph]
  exact congrArg (fun e : Finset (Sym2 (Fin (compassCard W))) =>
    societySize (compassCard W) e.card) hE

/-- The compact input fits the size bound used by the (9.9) loop. -/
theorem case3CompactSocietyInput_size_le {h n : ℕ} (G : MultiDigraph n)
    (X : Finset (Fin n)) (W : WallOfHeight h (G.deleteVertices X))
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    alg81Size (case3CompactSocietyInput (G.deleteVertices X) W h2 he hW) ≤
      (n + 1) * (G.numEdges + n + 1) := by
  rw [case3CompactSocietyInput_size_eq]
  apply (alg81Size_case3Alg81Input_le _ W h2 he hW).trans
  exact Nat.mul_le_mul_left (n + 1)
    (Nat.add_le_add_right (Nat.add_le_add_right (G.numEdges_deleteVertices_le X) n) 1)

end GraphMinor.Compute
