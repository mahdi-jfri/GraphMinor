module

public import GraphMinor.Compute.Case3StepsRuralLift
public import GraphMinor.Compute.Case3StepsCornerOrder

/-!
# Lifting the compact division to the original wall society

For step (5) of XIII (9.9), page 104, we restore multigraph edges in the compact
compass and then rename its labels back to the input graph. The graph and its
corner order become exactly the wall society. The rural division is carried
along this renaming.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.GM09 GraphMinor.GM13 GraphMinor.Transport Classical

/-- A multigraph society with its boundary given in list order. -/
noncomputable def case3MultigraphSociety {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) : Society ℕ (ℕ × ℕ × ℕ) where
  G := D.toGMDigraph.toGraph
  Ω := relabelCyclicPerm ⟨Fin.val, Fin.val_injective⟩
    (case3SimpleSocietyInput D omega homega).toSociety.Ω
  finite_V := D.isFinite_toGMDigraph.finite_V
  finite_E := D.isFinite_toGMDigraph.finite_E
  bar_subset := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2

/-- The compact compass society, renamed back to the original graph labels. -/
noncomputable def case3CompassSociety {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    Society ℕ (ℕ × ℕ × ℕ) :=
  relabelSociety (origVertexEmb (compassEmb W) (compassEmb W).injective)
    (origEdgeEmb (compassEmb W) (compassEmb W).injective)
    (case3MultigraphSociety (case3CompactCompassMultigraph D W)
      (List.ofFn (compactCorner W h2 he))
      (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW)))

/-- The renamed compact compass society is the society of the original wall. -/
theorem case3CompassSociety_isWallSociety {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    IsWallSociety D.toGMDigraph.toGraph (W.toGMWall h2 he hW)
      (case3CompassSociety D W h2 he hW) := by
  constructor
  · change relabelGraph _ _ (case3CompactCompassMultigraph D W).toGMDigraph.toGraph = _
    rw [case3CompactCompassMultigraph_relabel]
    change D.toGMDigraph.toGraph.induce W.compassFinset.toNatSet =
      D.toGMDigraph.toGraph.induce (wallCompassVerts D.toGMDigraph.toGraph (W.toGMWall h2 he hW))
    apply congrArg (fun V => D.toGMDigraph.toGraph.induce V)
    exact W.val_compassFinset_eq_wallCompassVerts h2 he hW
  · change relabelCyclicPerm _ (relabelCyclicPerm _
      (cyclicPermOfNodupList (List.ofFn (compactCorner W h2 he))
        (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW)))) = _
    exact case3CompactCornerOrder_relabel D W h2 he hW

/-- The same compass society is the wall society after deleting `X`. -/
theorem case3CompassSociety_isWallSociety_delGraph {h n : ℕ} {G D : MultiDigraph n}
    {X : Finset (Fin n)} (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h)
    (hW : W.IsValid) (hD : G.deleteVertices X = D) :
    IsWallSociety (delGraph G X) (W.toGMWall h2 he hW)
      (case3CompassSociety D W h2 he hW) := by
  have hs := case3CompassSociety_isWallSociety D W h2 he hW
  exact ⟨hs.1.trans (W.wallCompass_delGraph_eq_wallCompass_toGMDigraph h2 he hW hD).symm, hs.2⟩

/-- The rural division obtained on the compact simple compass lifts to a rural
division of the original multigraph wall society. Parallel copies stay in the
member of their simple edge. Every loop is assigned to one member containing
its vertex, using `case3LoopOwner`. -/
theorem case3CompassDivision_lift {h n : ℕ} (D : MultiDigraph n)
    (W : WallOfHeight h D) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (F : Set (Alg86Subgraph (case3CompactCompassMultigraph D W).toSimpleGraph))
    (hR : IsRuralDivision
      (case3SimpleSocietyInput (case3CompactCompassMultigraph D W)
        (List.ofFn (compactCorner W h2 he))
        (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW))).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    (assignment : Case3LoopAssignment
      (case3SimpleSocietyInput (case3CompactCompassMultigraph D W)
        (List.ofFn (compactCorner W h2 he))
        (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW))) F :=
      case3DefaultLoopAssignment
        (case3SimpleSocietyInput (case3CompactCompassMultigraph D W)
          (List.ofFn (compactCorner W h2 he))
          (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW))) F hR.isDivision) :
    IsRuralDivision (case3CompassSociety D W h2 he hW)
      (relabelGraph (origVertexEmb (compassEmb W) (compassEmb W).injective)
        (origEdgeEmb (compassEmb W) (compassEmb W).injective) ''
          case3LiftedFamily (case3CompactCompassMultigraph D W)
            (List.ofFn (compactCorner W h2 he))
            (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW)) F hR.isDivision assignment) := by
  apply IsRuralDivision.relabel
  exact case3LiftedFamily_isRuralDivision (case3CompactCompassMultigraph D W)
    (List.ofFn (compactCorner W h2 he))
    (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW)) F hR
    (case3MultigraphSociety (case3CompactCompassMultigraph D W)
      (List.ofFn (compactCorner W h2 he))
      (List.nodup_ofFn.mpr (compactCorner_injective W h2 he hW))) rfl rfl assignment

end GraphMinor.Compute
