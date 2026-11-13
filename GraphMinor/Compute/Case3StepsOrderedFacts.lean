module

public import GraphMinor.Compute.Case3StepsCoreGroupingOrdered
public import GraphMinor.Compute.Case3StepsScanInputs

/-!
# Facts about the ordered compass data

The abstract data returned by the grouping computation are the computed
compass graph and corners. Their full edge count is bounded by the deleted
ambient graph, and validity of the computed division gives rurality. The
retained inverse array is the counted increasing vertex list followed by
its unused padding.
-/

public section

namespace GraphMinor.Compute

/-- The ordered compact graph retains at most the deleted ambient copies. -/
theorem case3OrderedCompass_numEdges_le {h N : ℕ} (G : MultiDigraph N)
    (X : Finset (Fin N)) (W : WallOfHeight h (G.deleteVertices X))
    (S : Finset (Fin N)) (hS : S = W.compassFinset) (D : MultiDigraph S.card)
    (hD : HEq D (case3CompactCompassMultigraph (G.deleteVertices X) W)) :
    D.numEdges ≤ (G.deleteVertices X).numEdges := by
  subst S
  cases hD
  exact case3NumEdges_induce_le (G.deleteVertices X) (compassEmb W).toEmbedding

/-- The valid division on the ordered data is rural, by the computed
compact wall-society division theorem. -/
theorem case3OrderedCompass_isRuralDivision {h N : ℕ} (G : MultiDigraph N)
    (X : Finset (Fin N)) (W : WallOfHeight h (G.deleteVertices X))
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (S : Finset (Fin N)) (hS : S = W.compassFinset) (D : MultiDigraph S.card)
    (hD : HEq D (case3CompactCompassMultigraph (G.deleteVertices X) W))
    (om : List (Fin S.card)) (hom : om.Nodup)
    (homEq : HEq om (List.ofFn (compactCorner W h2 he))) :
    let x := case3SimpleSocietyInput D om hom
    ∀ d : Alg86DivisionOutput x, IsValidAlg86DivisionOutput x d →
      GM13.IsRuralDivision x.toSociety (Alg86Subgraph.toGMGraph '' case3SelectedMembers x d.core.Z) := by
  subst S
  cases hD
  cases homEq
  exact case3CompactSelectedMembers_isRuralDivision (G.deleteVertices X) W h2 he hW

/-- The increasing vertex list is the same ordered list used by compact labels. -/
theorem case3BoundaryVertices_map_eq_ofFn {N : ℕ} (S : Finset (Fin N)) :
    (case3BoundaryVertices S).map Fin.val =
      List.ofFn (fun u : Fin S.card => ((S.orderEmbOfFin rfl).toEmbedding u).1) := by
  apply List.ext_getElem (by rw [List.length_map, case3BoundaryVertices_length, List.length_ofFn])
  intro i hi hi'
  have hic : i < S.card := by simpa only [List.length_ofFn] using hi'
  rw [← List.getD_eq_getElem _ 0 hi, case3BoundaryVertices_getD_orderEmb S ⟨i, hic⟩,
    List.getElem_ofFn]
  rfl

/-- The retained inverse array has exactly the counted prefix used by the
final compass-list writer. -/
theorem case3ScanInverseLabels_eq_ofFn {N : ℕ} (S : Finset (Fin N)) :
    case3ScanInverseLabels S =
      List.ofFn (fun u : Fin S.card => ((S.orderEmbOfFin rfl).toEmbedding u).1) ++
        List.replicate (N - S.card) 0 := by
  rw [case3ScanInverseLabels, case3BoundaryVertices_map_eq_ofFn]

end GraphMinor.Compute
