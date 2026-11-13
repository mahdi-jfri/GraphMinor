module

public import GraphMinor.Compute.Case3StepsParsedSociety
public import GraphMinor.Compute.Case3StepsRecordDivision
public import GraphMinor.Compute.Case3StepsCompactSelectedDivision

/-!
# Rurality of the parsed member family

The parsed society is the restored compass society. Complete record
coverage makes its decoded member family the full multigraph lift of the
computed (8.6) division. The proved rural-division lift then establishes
rurality for the actual objects read by the frozen decoder.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- A complete parsed record family is a rural division of the restored
multigraph society of the given rural simple division. -/
theorem case3ParsedBlock_isRuralDivision {n N : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) (Z : Finset (Fin n))
    (hR : GM13.IsRuralDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (e : Fin n ↪ Fin N) (G : MultiDigraph N) (X : Finset (Fin N))
    (p : ParsedCase3Block (G.deleteVertices X) X)
    (hbase : relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      D.toGMDigraph.toGraph ≤ delGraph G X)
    (entries : List (Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z × List ℕ))
    (hcover : ∀ i, i ∈ entries.map Prod.fst)
    (hm : p.members = case3SelectedRecordList (case3SimpleSocietyInput D omega homega) D Z e entries) :
    GM13.IsRuralDivision
      (relabelSociety (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
        (case3MultigraphSociety D omega homega)) p.toDivision := by
  let x := case3SimpleSocietyInput D omega homega
  have hfamily := case3SelectedRecordList_toDivision D omega homega Z hR.isDivision
    e (delGraph G X) hbase entries hcover
  have hrural := case3LiftedFamily_isRuralDivision D omega homega
    (case3SelectedMembers x Z) hR (case3MultigraphSociety D omega homega) rfl rfl
    (case3OrderedLoopAssignment x Z hR.isDivision)
  have hrenamed := GraphMinor.Transport.IsRuralDivision.relabel
    (origVertexEmb e e.injective) (origEdgeEmb e e.injective) hrural
  have heq : p.toDivision = relabelGraph (origVertexEmb e e.injective)
      (origEdgeEmb e e.injective) '' case3LiftedFamily D omega homega
        (case3SelectedMembers x Z) hR.isDivision (case3OrderedLoopAssignment x Z hR.isDivision) := by
    change {A | ∃ r ∈ p.members, r.toSubgraph (delGraph G X) = A} = _
    rw [hm]
    exact hfamily
  rw [heq]
  exact hrenamed

end GraphMinor.Compute
