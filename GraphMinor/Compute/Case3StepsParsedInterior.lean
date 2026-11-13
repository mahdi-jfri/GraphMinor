module

public import GraphMinor.Compute.Case3StepsRecordDivision
public import GraphMinor.Compute.Case3StepsRecordDecomposition
public import GraphMinor.Compute.Case3StepsInteriorMath

/-!
# Interior decompositions after decoding the block

Every decoded member comes from a retained selected record. Its vertices
are the original-label image of the selected vertices. Disjointness from
the whole wall perimeter therefore gives precisely the compact interior
test used by the scan. The retained valid code supplies the decomposition
returned by the frozen block lookup.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- Valid codes retained for the compact interior test give all the
interior decompositions claimed by the frozen block decoder. -/
theorem case3ParsedBlock_interior_decompositions {n N h B : ℕ}
    (D : MultiDigraph n) (omega : List (Fin n)) (homega : omega.Nodup) (Z : Finset (Fin n))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (e : Fin n ↪ Fin N) (G : MultiDigraph N) (X : Finset (Fin N))
    (p : ParsedCase3Block (G.deleteVertices X) X)
    (W : WallOfHeight h (G.deleteVertices X)) (h2 : 2 ≤ h) (heven : Even h) (hW : W.IsValid)
    (hpwall : p.toGMWall = W.toGMWall h2 heven hW)
    (hbase : relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      D.toGMDigraph.toGraph ≤ delGraph G X)
    (entries : List (Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z × List ℕ))
    (hm : p.members = case3SelectedRecordList (case3SimpleSocietyInput D omega homega) D Z e entries)
    (hcodes : ∀ q ∈ entries,
      Disjoint (case3SelectedMember (case3SimpleSocietyInput D omega homega) Z q.1).verts
        (case3PullbackBits e W.perimeterFinset) →
      IsValidBranchDecompCode B (case3CompactMember (case3SimpleSocietyInput D omega homega) D Z q.1) q.2)
    (block : List ℕ) (hparse : parseCase3Block (G.deleteVertices X) X block = some p) :
    ∀ A : Graph ℕ (ℕ × ℕ × ℕ), GM13.IsInteriorMember p.toGMWall p.toDivision A →
      let bd := case3Decoder.branchDecomp N G X block A
      E(A).ncard ≤ 1 ∨ (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
        GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ B) := by
  intro A hA
  rcases hA with ⟨hmem, hdj⟩
  obtain ⟨r, hr, rfl⟩ := hmem
  rw [hm] at hr
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hr
  have hrecord := case3SelectedRecord_toSubgraph D omega homega Z hdiv e (delGraph G X) hbase q.1 q.2
  dsimp only at hrecord
  change Disjoint V((case3SelectedRecord (case3SimpleSocietyInput D omega homega) D Z e q.1 q.2).toSubgraph
    (delGraph G X)) V(p.toGMWall.perimeter) at hdj
  rw [hpwall, hrecord, vertexSet_relabelGraph, case3LiftMember_vertexSet,
    WallOfHeight.vertexSet_perimeter_toGMWall_eq] at hdj
  have hint := (case3PullbackBits_disjoint_orig_iff e e.injective _ W.perimeterFinset).mpr hdj
  have hcode := hcodes q hq hint
  let x := case3SimpleSocietyInput D omega homega
  let A := case3SelectedMember x Z q.1
  let orig := e ∘ A.verts.orderEmbOfFin rfl
  have hinj := e.injective.comp (A.verts.orderEmbOfFin rfl).injective
  have hrel := case3SelectedRecord_relabel D omega homega Z hdiv q.1 e
  have hsub : relabelGraph (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
      (case3CompactMember x D Z q.1).toGMDigraph.toGraph ≤ delGraph G X := by
    rw [hrel]
    exact (relabelGraph_mono (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      (case3LiftMember_le D A (case3AssignedLoops (case3OrderedLoopAssignment x Z hdiv) A))).trans hbase
  have hr' : case3SelectedRecord x D Z e q.1 q.2 ∈ p.members := by
    rw [hm]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact case3ParsedBlock_record_decomposition (case3CompactMember x D Z q.1)
    (origVertexEmb orig hinj) (origEdgeEmb orig hinj) q.2 hcode G X p block hparse hr' hsub

end GraphMinor.Compute
