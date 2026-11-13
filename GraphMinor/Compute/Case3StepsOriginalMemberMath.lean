module

public import GraphMinor.Compute.Case3StepsPushMemberGraph
public import GraphMinor.Compute.Case3StepsRoutedMember
public import GraphMinor.Compute.Case3StepsCompassLift
import GraphMinor.Compute.Algorithm99TransportMove

/-!
# The original-label member and its boundary

The restored multigraph restricted to the image of a selected member is
exactly that member in the renamed lifted division. It has all the member's
edges. Its boundary is the image of the simple member boundary, because
restoring parallel copies and assigning each loop once preserves boundaries.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- The restored selected member is exactly its member in the lifted and
renamed division, including its isolated boundary vertices. -/
theorem case3OriginalSelectedMember_eq_relabel {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (omega : List (Fin S.card)) (homega : omega.Nodup)
    (Z : Finset (Fin S.card))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    (case3PushMultigraph S (case3RoutedMember x D Z (case3RawIndexLabel x i.1))).toGMDigraph.toGraph.induce
      (A.verts.image (S.orderEmbOfFin rfl)).toNatSet =
        relabelGraph (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
          (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
          (case3LiftMember D A (case3AssignedLoops (case3OrderedLoopAssignment x Z hdiv) A)) := by
  let x := case3SimpleSocietyInput D omega homega
  let A := case3SelectedMember x Z i
  let R := case3RoutedMember x D Z (case3RawIndexLabel x i.1)
  change (case3PushMultigraph S R).toGMDigraph.toGraph.induce _ = _
  rw [← case3PushMultigraph_relabel_induce S R A.verts]
  apply congrArg (relabelGraph _ _)
  change R.toGMDigraph.toGraph.induce A.verts.toNatSet = _
  rw [show R = _ from case3RoutedMember_eq_lift D omega homega Z hdiv i]
  rfl

/-- The ambient-label multigraph encoding has exactly the edges of the
original selected member, even though its ambient vertex type is larger. -/
theorem case3OriginalSelectedMember_edgeSet {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (omega : List (Fin S.card)) (homega : omega.Nodup)
    (Z : Finset (Fin S.card))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    let P := case3PushMultigraph S (case3RoutedMember x D Z (case3RawIndexLabel x i.1))
    E(P.toGMDigraph.toGraph) = E(P.toGMDigraph.toGraph.induce (A.verts.image (S.orderEmbOfFin rfl)).toNatSet) := by
  dsimp only
  rw [case3PushMultigraph_edgeSet, case3OriginalSelectedMember_eq_relabel S D omega homega Z hdiv i,
    edgeSet_relabelGraph, case3LiftMember_edgeSet]
  exact congrArg (fun R : MultiDigraph S.card =>
    origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective '' E(R.toGMDigraph.toGraph))
      (case3RoutedMember_eq_lift D omega homega Z hdiv i)

/-- The multigraph society's boundary uses the same listed vertices as the
simple society, through natural-number vertex labels. -/
theorem case3MultigraphSociety_bar {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) :
    (case3MultigraphSociety D omega homega).Ω.bar = Fin.val '' (omega.toFinset : Set (Fin n)) := by
  rw [case3MultigraphSociety, relabelCyclicPerm_bar]
  apply congrArg (Set.image Fin.val)
  ext u
  rw [Alg81Input.toSociety_bar]
  exact List.mem_toFinset.symm

/-- The boundary of the renamed member is exactly the ordered image of
its simple member boundary. -/
theorem case3OriginalSelectedMember_boundary {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (omega : List (Fin S.card)) (homega : omega.Nodup)
    (Z : Finset (Fin S.card))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    GM13.divBoundary
      (relabelSociety (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
        (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
        (case3MultigraphSociety D omega homega))
      ((case3PushMultigraph S (case3RoutedMember x D Z (case3RawIndexLabel x i.1))).toGMDigraph.toGraph.induce
        (A.verts.image (S.orderEmbOfFin rfl)).toNatSet) =
      ((alg86Boundary x A).image (S.orderEmbOfFin rfl)).toNatSet := by
  dsimp only
  rw [case3OriginalSelectedMember_eq_relabel S D omega homega Z hdiv i, divBoundary_relabelSociety]
  rw [case3LiftMember_boundary_eq D omega homega _ hdiv (Set.mem_range_self i)
    (case3MultigraphSociety D omega homega) rfl (case3MultigraphSociety_bar D omega homega)
    (case3OrderedLoopAssignment (case3SimpleSocietyInput D omega homega) Z hdiv)]
  exact (toNatSet_image_orig (S.orderEmbOfFin rfl).injective _).symm

end GraphMinor.Compute
