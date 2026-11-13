module

public import GraphMinor.Compute.Case3StepsOriginalMemberMath
import GraphMinor.Compute.Algorithm99TransportMove

/-!
# Membership and vertices after restoring original labels

The member encoded for step (8) is the selected member in the renamed
lifted family. Its induced vertex set is exactly the original-label image
of the compact member vertices. These facts connect the output arrays to
the rural division, rather than just to an isomorphic graph.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- Restoring a selected member places it in the same renamed lifted
family used to prove the rural division. -/
theorem case3OriginalSelectedMember_mem {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (omega : List (Fin S.card)) (homega : omega.Nodup)
    (Z : Finset (Fin S.card))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    (case3PushMultigraph S (case3RoutedMember x D Z (case3RawIndexLabel x i.1))).toGMDigraph.toGraph.induce
      (A.verts.image (S.orderEmbOfFin rfl)).toNatSet ∈
        relabelGraph (origVertexEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective)
          (origEdgeEmb (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl).injective) ''
          case3LiftedFamily D omega homega (case3SelectedMembers x Z) hdiv
            (case3OrderedLoopAssignment x Z hdiv) := by
  dsimp only
  rw [case3OriginalSelectedMember_eq_relabel S D omega homega Z hdiv i]
  exact ⟨_, ⟨_, Set.mem_range_self i, rfl⟩, rfl⟩

/-- The original member vertex list describes precisely the graph's
vertices, including the isolated boundary vertices. -/
theorem case3OriginalSelectedMember_vertexSet {N : ℕ} (S : Finset (Fin N))
    (D : MultiDigraph S.card) (omega : List (Fin S.card)) (homega : omega.Nodup)
    (Z : Finset (Fin S.card))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    V((case3PushMultigraph S (case3RoutedMember x D Z (case3RawIndexLabel x i.1))).toGMDigraph.toGraph.induce
      (A.verts.image (S.orderEmbOfFin rfl)).toNatSet) =
        (A.verts.image (S.orderEmbOfFin rfl)).toNatSet := by
  dsimp only
  rw [case3OriginalSelectedMember_eq_relabel S D omega homega Z hdiv i,
    vertexSet_relabelGraph, case3LiftMember_vertexSet]
  exact (toNatSet_image_orig (S.orderEmbOfFin rfl).injective _).symm

/-- Every restored member vertex remains inside the original compass
vertex set. -/
theorem case3OriginalMember_image_subset {N : ℕ} (S : Finset (Fin N))
    (T : Finset (Fin S.card)) : T.image (S.orderEmbOfFin rfl) ⊆ S := by
  intro u hu
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
  exact S.orderEmbOfFin_mem rfl v

end GraphMinor.Compute
