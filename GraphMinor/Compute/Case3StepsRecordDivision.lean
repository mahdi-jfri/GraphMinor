module

public import GraphMinor.Compute.Case3StepsRecordGraph
public import GraphMinor.Compute.Case3StepsBranchRecord
public import GraphMinor.Compute.Case3StepsDivisionLift

/-!
# Decoding the complete selected member family

The record graph equals the renamed full member inside any ambient graph
containing the renamed compass. A record history covering every selected
candidate therefore decodes to exactly the lifted rural division. This
uses full edge copies and retains isolated vertices of each member.
-/

public section

namespace GraphMinor.Compute

open Graph GraphMinor.Transport

/-- Reading the lists of a selected record restores the corresponding full
member in any ambient graph containing the original-label compass. -/
theorem case3SelectedRecord_toSubgraph {n N : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) (Z : Finset (Fin n))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (e : Fin n ↪ Fin N) (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (hG₀ : relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      D.toGMDigraph.toGraph ≤ G₀)
    (i : Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z) (code : List ℕ) :
    let x := case3SimpleSocietyInput D omega homega
    let A := case3SelectedMember x Z i
    (case3SelectedRecord x D Z e i code).toSubgraph G₀ =
      relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
        (case3LiftMember D A (case3AssignedLoops (case3OrderedLoopAssignment x Z hdiv) A)) := by
  dsimp only
  have hr := case3SelectedRecord_relabel D omega homega Z hdiv i e
  dsimp only at hr
  have hsub := (relabelGraph_mono (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
    (case3LiftMember_le D (case3SelectedMember (case3SimpleSocietyInput D omega homega) Z i)
      (case3AssignedLoops (case3OrderedLoopAssignment (case3SimpleSocietyInput D omega homega) Z hdiv)
        (case3SelectedMember (case3SimpleSocietyInput D omega homega) Z i)))).trans hG₀
  unfold case3SelectedRecord
  rw [case3BranchRecord_toSubgraph _ _ _ code G₀ (by rw [hr]; exact hsub)]
  exact hr

/-- Covering every candidate makes the family obtained from the member
records exactly the original-label lifted division. -/
theorem case3SelectedRecordList_toDivision {n N : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) (Z : Finset (Fin n))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' case3SelectedMembers (case3SimpleSocietyInput D omega homega) Z))
    (e : Fin n ↪ Fin N) (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (hG₀ : relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective)
      D.toGMDigraph.toGraph ≤ G₀)
    (entries : List (Case3SelectedGroup (case3SimpleSocietyInput D omega homega) Z × List ℕ))
    (hcover : ∀ i, i ∈ entries.map Prod.fst) :
    let x := case3SimpleSocietyInput D omega homega
    {A | ∃ r ∈ case3SelectedRecordList x D Z e entries, r.toSubgraph G₀ = A} =
      relabelGraph (origVertexEmb e e.injective) (origEdgeEmb e e.injective) ''
        case3LiftedFamily D omega homega (case3SelectedMembers x Z) hdiv
          (case3OrderedLoopAssignment x Z hdiv) := by
  dsimp only
  ext A
  constructor
  · rintro ⟨r, hr, rfl⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    rw [case3SelectedRecord_toSubgraph D omega homega Z hdiv e G₀ hG₀ p.1 p.2]
    exact ⟨_, ⟨_, Set.mem_range_self p.1, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
    obtain ⟨p, hp, hip⟩ := List.mem_map.mp (hcover i)
    refine ⟨case3SelectedRecord (case3SimpleSocietyInput D omega homega) D Z e p.1 p.2,
      List.mem_map.mpr ⟨p, hp, rfl⟩, ?_⟩
    cases hip
    exact case3SelectedRecord_toSubgraph D omega homega Z hdiv e G₀ hG₀ p.1 p.2

end GraphMinor.Compute
