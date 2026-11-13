module

public import GraphMinor.Compute.GM13SocietyOwnerTable
public import GraphMinor.Compute.Case3StepsCompassLift

/-!
# Reading a multigraph rural division from records and loop owners

The member records specify the simple edge classes. Each such class keeps
all its actual parallel edges. A separate owner table specifies the member
receiving every loop. The reader only looks up records and owner indices.
The existing rural-division lift proves the six division conditions and
rurality for this explicit assignment, including isolated vertices.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph GM13 GM09

/-- Simple members read from an explicit list of vertex and edge records. -/
def gm13RecordFamily {n : ℕ} (D : MultiDigraph n)
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) : Set (Alg86Subgraph D.toSimpleGraph) :=
  {A | A ∈ L.map (alg86SubgraphOfPair D.toSimpleGraph)}

/-- Loops assigned to a member by the stored one-based owner indices. This
reader performs no graph search and makes no choice of a member. -/
noncomputable def gm13RecordLoops {n : ℕ} (D : MultiDigraph n)
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (owners : List ℕ)
    (A : Alg86Subgraph D.toSimpleGraph) : Finset (Fin n) :=
  open Classical in
  Finset.univ.filter (fun v => owners.getD v.1 0 ≠ 0 ∧
    ∃ p, L[owners.getD v.1 0 - 1]? = some p ∧ alg86SubgraphOfPair D.toSimpleGraph p = A)

/-- The actual division represented by the simple records and explicit loop
owners. All parallel copies of each listed edge are retained. -/
noncomputable def gm13RecordedDivision {n : ℕ} (D : MultiDigraph n)
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (owners : List ℕ) :
    Set (Graph ℕ (ℕ × ℕ × ℕ)) :=
  (fun A => case3LiftMember D A (gm13RecordLoops D L owners A)) '' gm13RecordFamily D L

private theorem gm13_owner_pos {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n)))
    (hcover : ∀ v : Fin n, ∃ p ∈ L, v ∈ p.1) (v : Fin n) :
    0 < gm13LastOwner L v := by
  obtain ⟨p, hp, hv⟩ := hcover v
  have hn : gm13LastOwner L v ≠ 0 := fun h =>
    (gm13LastOwner_eq_zero_iff L v).mp h p hp hv
  exact Nat.pos_of_ne_zero hn

private def gm13RecordAssignment {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (L : List (Finset (Fin n) × List (Fin n × Fin n)))
    (hcover : ∀ v : Fin n, ∃ p ∈ L, v ∈ p.1) :
    Case3LoopAssignment (case3SimpleSocietyInput D omega homega) (gm13RecordFamily D L) where
  member v :=
    have hi : gm13LastOwner L v - 1 < L.length := by
      have hp := gm13_owner_pos L hcover v
      have hl := gm13LastOwner_le_length L v
      omega
    ⟨alg86SubgraphOfPair D.toSimpleGraph L[gm13LastOwner L v - 1],
      List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩⟩
  contains_vertex v := by
    obtain ⟨hi, hv⟩ := gm13LastOwner_spec L v (gm13_owner_pos L hcover v)
    exact hv

/-- Looking up the computed owner table returns its stored index. -/
theorem gm13LoopOwnerTable_getD {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (v : Fin n) :
    (gm13LoopOwnerTable L).getD v.1 0 = gm13LastOwner L v := by
  rw [List.getD_eq_getElem _ _ (by simpa only [gm13LoopOwnerTable, List.length_ofFn] using v.2)]
  simp only [gm13LoopOwnerTable, List.getElem_ofFn]

private theorem gm13RecordLoops_eq {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (L : List (Finset (Fin n) × List (Fin n × Fin n)))
    (hcover : ∀ v : Fin n, ∃ p ∈ L, v ∈ p.1) (A : Alg86Subgraph D.toSimpleGraph) :
    gm13RecordLoops D L (gm13LoopOwnerTable L) A =
      case3AssignedLoops (gm13RecordAssignment D omega homega L hcover) A := by
  classical
  ext v
  have hp := gm13_owner_pos L hcover v
  have hl := gm13LastOwner_le_length L v
  have hi : gm13LastOwner L v - 1 < L.length := by omega
  rw [mem_case3AssignedLoops]
  unfold gm13RecordLoops
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, gm13LoopOwnerTable_getD,
    ne_eq, Nat.ne_of_gt hp, not_false_eq_true, List.getElem?_eq_getElem hi, Option.some.injEq]
  change (∃ p, L[gm13LastOwner L v - 1] = p ∧ alg86SubgraphOfPair D.toSimpleGraph p = A) ↔
    alg86SubgraphOfPair D.toSimpleGraph L[gm13LastOwner L v - 1] = A
  constructor
  · rintro ⟨p, hp, hA⟩
    subst p
    exact hA
  · intro hA
    exact ⟨_, rfl, hA⟩

/-- The recorded multigraph division is rural whenever its simple member
records are a rural division. This uses only the written loop-owner table,
not a choice of members in the output reader. -/
theorem gm13RecordedDivision_isRural {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (L : List (Finset (Fin n) × List (Fin n × Fin n)))
    (hR : IsRuralDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' gm13RecordFamily D L)) :
    IsRuralDivision (case3MultigraphSociety D omega homega)
      (gm13RecordedDivision D L (gm13LoopOwnerTable L)) := by
  have hcover : ∀ v : Fin n, ∃ p ∈ L, v ∈ p.1 := by
    intro v
    obtain ⟨A, hA, hv⟩ := case3Division_vertex_covered hR.isDivision v
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hA
    exact ⟨p, hp, hv⟩
  let assignment := gm13RecordAssignment D omega homega L hcover
  have hr := case3LiftedFamily_isRuralDivision D omega homega (gm13RecordFamily D L)
    hR (case3MultigraphSociety D omega homega) rfl rfl assignment
  have heq : gm13RecordedDivision D L (gm13LoopOwnerTable L) =
      case3LiftedFamily D omega homega (gm13RecordFamily D L) hR.isDivision assignment := by
    unfold gm13RecordedDivision case3LiftedFamily
    congr 1
    funext A
    rw [gm13RecordLoops_eq D omega homega L hcover A]
  rw [heq]
  exact hr

end GraphMinor.Compute
