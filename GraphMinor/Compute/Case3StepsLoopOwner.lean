module

public import GraphMinor.Compute.Case3StepsLift

/-!
# Assigning loops without changing division boundaries

A simple division covers every vertex. Assign all loops at a vertex to one
member containing it. If another member also contains that vertex, condition
(ii) of the division puts it on both boundaries. Restoring loops therefore
adds no boundary vertex. Parallel copies add none either, by the edge formula
in `Case3StepsLift`.

The division conditions used here are those of Graph Minors XIII, Section 8,
pages 95--96. These lemmas concern boundaries and loop assignment. They do not
yet prove all conditions of a rural division for the lifted family.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Classical

/-- Each vertex of a simple society belongs to a member of its division. -/
theorem case3Division_vertex_covered {x : Alg81Input}
    {F : Set (Alg86Subgraph x.G)}
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    (u : Fin x.n) : ∃ A ∈ F, u ∈ A.verts := by
  have hu : u ∈ V(x.toSociety.G) := by
    rw [Alg81Input.toSociety_G]
    trivial
  rw [← hdiv.sUnion_eq, GM09.vertexSet_subgraphSUnion] at hu
  obtain ⟨B, hB, huB⟩ := Set.mem_iUnion₂.mp hu
  obtain ⟨A, hA, rfl⟩ := hB
  exact ⟨A, hA, huB⟩

/-- One member containing `u`, to which every loop at `u` is assigned. -/
noncomputable def case3LoopOwner (x : Alg81Input) (F : Set (Alg86Subgraph x.G))
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    (u : Fin x.n) : Alg86Subgraph x.G :=
  (case3Division_vertex_covered hdiv u).choose

/-- The selected loop owner is a member and contains the vertex. -/
theorem case3LoopOwner_spec (x : Alg81Input) (F : Set (Alg86Subgraph x.G))
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    (u : Fin x.n) :
    case3LoopOwner x F hdiv u ∈ F ∧ u ∈ (case3LoopOwner x F hdiv u).verts := by
  exact (case3Division_vertex_covered hdiv u).choose_spec

/-- A choice of a member containing each vertex. These are the data needed
to assign all loops at a vertex to one member when restoring multigraph edges. -/
structure Case3LoopAssignment (x : Alg81Input) (F : Set (Alg86Subgraph x.G)) where
  /-- The member to which the loops at each vertex are assigned. -/
  member : Fin x.n → F
  /-- A loop is assigned only to a member containing its vertex. -/
  contains_vertex : ∀ u, u ∈ (member u).1.verts

/-- The existence of a containing member follows from division coverage. -/
noncomputable def case3DefaultLoopAssignment (x : Alg81Input) (F : Set (Alg86Subgraph x.G))
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F)) :
    Case3LoopAssignment x F where
  member u := ⟨case3LoopOwner x F hdiv u, (case3LoopOwner_spec x F hdiv u).1⟩
  contains_vertex u := (case3LoopOwner_spec x F hdiv u).2

/-- The vertices whose loops are assigned to one member by a specified choice. -/
noncomputable def case3AssignedLoops {x : Alg81Input} {F : Set (Alg86Subgraph x.G)}
    (assignment : Case3LoopAssignment x F) (A : Alg86Subgraph x.G) : Finset (Fin x.n) :=
  Finset.univ.filter (fun u => (assignment.member u).1 = A)

/-- Membership in a specified loop assignment. -/
theorem mem_case3AssignedLoops {x : Alg81Input} {F : Set (Alg86Subgraph x.G)}
    (assignment : Case3LoopAssignment x F) (A : Alg86Subgraph x.G) (u : Fin x.n) :
    u ∈ case3AssignedLoops assignment A ↔ (assignment.member u).1 = A := by
  simp only [case3AssignedLoops, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Vertices whose loops are assigned to `A`. The choice is shared by all
members, so a loop is never assigned twice. -/
noncomputable def case3LoopVertices (x : Alg81Input) (F : Set (Alg86Subgraph x.G))
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    (A : Alg86Subgraph x.G) : Finset (Fin x.n) :=
  Finset.univ.filter (fun u => case3LoopOwner x F hdiv u = A)

/-- Membership in the loop assignment is equality with the chosen owner. -/
theorem mem_case3LoopVertices (x : Alg81Input) (F : Set (Alg86Subgraph x.G))
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    (A : Alg86Subgraph x.G) (u : Fin x.n) :
    u ∈ case3LoopVertices x F hdiv A ↔ case3LoopOwner x F hdiv u = A := by
  simp only [case3LoopVertices, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Condition (ii) of a division puts a shared vertex on both boundaries. -/
theorem case3Division_shared_vertex_boundary {x : Alg81Input}
    {F : Set (Alg86Subgraph x.G)}
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    {A B : Alg86Subgraph x.G} (hA : A ∈ F) (hB : B ∈ F) (hne : A ≠ B)
    {u : Fin x.n} (huA : u ∈ A.verts) (huB : u ∈ B.verts) :
    u ∈ alg86Boundary x A := by
  have hneq : A.toGMGraph ≠ B.toGMGraph :=
    fun h => hne (Alg86Subgraph.toGMGraph_injective h)
  have hu : u ∈ V(A.toGMGraph) ∩ V(B.toGMGraph) := ⟨huA, huB⟩
  rw [hdiv.vertex_inter_eq ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ hneq,
    divBoundary_toGMGraph, divBoundary_toGMGraph] at hu
  exact hu.1

/-- If the loops at a member vertex are assigned elsewhere, the vertex was
already on the simple boundary. This proves that omitted loops add no boundary. -/
theorem case3LoopVertices_not_mem_boundary {x : Alg81Input}
    {F : Set (Alg86Subgraph x.G)}
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    {A : Alg86Subgraph x.G} (hA : A ∈ F) {u : Fin x.n} (hu : u ∈ A.verts)
    (hnot : u ∉ case3LoopVertices x F hdiv A) :
    u ∈ alg86Boundary x A := by
  have howner := case3LoopOwner_spec x F hdiv u
  have hne : A ≠ case3LoopOwner x F hdiv u := by
    intro h
    exact hnot ((mem_case3LoopVertices x F hdiv A u).mpr h.symm)
  exact case3Division_shared_vertex_boundary hdiv hA howner.1 hne hu howner.2

/-- A vertex shared with the member receiving its loops was already on the
simple boundary, independently of how the containing member was chosen. -/
theorem case3AssignedLoops_not_mem_boundary {x : Alg81Input}
    {F : Set (Alg86Subgraph x.G)}
    (hdiv : GM13.IsSocietyDivision x.toSociety (Alg86Subgraph.toGMGraph '' F))
    (assignment : Case3LoopAssignment x F)
    {A : Alg86Subgraph x.G} (hA : A ∈ F) {u : Fin x.n} (hu : u ∈ A.verts)
    (hnot : u ∉ case3AssignedLoops assignment A) :
    u ∈ alg86Boundary x A := by
  have hne : A ≠ (assignment.member u).1 := by
    intro h
    exact hnot ((mem_case3AssignedLoops assignment A u).mpr h.symm)
  exact case3Division_shared_vertex_boundary hdiv hA (assignment.member u).2 hne
    hu (assignment.contains_vertex u)

/-- The underlying simple society of a multigraph, with a specified boundary
order, is an input of (8.6) (XIII, page 96). -/
noncomputable abbrev case3SimpleSocietyInput {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup) : Alg81Input where
  n := n
  G := D.toSimpleGraph
  decAdj := inferInstance
  omega := omega
  nodup_omega := homega

/-- Restoring all parallel copies and assigning loops to one member preserves
its boundary, under the map `u ↦ u.val` from the simple society's labels. -/
theorem case3LiftMember_boundary_eq {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (F : Set (Alg86Subgraph D.toSimpleGraph))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    {A : Alg86Subgraph D.toSimpleGraph} (hA : A ∈ F)
    (S : GM09.Society ℕ (ℕ × ℕ × ℕ)) (hS : S.G = D.toGMDigraph.toGraph)
    (hbar : S.Ω.bar = Fin.val '' (omega.toFinset : Set (Fin n)))
    (assignment : Case3LoopAssignment (case3SimpleSocietyInput D omega homega) F :=
      case3DefaultLoopAssignment (case3SimpleSocietyInput D omega homega) F hdiv) :
    GM13.divBoundary S
      (case3LiftMember D A (case3AssignedLoops assignment A)) =
        Fin.val '' (alg86Boundary (case3SimpleSocietyInput D omega homega) A :
          Set (Fin (case3SimpleSocietyInput D omega homega).n)) := by
  let x := case3SimpleSocietyInput D omega homega
  ext v
  constructor
  · intro hv
    obtain ⟨u, hu, rfl⟩ := hv.1
    have hb := (case3LiftMember_boundary_iff D A (case3AssignedLoops assignment A) S hS u).mp hv
    refine ⟨u, ?_, rfl⟩
    rcases hb.2 with hb | hb | hb
    · apply (mem_alg86Boundary x A u).mpr
      refine ⟨hu, Or.inl ?_⟩
      rw [hbar] at hb
      obtain ⟨w, hw, heq⟩ := hb
      exact Fin.val_injective heq ▸ hw
    · exact (mem_alg86Boundary x A u).mpr ⟨hu, Or.inr hb⟩
    · exact case3AssignedLoops_not_mem_boundary hdiv assignment hA hu hb.2
  · rintro ⟨u, hu, rfl⟩
    apply (case3LiftMember_boundary_iff D A (case3AssignedLoops assignment A) S hS u).mpr
    have hb := (mem_alg86Boundary x A u).mp hu
    refine ⟨hb.1, ?_⟩
    rcases hb.2 with hb | hb
    · exact Or.inl (hbar ▸ ⟨u, hb, rfl⟩)
    · exact Or.inr (Or.inl hb)

end GraphMinor.Compute
