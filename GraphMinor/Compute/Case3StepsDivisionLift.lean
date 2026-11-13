module

public import GraphMinor.Compute.Case3StepsLiftFamily
public import GraphMinor.Compute.Case3StepsPaths

/-!
# The division conditions after restoring multigraph edges

Graph Minors XIII, Section 8, pages 95--96, gives six conditions for a
division. We restore parallel copies of each member edge and assign loops to
one member containing their vertex. The boundary and path lemmas show that
this construction preserves the division conditions.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13 Classical

/-- The lifted family of a simple division, with each loop assigned once. -/
noncomputable def case3LiftedFamily {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (F : Set (Alg86Subgraph D.toSimpleGraph))
    (hdiv : IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    (assignment : Case3LoopAssignment (case3SimpleSocietyInput D omega homega) F :=
      case3DefaultLoopAssignment (case3SimpleSocietyInput D omega homega) F hdiv) : Set (Graph ℕ (ℕ × ℕ × ℕ)) :=
  (fun A => case3LiftMember D A
    (case3AssignedLoops assignment A)) '' F

/-- The union of all lifted members is the original multigraph graph. -/
theorem case3LiftedFamily_union {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (F : Set (Alg86Subgraph D.toSimpleGraph))
    (hdiv : IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    (assignment : Case3LoopAssignment (case3SimpleSocietyInput D omega homega) F :=
      case3DefaultLoopAssignment (case3SimpleSocietyInput D omega homega) F hdiv) :
    subgraphSUnion D.toGMDigraph.toGraph (case3LiftedFamily D omega homega F hdiv assignment) =
      D.toGMDigraph.toGraph := by
  let x := case3SimpleSocietyInput D omega homega
  let L := fun A => case3LiftMember D A (case3AssignedLoops assignment A)
  have hsub : ∀ Q ∈ L '' F, Q ≤ D.toGMDigraph.toGraph := by
    rintro Q ⟨A, _, rfl⟩
    exact case3LiftMember_le D A _
  change subgraphSUnion D.toGMDigraph.toGraph (L '' F) = _
  refine (Compatible.of_le_le (subgraphSUnion_le hsub) le_rfl).ext ?_ ?_
  · apply Set.Subset.antisymm (subgraphSUnion_le hsub).vertexSet_mono
    intro v hv
    let u : Fin n := ⟨v, hv⟩
    let A := (assignment.member u).1
    have hA : A ∈ F ∧ u ∈ A.verts := ⟨(assignment.member u).2, assignment.contains_vertex u⟩
    rw [vertexSet_subgraphSUnion]
    exact Set.mem_iUnion₂.mpr ⟨L A, ⟨A, hA.1, rfl⟩, ⟨u, hA.2, rfl⟩⟩
  · rw [edgeSet_subgraphSUnion hsub]
    apply Set.Subset.antisymm
    · rintro e he
      obtain ⟨Q, hQ, heQ⟩ := Set.mem_iUnion₂.mp he
      exact (hsub Q hQ).edgeSet_mono heQ
    · intro e he
      obtain ⟨A, hA, heA⟩ := case3LiftFamily_edge_covered D omega homega F hdiv he assignment
      exact Set.mem_iUnion₂.mpr ⟨L A, ⟨A, hA, rfl⟩, heA⟩

/-- The six division conditions of XIII, Section 8, pages 95--96, are
preserved when parallel copies and assigned loops are restored. -/
theorem case3LiftedFamily_isDivision {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (F : Set (Alg86Subgraph D.toSimpleGraph))
    (hdiv : IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    (S : Society ℕ (ℕ × ℕ × ℕ)) (hS : S.G = D.toGMDigraph.toGraph)
    (hbar : S.Ω.bar = Fin.val '' (omega.toFinset : Set (Fin n)))
    (assignment : Case3LoopAssignment (case3SimpleSocietyInput D omega homega) F :=
      case3DefaultLoopAssignment (case3SimpleSocietyInput D omega homega) F hdiv) :
    IsSocietyDivision S (case3LiftedFamily D omega homega F hdiv assignment) := by
  let x := case3SimpleSocietyInput D omega homega
  let L := fun A => case3LiftMember D A (case3AssignedLoops assignment A)
  have hb : ∀ A ∈ F, divBoundary S (L A) = Fin.val '' divBoundary x.toSociety A.toGMGraph := by
    intro A hA
    rw [divBoundary_toGMGraph]
    exact case3LiftMember_boundary_eq D omega homega F hdiv hA S hS hbar assignment
  have hV : ∀ A, V(L A) = Fin.val '' V(A.toGMGraph) := fun _ => rfl
  have hcard : ∀ A ∈ F, (divBoundary S (L A)).ncard =
      (divBoundary x.toSociety A.toGMGraph).ncard := by
    intro A hA
    rw [hb A hA, Set.ncard_image_of_injective _ Fin.val_injective]
  change IsSocietyDivision S (L '' F)
  refine
    { sub_of_mem := ?_
      sUnion_eq := ?_
      edge_disjoint := ?_
      vertex_inter_eq := ?_
      boundary_ncard_le_three := ?_
      disjoint_paths_to_bar := ?_
      internal_path := ?_
      boundary_injOn := ?_
      has_private_element := ?_ }
  · rintro Q ⟨A, hA, rfl⟩
    rw [hS]
    exact case3LiftMember_le D A _
  · rw [hS]
    exact case3LiftedFamily_union D omega homega F hdiv assignment
  · rintro Q R ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ hne
    exact case3LiftFamily_edge_disjoint D omega homega F hdiv hA hB (fun h => hne (congrArg L h)) assignment
  · rintro Q R ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ hne
    have hneq : A.toGMGraph ≠ B.toGMGraph := by
      intro h
      exact hne (congrArg L (Alg86Subgraph.toGMGraph_injective h))
    rw [hV, hV, hb A hA, hb B hB, ← Set.image_inter Fin.val_injective,
      ← Set.image_inter Fin.val_injective,
      hdiv.vertex_inter_eq ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ hneq]
  · rintro Q ⟨A, hA, rfl⟩
    rw [hcard A hA]
    exact hdiv.boundary_ncard_le_three ⟨A, hA, rfl⟩
  · rintro Q ⟨A, hA, rfl⟩
    obtain ⟨P, hdisj, hpaths⟩ := hdiv.disjoint_paths_to_bar ⟨A, hA, rfl⟩
    have hex : ∀ i : Fin (divBoundary S (L A)).ncard,
        ∃ (Q : Graph ℕ (ℕ × ℕ × ℕ)) (a b : Fin n),
          a ∈ divBoundary x.toSociety A.toGMGraph ∧ b ∈ x.toSociety.Ω.bar ∧
          IsGraphPathWithEnds S.G Q a.1 b.1 ∧
          V(Q) = Fin.val '' V(P (Fin.cast (hcard A hA) i)) := by
      intro i
      obtain ⟨a, ha, b, hbb, hp⟩ := hpaths (Fin.cast (hcard A hA) i)
      rw [Alg81Input.toSociety_G] at hp
      obtain ⟨Q, hQ, hQV⟩ := case3LiftPath_ambient D hp
      exact ⟨Q, a, b, ha, hbb, hS ▸ hQ, hQV⟩
    choose Q a b ha hbb hQ hQV using hex
    refine ⟨Q, ?_, ?_⟩
    · intro i j hij
      rw [hQV, hQV]
      apply Set.disjoint_left.mpr
      rintro v ⟨u, hu, rfl⟩ ⟨w, hw, heq⟩
      exact Set.disjoint_left.mp (hdisj (fun heq => hij (Fin.ext (congrArg (fun z : Fin (divBoundary x.toSociety A.toGMGraph).ncard => z.val) heq))))
        hu (Fin.val_injective heq ▸ hw)
    · intro i
      refine ⟨(a i).1, ?_, (b i).1, ?_, hQ i⟩
      · rw [hb A hA]
        exact ⟨a i, ha i, rfl⟩
      · rw [hbar]
        have hbi := hbb i
        rw [Alg81Input.toSociety_bar] at hbi
        exact ⟨b i, List.mem_toFinset.mpr hbi, rfl⟩
  · rintro Q ⟨A, hA, rfl⟩ a ha b hbb
    rw [hb A hA] at ha hbb
    obtain ⟨u, hu, rfl⟩ := ha
    obtain ⟨v, hv, rfl⟩ := hbb
    obtain ⟨P, hP, havoid⟩ := hdiv.internal_path ⟨A, hA, rfl⟩ u hu v hv
    obtain ⟨Q, hQ, hQV⟩ := case3LiftPath D A _ hP
    refine ⟨Q, hQ, ?_⟩
    rw [hQV, hb A hA, ← Set.image_inter Fin.val_injective]
    rintro z ⟨w, hw, rfl⟩
    rcases havoid hw with h | h
    · exact Or.inl (congrArg Fin.val h)
    · exact Or.inr (congrArg Fin.val h)
  · rintro Q ⟨A, hA, rfl⟩ R ⟨B, hB, rfl⟩ heq
    rw [hb A hA, hb B hB] at heq
    have heq' : divBoundary x.toSociety A.toGMGraph = divBoundary x.toSociety B.toGMGraph :=
      Set.image_injective.mpr Fin.val_injective heq
    have hAB := hdiv.boundary_injOn ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ heq'
    exact congrArg L (Alg86Subgraph.toGMGraph_injective hAB)
  · rintro Q ⟨A, hA, rfl⟩
    rcases hdiv.has_private_element ⟨A, hA, rfl⟩ with ⟨u, hu, hpriv⟩ | ⟨e, he, _⟩
    · refine Or.inl ⟨u.1, ⟨u, hu, rfl⟩, ?_⟩
      rintro R ⟨B, hB, rfl⟩ hne ⟨v, hv, heq⟩
      have hneq : B.toGMGraph ≠ A.toGMGraph :=
        fun h => hne (congrArg L (Alg86Subgraph.toGMGraph_injective h))
      exact hpriv B.toGMGraph ⟨B, hB, rfl⟩ hneq (Fin.val_injective heq ▸ hv)
    · obtain ⟨u, v, hl⟩ := A.toGMGraph.exists_isLink_of_mem_edgeSet he
      have hl' := case3LiftLink D A (case3AssignedLoops assignment A) hl
      refine Or.inr ⟨_, hl'.edge_mem, ?_⟩
      rintro R ⟨B, hB, rfl⟩ hne heB
      have hd := case3LiftFamily_edge_disjoint D omega homega F hdiv hA hB
        (fun h => hne (congrArg L h.symm)) assignment
      exact Set.disjoint_left.mp hd hl'.edge_mem heB

end GraphMinor.Compute
