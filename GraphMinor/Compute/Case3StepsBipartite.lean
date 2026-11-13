module

public import GraphMinor.Compute.Case3StepsRuralIso

/-!
# The bipartite graph after renaming division members

A rural division is defined using the bipartite graph whose edges join each
member to its boundary vertices (XIII, Section 8, page 96). A bijection of
members that preserves their boundary sets gives an isomorphism of these
graphs. The maps in this file will be applied to the multigraph edge lift.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph GraphMinor.GM09 GraphMinor.GM13 Classical

universe u u' v v'

section
variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
variable (S : Society α β) (S' : Society α' β')
variable (F : Set (Graph α β)) (F' : Set (Graph α' β'))
variable (m : F ≃ F') (f : α ↪ α')

/-- Extend the member bijection to all graph labels. Its value off the family
is irrelevant to the bipartite graph. -/
noncomputable def case3BipartiteMemberMap (A : Graph α β) : Graph α' β' :=
  if h : A ∈ F then (m ⟨A, h⟩).1 else S'.G

@[simp]
theorem case3BipartiteMemberMap_mem (A : F) :
    case3BipartiteMemberMap S' F F' m A.1 = (m A).1 := by
  simp only [case3BipartiteMemberMap, A.2, ↓reduceDIte]

private theorem case3BipartiteMemberMap_injOn :
    Set.InjOn (case3BipartiteMemberMap S' F F' m) F := by
  intro A hA B hB heq
  have heq' : (m ⟨A, hA⟩).1 = (m ⟨B, hB⟩).1 := by
    simpa only [case3BipartiteMemberMap_mem S' F F' m ⟨A, hA⟩,
      case3BipartiteMemberMap_mem S' F F' m ⟨B, hB⟩] using heq
  exact congrArg Subtype.val (m.injective (Subtype.ext heq'))

/-- The vertex map on the bipartite graph. -/
noncomputable def case3BipartiteVertexMap : Graph α β ⊕ α → Graph α' β' ⊕ α' :=
  Sum.map (case3BipartiteMemberMap S' F F' m) f

/-- The edge map on the bipartite graph. -/
noncomputable def case3BipartiteEdgeMap : Graph α β × α → Graph α' β' × α' :=
  Prod.map (case3BipartiteMemberMap S' F F' m) f

variable (hbar : S'.Ω.bar = f '' S.Ω.bar)
variable (hbd : ∀ A : F, divBoundary S' (m A).1 = f '' divBoundary S A.1)

include m hbar hbd in
/-- Total boundaries, together with the society boundary, are renamed by `f`. -/
theorem case3BipartiteBoundary_image :
    divTotalBoundary S' F' ∪ S'.Ω.bar = f '' (divTotalBoundary S F ∪ S.Ω.bar) := by
  ext v
  constructor
  · rintro (hv | hv)
    · obtain ⟨B, hB, hvB⟩ := Set.mem_iUnion₂.mp hv
      let A := m.symm ⟨B, hB⟩
      have heq : m A = ⟨B, hB⟩ := m.apply_symm_apply _
      have hv' : v ∈ divBoundary S' (m A).1 := by simpa only [heq] using hvB
      rw [hbd A] at hv'
      obtain ⟨u, hu, rfl⟩ := hv'
      exact ⟨u, Or.inl (Set.mem_iUnion₂.mpr ⟨A.1, A.2, hu⟩), rfl⟩
    · rw [hbar] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact ⟨u, Or.inr hu, rfl⟩
  · rintro ⟨u, hu | hu, rfl⟩
    · obtain ⟨A, hA, huA⟩ := Set.mem_iUnion₂.mp hu
      refine Or.inl (Set.mem_iUnion₂.mpr ⟨(m ⟨A, hA⟩).1, (m ⟨A, hA⟩).2, ?_⟩)
      rw [hbd ⟨A, hA⟩]
      exact ⟨u, huA, rfl⟩
    · exact Or.inr (hbar ▸ ⟨u, hu, rfl⟩)

include hbar hbd in
theorem case3BipartiteVertex_bijOn :
    Set.BijOn (case3BipartiteVertexMap S' F F' m f)
      V(divisionBipartiteGraph S F) V(divisionBipartiteGraph S' F') := by
  let U := divTotalBoundary S F ∪ S.Ω.bar
  let U' := divTotalBoundary S' F' ∪ S'.Ω.bar
  have hU : U' = f '' U := case3BipartiteBoundary_image S S' F F' m f hbar hbd
  have hsrc_inl : ∀ A, Sum.inl A ∈ V(divisionBipartiteGraph S F) ↔ A ∈ F := by
    intro A
    simp only [divisionBipartiteGraph, Set.mem_union, Set.mem_image, Sum.inl.injEq,
      Sum.inr_ne_inl, and_false, exists_false, or_false, exists_eq_right]
  have hsrc_inr : ∀ u, Sum.inr u ∈ V(divisionBipartiteGraph S F) ↔ u ∈ U := by
    intro u
    simp only [divisionBipartiteGraph, Set.mem_union, Set.mem_image, Sum.inr.injEq,
      Sum.inl_ne_inr, and_false, exists_false, false_or, exists_eq_right, U] 
  have htgt_inl : ∀ A, Sum.inl A ∈ V(divisionBipartiteGraph S' F') ↔ A ∈ F' := by
    intro A
    simp only [divisionBipartiteGraph, Set.mem_union, Set.mem_image, Sum.inl.injEq,
      Sum.inr_ne_inl, and_false, exists_false, or_false, exists_eq_right]
  have htgt_inr : ∀ u, Sum.inr u ∈ V(divisionBipartiteGraph S' F') ↔ u ∈ U' := by
    intro u
    simp only [divisionBipartiteGraph, Set.mem_union, Set.mem_image, Sum.inr.injEq,
      Sum.inl_ne_inr, and_false, exists_false, false_or, exists_eq_right, U']
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    cases v with
    | inl A =>
      have hA := (hsrc_inl A).mp hv
      apply (htgt_inl _).mpr
      change case3BipartiteMemberMap S' F F' m A ∈ F'
      rw [case3BipartiteMemberMap_mem S' F F' m ⟨A, hA⟩]
      exact (m ⟨A, hA⟩).2
    | inr u =>
      apply (htgt_inr _).mpr
      rw [hU]
      exact ⟨u, (hsrc_inr u).mp hv, rfl⟩
  · intro a ha b hb heq
    cases a with
    | inl A =>
      cases b with
      | inl B =>
        exact congrArg Sum.inl (case3BipartiteMemberMap_injOn S' F F' m
          ((hsrc_inl A).mp ha) ((hsrc_inl B).mp hb) (Sum.inl.inj heq))
      | inr u =>
        change Sum.inl _ = Sum.inr _ at heq
        exact False.elim (Sum.inl_ne_inr heq)
    | inr u =>
      cases b with
      | inl B =>
        change Sum.inr _ = Sum.inl _ at heq
        exact False.elim (Sum.inr_ne_inl heq)
      | inr v => exact congrArg Sum.inr (f.injective (Sum.inr.inj heq))
  · intro v hv
    cases v with
    | inl B =>
      have hB := (htgt_inl B).mp hv
      let A := m.symm ⟨B, hB⟩
      refine ⟨Sum.inl A.1, (hsrc_inl _).mpr A.2, ?_⟩
      change Sum.inl (case3BipartiteMemberMap S' F F' m A.1) = _
      rw [case3BipartiteMemberMap_mem]
      exact congrArg (fun A : F' => Sum.inl A.1) (m.apply_symm_apply ⟨B, hB⟩)
    | inr v =>
      have hv' := (htgt_inr v).mp hv
      rw [hU] at hv'
      obtain ⟨u, hu, rfl⟩ := hv'
      exact ⟨Sum.inr u, (hsrc_inr u).mpr hu, rfl⟩

include hbd in
theorem case3BipartiteEdge_bijOn :
    Set.BijOn (case3BipartiteEdgeMap S' F F' m f)
      E(divisionBipartiteGraph S F) E(divisionBipartiteGraph S' F') := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨A, u⟩ ⟨hA, hu⟩
    change case3BipartiteMemberMap S' F F' m A ∈ F' ∧
      f u ∈ divBoundary S' (case3BipartiteMemberMap S' F F' m A)
    rw [case3BipartiteMemberMap_mem S' F F' m ⟨A, hA⟩, hbd ⟨A, hA⟩]
    exact ⟨(m ⟨A, hA⟩).2, u, hu, rfl⟩
  · rintro ⟨A, u⟩ ⟨hA, hu⟩ ⟨B, v⟩ ⟨hB, hv⟩ heq
    exact Prod.ext (case3BipartiteMemberMap_injOn S' F F' m hA hB (congrArg Prod.fst heq))
      (f.injective (congrArg Prod.snd heq))
  · rintro ⟨B, v⟩ ⟨hB, hv⟩
    let A := m.symm ⟨B, hB⟩
    have heq : m A = ⟨B, hB⟩ := m.apply_symm_apply _
    have hv' : v ∈ divBoundary S' (m A).1 := by simpa only [heq] using hv
    rw [hbd A] at hv'
    obtain ⟨u, hu, rfl⟩ := hv'
    refine ⟨(A.1, u), ⟨A.2, hu⟩, ?_⟩
    change (case3BipartiteMemberMap S' F F' m A.1, f u) = _
    rw [case3BipartiteMemberMap_mem]
    exact congrArg (fun A : F' => (A.1, f u)) heq

/-- The isomorphism sends member `A` to `m A` and boundary vertex `u` to `f u`. -/
noncomputable def case3DivisionBipartiteIso
    (m : F ≃ F') (f : α ↪ α')
    (hbar : S'.Ω.bar = f '' S.Ω.bar)
    (hbd : ∀ A : F, divBoundary S' (m A).1 = f '' divBoundary S A.1) :
    GraphMinor.Iso (divisionBipartiteGraph S F) (divisionBipartiteGraph S' F') where
  vertexEquiv := Set.BijOn.equiv _ (case3BipartiteVertex_bijOn S S' F F' m f hbar hbd)
  edgeEquiv := Set.BijOn.equiv _ (case3BipartiteEdge_bijOn S S' F F' m f hbd)
  isLink_iff := by
    intro e a b
    have he := e.2
    have hmaps := (case3BipartiteEdge_bijOn S S' F F' m f hbd).mapsTo he
    have hm1 : case3BipartiteMemberMap S' F F' m e.1.1 ∈ F' := hmaps.1
    have hm2 : f e.1.2 ∈ divBoundary S' (case3BipartiteMemberMap S' F F' m e.1.1) := hmaps.2
    have hinj := (case3BipartiteVertex_bijOn S S' F F' m f hbar hbd).injOn
    let va : Graph α β ⊕ α := Sum.inl e.1.1
    let vb : Graph α β ⊕ α := Sum.inr e.1.2
    have hva : va ∈ V(divisionBipartiteGraph S F) :=
      Or.inl ⟨e.1.1, he.1, rfl⟩
    have hvb : vb ∈ V(divisionBipartiteGraph S F) :=
      Or.inr ⟨e.1.2, Or.inl (Set.mem_iUnion₂.mpr ⟨e.1.1, he.1, he.2⟩), rfl⟩
    have h₁ : case3BipartiteVertexMap S' F F' m f a.1 = case3BipartiteVertexMap S' F F' m f va ↔ a.1 = va :=
      ⟨hinj a.2 hva, congrArg _⟩
    have h₂ : case3BipartiteVertexMap S' F F' m f b.1 = case3BipartiteVertexMap S' F F' m f vb ↔ b.1 = vb :=
      ⟨hinj b.2 hvb, congrArg _⟩
    have h₃ : case3BipartiteVertexMap S' F F' m f a.1 = case3BipartiteVertexMap S' F F' m f vb ↔ a.1 = vb :=
      ⟨hinj a.2 hvb, congrArg _⟩
    have h₄ : case3BipartiteVertexMap S' F F' m f b.1 = case3BipartiteVertexMap S' F F' m f va ↔ b.1 = va :=
      ⟨hinj b.2 hva, congrArg _⟩
    change (_ ∧ _ ∧ ((a.1 = va ∧ b.1 = vb) ∨ (a.1 = vb ∧ b.1 = va))) ↔
      (case3BipartiteMemberMap S' F F' m e.1.1 ∈ F' ∧
        f e.1.2 ∈ divBoundary S' (case3BipartiteMemberMap S' F F' m e.1.1) ∧
        ((case3BipartiteVertexMap S' F F' m f a.1 = case3BipartiteVertexMap S' F F' m f va ∧
        case3BipartiteVertexMap S' F F' m f b.1 = case3BipartiteVertexMap S' F F' m f vb) ∨
        (case3BipartiteVertexMap S' F F' m f a.1 = case3BipartiteVertexMap S' F F' m f vb ∧
        case3BipartiteVertexMap S' F F' m f b.1 = case3BipartiteVertexMap S' F F' m f va)))
    simp only [he.1, he.2, hm1, hm2, true_and, h₁, h₂, h₃, h₄]

/-- The isomorphism's vertex map on the boundary side. -/
theorem case3DivisionBipartiteIso_vertex_inr (u : α)
    (hu : Sum.inr u ∈ V(divisionBipartiteGraph S F)) :
    ((case3DivisionBipartiteIso S S' F F' m f hbar hbd).vertexEquiv ⟨Sum.inr u, hu⟩).1 =
      Sum.inr (f u) := by
  rfl

end
end GraphMinor.Compute
