module

public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.TerminationSupportMaps
public import GraphMinor.GM02.PairPathUnionMaps
public import GraphMinor.GM02.FeasibilityVertices

/-!
# Expanding boundary crossing schemes to the original vertex type

A boundary contains every original terminal and separator vertex. Map
its numbered terminations and reserved sets through the subtype inclusion.
Inside the boundary, the printed conditions are exactly their restricted
versions. Outside it, both terminal supports and the separator are empty.
Mapping the complete path union supplies the last condition, including
edge coverage. Thus valid boundary patterns give actual parent schemes.
-/

public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u v

private theorem subtype_image_mem {α : Type u} {S : Set α} (T : Set S) (a : S) :
    a.val ∈ Subtype.val '' T ↔ a ∈ T := by
  constructor
  · rintro ⟨b, hb, he⟩
    exact Subtype.val_injective he ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

private theorem map_sup_graph {α : Type u} {α' : Type u} (F F' : SimpleGraph α) (f : α ↪ α') :
    (F ⊔ F').map f = F.map f ⊔ F'.map f := by
  ext a b
  simp only [SimpleGraph.map_adj, SimpleGraph.sup_adj]
  constructor
  · rintro ⟨x, y, hxy, hxa, hyb⟩
    rcases hxy with hxy | hxy
    · exact Or.inl ⟨x, y, hxy, hxa, hyb⟩
    · exact Or.inr ⟨x, y, hxy, hxa, hyb⟩
  · rintro (⟨x, y, hxy, hxa, hyb⟩ | ⟨x, y, hxy, hxa, hyb⟩)
    · exact ⟨x, y, Or.inl hxy, hxa, hyb⟩
    · exact ⟨x, y, Or.inr hxy, hxa, hyb⟩

/-- Expand a scheme on a containing boundary to an actual parent scheme,
retaining the original containing graphs and original terminal pairs. -/
noncomputable def CrossingScheme.expandBoundary {α : Type u} {β : Type v}
    (G H H' : Graph α β) (A : Termination V(G)) {S : Set α}
    (hSG : S ⊆ V(G)) (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S)
    (C : CrossingScheme (Graph.noEdge (Set.univ : Set S) Unit)
      (Graph.noEdge (Subtype.val ⁻¹' V(H)) Unit) (Graph.noEdge (Subtype.val ⁻¹' V(H')) Unit)
      (A.rebase hAS).onVertices) : CrossingScheme G H H' A := by
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq S := Classical.decEq S
  let A₀ := (A.rebase hAS).onVertices
  let f : S ↪ α := ⟨Subtype.val, Subtype.val_injective⟩
  have hLS : (C.left.mapEmbedding f).support ⊆ V(G) := by
    rw [Termination.mapEmbedding_support]
    rintro a ⟨b, _, rfl⟩
    exact hSG b.property
  have hRS : (C.right.mapEmbedding f).support ⊆ V(G) := by
    rw [Termination.mapEmbedding_support]
    rintro a ⟨b, _, rfl⟩
    exact hSG b.property
  let L := (C.left.mapEmbedding f).rebase hLS
  let R := (C.right.mapEmbedding f).rebase hRS
  have hL : L.support = Subtype.val '' C.left.support := by
    rw [Termination.rebase_support, Termination.mapEmbedding_support]
    rfl
  have hR : R.support = Subtype.val '' C.right.support := by
    rw [Termination.rebase_support, Termination.mapEmbedding_support]
    rfl
  have hA₀ : A₀.support = Subtype.val ⁻¹' A.support := by
    rw [Termination.onVertices_support, Termination.rebase_support]
  have hLm (a : S) : a.val ∈ L.support ↔ a ∈ C.left.support := by
    rw [hL]
    exact subtype_image_mem _ a
  have hRm (a : S) : a.val ∈ R.support ↔ a ∈ C.right.support := by
    rw [hR]
    exact subtype_image_mem _ a
  have hLinS : L.support ⊆ S := by
    rw [hL]
    rintro a ⟨b, _, rfl⟩
    exact b.property
  have hRinS : R.support ⊆ S := by
    rw [hR]
    rintro a ⟨b, _, rfl⟩
    exact b.property
  refine
    { left := L
      right := R
      reservedLeft := Subtype.val '' C.reservedLeft
      reservedRight := Subtype.val '' C.reservedRight
      reservedLeft_subset := ?_
      reservedRight_subset := ?_
      left_support := ?_
      right_support := ?_
      even_support := ?_
      reserved_disjoint := ?_
      reserved_union := ?_
      path_union := ?_ }
  · rintro a ⟨b, hb, rfl⟩
    exact C.reservedLeft_subset hb
  · rintro a ⟨b, hb, rfl⟩
    exact C.reservedRight_subset hb
  · ext a
    change (a ∈ L.support ∧ a ∉ V(H) ∩ V(H')) ↔ (a ∈ A.support ∧ a ∈ V(H) ∧ a ∉ V(H'))
    by_cases ha : a ∈ S
    · let b : S := ⟨a, ha⟩
      have he := Set.ext_iff.1 C.left_support b
      change (b ∈ C.left.support ∧ a ∉ V(H) ∩ V(H')) ↔
        (b ∈ A₀.support ∧ a ∈ V(H) ∧ a ∉ V(H')) at he
      rw [hA₀, ← hLm b] at he
      exact he
    · have hnL : a ∉ L.support := fun h => ha (hLinS h)
      have hnA : a ∉ A.support := fun h => ha (hAS h)
      simp only [hnL, hnA, false_and]
  · ext a
    change (a ∈ R.support ∧ a ∉ V(H) ∩ V(H')) ↔ (a ∈ A.support ∧ a ∈ V(H') ∧ a ∉ V(H))
    by_cases ha : a ∈ S
    · let b : S := ⟨a, ha⟩
      have he := Set.ext_iff.1 C.right_support b
      change (b ∈ C.right.support ∧ a ∉ V(H) ∩ V(H')) ↔
        (b ∈ A₀.support ∧ a ∈ V(H') ∧ a ∉ V(H)) at he
      rw [hA₀, ← hRm b] at he
      exact he
    · have hnR : a ∉ R.support := fun h => ha (hRinS h)
      have hnA : a ∉ A.support := fun h => ha (hAS h)
      simp only [hnR, hnA, false_and]
  · intro a ha
    let b : S := ⟨a, hXS ha⟩
    have he := C.even_support b ha
    change Even ((if b ∈ A₀.support then 1 else 0) +
      (if b ∈ C.left.support then 1 else 0) + (if b ∈ C.right.support then 1 else 0) : ℕ) at he
    rw [hA₀, ← hLm b, ← hRm b] at he
    exact he
  · apply Set.disjoint_left.2
    intro a ha hb
    obtain ⟨b, hb, rfl⟩ := ha
    obtain ⟨c, hc, hcb⟩ := hb
    have he : c = b := Subtype.val_injective hcb
    exact Set.disjoint_left.1 C.reserved_disjoint hb (he ▸ hc)
  · ext a
    by_cases ha : a ∈ S
    · let b : S := ⟨a, ha⟩
      have he := Set.ext_iff.1 C.reserved_union b
      change (b ∈ C.reservedLeft ∨ b ∈ C.reservedRight) ↔
        (a ∈ V(H) ∩ V(H') ∧ b ∉ A₀.support ∪ C.left.support ∪ C.right.support) at he
      rw [hA₀] at he
      simp only [Set.mem_union, ← hLm b, ← hRm b] at he
      change (a ∈ Subtype.val '' C.reservedLeft ∨ a ∈ Subtype.val '' C.reservedRight) ↔ _
      rw [subtype_image_mem _ b, subtype_image_mem _ b]
      exact he
    · have hnX : a ∉ V(H) ∩ V(H') := fun h => ha (hXS h)
      have hnL : a ∉ Subtype.val '' C.reservedLeft := by rintro ⟨b, _, rfl⟩; exact ha b.property
      have hnR : a ∉ Subtype.val '' C.reservedRight := by rintro ⟨b, _, rfl⟩; exact ha b.property
      change (a ∈ Subtype.val '' C.reservedLeft ∨ a ∈ Subtype.val '' C.reservedRight) ↔ _
      simp only [hnL, hnR, false_or, Set.mem_sdiff, hnX, false_and]
  · have hp := C.path_union.mapEmbedding f
    have hApairs : (A₀.mapEmbedding f).pairs = A.pairs :=
      (A.rebase hAS).onVertices_map_pairs
    have hp' := (isPairPathUnion_iff_of_pairs_eq (A₀.mapEmbedding f) A _ _ hApairs).1 hp
    have hF : SimpleGraph.fromEdgeSet (L.pairs ∪ R.pairs : Finset (Sym2 α)) =
        (SimpleGraph.fromEdgeSet (C.left.pairs ∪ C.right.pairs : Finset (Sym2 S))).map f := by
      simp only [Finset.coe_union, SimpleGraph.fromEdgeSet_union]
      change L.pairGraph ⊔ R.pairGraph = (C.left.pairGraph ⊔ C.right.pairGraph).map f
      rw [Termination.rebase_pairGraph, Termination.rebase_pairGraph,
        Termination.mapEmbedding_pairGraph, Termination.mapEmbedding_pairGraph, map_sup_graph]
    have htarget : IsPairPathUnion A
        (SimpleGraph.fromEdgeSet (L.pairs ∪ R.pairs : Finset (Sym2 α))) (L.support ∪ R.support) := by
      rw [hF, hL, hR, ← Set.image_union]
      exact hp'
    exact htarget

section Data
variable {α : Type u} {β : Type v} (G H H' : Graph α β) (A : Termination V(G)) {S : Set α}
  (hSG : S ⊆ V(G)) (hAS : A.support ⊆ S) (hXS : V(H) ∩ V(H') ⊆ S)
  (C : CrossingScheme (Graph.noEdge (Set.univ : Set S) Unit)
    (Graph.noEdge (Subtype.val ⁻¹' V(H)) Unit) (Graph.noEdge (Subtype.val ⁻¹' V(H')) Unit)
    (A.rebase hAS).onVertices)

/-- Expansion maps exactly the first boundary pair set to original names. -/
theorem CrossingScheme.expandBoundary_left_pairs :
    (CrossingScheme.expandBoundary G H H' A hSG hAS hXS C).left.pairs =
      C.left.pairs.image (Sym2.map Subtype.val) := by
  unfold CrossingScheme.expandBoundary
  rfl

/-- Expansion maps exactly the second boundary pair set to original names. -/
theorem CrossingScheme.expandBoundary_right_pairs :
    (CrossingScheme.expandBoundary G H H' A hSG hAS hXS C).right.pairs =
      C.right.pairs.image (Sym2.map Subtype.val) := by
  unfold CrossingScheme.expandBoundary
  rfl

/-- Expansion maps exactly the first reserved boundary set to original names. -/
theorem CrossingScheme.expandBoundary_reservedLeft :
    (CrossingScheme.expandBoundary G H H' A hSG hAS hXS C).reservedLeft =
      Subtype.val '' C.reservedLeft := by
  unfold CrossingScheme.expandBoundary
  rfl

/-- Expansion maps exactly the second reserved boundary set to original names. -/
theorem CrossingScheme.expandBoundary_reservedRight :
    (CrossingScheme.expandBoundary G H H' A hSG hAS hXS C).reservedRight =
      Subtype.val '' C.reservedRight := by
  unfold CrossingScheme.expandBoundary
  rfl
end Data

end GraphMinor.GM02
