module

public import GraphMinor.GM02.PairPathUnion
public import GraphMinor.GM02.PairPathInduce
public import GraphMinor.GM02.TerminationVertices

/-!
# Restricting crossing path unions to their finite boundary

Every path in a path union lies in its stated vertex union. When that
union is contained in the boundary, induce every path on the boundary
subtype. The induced family remains disjoint and covers the induced
vertices and edges. This is the reverse direction needed to enumerate
all crossing schemes by numbered boundary patterns.
-/

public section
namespace GraphMinor.GM02
open Set SimpleGraph Classical
universe u

/-- Restrict a complete joining-path union to any containing vertex set. -/
theorem IsPairPathUnion.induce {α : Type u} {S T : Set α} {A : Termination S} {F : SimpleGraph α}
    (h : IsPairPathUnion A F T) (hTS : T ⊆ S) :
    IsPairPathUnion A.onVertices (F.induce S) (Subtype.val ⁻¹' T) := by
  obtain ⟨P, hdisj, hcover, hedge⟩ := (isPairPathUnion_iff_pairPaths A F T).1 h
  have hPS (p : {p // p ∈ A.pairs}) : (P p).vertices ⊆ S := by
    intro a ha
    exact hTS (hcover ▸ Set.mem_iUnion.2 ⟨p, ha⟩)
  let pre (p : {p // p ∈ A.onVertices.pairs}) : {p // p ∈ A.pairs} :=
    ⟨p.val.map Subtype.val, (A.mem_onVertices_pairs p.val).1 p.property⟩
  let insert (p : {p // p ∈ A.pairs}) : {p // p ∈ A.onVertices.pairs} :=
    ⟨p.val.attachWith (A.vertex_mem p.val p.property),
      (A.mem_onVertices_pairs _).2 (by simpa only [Sym2.attachWith_map_subtypeVal] using p.property)⟩
  have hpre_insert (p : {p // p ∈ A.pairs}) : pre (insert p) = p := by
    apply Subtype.ext
    exact Sym2.attachWith_map_subtypeVal _
  let Q (p : {p // p ∈ A.onVertices.pairs}) : PairPath (F.induce S) p.val :=
    { start := ((P (pre p)).induce (hPS (pre p))).start
      finish := ((P (pre p)).induce (hPS (pre p))).finish
      ends_eq := by
        apply Sym2.map.injective Subtype.val_injective
        change s((P (pre p)).start, (P (pre p)).finish) = (pre p).val
        exact (P (pre p)).ends_eq
      walk := ((P (pre p)).induce (hPS (pre p))).walk
      isPath := ((P (pre p)).induce (hPS (pre p))).isPath }
  have hQmem (p : {p // p ∈ A.onVertices.pairs}) (a : S) :
      a ∈ (Q p).vertices ↔ a.val ∈ (P (pre p)).vertices :=
    (P (pre p)).mem_induce_vertices (hPS (pre p)) a
  have hQedges (p : {p // p ∈ A.onVertices.pairs}) :
      (Q p).walk.edges.map (Sym2.map Subtype.val) = (P (pre p)).walk.edges :=
    (P (pre p)).induce_edges_map (hPS (pre p))
  apply (isPairPathUnion_iff_pairPaths A.onVertices (F.induce S) (Subtype.val ⁻¹' T)).2
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro p q hpq
    have hne : pre p ≠ pre q := by
      intro he
      apply hpq
      apply Subtype.ext
      apply Sym2.map.injective Subtype.val_injective
      exact congrArg Subtype.val he
    apply Set.disjoint_left.2
    intro a hap haq
    exact Set.disjoint_left.1 (hdisj (pre p) (pre q) hne)
      ((hQmem p a).1 hap) ((hQmem q a).1 haq)
  · ext a
    constructor
    · intro ha
      obtain ⟨p, hp⟩ := Set.mem_iUnion.1 ha
      exact hcover ▸ Set.mem_iUnion.2 ⟨pre p, (hQmem p a).1 hp⟩
    · intro ha
      have haT : a.val ∈ T := ha
      rw [← hcover] at haT
      obtain ⟨p, hp⟩ := Set.mem_iUnion.1 haT
      apply Set.mem_iUnion.2
      refine ⟨insert p, (hQmem _ _).2 ?_⟩
      rw [hpre_insert]
      exact hp
  · intro e he
    have heF : e.map Subtype.val ∈ F.edgeSet :=
      ((SimpleGraph.Embedding.induce S).mapEdgeSet ⟨e, he⟩).property
    obtain ⟨p, hp⟩ := hedge _ heF
    have hmem : e.map Subtype.val ∈ (Q (insert p)).walk.edges.map (Sym2.map Subtype.val) := by
      rw [hQedges, hpre_insert]
      exact hp
    obtain ⟨e₀, he₀, heq⟩ := List.mem_map.1 hmem
    have heq' : e₀ = e := Sym2.map.injective Subtype.val_injective heq
    exact ⟨insert p, heq' ▸ he₀⟩

end GraphMinor.GM02
