module

public import GraphMinor.GM02.PairPathUnion
public import GraphMinor.GM02.FeasibilityMaps

/-!
# Mapping crossing-scheme path unions

A finite boundary pattern names the original graph's boundary vertices
by an injection. Map each joining path by that injection. The paths stay
simple and disjoint, their vertex union becomes the image of the old
union, and their edges cover exactly the mapped graph's edges. This
justifies expanding numbered crossing-scheme patterns to original names.
-/

public section
namespace GraphMinor.GM02
open Set SimpleGraph Classical
universe u u'

/-- An injective change of boundary vertex names preserves the complete
path-union condition, including coverage of all vertices and edges. -/
theorem IsPairPathUnion.mapEmbedding {α : Type u} {α' : Type u'}
    {vertices : Set α} {A : Termination vertices} {F : SimpleGraph α} {S : Set α}
    (h : IsPairPathUnion A F S) (f : α ↪ α') :
    IsPairPathUnion (A.mapEmbedding f) (F.map f) (f '' S) := by
  obtain ⟨P, hdisj, hcover, hedge⟩ := (isPairPathUnion_iff_pairPaths A F S).1 h
  let B := A.mapEmbedding f
  let φ : F →g F.map f := (SimpleGraph.Embedding.map f F).toHom
  have hinj : Function.Injective φ := f.injective
  have hpreExists (p : {p // p ∈ B.pairs}) : ∃ q ∈ A.pairs, q.map f = p.val :=
    Finset.mem_image.1 p.property
  let pre (p : {p // p ∈ B.pairs}) : {q // q ∈ A.pairs} :=
    ⟨(hpreExists p).choose, (hpreExists p).choose_spec.1⟩
  have hpre (p : {p // p ∈ B.pairs}) : (pre p).val.map f = p.val :=
    (hpreExists p).choose_spec.2
  let insert (p : {p // p ∈ A.pairs}) : {q // q ∈ B.pairs} :=
    ⟨p.val.map f, Finset.mem_image.2 ⟨p.val, p.property, rfl⟩⟩
  have hpre_insert (p : {p // p ∈ A.pairs}) : pre (insert p) = p := by
    apply Subtype.ext
    exact Sym2.map.injective f.injective (hpre (insert p))
  let Q (p : {p // p ∈ B.pairs}) : PairPath (F.map f) p.val :=
    { start := φ (P (pre p)).start
      finish := φ (P (pre p)).finish
      ends_eq := ((P (pre p)).mapHom φ hinj).ends_eq.trans (hpre p)
      walk := ((P (pre p)).mapHom φ hinj).walk
      isPath := ((P (pre p)).mapHom φ hinj).isPath }
  have hQvertices (p : {p // p ∈ B.pairs}) : (Q p).vertices = f '' (P (pre p)).vertices :=
    (P (pre p)).mapHom_vertices φ hinj
  apply (isPairPathUnion_iff_pairPaths B (F.map f) (f '' S)).2
  refine ⟨Q, ?_, ?_, ?_⟩
  · intro p q hpq
    have hne : pre p ≠ pre q := by
      intro he
      apply hpq
      apply Subtype.ext
      exact (hpre p).symm.trans ((congrArg (fun r : {r // r ∈ A.pairs} => r.val.map f) he).trans (hpre q))
    rw [hQvertices, hQvertices]
    apply Set.disjoint_left.2
    intro a hap haq
    obtain ⟨b, hb, rfl⟩ := hap
    obtain ⟨c, hc, hcb⟩ := haq
    have he : c = b := f.injective hcb
    exact Set.disjoint_left.1 (hdisj (pre p) (pre q) hne) hb (he ▸ hc)
  · ext a
    constructor
    · intro ha
      obtain ⟨p, hp⟩ := Set.mem_iUnion.1 ha
      rw [hQvertices] at hp
      obtain ⟨b, hb, rfl⟩ := hp
      exact ⟨b, hcover ▸ Set.mem_iUnion.2 ⟨pre p, hb⟩, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      rw [← hcover] at hb
      obtain ⟨p, hp⟩ := Set.mem_iUnion.1 hb
      apply Set.mem_iUnion.2
      refine ⟨insert p, ?_⟩
      rw [hQvertices, hpre_insert]
      exact ⟨b, hp, rfl⟩
  · intro e he
    rw [SimpleGraph.edgeSet_map] at he
    obtain ⟨e₀, he₀, rfl⟩ := he
    obtain ⟨p, hp⟩ := hedge e₀ he₀
    have heq : (Q (insert p)).walk.edges = (P p).walk.edges.map (Sym2.map f) := by
      change ((P (pre (insert p))).walk.map φ).edges = _
      rw [Walk.edges_map, hpre_insert]
      rfl
    refine ⟨insert p, ?_⟩
    rw [heq]
    exact List.mem_map.2 ⟨e₀, hp, rfl⟩

end GraphMinor.GM02
