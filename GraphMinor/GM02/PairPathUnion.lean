module

public import GraphMinor.GM02.CrossingScheme
public import GraphMinor.GM02.Feasibility
public import GraphMinor.GM02.OrientPairPath

/-!
# Path unions with unoriented endpoint pairs

Crossing schemes describe a graph as a disjoint union of paths joining
the original terminal pairs. The printed definition fixes one orientation
per pair. For changing vertex names, it is useful to use pair paths with
unoriented ends instead. Orienting each path by its pair representative
preserves its vertices and edges, so the two descriptions agree.
-/

public section
namespace GraphMinor.GM02
open Set SimpleGraph Classical
universe u

/-- The path-union condition is unchanged if witnesses record unordered
end pairs instead of a fixed choice of orientation. -/
theorem isPairPathUnion_iff_pairPaths {α : Type u} {vertices : Set α}
    (A : Termination vertices) (F : SimpleGraph α) (S : Set α) :
    IsPairPathUnion A F S ↔
      ∃ P : ∀ p : {p // p ∈ A.pairs}, PairPath F p.val,
        (∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices) ∧
        (⋃ p, (P p).vertices) = S ∧
        ∀ e ∈ F.edgeSet, ∃ p, e ∈ (P p).walk.edges := by
  constructor
  · rintro ⟨P, hpath, hdisj, hcover, hedge⟩
    let Q (p : {p // p ∈ A.pairs}) : PairPath F p.val :=
      { start := p.val.out.1
        finish := p.val.out.2
        ends_eq := p.val.out_eq
        walk := P p
        isPath := hpath p }
    exact ⟨Q, hdisj, hcover, hedge⟩
  · rintro ⟨P, hdisj, hcover, hedge⟩
    refine ⟨fun p => (P p).outPath.val, fun p => (P p).outPath.property, ?_, ?_, ?_⟩
    · intro p q hpq
      rw [(P p).outPath_vertices, (P q).outPath_vertices]
      exact hdisj p q hpq
    · simp_rw [PairPath.outPath_vertices]
      exact hcover
    · intro e he
      obtain ⟨p, hp⟩ := hedge e he
      exact ⟨p, ((P p).outPath_edges e).2 hp⟩

/-- Only the original pair set enters the path-union condition. Changing
its stated containing vertex set preserves the same path-union problem. -/
theorem isPairPathUnion_iff_of_pairs_eq {α : Type u} {S T : Set α}
    (A : Termination S) (B : Termination T) (F : SimpleGraph α) (U : Set α)
    (h : A.pairs = B.pairs) : IsPairPathUnion A F U ↔ IsPairPathUnion B F U := by
  unfold IsPairPathUnion
  rw [h]

end GraphMinor.GM02
