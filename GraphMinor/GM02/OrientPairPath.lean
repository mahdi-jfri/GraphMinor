module

public import GraphMinor.GM02.Feasibility

/-!
# Orienting paths between unordered endpoints

To join the pieces of a crossing scheme in II (2.9), orient each pair path
in the direction in which its edge is traversed. Its endpoint equality
gives either the walk itself or its reverse. Both have the same vertex set.
-/

public section
namespace GraphMinor.GM02
open SimpleGraph Set Classical
universe u

/-- A pair path can be oriented from either prescribed endpoint to the
other without changing its vertex support. -/
theorem PairPath.exists_oriented_walk {α : Type u} {F : SimpleGraph α} {a b : α}
    (P : PairPath F s(a, b)) :
    ∃ w : F.Walk a b, {x | x ∈ w.support} = P.vertices := by
  rcases Sym2.eq_iff.1 P.ends_eq with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · refine ⟨P.walk.copy hs ht, ?_⟩
    ext x
    simp only [Walk.support_copy, PairPath.vertices]
  · refine ⟨P.walk.reverse.copy ht hs, ?_⟩
    ext x
    simp only [Walk.support_copy, Walk.support_reverse, List.mem_reverse, PairPath.vertices]

/-- Choose the orientation required for traversing an edge. -/
noncomputable def PairPath.orientedWalk {α : Type u} {F : SimpleGraph α} {a b : α}
    (P : PairPath F s(a, b)) : F.Walk a b := P.exists_oriented_walk.choose

/-- The chosen orientation preserves exactly the path's vertices. -/
theorem PairPath.orientedWalk_vertices {α : Type u} {F : SimpleGraph α} {a b : α}
    (P : PairPath F s(a, b)) : {x | x ∈ P.orientedWalk.support} = P.vertices :=
  P.exists_oriented_walk.choose_spec

/-- Orient a pair path while preserving its path property, vertices, and
edges. Recording all three properties avoids any dependence on which
existential witness is chosen later. -/
theorem PairPath.exists_oriented_path {α : Type u} {F : SimpleGraph α} {a b : α}
    (P : PairPath F s(a, b)) : ∃ q : F.Path a b,
      {x | x ∈ q.val.support} = P.vertices ∧ ∀ e, e ∈ q.val.edges ↔ e ∈ P.walk.edges := by
  rcases Sym2.eq_iff.1 P.ends_eq with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · refine ⟨⟨P.walk.copy hs ht, (Walk.isPath_copy _ _ _).2 P.isPath⟩, ?_, ?_⟩
    · ext x; simp only [Walk.support_copy, PairPath.vertices]
    · intro e; simp only [Walk.edges_copy]
  · refine ⟨⟨P.walk.reverse.copy ht hs, (Walk.isPath_copy _ _ _).2 P.isPath.reverse⟩, ?_, ?_⟩
    · ext x; simp only [Walk.support_copy, Walk.support_reverse, List.mem_reverse, PairPath.vertices]
    · intro e; simp only [Walk.edges_copy, Walk.edges_reverse, List.mem_reverse]

/-- Orient a pair path by the fixed representative of its unordered pair. -/
noncomputable def PairPath.outPath {α : Type u} {F : SimpleGraph α} {p : Sym2 α}
    (P : PairPath F p) : F.Path p.out.1 p.out.2 :=
  let Q : PairPath F s(p.out.1, p.out.2) :=
    ⟨P.start, P.finish, P.ends_eq.trans p.out_eq.symm, P.walk, P.isPath⟩
  Q.exists_oriented_path.choose

/-- The fixed orientation preserves all vertices. -/
theorem PairPath.outPath_vertices {α : Type u} {F : SimpleGraph α} {p : Sym2 α}
    (P : PairPath F p) : {x | x ∈ P.outPath.val.support} = P.vertices := by
  let Q : PairPath F s(p.out.1, p.out.2) :=
    ⟨P.start, P.finish, P.ends_eq.trans p.out_eq.symm, P.walk, P.isPath⟩
  exact Q.exists_oriented_path.choose_spec.1

/-- The fixed orientation preserves all edges. -/
theorem PairPath.outPath_edges {α : Type u} {F : SimpleGraph α} {p : Sym2 α}
    (P : PairPath F p) (e : Sym2 α) : e ∈ P.outPath.val.edges ↔ e ∈ P.walk.edges := by
  let Q : PairPath F s(p.out.1, p.out.2) :=
    ⟨P.start, P.finish, P.ends_eq.trans p.out_eq.symm, P.walk, P.isPath⟩
  exact Q.exists_oriented_path.choose_spec.2 e

end GraphMinor.GM02
