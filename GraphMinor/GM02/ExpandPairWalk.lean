module

public import GraphMinor.GM02.OrientPairPath

/-!
# Replacing edges of a walk by pair paths

In the gluing argument of II (2.9), every edge of the crossing-scheme graph
stands for a path in one induced graph. Orient these paths along a walk
and concatenate them. Apart from the initial vertex, every resulting
vertex lies on a replacement for an edge traversed by the original walk.
For a nontrivial walk the initial vertex is on its first replacement too.
-/

@[expose] public section
namespace GraphMinor.GM02
open SimpleGraph Set Classical
universe u

/-- Expand every edge of a walk using its specified replacement path. -/
noncomputable def expandPairWalk {α : Type u} {F K : SimpleGraph α}
    (R : ∀ e : F.edgeSet, PairPath K e.val) {a b : α} : F.Walk a b → K.Walk a b
  | .nil => .nil
  | .cons h q => (R ⟨s(_, _), (SimpleGraph.mem_edgeSet _).2 h⟩).orientedWalk.append (expandPairWalk R q)

/-- Every vertex of the expanded walk is its initial vertex or belongs
to a replacement for one of the traversed edges. -/
theorem mem_expandPairWalk_support {α : Type u} {F K : SimpleGraph α}
    (R : ∀ e : F.edgeSet, PairPath K e.val) {a b : α} (p : F.Walk a b)
    {x : α} (hx : x ∈ (expandPairWalk R p).support) :
    x = a ∨ ∃ e : F.edgeSet, e.val ∈ p.edges ∧ x ∈ (R e).vertices := by
  induction p with
  | nil => exact Or.inl (List.mem_singleton.1 hx)
  | @cons a b c hab q ih =>
    let e : F.edgeSet := ⟨s(a, b), (SimpleGraph.mem_edgeSet _).2 hab⟩
    change x ∈ ((R e).orientedWalk.append (expandPairWalk R q)).support at hx
    rw [Walk.support_append] at hx
    rcases List.mem_append.1 hx with hxR | hxQ
    · apply Or.inr
      refine ⟨e, by simp [e], ?_⟩
      have heq := (R e).orientedWalk_vertices
      exact heq ▸ hxR
    · have hxQ' := List.mem_of_mem_tail hxQ
      rcases ih hxQ' with hxb | ⟨f, hf, hxF⟩
      · subst x
        exact Or.inr ⟨e, by simp [e], (R e).endpoint_mem (Sym2.mem_mk_right _ _)⟩
      · exact Or.inr ⟨f, List.mem_cons_of_mem _ hf, hxF⟩

/-- For distinct endpoints, every vertex of the expanded walk lies on a
replacement for one of the traversed edges. -/
theorem mem_expandPairWalk_support_of_ne {α : Type u} {F K : SimpleGraph α}
    (R : ∀ e : F.edgeSet, PairPath K e.val) {a b : α} (p : F.Walk a b) (hab : a ≠ b)
    {x : α} (hx : x ∈ (expandPairWalk R p).support) :
    ∃ e : F.edgeSet, e.val ∈ p.edges ∧ x ∈ (R e).vertices := by
  rcases mem_expandPairWalk_support R p hx with rfl | hex
  · cases p with
    | nil => exact (hab rfl).elim
    | @cons _ b _ h q =>
      let e : F.edgeSet := ⟨s(x, b), (SimpleGraph.mem_edgeSet _).2 h⟩
      exact ⟨e, by simp [e], (R e).endpoint_mem (Sym2.mem_mk_left _ _)⟩
  · exact hex

end GraphMinor.GM02
