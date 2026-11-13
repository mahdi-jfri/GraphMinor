module

public import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.SubdivisionConnected

/-!
# Moving an endpoint along a path avoiding a separator

Graph Minors I, proof of (4.5), page 57, joins a separator vertex to a
block by a path avoiding another separator. Either endpoint is then
separated from the root exactly when the other is. Concatenating the
avoiding path with a path to the root proves this fact in each direction.
-/

public section

namespace GraphMinor.GM01

open Set Graph Relation GraphMinor.GM09

/-- Moving an endpoint along an avoiding path preserves whether the
cut separates it from a fixed vertex. This is the path transfer in the
proof of GM01 (4.5), page 57. -/
theorem graphSeparates_singleton_iff_of_path {α β : Type*} {G P : Graph α β}
    {X : Set α} {a b root : α} (hP : IsGraphPathWithEnds G P a b)
    (hAvoid : Disjoint V(P) X) :
    GraphSeparates G X {a} {root} ↔ GraphSeparates G X {b} {root} := by
  have hPdel : P ≤ G.deleteVerts X := by
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [vertexSet_deleteVerts]
      exact ⟨hP.le.vertexSet_mono hx, fun h ↦ Set.disjoint_left.mp hAvoid hx h⟩
    · intro e x y he
      exact (G.deleteVerts_isLink X).mpr ⟨he.mono hP.le,
        fun h ↦ Set.disjoint_left.mp hAvoid he.left_mem h,
        fun h ↦ Set.disjoint_left.mp hAvoid he.right_mem h⟩
  have hr : ReflTransGen (G.deleteVerts X).Adj a b :=
    ReflTransGen.mono (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hPdel⟩)
      a b ((graphConnected_of_isGraphPath hP).2 a hP.left_mem b hP.right_mem)
  constructor
  · intro hsep x hx y hy hxv hyv hxy
    have hxb : x = b := mem_singleton_iff.mp hx
    have hyr : y = root := mem_singleton_iff.mp hy
    subst x
    subst y
    exact hsep a rfl root rfl (hPdel.vertexSet_mono hP.left_mem) hyv (hr.trans hxy)
  · intro hsep x hx y hy hxv hyv hxy
    have hxa : x = a := mem_singleton_iff.mp hx
    have hyr : y = root := mem_singleton_iff.mp hy
    subst x
    subst y
    exact hsep b rfl root rfl (hPdel.vertexSet_mono hP.right_mem) hyv
      ((Std.Symm.symm _ _ hr).trans hxy)

/-- A vertex in the cut is separated from every vertex, since an
avoiding path cannot contain that endpoint. This is the equal-index
case in GM01 (4.5), page 57. -/
theorem graphSeparates_singleton_of_mem {α β : Type*} {G : Graph α β}
    {X : Set α} {a root : α} (ha : a ∈ X) : GraphSeparates G X {a} {root} := by
  intro x hx y hy hxv hyv _
  have hxa : x = a := mem_singleton_iff.mp hx
  exact (((G.vertexSet_deleteVerts X) ▸ hxv)).2 (hxa.symm ▸ ha)

end GraphMinor.GM01
