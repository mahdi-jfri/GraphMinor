module

public import GraphMinor.GM09.Basic

/-!
# Independent joins through two clean subdivision attachments

In Graph Minors I, (4.14), page 59, each external path meets the
subdivision only at its attachment vertex. An internal path from
that vertex can therefore be joined to it. The two resulting joins
are disjoint if the external paths and internal paths are separately
disjoint and each internal path avoids the other attachment vertex.
These checks account for all four possible intersections.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- Join an external first-hit path to an internal path. This is the
actual union used for each join in GM01 (4.14), page 59. -/
theorem isGraphPath_join_of_clean_hit {α β : Type*} {G D P Q : Graph α β}
    (hDG : D ≤ G) {d w t : α} (hP : IsGraphPathWithEnds G P d w)
    (hPD : V(P) ∩ V(D) = {d}) (hQ : IsGraphPathWithEnds D Q d t) :
    IsGraphPathWithEnds G (subgraphUnion G P Q) w t := by
  have hPQ : V(P) ∩ V(Q) = {d} := by
    apply Set.Subset.antisymm
    · intro x hx
      exact hPD ▸ ⟨hx.1, hQ.le.vertexSet_mono hx.2⟩
    · intro x hx
      have hxd : x = d := hx
      subst x
      exact ⟨hP.left_mem, hQ.left_mem⟩
  exact hP.symm.subgraphUnion (hQ.mono hDG) hPQ

/-- The two clean-hit unions are disjoint in GM01 (4.14), page 59.
No cross-intersection can occur at an old attachment vertex. -/
theorem disjoint_clean_hit_joins {α : Type*} {X A B C D : Set α} {a b : α}
    (hAX : A ∩ X ⊆ {a}) (hBX : B ∩ X ⊆ {b}) (hCX : C ⊆ X) (hDX : D ⊆ X)
    (hAB : Disjoint A B) (hCD : Disjoint C D) (ha : a ∉ D) (hb : b ∉ C) :
    Disjoint (A ∪ C) (B ∪ D) := by
  have hAD : Disjoint A D := by
    apply Set.disjoint_left.mpr
    intro x hxA hxD
    have hxa : x = a := hAX ⟨hxA, hDX hxD⟩
    exact ha (hxa ▸ hxD)
  have hCB : Disjoint C B := by
    apply Set.disjoint_left.mpr
    intro x hxC hxB
    have hxb : x = b := hBX ⟨hxB, hCX hxC⟩
    exact hb (hxb ▸ hxC)
  exact (hAB.union_right hAD).union_left (hCB.union_right hCD)

end GraphMinor.GM01
