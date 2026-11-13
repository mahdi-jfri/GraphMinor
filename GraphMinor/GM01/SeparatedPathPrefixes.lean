module

public import GraphMinor.GM01.SeparatorPathTransfer
import GraphMinor.GM16.PathEndSubpath

/-!
# A path prefix stays on the separated side

Graph Minors I, proof of (4.7), page 58, takes a path from a layer
vertex to its preceding separator. Stop at the first vertex in that
separator. Every earlier vertex is on the same side as the initial
vertex, because its initial subpath avoids the separator. The last
vertex lies in the separator and is itself separated from the root.
-/

public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09

/-- A path ending at its first vertex of a separator stays on the
separated side when its initial vertex is on that side. This is the
prefix check in the path construction for GM01 (4.7), page 58. -/
theorem separated_vertices_of_first_hit_path {α β : Type*} {G P : Graph α β}
    {X : Set α} {a b root : α} (hP : IsGraphPathWithEnds G P a b)
    (hinter : V(P) ∩ X = {b}) (ha : a ∉ X)
    (hsep : GraphSeparates G X {a} {root}) :
    ∀ x ∈ V(P), GraphSeparates G X {x} {root} := by
  classical
  intro x hx
  by_cases hxX : x ∈ X
  · exact graphSeparates_singleton_of_mem hxX
  obtain ⟨Q, hQP, _, hQ⟩ := hP.exists_subpath hP.left_mem hx
  have hAvoid : Disjoint V(Q) X := by
    apply Set.disjoint_left.mpr
    intro y hy hyX
    have hyb : y = b := mem_singleton_iff.mp (hinter ▸ ⟨hQP.vertexSet_mono hy, hyX⟩)
    subst y
    have hbEnds := GraphMinor.GM16.path_start_mem_subpath_is_end hP.symm hQ hQP hy
    rcases hbEnds with hba | hbx
    · exact ha (hba ▸ hyX)
    · exact hxX (hbx ▸ hyX)
  exact (graphSeparates_singleton_iff_of_path hQ hAvoid).mp hsep

/-- Every vertex on an avoiding path to the root is not separated
from the root. Take the terminal subpath from that vertex. -/
theorem not_separated_vertices_of_avoiding_root_path {α β : Type*}
    {G P : Graph α β} {X : Set α} {a root : α}
    (hP : IsGraphPathWithEnds G P a root) (hAvoid : Disjoint V(P) X) :
    ∀ x ∈ V(P), ¬ GraphSeparates G X {x} {root} := by
  intro x hx
  obtain ⟨Q, hQP, _, hQ⟩ := hP.exists_subpath hx hP.right_mem
  exact (not_graphSeparates_iff (A := {x}) (B := {root})).mpr
    ⟨x, rfl, root, rfl, Q, hQ, hAvoid.mono_left hQP.vertexSet_mono⟩

end GraphMinor.GM01
