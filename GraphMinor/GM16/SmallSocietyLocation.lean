module

public import GraphMinor.GM16.Defs
import GraphMinor.GM09.Basic

/-!
# The local location for a small society

For a society with at most three boundary vertices, the location in
XVI (1.3), page 51, removes the whole society. Its right side inside
the society is the edgeless graph on its boundary. Every torso of its
local design therefore has at most three vertices.
-/

@[expose] public section
namespace GraphMinor.GM16
open Set Graph GM06 GM09 GM14
universe u v

/-- The edgeless graph on the boundary of a society. -/
def societyBoundaryGraph {α : Type u} {β : Type v} (A : Society α β) : Graph α β :=
  (A.G.induce A.Ω.bar).restrict ∅

/-- The boundary graph has exactly the boundary vertices. -/
theorem vertexSet_societyBoundaryGraph {α : Type u} {β : Type v} (A : Society α β) :
    V(societyBoundaryGraph A) = A.Ω.bar := rfl

/-- Removing the whole society leaves its boundary graph on the right. -/
theorem societyBoundaryGraph_isSeparation {α : Type u} {β : Type v} (A : Society α β) :
    IsGraphSeparation A.G A.G (societyBoundaryGraph A) := by
  have hle : societyBoundaryGraph A ≤ A.G :=
    restrict_le.trans (A.G.induce_le A.bar_subset)
  refine ⟨le_rfl, hle, ?_, ?_, ?_⟩
  · change V(A.G) ∪ A.Ω.bar = V(A.G)
    exact union_eq_self_of_subset_right A.bar_subset
  · simp only [societyBoundaryGraph, edgeSet_restrict, inter_empty, union_empty]
  · simp only [societyBoundaryGraph, edgeSet_restrict, inter_empty, disjoint_empty]

/-- The single separation assigned to a small society in XVI, page 51. -/
def smallSocietyLocation {α : Type u} {β : Type v} (A : Society α β) :
    Set (Graph α β × Graph α β) := {(A.G, societyBoundaryGraph A)}

/-- The local location for a small society satisfies the location condition. -/
theorem smallSocietyLocation_isLocation {α : Type u} {β : Type v} (A : Society α β) :
    IsGraphLocation A.G (smallSocietyLocation A) := by
  refine ⟨finite_singleton _, ?_, ?_⟩
  · rintro p (rfl : p = _)
    exact societyBoundaryGraph_isSeparation A
  · rintro p (rfl : p = _) q (rfl : q = _) hne
    exact (hne rfl).elim

/-- Every torso of the local design of a small society has exactly its
boundary vertices, so its added edges can be drawn inside the society disc. -/
theorem smallSocietyLocation_torso_vertices {α : Type u} {β : Type v}
    (A : Society α β) {H : Graph α β}
    (hH : IsTorsoOfDesign (graphLocationDesign A.G (smallSocietyLocation A)) H) :
    V(H) = A.Ω.bar := by
  rw [← hH.1]
  ext x
  change (x ∈ V(A.G) ∧ ∀ p ∈ smallSocietyLocation A, x ∈ V(p.2)) ↔ x ∈ A.Ω.bar
  constructor
  · intro hx
    exact hx.2 _ (mem_singleton _)
  · intro hx
    refine ⟨A.bar_subset hx, ?_⟩
    rintro p (rfl : p = _)
    exact hx

end GraphMinor.GM16
