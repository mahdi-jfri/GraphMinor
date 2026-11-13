module

public import GraphMinor.GM19.Defs2
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM19.CutFragment
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The two discs that cap a two-cuff surface

Graph Minors V, (8.10), caps the two lifts of a cut circle. The library
capping has one closed disc for each cuff. If these are the only two
cuffs, their caps are disjoint and their complement is homeomorphic to
the interior of the cut surface, by the capping embedding.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- The library capping embedding identifies the interior of a surface
with the complement of all its closed capping discs. -/
theorem capped_interior_homeomorph {Y T : Type}
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace T]
    (hY : IsSurface Y) (cap : IsCappedSurface Y T) :
    Nonempty (↥((bd Y)ᶜ) ≃ₜ ↥((⋃ Θ ∈ cuffs Y,closure (cap.cuffDisc Θ))ᶜ)) := by
  let : T2Space T := cap.isSurface.2.1
  exact ⟨(cap.isEmbedding.homeomorphImage (bd Y)ᶜ).trans
    (Homeomorph.setCongr (cap.compl_eq_image hY).symm)⟩

/-- A surface with a single cuff has one closed capping disc whose
complement is homeomorphic to its interior. -/
theorem capped_single_complement {Y T : Type}
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace T]
    (hY : IsSurface Y) (cap : IsCappedSurface Y T) {X : Set Y}
    (hcuffs : cuffs Y={X}) :
    ∃ D : Set T, IsClosedDisc D ∧ Nonempty (↥((bd Y)ᶜ) ≃ₜ ↥(Dᶜ)) := by
  have hX : X ∈ cuffs Y := by rw [hcuffs]; exact mem_singleton _
  refine ⟨closure (cap.cuffDisc X),cap.cuffDisc_closedDisc X hX,?_⟩
  have hh := capped_interior_homeomorph hY cap
  rw [hcuffs,biUnion_singleton] at hh
  exact hh

/-- A surface with precisely two distinct cuffs has two disjoint closed
capping discs. Their complement is the interior, under the restriction
of the capping embedding. -/
theorem capped_pair_complement {Y T : Type}
    [TopologicalSpace Y] [T2Space Y] [TopologicalSpace T]
    (hY : IsSurface Y) (cap : IsCappedSurface Y T) {X X' : Set Y}
    (hcuffs : cuffs Y={X,X'}) (hne : X ≠ X') :
    ∃ D D' : Set T, IsClosedDisc D ∧ IsClosedDisc D' ∧ Disjoint D D' ∧
      Nonempty (↥((bd Y)ᶜ) ≃ₜ ↥((D ∪ D')ᶜ)) := by
  have hX : X ∈ cuffs Y := by rw [hcuffs]; exact mem_insert _ _
  have hX' : X' ∈ cuffs Y := by rw [hcuffs]; exact mem_insert_of_mem _ (mem_singleton _)
  refine ⟨closure (cap.cuffDisc X),closure (cap.cuffDisc X'),
    cap.cuffDisc_closedDisc X hX,cap.cuffDisc_closedDisc X' hX',
    cap.cuffDisc_disjoint X hX X' hX' hne,?_⟩
  have hh := capped_interior_homeomorph hY cap
  rw [hcuffs,biUnion_insert,biUnion_singleton] at hh
  exact hh

end GraphMinor.GM05
