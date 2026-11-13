module

public import GraphMinor.GM02.SidePieceIndex
import GraphMinor.GM02.SideRunRecords
import GraphMinor.GM02.ChunkIntersections

/-!
# Intersections of arbitrary original side pieces

In the forward construction for corrected II (2.9), different pieces of
an original linkage meet only at common piece endpoints, regardless of
color. Pieces from different original paths are disjoint. Within one
path, the ordered chunk intersection lemma identifies any common vertex
as the earlier piece's end and the later piece's start. This prevents a
vertex reserved for one side from being used internally on the other.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

include hP in
/-- Distinct pieces of an original feasible family can intersect only at
endpoints shared by their two piece pairs. -/
theorem RunPieceIndex.inter_subset (i j : RunPieceIndex A G H P) (hne : i ≠ j) :
    (i.path A G H P).vertices ∩ (j.path A G H P).vertices ⊆
      {a | a ∈ i.pair A G H P ∧ a ∈ j.pair A G H P} := by
  intro a ha
  by_cases hpq : i.1 = j.1
  · rcases i with ⟨p, r⟩
    rcases j with ⟨q, s⟩
    change p = q at hpq
    subst q
    have hrs : r.val ≠ s.val := by
      intro heq
      exact hne (congrArg (fun t => (⟨p, t⟩ : RunPieceIndex A G H P)) (Subtype.ext heq))
    have hnd : ((P p).start :: ((sideRunRecords H (P p).walk).map Prod.snd).flatten).Nodup := by
      rw [sideRunRecords_flatten]
      exact (P p).isPath.support_nodup
    have hrecords := chunkVertexPaths_intersections (P p).start (sideRunRecords H (P p).walk)
      (sideRunRecords_nonempty (P p).walk) hnd
    rw [sideRunRecords_restore] at hrecords
    have hpair := List.pairwise_map.1 hrecords
    have har : a ∈ (dartFullRecord (separationEdgeColor H) (P p).start r.val).2 := by
      rw [sideRunWalk_fullRecord _ _ r.property]
      exact ha.1
    have has : a ∈ (dartFullRecord (separationEdgeColor H) (P p).start s.val).2 := by
      rw [sideRunWalk_fullRecord _ _ s.property]
      exact ha.2
    rcases relation_or_reverse_of_pairwise hpair r.property s.property hrs with h | h
    · have he := h a har has
      rw [sideRunWalk_fullRecord _ _ r.property, sideRunWalk_fullRecord _ _ s.property] at he
      exact ⟨(RunPieceIndex.path A G H P ⟨p, r⟩).mem_pair_of_mem_head_or_last (Or.inr he.1),
        (RunPieceIndex.path A G H P ⟨p, s⟩).mem_pair_of_mem_head_or_last (Or.inl he.2)⟩
    · have he := h a has har
      rw [sideRunWalk_fullRecord _ _ s.property, sideRunWalk_fullRecord _ _ r.property] at he
      exact ⟨(RunPieceIndex.path A G H P ⟨p, r⟩).mem_pair_of_mem_head_or_last (Or.inl he.2),
        (RunPieceIndex.path A G H P ⟨p, s⟩).mem_pair_of_mem_head_or_last (Or.inr he.1)⟩
  · have hdis := (hP i.1 j.1 hpq).mono (i.vertices_subset A G H P) (j.vertices_subset A G H P)
    exact (Set.disjoint_left.1 hdis ha.1 ha.2).elim

end GraphMinor.GM02
