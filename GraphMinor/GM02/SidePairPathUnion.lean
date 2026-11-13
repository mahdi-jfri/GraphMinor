module

public import GraphMinor.GM02.SideBoundaryPath
public import GraphMinor.GM02.CrossingScheme
import GraphMinor.GM02.OrientPairPath

/-!
# The path-union condition for the extracted side terminations

In the forward construction for corrected II (2.9), contracting the maximal
side pieces gives disjoint paths for the original pairs. Every new endpoint
belongs to one of these paths, and every contracted edge is one of the
piece pairs. This proves condition (iv) of the crossing-scheme definition
for the two extracted terminations.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- The contracted side pieces satisfy the full path-union condition (iv)
of II's crossing-scheme definition, page 315. -/
theorem sidePairGraph_isPairPathUnion : IsPairPathUnion A (sidePairGraph A G H P hP)
    ((sideTermination A G H P hP true).support ∪ (sideTermination A G H P hP false).support) := by
  let Q := sideBoundaryPairPath A G H P hP
  let W := fun p : {p // p ∈ A.pairs} => (Q p).outPath.val
  have hW : ∀ p, {a | a ∈ (W p).support} = (Q p).vertices :=
    fun p => (Q p).outPath_vertices
  refine ⟨W, fun p => (Q p).outPath.property, ?_, ?_, ?_⟩
  · intro p q hpq
    rw [hW p, hW q]
    exact (hP p q hpq).mono (sideBoundaryPairPath_vertices_subset A G H P hP p)
      (sideBoundaryPairPath_vertices_subset A G H P hP q)
  · ext a
    constructor
    · intro ha
      obtain ⟨p, hap⟩ := Set.mem_iUnion.1 ha
      have haQ : a ∈ (Q p).vertices := (hW p) ▸ hap
      obtain ⟨e, he, hae⟩ :=
        (Walk.mem_support_iff_exists_mem_edges_of_not_nil ((Q p).not_nil (A.not_diag p.val p.property))).1 haQ
      have heF := (Q p).walk.edges_subset_edgeSet he
      obtain ⟨i, hi⟩ := (sidePairGraph_mem_edgeSet A G H P hP e).1 heF
      have hai : a ∈ i.pair A G H P := hi.symm ▸ hae
      cases hc : i.color A G H P with
      | false => exact Or.inr ((mem_sideTermination_support A G H P hP false a).2 ⟨i, hc, hai⟩)
      | true => exact Or.inl ((mem_sideTermination_support A G H P hP true a).2 ⟨i, hc, hai⟩)
    · intro ha
      have hex : ∃ i : RunPieceIndex A G H P, a ∈ i.pair A G H P := by
        rcases ha with ha | ha
        · obtain ⟨i, _, hi⟩ := (mem_sideTermination_support A G H P hP true a).1 ha
          exact ⟨i, hi⟩
        · obtain ⟨i, _, hi⟩ := (mem_sideTermination_support A G H P hP false a).1 ha
          exact ⟨i, hi⟩
      obtain ⟨i, hai⟩ := hex
      have he := sideBoundaryPairPath_piece_edge A G H P hP i
      have haQ : a ∈ (Q i.1).vertices := (Q i.1).walk.mem_support_of_mem_edges he hai
      have haW : a ∈ {a | a ∈ (W i.1).support} := (hW i.1).symm ▸ haQ
      exact Set.mem_iUnion.2 ⟨i.1, haW⟩
  · intro e he
    obtain ⟨i, hi⟩ := (sidePairGraph_mem_edgeSet A G H P hP e).1 he
    refine ⟨i.1, ?_⟩
    apply ((Q i.1).outPath_edges e).2
    have heI := sideBoundaryPairPath_piece_edge A G H P hP i
    exact hi ▸ heI

end GraphMinor.GM02
