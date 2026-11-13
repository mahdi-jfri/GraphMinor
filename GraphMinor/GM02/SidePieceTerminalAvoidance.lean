module

public import GraphMinor.GM02.SideEndpointConditions
public import GraphMinor.GM02.SidePieceIntersections

/-!
# Side pieces avoid original terminals assigned elsewhere

Every original terminal is an endpoint of some contracted piece. If it
also lies on another piece, the piece intersection lemma makes it an
endpoint there too. Thus a piece cannot pass through an original terminal
absent from its side termination. This is the extra avoidance condition
needed for the corrected induced graphs in II (2.9).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- An original terminal on a side piece is an endpoint of that piece's side termination. -/
theorem RunPieceIndex.original_mem_side_support (i : RunPieceIndex A G H P)
    {a : α} (haA : a ∈ A.support) (hai : a ∈ (i.path A G H P).vertices) :
    a ∈ (sideTermination A G H P hP (i.color A G H P)).support := by
  have haU := (sideTermination_isPairPathUnion A G H P hP).original_support_subset A
    (sideTermination A G H P hP true) (sideTermination A G H P hP false) haA
  obtain ⟨j, haj⟩ : ∃ j : RunPieceIndex A G H P, a ∈ j.pair A G H P := by
    rcases haU with hL | hR
    · obtain ⟨j, _, hj⟩ := (mem_sideTermination_support A G H P hP true a).1 hL
      exact ⟨j, hj⟩
    · obtain ⟨j, _, hj⟩ := (mem_sideTermination_support A G H P hP false a).1 hR
      exact ⟨j, hj⟩
  have haPair : a ∈ i.pair A G H P := by
    by_cases hij : i = j
    · exact hij.symm ▸ haj
    · exact (RunPieceIndex.inter_subset A G H P hP i j hij
        ⟨hai, (j.path A G H P).endpoint_mem haj⟩).1
  exact (mem_sideTermination_support A G H P hP _ a).2 ⟨i, rfl, haPair⟩

/-- Opposite-side pieces can meet only at endpoints present on both sides. -/
theorem RunPieceIndex.opposite_inter_mem_support (i j : RunPieceIndex A G H P)
    (hc : i.color A G H P ≠ j.color A G H P) {a : α}
    (hai : a ∈ (i.path A G H P).vertices) (haj : a ∈ (j.path A G H P).vertices) :
    a ∈ (sideTermination A G H P hP (i.color A G H P)).support ∩
      (sideTermination A G H P hP (j.color A G H P)).support := by
  have hij : i ≠ j := fun he => hc (congrArg (RunPieceIndex.color A G H P) he)
  have he := RunPieceIndex.inter_subset A G H P hP i j hij ⟨hai, haj⟩
  exact ⟨(mem_sideTermination_support A G H P hP _ a).2 ⟨i, rfl, he.1⟩,
    (mem_sideTermination_support A G H P hP _ a).2 ⟨j, rfl, he.2⟩⟩

end GraphMinor.GM02
