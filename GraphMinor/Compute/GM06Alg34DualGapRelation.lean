module

public import GraphMinor.Compute.GM06Alg34Input

/-!
# Computing the dual division relation on boundary gaps

Place the supplied boundary vertices at even cyclic positions and one
representative of each gap at the following odd position. For each
pair in a division block, record which side of that pair contains the
gap. Two gaps belong to the same dual block exactly when every such
side test agrees, which is the no-crossing relation of VI Section 2.
Equality of these side bits proves the relation is an equivalence.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

/-- The side of a supplied vertex pair occupied by one boundary gap.
Even positions represent vertices and the following odd positions gaps. -/
def gapSide {n : ℕ} (L : List (Fin n)) (a b : Fin n) (i : Fin L.length) : Bool :=
  decide (a ∈ L ∧ b ∈ L ∧ a ≠ b) &&
    cyclicBetween (2 * L.idxOf a) (2 * L.idxOf b) (2 * i.val + 1)

/-- The finite crossing test between a primal vertex pair and two boundary gaps. -/
def pairCrossesGaps {n : ℕ} (L : List (Fin n)) (a b : Fin n)
    (i j : Fin L.length) : Bool := gapSide L a b i != gapSide L a b j

/-- The computable no-crossing relation defining the dual division in
Graph Minors VI, Section 2, page 117. -/
def dualGapRelated (x : GM06DrawingData) (L : List (Fin x.n))
    (i j : Fin L.length) : Bool :=
  x.division.all fun B => B.all fun a => B.all fun b => gapSide L a b i == gapSide L a b j

/-- Two gaps are related exactly when every supplied block-pair side test agrees. -/
theorem dualGapRelated_iff (x : GM06DrawingData) (L : List (Fin x.n))
    (i j : Fin L.length) :
    x.dualGapRelated L i j = true ↔
      ∀ B ∈ x.division, ∀ a ∈ B, ∀ b ∈ B, gapSide L a b i = gapSide L a b j := by
  simp only [dualGapRelated, List.all_eq_true, beq_iff_eq]

/-- The relation is precisely the absence of a crossing pair in any supplied block. -/
theorem dualGapRelated_iff_no_crossing (x : GM06DrawingData) (L : List (Fin x.n))
    (i j : Fin L.length) :
    x.dualGapRelated L i j = true ↔
      ¬ ∃ B ∈ x.division, ∃ a ∈ B, ∃ b ∈ B, pairCrossesGaps L a b i j = true := by
  rw [x.dualGapRelated_iff]
  simp only [pairCrossesGaps, bne_iff_ne, not_exists, not_and]
  constructor
  · intro h B hB a ha b hb hne
    exact hne (h B hB a ha b hb)
  · intro h B hB a ha b hb
    exact Classical.byContradiction (fun hne => h B hB a ha b hb hne)

/-- Side equality makes the finite dual relation reflexive, symmetric, and transitive. -/
theorem dualGapRelated_equivalence (x : GM06DrawingData) (L : List (Fin x.n)) :
    Equivalence (fun i j : Fin L.length => x.dualGapRelated L i j = true) := by
  refine ⟨fun i => (x.dualGapRelated_iff L i i).mpr (fun _ _ _ _ _ _ => rfl), ?_, ?_⟩
  · intro i j hij
    exact (x.dualGapRelated_iff L j i).mpr (fun B hB a ha b hb =>
      ((x.dualGapRelated_iff L i j).mp hij B hB a ha b hb).symm)
  · intro i j k hij hjk
    exact (x.dualGapRelated_iff L i k).mpr (fun B hB a ha b hb =>
      ((x.dualGapRelated_iff L i j).mp hij B hB a ha b hb).trans
        ((x.dualGapRelated_iff L j k).mp hjk B hB a ha b hb))

end GraphMinor.Compute.GM06DrawingData
