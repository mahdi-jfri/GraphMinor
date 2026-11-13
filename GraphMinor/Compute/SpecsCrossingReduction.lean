module

public import GraphMinor.Compute.SpecsCrossing
public import GraphMinor.Compute.TwoPathsSetup
public import GraphMinor.Compute.TwoPathsReduction

/-!
# Shiloach's statement from the crossing extractor

This file defines the reduction program used in `SpecsCrossingReductionProved`.
It follows Section 1.2 of
Humeau and Pous, as `TwoPathsReduction.lean` does: two disjoint paths of `G` joining `s₁, t₁` and
`s₂, t₂` are a crossing of the cycle `s₁ s₂ t₁ t₂` in `G` plus the four edges of this cycle.

The program
1. copies the lists of `G` into arrays `40`–`42` (`restrictGraphProg` with all vertices), lists
   the edges of the frame that `G` lacks (`frameEdgesProg`), and builds the lists of `G` plus the
   frame in arrays `51`–`53` (`unionProg`), as `setupProg` of `TwoPathsSetup.lean` does;
2. writes the cycle `s₁ s₂ t₁ t₂` into array `43` (`cycWrite`);
3. runs the extractor, with its output in register `170` and arrays `45`, `46`, and its scratch
   space from index `200`;
4. writes the answer into register `35`, and for the answer `1` copies the two paths into arrays
   `33` and `34`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.HP25 GraphMinor.Compute.TwoPaths

/-- The output of the reduction: the answer into register `35`, and the paths into `33`, `34`. -/
def redOutProg : Cmd :=
  .seq (.assign 35 (.reg 170))
    (.ite (.op .eq (.reg 170) (.const 1)) (.seq (copyProg 33 45) (copyProg 34 46)) .skip)

/-- The program of the reduction, around the extractor program `P`. -/
def redProg (P : Cmd) : Cmd :=
  .seq (.assign 40 (.reg 30)) (.seq (initUnivBitSetProg aY 40 149)
  (.seq (.assign 148 (.op .mul (.reg 40) (.reg 40)))
  (.seq (restrictGraphProg 30 31 32 aY 40 41 42 40 148 141 142 143 144 145 146 147)
  (.seq frameEdgesProg (.seq unionProg (.seq cycWrite (.seq P redOutProg)))))))

theorem notMem_of_lt {l : List ℕ} {r b : ℕ} (h : ∀ y ∈ l, b ≤ y) (hr : r < b) : r ∉ l :=
  fun hm => by have := h r hm; omega

theorem ncard_edgeSet_eq {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] :
    G.edgeSet.ncard = G.edgeFinset.card := by
  rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]

end GraphMinor.Compute.Crossing
