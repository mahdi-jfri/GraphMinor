module

public import GraphMinor.Crossing.DefsHistory

/-!
# The lift through all accepted operations, as a statement

Section 11 of `docs/crossing/crossing_extractor.tex`: "Thus every contraction lifts without a
search. Reversing all accepted operations gives two disjoint $C$-paths in the original graph, with
alternating ends." This combines the reverse direction of Lemma 1 (`Lemma1ReverseStatement`) and the
three lifts of Section 11 (`Lift11OffOffStatement`, `Lift11OneOnStatement`, `Lift11BothOnStatement`)
with the deletions of Sections 4 and 7.2, along a history (`IsHistory`).
-/

@[expose] public section

namespace GraphMinor.Crossing

universe u

/-- **The lift through all accepted operations** (Section 11): "Reversing all accepted operations
gives two disjoint $C$-paths in the original graph, with alternating ends." For a history from
`(G, S, D)` to `(G', S', D')`, a crossing pair of `D'` in `G'` has a lift, and every lift is a
crossing pair of `D` in `G`. A cycle-edge contraction is accepted only when the cycle has at least
five vertices (Section 10: "contractions of cycle edges are skipped when $|D|=4$"). -/
def LiftHistoryStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (G : SimpleGraph V) (S : Set V) (D : List V)
    (recs : List (CrossRecord V)) (G' : SimpleGraph V) (S' : Set V) (D' : List V)
    (L₁ L₂ : List V),
    S.Finite → HP25.IsSupportedOn G S → HP25.IsCycleList G D →
    IsHistory (G, S, D) recs (G', S', D') →
    (∀ r, CrossRecord.contr r ∈ recs → r.u ∈ r.cycle → 4 < r.cycle.length) →
    IsCrossingPair G' D' L₁ L₂ →
    (∃ P, IsLift recs (L₁, L₂) P) ∧ ∀ P, IsLift recs (L₁, L₂) P → IsCrossingPair G D P.1 P.2

end GraphMinor.Crossing
