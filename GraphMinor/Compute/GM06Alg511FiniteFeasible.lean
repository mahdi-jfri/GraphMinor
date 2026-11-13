module

public import GraphMinor.Compute.GM06Alg511LabelGraph
public import Mathlib.Basic.Real.Basic

/-!
# Feasibility expressed over finite edge labels

A finite linkage candidate for VI (5.11) consists of disjoint simple
walks from the prescribed first cuff labels to the second cuff labels.
Its scaled winding is read from its integer turn sum and endpoint
indices. This is a predicate on supplied finite graph and turn data,
not a field in the input array and not a decision supplied to a program.
The geometric equivalence is proved in the corresponding GM06 files.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Surface

/-- Finite labelled paths witnessing a prescribed winding. No path
family or feasibility bit is included in the algorithm input. -/
def GM06Alg511FiniteFeasible {n k : ℕ} (pairs : List (Fin n × Fin n)) (turns : List ℤ)
    (source target : Fin k → Fin n) (theta : ℝ) : Prop :=
  ∃ finish : Fin k → Fin k,
    ∃ walks : ∀ i, GraphWalk (gm06Alg511LabelGraph pairs) (source i) (target (finish i)),
      (∀ i, (walks i).IsSimple) ∧
      (∀ i j, i ≠ j → List.Disjoint (walks i).support (walks j).support) ∧
      ∀ i, (k : ℝ) * theta =
        (((k : ℤ) * gm06Alg511LabelWalkTurn pairs turns (walks i) +
          ((finish i).val : ℤ) - (i.val : ℤ) : ℤ) : ℝ)

end GraphMinor.Compute
