module

public import GraphMinor.Compute.Algorithm99SpecShift
public import GraphMinor.Compute.Algorithm99Order
public import GraphMinor.Compute.Algorithm99Small
public import GraphMinor.Compute.TwoPathsRun

/-!
# Runs of Algorithm (9.9) and its edge-order conversion

The small-parameter program produces a one-vertex clique model or the empty
branch-decomposition. The sorting example has repeated tails and checks that
the assignments within each bucket retain their source order. An empty source
and unused vertex buckets are checked separately.
-/

@[expose] public section
namespace GraphMinor.Compute.Alg99Examples

/-- Tail keys and distinct leaf assignments, with a sentinel in other arrays. -/
def sortState : State where
  regs r := if r = 20 then 4 else 0
  arrs a := if a = 0 then [2, 0, 1, 2, 0, 2]
    else if a = 1 then [10, 11, 12, 13, 14, 15] else [99]

set_option maxRecDepth 10000 in
/-- Equal tails keep their order, while unused vertex buckets remain empty. -/
theorem stable_tail_sort_run :
    ((alg99TailSortProg 0 10 20).run 8 1000 sortState).map
      (fun result => (result.1.arrs 4, result.1.arrs 2, result.1.arrs 5)) =
      some ([11, 14, 12, 10, 13, 15], [2, 1, 3, 0], [99]) := by
  decide +kernel

/-- Empty key and value arrays, with a sentinel in unrelated arrays. -/
def emptySortState : State where
  regs r := if r = 20 then 3 else 0
  arrs a := if a = 0 ∨ a = 1 then [] else [99]

set_option maxRecDepth 10000 in
/-- The sorter accepts an empty source even when vertex buckets exist. -/
theorem empty_tail_sort_run :
    ((alg99TailSortProg 0 10 20).run 8 1000 emptySortState).map
      (fun result => (result.1.arrs 4, result.1.arrs 2, result.1.arrs 3)) =
      some ([], [0, 0, 0], [0, 0, 0]) := by
  decide +kernel

/-- For `p = 1`, a graph with three vertices yields the model `{0}`. -/
theorem one_clique_run :
    (alg99OneProg.run 8 100 (initState [3, 0])).map (fun result => result.1.arrs outArr) =
      some [1, 1, 0, 0] := by
  decide +kernel

/-- For `p = 1`, the graph with no vertices yields the empty decomposition. -/
theorem empty_graph_run :
    (alg99OneProg.run 8 100 (initState [0, 0])).map (fun result => result.1.arrs outArr) =
      some [0, 0, 0] := by
  decide +kernel

/-- Two arcs whose active-pair edge order is the reverse of caller row order. -/
def reorderedGraph : MultiDigraph 3 where
  edgeMult u v := if (u.1 = 1 ∧ v.1 = 0) ∨ (u.1 = 0 ∧ v.1 = 2) then 1 else 0

/-- A decomposition code and the saved graph, at their shifted caller addresses.
Protected registers and unrelated arrays contain sentinels. -/
def shiftedBDState : State where
  regs _ := 7
  arrs a := if a = 33 then [0, 2, 2, 0, 0, 0, 1]
    else if a = 80 then reorderedGraph.enc else [99]

/-- The shifted output handler followed by the actual caller register writes. -/
def shiftedBDProg : Cmd :=
  .seq ((alg99SpecHandleProg 40 100).shift 32 53) alg99SpecFinishProg

set_option maxRecDepth 10000 in
/-- The decomposition branch reverses the two leaf words, writes the tag and
size, and preserves a protected register and an array below the caller base. -/
theorem shifted_decomposition_run :
    (shiftedBDProg.run 12 1000 shiftedBDState).map (fun result =>
      (result.1.regs 51, result.1.regs 52, result.1.arrs 34,
        result.1.arrs 35, result.1.arrs 31, result.1.regs 0)) =
      some (0, 2, [0, 0], [1, 0], [99], 7) := by
  decide +kernel

end GraphMinor.Compute.Alg99Examples
