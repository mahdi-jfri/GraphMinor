module

public import GraphMinor.Compute.PlanarityRamWork
public import GraphMinor.Compute.BFS
import Mathlib.Algebra.BigOperators.Fin

/-!
# The initial DFS work budget

The sum of the adjacency-list lengths is the edge-arena capacity. Adding
one completion unit per vertex gives the initial frame-step budget. This
also identifies the fuel expression in `depthFirstSearch` with the count
computed by the RAM preparation program.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity
open scoped BigOperators

/-- The functional fuel counts the same entries as the RAM header pass. -/
theorem adjacency_fold_eq_total {N : ℕ} (lists : Fin N → List ℕ) :
    (List.ofFn lists).toArray.foldl (fun total l => total + l.length) 0 = totalAdjEntries lists := by
  rw [List.foldl_toArray' _ _ _ rfl, ← List.foldl_map, ← List.sum_eq_foldl,
    List.map_ofFn, List.sum_ofFn]
  rfl

/-- The initial search has exactly M adjacency-scan work and N completion
units, with an arbitrary completion weight c. -/
theorem initial_searchWork {N : ℕ} (lists : Fin N → List ℕ) (c : ℕ) :
    searchWork (List.ofFn lists).toArray c (initialSearch N) [] = totalAdjEntries lists + N * c := by
  simp only [searchWork, initialSearch, frameWork, List.map_nil, List.sum_nil, Nat.add_zero]
  have hsize : (List.ofFn lists).toArray.size = N := by simp
  rw [hsize, unseenWork_initial, Finset.sum_add_distrib]
  have hdegrees : (∑ v : Fin N, (List.ofFn lists).toArray[v.val]!.length) = totalAdjEntries lists := by
    apply Finset.sum_congr rfl
    intro v _
    rw [getElem!_pos (List.ofFn lists).toArray v.val (by simp)]
    simp
  rw [hdegrees]
  simp

end GraphMinor.Compute.PlanarityRam
