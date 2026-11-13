module

public import GraphMinor.Compute.GM06Alg34GapRegionUpdate
public import GraphMinor.Compute.GM06Alg34RootRanks
import GraphMinor.Compute.GM06Alg34RankLabels

/-!
# Recovering an updated gap region from root masks and ranks

An old region's complement component contains exactly one canonical
root. The root-mask prefix at that root is its index in the ordered
root list, hence exactly the updated region label. These facts justify
the RAM scan of the component marks and root arrays.
-/

public section
namespace GraphMinor.Compute

private theorem indicator_sum {α : Type*} (L : List α) (p : α → Bool) :
    (L.map (fun a => if p a then (1 : ℕ) else 0)).sum = (L.filter p).length := by
  induction L with
  | nil => rfl
  | cons a L ih => cases hp : p a <;> simp [hp, ih, Nat.add_comm]

namespace GM06DrawingData

/-- The root-mask prefix at a root is its position in the ordered root list. -/
theorem regionRoot_prefix_rank (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (ha : a ∈ x.regionRoots vs) :
    ((gm06RootMask x vs).take a.val).sum = (x.regionRoots vs).idxOf a := by
  have hp : x.isRegionRoot vs a = true := (List.mem_filter.mp ha).2
  rw [gm06RootMask, List.ofFn_eq_map, ← List.map_take, indicator_sum]
  have hh := gm06_idxOf_filter_eq_length_take (x.isRegionRoot vs) (List.finRange x.cellCount)
    a (List.mem_finRange a) hp
  simpa only [regionRoots, List.idxOf_finRange] using hh.symm

/-- The rank read at an old region's selected root is exactly its new label. -/
theorem regionAfterDeletion_prefix_rank (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) :
    ((gm06RootMask x vs).take (x.regionRootAfterDeletion vs r).val).sum =
      (x.regionAfterDeletion vs r).val := by
  rw [x.regionRoot_prefix_rank vs _ (x.regionRootAfterDeletion_mem vs r)]
  have hh := gm06ListIndex_get_index (x.regionRoots vs) (x.regionRoots_nodup vs)
    (Fin.cast (x.inducedData_regions_length vs) (x.regionAfterDeletion vs r))
  exact congrArg (fun i : Fin (x.regionRoots vs).length => i.val) hh

/-- A reached cell has the root flag exactly when it is the selected root. -/
theorem gap_reached_root_iff (x : GM06DrawingData) (vs : List (Fin x.n))
    (r : Fin x.regions.length) (a : Fin x.cellCount) :
    ((x.complementGraph vs).Reachable (x.cellNumbering (.inr (.inr r))) a ∧
      x.isRegionRoot vs a = true) ↔ a = x.regionRootAfterDeletion vs r := by
  constructor
  · rintro ⟨hr, ha⟩
    have hamem : a ∈ x.regionRoots vs := List.mem_filter.mpr ⟨List.mem_finRange a, ha⟩
    exact x.regionRoots_eq_of_reachable vs hamem (x.regionRootAfterDeletion_mem vs r)
      (hr.symm.trans (x.regionAfterDeletion_reachable vs r))
  · rintro rfl
    exact ⟨x.regionAfterDeletion_reachable vs r,
      (List.mem_filter.mp (x.regionRootAfterDeletion_mem vs r)).2⟩

end GM06DrawingData
end GraphMinor.Compute
