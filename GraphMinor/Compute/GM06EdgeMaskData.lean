module

public import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Reusing endpoint labels with a new activity mask

The cylinder reductions keep original edge indices. Replacing
an activity mask changes only the flags paired with those indices.
The endpoint pairs and their order stay fixed. These equations
allow the next component search to interpret the updated arrays
as another finite active graph on the same label space.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Pair the original endpoint rows with the supplied new activity words. -/
def gm06RetagEdges {n : ℕ} (tagged : List ((Fin n × Fin n) × ℕ)) (mask : List ℕ) :
    List ((Fin n × Fin n) × ℕ) :=
  tagged.mapIdx fun i p => (p.1, mask[i]?.getD 0)

/-- Updating activity words leaves the number of original edge labels unchanged. -/
theorem gm06RetagEdges_length {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (mask : List ℕ) :
    (gm06RetagEdges tagged mask).length = tagged.length := by
  simp only [gm06RetagEdges, List.length_mapIdx]

/-- Each updated row has the same endpoints and the new activity word. -/
theorem gm06RetagEdges_getElem {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (mask : List ℕ)
    (hlen : mask.length = tagged.length) {i : ℕ} (hi : i < tagged.length) :
    (gm06RetagEdges tagged mask)[i]'(by rw [gm06RetagEdges_length]; exact hi) =
      (tagged[i].1, mask[i]'(hlen.symm ▸ hi)) := by
  simp only [gm06RetagEdges, List.getElem_mapIdx, List.getElem?_eq_getElem (hlen.symm ▸ hi), Option.getD_some]

/-- All endpoint pairs are preserved in their original order. -/
theorem gm06RetagEdges_endpoints {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (mask : List ℕ) :
    (gm06RetagEdges tagged mask).map Prod.fst = tagged.map Prod.fst := by
  apply List.ext_getElem (by simp only [List.length_map, gm06RetagEdges_length])
  intro i hi hi'
  simp only [List.getElem_map, gm06RetagEdges, List.getElem_mapIdx]

/-- A mask of the right length is exactly the new sequence of activity words. -/
theorem gm06RetagEdges_activity {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (mask : List ℕ) (hlen : mask.length = tagged.length) :
    (gm06RetagEdges tagged mask).map Prod.snd = mask := by
  apply List.ext_getElem (by simp only [List.length_map, gm06RetagEdges_length, hlen])
  intro i hi hi'
  have hiT : i < tagged.length := by simpa only [List.length_map, gm06RetagEdges_length] using hi
  simp only [List.getElem_map, gm06RetagEdges_getElem tagged mask hlen hiT]

/-- Replacing flags by zero-one words retains the same bound on every row flag. -/
theorem gm06RetagEdges_flags_le_one {n : ℕ}
    (tagged : List ((Fin n × Fin n) × ℕ)) (mask : List ℕ) (hlen : mask.length = tagged.length)
    (hbits : ∀ b ∈ mask, b ≤ 1) : ∀ p ∈ gm06RetagEdges tagged mask, p.2 ≤ 1 := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  have hiT : i < tagged.length := by simpa only [gm06RetagEdges_length] using hi
  rw [gm06RetagEdges_getElem tagged mask hlen hiT]
  exact hbits _ (List.getElem_mem (hlen.symm ▸ hiT))

end GraphMinor.Compute
