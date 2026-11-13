module

public import GraphMinor.GM01.RegionPartition

/-!
# Initial and final unions of the ordered blocks

The boundary paths in Graph Minors I, (4.8) and (4.11), page 58, use
that an initial union of blocks is a region complement and a final
union is a region. This follows by locating the unique block of a
vertex in the partition of the initial region.
-/

public section

namespace GraphMinor.GM01

open Set

/-- A final union of the blocks equals its initial boundary region. -/
theorem iUnion_orderedRegionBlock_ge {α : Type*} {R : ℕ → Set α}
    (hR : Antitone R) (n : ℕ) (hend : R n = ∅) (a : ℕ) :
    (⋃ i : Fin n, ⋃ (_ : a ≤ i.val), orderedRegionBlock R i) = R a := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact hR hi hxi.1
  · intro x hx
    have hx0 := hR (Nat.zero_le a) hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp ((iUnion_orderedRegionBlock hR n hend).symm ▸ hx0)
    have hai : a ≤ i.val := by
      by_contra hnot
      have hia : i.val < a := Nat.lt_of_not_ge hnot
      exact hxi.2 (hR (Nat.succ_le_of_lt hia) hx)
    exact Set.mem_iUnion₂.mpr ⟨i, hai, hxi⟩

/-- An initial union of the blocks equals the complement of its final
boundary region within the initial region. -/
theorem iUnion_orderedRegionBlock_lt {α : Type*} {R : ℕ → Set α}
    (hR : Antitone R) (n : ℕ) (hend : R n = ∅) (a : ℕ) :
    (⋃ i : Fin n, ⋃ (_ : i.val < a), orderedRegionBlock R i) = R 0 \ R a := by
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    exact ⟨hR (Nat.zero_le i.val) hxi.1,
      fun h ↦ hxi.2 (hR (Nat.succ_le_of_lt hi) h)⟩
  · intro x hx
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp ((iUnion_orderedRegionBlock hR n hend).symm ▸ hx.1)
    have hia : i.val < a := by
      by_contra hnot
      exact hx.2 (hR (Nat.le_of_not_gt hnot) hxi.1)
    exact Set.mem_iUnion₂.mpr ⟨i, hia, hxi⟩

end GraphMinor.GM01
