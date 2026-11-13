module

public import GraphMinor.GM01.CombPrefixes
import GraphMinor.GM01.RegionBlockUnions

/-!
# Initial and final unions of comb blocks

For the boundary paths in Graph Minors I, (4.8) and (4.11), page 58,
identify the union of blocks before a boundary with its connected
prefix, and the union at and after that boundary with its later
region. We apply the union identities for successive differences to
the truncated sequence of even-indexed comb regions.
-/

public section

namespace GraphMinor.GM01

open Set Graph

private theorem even_regions_antitone {α : Type*} {F : ℕ → Set α}
    (hF : Antitone F) (n : ℕ) :
    Antitone (fun k ↦ if k < n then F (2 * k) else ∅) := by
  intro a b hab
  by_cases hb : b < n
  · have ha : a < n := lt_of_le_of_lt hab hb
    simp only [ha, hb, ↓reduceIte]
    exact hF (Nat.mul_le_mul_left 2 hab)
  · simp only [hb, ↓reduceIte]
    exact empty_subset _

/-- All blocks at or after a boundary form its later region. The last
block includes the whole remaining tail. -/
theorem iUnion_combBlock_ge {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α)
    (hR : Antitone (combSpineRegion hL H c)) (a : Fin n) :
    (⋃ i : Fin n, ⋃ (_ : a ≤ i), combBlock hL H c i) =
      combSpineRegion hL H c (2 * a.val) := by
  let F := fun k ↦ if k < n then combSpineRegion hL H c (2 * k) else ∅
  have hF : Antitone F := even_regions_antitone hR n
  have hend : F n = ∅ := by simp only [F, lt_self_iff_false, ↓reduceIte]
  change (⋃ i : Fin n, ⋃ (_ : a.val ≤ i.val), orderedRegionBlock F i) = _
  rw [iUnion_orderedRegionBlock_ge hF n hend a.val]
  simp only [F, a.isLt, ↓reduceIte]

/-- All blocks before a boundary form its initial piece. -/
theorem iUnion_combBlock_lt {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α)
    (hR : Antitone (combSpineRegion hL H c)) (a : Fin n) :
    (⋃ i : Fin n, ⋃ (_ : i < a), combBlock hL H c i) = combPrefix hL H c a.val := by
  let F := fun k ↦ if k < n then combSpineRegion hL H c (2 * k) else ∅
  have hF : Antitone F := even_regions_antitone hR n
  have hend : F n = ∅ := by simp only [F, lt_self_iff_false, ↓reduceIte]
  change (⋃ i : Fin n, ⋃ (_ : i.val < a.val), orderedRegionBlock F i) = _
  rw [iUnion_orderedRegionBlock_lt hF n hend a.val]
  have hn : 0 < n := Nat.zero_lt_of_lt a.isLt
  simp only [F, hn, a.isLt, ↓reduceIte, Nat.mul_zero, combSpineRegion_zero, combPrefix]

end GraphMinor.GM01
