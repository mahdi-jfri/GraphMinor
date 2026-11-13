module

public import GraphMinor.GM01.CombBlockUnions
public import GraphMinor.GM01.LayerBlockSets

/-!
# Region formulas for the block sets around a layer

For the extension in Graph Minors I, (4.8), page 58, the early set is
an initial piece of the comb and the late set is a final region. At
the first two layers the early set is empty. At the last layer the
late set is empty. The formulas below translate the printed one-based
index bounds to the region identities for zero-based blocks.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The early set preceding GM01 (4.6) is a comb prefix. -/
theorem layerEarlyBlocks_eq_combPrefix {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α)
    (hR : Antitone (combSpineRegion hL H c)) (ν i : ℕ) (p : Fin n)
    (hp : p.val = ν * (i - 1)) :
    layerEarlyBlocks (fun k : Fin n ↦ combBlock hL H c k) ν i = combPrefix hL H c p.val := by
  rw [← iUnion_combBlock_lt hL H c hR p]
  ext x
  simp only [layerEarlyBlocks, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk, hxk⟩
    exact ⟨k, by change k.val < p.val; omega, hxk⟩
  · rintro ⟨k, hk, hxk⟩
    exact ⟨k, by change k.val < p.val at hk; omega, hxk⟩

/-- The late set preceding GM01 (4.6) is a later comb region. -/
theorem layerLateBlocks_eq_combSpineRegion {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (H : Graph α β) (c : (pathComb γ L).verts → α)
    (hR : Antitone (combSpineRegion hL H c)) (ν i : ℕ) (q : Fin n)
    (hq : q.val + 1 = ν * (i + 1)) :
    layerLateBlocks (fun k : Fin n ↦ combBlock hL H c k) ν i =
      combSpineRegion hL H c (2 * q.val) := by
  rw [← iUnion_combBlock_ge hL H c hR q]
  ext x
  simp only [layerLateBlocks, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk, hxk⟩
    exact ⟨k, by change q.val ≤ k.val; omega, hxk⟩
  · rintro ⟨k, hk, hxk⟩
    exact ⟨k, by change q.val ≤ k.val at hk; omega, hxk⟩

/-- There are no early blocks for the first two layers. -/
theorem layerEarlyBlocks_eq_empty {α : Type*} {n ν i : ℕ} (S : Fin n → Set α)
    (hi : i ≤ 1) : layerEarlyBlocks S ν i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨k, hk, _⟩ := Set.mem_iUnion₂.mp hx
  have hi0 : i - 1 = 0 := Nat.sub_eq_zero_of_le hi
  rw [hi0, Nat.mul_zero] at hk
  omega

/-- A late index range beginning beyond the last block is empty. -/
theorem layerLateBlocks_eq_empty {α : Type*} {n ν i : ℕ} (S : Fin n → Set α)
    (hi : n < ν * (i + 1)) : layerLateBlocks S ν i = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨k, hk, _⟩ := Set.mem_iUnion₂.mp hx
  have hkn := k.isLt
  omega

end GraphMinor.GM01
