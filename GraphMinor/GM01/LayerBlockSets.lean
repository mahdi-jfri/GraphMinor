module

public import GraphMinor.GM01.SeparatorLayers
import Lean.Elab.Tactic.Omega

/-!
# The early and late blocks around a layer

Graph Minors I, page 57, defines `A` from blocks at and after
`ν(i+1)`, and `B` from blocks at and before `ν(i-1)`. Their index
ranges are disjoint. We retain the printed one-based bounds while the
block family itself is indexed from zero.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set

/-- The set `A` preceding GM01 (4.6), page 57: the union of blocks
whose one-based index is at least `ν(i+1)`. -/
def layerLateBlocks {α : Type*} {n : ℕ} (S : Fin n → Set α) (ν i : ℕ) : Set α :=
  ⋃ k : Fin n, ⋃ (_ : ν * (i + 1) ≤ k.val + 1), S k

/-- The set `B` preceding GM01 (4.6), page 57: the union of blocks
whose one-based index is at most `ν(i-1)`. -/
def layerEarlyBlocks {α : Type*} {n : ℕ} (S : Fin n → Set α) (ν i : ℕ) : Set α :=
  ⋃ k : Fin n, ⋃ (_ : k.val + 1 ≤ ν * (i - 1)), S k

/-- The early and late block sets in GM01 (4.6) are disjoint because
their index ranges are disjoint and the blocks form a disjoint family. -/
theorem disjoint_layerLateBlocks_layerEarlyBlocks {α : Type*} {n ν : ℕ}
    (S : Fin n → Set α) (hν : 0 < ν)
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j))) (i : ℕ) :
    Disjoint (layerLateBlocks S ν i) (layerEarlyBlocks S ν i) := by
  apply Set.disjoint_left.mpr
  intro x hxA hxB
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxA
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxB
  have hlt : ν * (i - 1) < ν * (i + 1) :=
    Nat.mul_lt_mul_of_pos_left (by omega : i - 1 < i + 1) hν
  have hjk : j.val < k.val := by omega
  exact Set.disjoint_left.mp (hdis (fun h ↦ (Nat.ne_of_lt hjk) (congrArg Fin.val h.symm))) hxk hxj

end GraphMinor.GM01
