module

public import Mathlib.Data.Set.Lattice.Indexed
public import Mathlib.Data.Set.Lattice.Disjoint
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

/-!
# Partition by successive differences of nested regions

On page 55 of Graph Minors I, consecutive differences of nested regions,
followed by the last region, partition the vertices of the comb. This
set lemma treats the final region by adding an empty endpoint to the
sequence. Each vertex belongs to the block just before the first region
that omits it. This proves coverage and disjointness independently of
the later graph-theoretic separator argument.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set

/-- A block between successive nested regions, as used in the page-55
partition of the subdivided comb. An empty final region makes the last
block equal to the preceding region. -/
def orderedRegionBlock {α : Type*} (R : ℕ → Set α) {n : ℕ} (i : Fin n) : Set α :=
  R i.val \ R (i.val + 1)

/-- Successive differences of a decreasing sequence of regions are
pairwise disjoint. -/
theorem orderedRegionBlock_pairwise_disjoint {α : Type*} {R : ℕ → Set α}
    (hR : Antitone R) (n : ℕ) : Pairwise (fun i j : Fin n ↦ Disjoint (orderedRegionBlock R i) (orderedRegionBlock R j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
  · exact hxi.2 (hR (by omega : i.val + 1 ≤ j.val) hxj.1)
  · exact hxj.2 (hR (by omega : j.val + 1 ≤ i.val) hxi.1)

/-- If the endpoint region is empty, every vertex of the initial region
belongs to one of the blocks. The first omitted region specifies its
block index. -/
theorem iUnion_orderedRegionBlock {α : Type*} {R : ℕ → Set α}
    (hR : Antitone R) (n : ℕ) (hend : R n = ∅) :
    (⋃ i : Fin n, orderedRegionBlock R i) = R 0 := by
  classical
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact hR (Nat.zero_le i.val) hi.1
  · intro x hx
    have hex : ∃ k : ℕ, x ∉ R k := ⟨n, by rw [hend]; exact notMem_empty x⟩
    let k := Nat.find hex
    have hk : x ∉ R k := Nat.find_spec hex
    have hkpos : 0 < k := by
      by_contra h
      have heq : k = 0 := by omega
      exact hk (heq ▸ hx)
    have hkn : k ≤ n := Nat.find_min' hex (by rw [hend]; exact notMem_empty x)
    have hprev : x ∈ R (k - 1) := by
      by_contra h
      have hbad := Nat.find_min' hex h
      change k ≤ k - 1 at hbad
      omega
    refine mem_iUnion.mpr ⟨⟨k - 1, by omega⟩, hprev, ?_⟩
    change x ∉ R (k - 1 + 1)
    simpa only [Nat.sub_add_cancel hkpos] using hk

/-- A block is contained in its initial region. -/
theorem orderedRegionBlock_subset_region {α : Type*} (R : ℕ → Set α) {n : ℕ}
    (i : Fin n) : orderedRegionBlock R i ⊆ R i.val := sdiff_subset

/-- Every earlier block is disjoint from a later boundary region. This
is the avoidance property used when extending a bypass through the tail
in the proof of Graph Minors I, (4.1). -/
theorem orderedRegionBlock_disjoint_later_region {α : Type*} {R : ℕ → Set α}
    (hR : Antitone R) {n : ℕ} (i : Fin n) (k : ℕ) (hik : i.val < k) :
    Disjoint (orderedRegionBlock R i) (R k) := by
  apply disjoint_left.mpr
  intro x hxi hxk
  exact hxi.2 (hR (Nat.succ_le_of_lt hik) hxk)

end GraphMinor.GM01
