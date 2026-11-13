module

public import GraphMinor.GM01.BlockAttachmentRegions
import Lean.Elab.Tactic.Omega

/-!
# The attachment windows around sampled separators

In the proof of Graph Minors I, (4.5), pages 56–57, the set called `Z`
is a window with ordinary blocks at its two ends and attachment regions
inside. Two disjoint index windows give disjoint vertex sets. A vertex
in the block union belongs only to its own block. Outside that union,
the interior attachment regions of the two windows have an intervening
block, which separates them by (4.1).
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph GraphMinor.GM09 GraphMinor.Surface

/-- The set `Z` in the proof of GM01 (4.5), page 57: two boundary
blocks and the attachment regions of the blocks strictly between them. -/
def blockAttachmentWindow {α β : Type*} {n : ℕ} (G : Graph α β)
    (S : Fin n → Set α) (l r : Fin n) : Set α :=
  S l ∪ (⋃ i, ⋃ (_ : l < i ∧ i < r),
    blockAttachmentRegion G (⋃ j, S j) (S i)) ∪ S r

/-- Regions attached to blocks with another block strictly between
them are disjoint, by the intervening block's separator property. -/
theorem disjoint_ordered_blockAttachmentRegions {α β : Type*} {n : ℕ}
    {G : Graph α β} (S : Fin n → Set α)
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hsep : ∀ k, GraphSeparates G (S k)
      (⋃ i, ⋃ (_ : i < k), S i) (⋃ i, ⋃ (_ : k < i), S i))
    (i j : Fin n) (hij : i.val + 1 < j.val) :
    Disjoint (blockAttachmentRegion G (⋃ k, S k) (S i))
      (blockAttachmentRegion G (⋃ k, S k) (S j)) := by
  let k : Fin n := ⟨i.val + 1, by have hjn := j.isLt; omega⟩
  have hik : i < k := by change i.val < i.val + 1; omega
  have hkj : k < j := hij
  apply disjoint_blockAttachmentRegion_of_separator
    ((hsep k).mono (fun _ hx ↦ Set.mem_iUnion₂.mpr ⟨i, hik, hx⟩)
      (fun _ hx ↦ Set.mem_iUnion₂.mpr ⟨j, hkj, hx⟩))
  · intro x hx
    exact ⟨Set.mem_iUnion.mpr ⟨k, hx⟩,
      fun h ↦ Set.disjoint_left.mp (hdis hik.ne.symm) hx h⟩
  · intro x hx
    exact ⟨Set.mem_iUnion.mpr ⟨k, hx⟩,
      fun h ↦ Set.disjoint_left.mp (hdis hkj.ne) hx h⟩

/-- Within the union of the blocks, a window contains only its own
index interval. -/
theorem mem_blockAttachmentWindow_of_mem_union {α β : Type*} {n : ℕ}
    {G : Graph α β} {S : Fin n → Set α} (hSG : ∀ i, S i ⊆ V(G))
    {l r : Fin n} (hlr : l ≤ r) {x : α}
    (hx : x ∈ blockAttachmentWindow G S l r) (hxU : x ∈ ⋃ j, S j) :
    ∃ i, l ≤ i ∧ i ≤ r ∧ x ∈ S i := by
  rcases hx with (hxl | hxi) | hxr
  · exact ⟨l, le_rfl, hlr, hxl⟩
  · obtain ⟨i, hi, hxZ⟩ := Set.mem_iUnion₂.mp hxi
    have hSiU : S i ⊆ ⋃ j, S j := fun _ h ↦ Set.mem_iUnion.mpr ⟨i, h⟩
    exact ⟨i, hi.1.le, hi.2.le, (blockAttachmentRegion_inter hSiU (hSG i)) ▸ ⟨hxZ, hxU⟩⟩
  · exact ⟨r, hlr, le_rfl, hxr⟩

/-- An attachment window avoids every block whose index is outside
its interval. This is the avoidance check for the second path in
GM01 (4.7), page 58. -/
theorem disjoint_blockAttachmentWindow_outside_blocks {α β : Type*} {n : ℕ}
    {G : Graph α β} (S : Fin n → Set α) (hSG : ∀ i, S i ⊆ V(G))
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (l r : Fin n) (hlr : l ≤ r) :
    Disjoint (blockAttachmentWindow G S l r)
      (⋃ k : Fin n, ⋃ (_ : k < l ∨ r < k), S k) := by
  apply Set.disjoint_left.mpr
  intro x hx hxOut
  obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxOut
  have hxU : x ∈ ⋃ j, S j := Set.mem_iUnion.mpr ⟨k, hxk⟩
  obtain ⟨j, hlj, hjr, hxj⟩ := mem_blockAttachmentWindow_of_mem_union hSG hlr hx hxU
  have hjk : j ≠ k := by
    intro heq
    subst k
    rcases hk with hk | hk
    · exact (not_lt_of_ge hlj) hk
    · exact (not_lt_of_ge hjr) hk
  exact Set.disjoint_left.mp (hdis hjk) hxj hxk

/-- The disjointness assertion used before and during GM01 (4.5),
pages 56–57: attachment windows with disjoint index intervals are
disjoint even when their two boundary blocks are consecutive. -/
theorem disjoint_blockAttachmentWindows {α β : Type*} {n : ℕ} {G : Graph α β}
    (S : Fin n → Set α) (hSG : ∀ i, S i ⊆ V(G))
    (hdis : Pairwise (fun i j ↦ Disjoint (S i) (S j)))
    (hsep : ∀ k, GraphSeparates G (S k)
      (⋃ i, ⋃ (_ : i < k), S i) (⋃ i, ⋃ (_ : k < i), S i))
    (l r l' r' : Fin n) (hlr : l ≤ r) (hlr' : l' ≤ r') (hgap : r < l') :
    Disjoint (blockAttachmentWindow G S l r) (blockAttachmentWindow G S l' r') := by
  classical
  apply Set.disjoint_left.mpr
  intro x hx hx'
  by_cases hxU : x ∈ ⋃ j, S j
  · obtain ⟨i, hli, hir, hxi⟩ := mem_blockAttachmentWindow_of_mem_union hSG hlr hx hxU
    obtain ⟨j, hlj, hjr, hxj⟩ := mem_blockAttachmentWindow_of_mem_union hSG hlr' hx' hxU
    exact Set.disjoint_left.mp (hdis (ne_of_lt (lt_of_le_of_lt hir (hgap.trans_le hlj)))) hxi hxj
  · have hNoBlock : ∀ i, x ∉ S i := fun i h ↦ hxU (Set.mem_iUnion.mpr ⟨i, h⟩)
    rcases hx with (hxl | hxi) | hxr
    · exact hNoBlock l hxl
    · rcases hx' with (hxl' | hxj) | hxr'
      · exact hNoBlock l' hxl'
      · obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hxi
        obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.mp hxj
        have hij : i.val + 1 < j.val := by
          have hir := hi.2; have hlj := hj.1
          change i.val < r.val at hir
          change l'.val < j.val at hlj
          change r.val < l'.val at hgap
          omega
        exact Set.disjoint_left.mp (disjoint_ordered_blockAttachmentRegions S hdis hsep i j hij) hxi hxj
      · exact hNoBlock r' hxr'
    · exact hNoBlock r hxr

/-- A vertex of a window can be joined to one of its blocks within the
same window. This is the path chosen in the proof of GM01 (4.5), page 57. -/
theorem exists_path_in_blockAttachmentWindow {α β : Type*} {n : ℕ}
    {G : Graph α β} {S : Fin n → Set α} (hSG : ∀ i, S i ⊆ V(G))
    {l r : Fin n} (hlr : l ≤ r) {x : α}
    (hx : x ∈ blockAttachmentWindow G S l r) :
    ∃ i, l ≤ i ∧ i ≤ r ∧ ∃ s ∈ S i, ∃ P : Graph α β,
      IsGraphPathWithEnds G P x s ∧ V(P) ⊆ blockAttachmentWindow G S l r := by
  have hconst : ∀ i, x ∈ S i → ∃ P : Graph α β,
      IsGraphPathWithEnds G P x x ∧ V(P) ⊆ S i := by
    intro i hxi
    obtain ⟨P, hP, hV, _⟩ := exists_isGraphPathWithEnds_of_walk
      (GraphWalk.nil (hSG i hxi))
    refine ⟨P, hP, ?_⟩
    intro y hy
    have hyx : y = x := by simpa only [Set.mem_ofPred_eq, GraphWalk.support_nil, List.mem_singleton] using hV hy
    exact hyx ▸ hxi
  rcases hx with (hxl | hxi) | hxr
  · obtain ⟨P, hP, hV⟩ := hconst l hxl
    exact ⟨l, le_rfl, hlr, x, hxl, P, hP, fun _ h ↦ Or.inl (Or.inl (hV h))⟩
  · obtain ⟨i, hi, hxZ⟩ := Set.mem_iUnion₂.mp hxi
    obtain ⟨s, hs, P, hP, hV⟩ := exists_path_in_blockAttachmentRegion hxZ
    exact ⟨i, hi.1.le, hi.2.le, s, hs, P, hP,
      fun _ h ↦ Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hV h⟩))⟩
  · obtain ⟨P, hP, hV⟩ := hconst r hxr
    exact ⟨r, hlr, le_rfl, x, hxr, P, hP, fun _ h ↦ Or.inr (hV h)⟩

end GraphMinor.GM01
