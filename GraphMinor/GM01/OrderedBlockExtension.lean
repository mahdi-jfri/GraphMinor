module

public import GraphMinor.GM01.BypassExtension
public import GraphMinor.GM01.RegionPartition
import Lean.Elab.Tactic.Omega

/-!
# Extending a block bypass to the final tail

Graph Minors I, (4.1), page 55, extends a clean bypass from block `i` to
the last block, avoiding all blocks before `i` and the next block.
For successive differences of nested regions, the region after the next
block avoids all those blocks. A later bypass end belongs to that region.
Its connectivity therefore permits the proved bypass extension.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function GraphMinor.GM09

/-- The ordered-block version of the path-extension step in GM01 (4.1).
All avoidance conditions are derived from the decreasing boundary regions
and the disjoint blocks. -/
theorem exists_ordered_block_extension {α β : Type*} {n : ℕ} {G H P : Graph α β}
    (hHG : H ≤ G) (F : ℕ → Set α) (hF : Antitone F) (hzero : F 0 = V(H))
    (i k : Fin n) (hik : i.val + 2 ≤ k.val) {a b t : α}
    (ha : a ∈ orderedRegionBlock F i) (hb : b ∈ orderedRegionBlock F k)
    (hP : IsGraphPathWithEnds G P a b) (hmeet : V(P) ∩ V(H) = {a,b})
    (hconn : GraphConnected (H.induce (F (i.val + 2)))) (ht : t ∈ F (i.val + 2)) :
    ∃ Q : Graph α β, IsGraphPathWithEnds G Q a t ∧
      Disjoint V(Q) ((⋃ j : Fin n, ⋃ (_ : j < i), orderedRegionBlock F j) ∪
        orderedRegionBlock F (⟨i.val + 1, by omega⟩ : Fin n)) := by
  let next : Fin n := ⟨i.val + 1, by omega⟩
  let X := (⋃ j : Fin n, ⋃ (_ : j < i), orderedRegionBlock F j) ∪ orderedRegionBlock F next
  have hsub : ∀ j : Fin n, orderedRegionBlock F j ⊆ V(H) := by
    intro j x hx
    rw [← hzero]
    exact hF (Nat.zero_le j.val) hx.1
  have hX : X ⊆ V(H) := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨j, hx⟩ := mem_iUnion.mp hx
      obtain ⟨_, hx⟩ := mem_iUnion.mp hx
      exact hsub j hx
    · exact hsub next hx
  have hdisj := orderedRegionBlock_pairwise_disjoint hF n
  have hnotX : ∀ j : Fin n, i.val ≤ j.val → j.val ≠ i.val + 1 →
      ∀ x ∈ orderedRegionBlock F j, x ∉ X := by
    intro j hij hjnext x hx hxX
    rcases hxX with hxX | hxX
    · obtain ⟨l, hxX⟩ := mem_iUnion.mp hxX
      obtain ⟨hli, hxX⟩ := mem_iUnion.mp hxX
      have hjl : j ≠ l := by intro heq; have := congrArg Fin.val heq; omega
      exact disjoint_left.mp (hdisj hjl) hx hxX
    · have hjn : j ≠ next := by intro heq; exact hjnext (congrArg Fin.val heq)
      exact disjoint_left.mp (hdisj hjn) hx hxX
  have haX : a ∉ X := hnotX i le_rfl (by omega) a ha
  have hbX : b ∉ X := hnotX k (by omega) (by omega) b hb
  have hTailSub : F (i.val + 2) ⊆ V(H) := by
    rw [← hzero]
    exact hF (Nat.zero_le _)
  have hTailG : H.induce (F (i.val + 2)) ≤ G := (H.induce_le hTailSub).trans hHG
  have hbTail : b ∈ F (i.val + 2) := hF hik hb.1
  have hTailX : Disjoint (F (i.val + 2)) X := by
    apply disjoint_left.mpr
    intro x hx hxX
    rcases hxX with hxX | hxX
    · obtain ⟨j, hxX⟩ := mem_iUnion.mp hxX
      obtain ⟨hji, hxX⟩ := mem_iUnion.mp hxX
      exact disjoint_left.mp
        (orderedRegionBlock_disjoint_later_region hF j (i.val + 2) (by omega)) hxX hx
    · exact disjoint_left.mp
        (orderedRegionBlock_disjoint_later_region hF next (i.val + 2) (by
          change i.val + 1 < i.val + 2
          omega)) hxX hx
  exact exists_bypass_extension hP hmeet hX haX hbX hTailG hconn hbTail ht hTailX

end GraphMinor.GM01
