module

public import GraphMinor.GM02.ListEdgeGraph

/-!
# Excluding cycles inside disjoint paths

A cycle graph lying in a disjoint union of path lists restricts to a cycle
graph on each list: an edge cannot leave that list, since the lists have
disjoint vertex sets. The leaf-removal result for one list makes every
such restriction empty. This is the uniqueness argument for the two
matchings in the counting proof of II (2.8).
-/

public section
namespace GraphMinor.GM02
open SimpleGraph Set Classical
universe u t

/-- A disjoint union of paths contains no nonempty graph of cycles. -/
theorem cycles_eq_bot_of_disjoint_list_cover {α : Type u} {I : Type t}
    {F D : SimpleGraph α} (P : I → List α) (hP : ∀ i, (P i).Nodup)
    (hdis : ∀ i j, i ≠ j → Disjoint {a | a ∈ P i} {a | a ∈ P j})
    (hcover : ∀ a b, F.Adj a b → ∃ i, (listEdgeGraph (P i)).Adj a b)
    (hDF : D ≤ F) (hc : D.IsCycles) : D = ⊥ := by
  have hstay : ∀ i a b, a ∈ P i → F.Adj a b → (listEdgeGraph (P i)).Adj a b := by
    intro i a b hai hab
    obtain ⟨j, hj⟩ := hcover a b hab
    have haj := (listEdgeGraph_adj_mem hj).1
    have heq : i = j := by
      by_contra hn
      exact Set.disjoint_left.1 (hdis i j hn) hai haj
    exact heq.symm ▸ hj
  have hempty : ∀ i, D ⊓ listEdgeGraph (P i) = ⊥ := by
    intro i
    apply isCycles_eq_bot_of_le_listEdgeGraph (hP i) (hle := inf_le_right)
    intro a ha
    obtain ⟨b, hab⟩ := ha
    have hai := (listEdgeGraph_adj_mem hab.2).1
    have hneigh : (D ⊓ listEdgeGraph (P i)).neighborSet a = D.neighborSet a := by
      ext x
      exact ⟨fun h => h.1, fun h => ⟨h, hstay i a x hai (hDF h)⟩⟩
    rw [hneigh]
    exact hc ⟨b, hab.1⟩
  apply le_bot_iff.1
  intro a b hab
  obtain ⟨i, hi⟩ := hcover a b (hDF hab)
  have h : (D ⊓ listEdgeGraph (P i)).Adj a b := ⟨hab, hi⟩
  rw [hempty i] at h
  exact h

end GraphMinor.GM02
