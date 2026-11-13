module

public import GraphMinor.GM01.PathIndexIntervals
public import GraphMinor.GM01.Defs
import GraphMinor.GM01.Basic

/-!
# Splitting a covering path at its ordered attachments

In the page-60 contraction of Graph Minors I, order the selected
attachment vertices along the root-to-leaf path. Start a new spine
piece at each attachment after the first. The first piece also
contains the path root. The pieces are disjoint index intervals,
so they are connected and consecutive pieces have a joining edge.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- Ordered marked vertices on a simple path give actual disjoint
connected spine pieces, with their root, marked vertices, and joining
edges, for the comb contraction on GM01 page 60. -/
theorem exists_spine_pieces_of_ordered_path_vertices {α β : Type*} {N δ : ℕ}
    (hδ : 0 < δ) (G : Graph α β) (v : Fin N → α) (hv : Injective v)
    (hV : ∀ i, v i ∈ V(G))
    (hAdj : ∀ i j, j.val = i.val + 1 → G.Adj (v i) (v j))
    (t : Fin δ → Fin N) (ht : StrictMono t) :
    ∃ C : Fin δ → Set α,
      (∀ i, C i ⊆ range v) ∧ (∀ i, C i ⊆ V(G)) ∧
      (∀ i, GraphConnected (G.induce (C i))) ∧
      (Pairwise fun i j ↦ Disjoint (C i) (C j)) ∧
      v ⟨0, Nat.zero_lt_of_lt (t ⟨0,hδ⟩).isLt⟩ ∈ C ⟨0,hδ⟩ ∧
      (∀ i, v (t i) ∈ C i) ∧
      (∀ i j, (pathGraph δ).Adj i j →
        ∃ e x, x ∈ C i ∧ ∃ y, y ∈ C j ∧ G.IsLink e x y) := by
  have hN : 0 < N := Nat.zero_lt_of_lt (t ⟨0,hδ⟩).isLt
  let lo : Fin δ → Fin N := fun i ↦ if i.val = 0 then ⟨0,hN⟩ else t i
  let hi : Fin δ → Fin N := fun i ↦ if hn : i.val + 1 < δ then
    ⟨(t ⟨i.val + 1,hn⟩).val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) (t _).isLt⟩
    else ⟨N - 1, by omega⟩
  have hLo : ∀ i, lo i ≤ t i := by
    intro i
    by_cases h : i.val = 0
    · simp only [lo,h,↓reduceIte]
      exact Nat.zero_le _
    · simp only [lo,h,↓reduceIte]
      exact le_rfl
  have hHi : ∀ i, t i ≤ hi i := by
    intro i
    by_cases hn : i.val + 1 < δ
    · have hlt := ht (show i < (⟨i.val + 1,hn⟩ : Fin δ) from Nat.lt_succ_self _)
      change (t i).val ≤ (hi i).val
      simp only [hi,hn,↓reduceDIte]
      change (t i).val < (t ⟨i.val + 1,hn⟩).val at hlt
      omega
    · change (t i).val ≤ (hi i).val
      simp only [hi,hn,↓reduceDIte]
      exact Nat.le_sub_one_of_lt (t i).isLt
  have hGap : ∀ i j, i < j → hi i < lo j := by
    intro i j hij
    have hnext : i.val + 1 < δ := Nat.lt_of_le_of_lt hij j.isLt
    have hnextj : (⟨i.val + 1,hnext⟩ : Fin δ) ≤ j := hij
    have hle := ht.monotone hnextj
    have hj0 : j.val ≠ 0 := by have := i.isLt; change i.val < j.val at hij; omega
    change (hi i).val < (lo j).val
    simp only [hi,hnext,↓reduceDIte,lo,hj0,↓reduceIte]
    have hpositive : 0 < (t ⟨i.val + 1,hnext⟩).val :=
      Nat.zero_lt_of_lt (ht (show i < (⟨i.val + 1,hnext⟩ : Fin δ) from Nat.lt_succ_self _))
    exact Nat.lt_of_lt_of_le (Nat.sub_lt hpositive (by decide)) hle
  let C := fun i ↦ v '' Icc (lo i) (hi i)
  have hCsub : ∀ i, C i ⊆ range v := fun _ _ hx ↦ image_subset_range _ _ hx
  have hCD : Pairwise fun i j ↦ Disjoint (C i) (C j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro x ⟨a,ha,hax⟩ ⟨b,hb,hbx⟩
    have hab := hv (hax.trans hbx.symm)
    subst b
    rcases lt_or_gt_of_ne hij with h | h
    · exact (not_lt_of_ge (hb.1.trans ha.2)) (hGap i j h)
    · exact (not_lt_of_ge (ha.1.trans hb.2)) (hGap j i h)
  have hForward : ∀ i j, i.val + 1 = j.val →
      ∃ e x, x ∈ C i ∧ ∃ y, y ∈ C j ∧ G.IsLink e x y := by
    intro i j hij
    have hj0 : j.val ≠ 0 := by omega
    have hnext : i.val + 1 < δ := hij ▸ j.isLt
    have hnextj : (⟨i.val + 1,hnext⟩ : Fin δ) = j := Fin.ext hij
    have htj : 0 < (t j).val := Nat.zero_lt_of_lt (ht (show i < j from by change i.val < j.val; omega))
    have hConsecutive : (lo j).val = (hi i).val + 1 := by
      simp only [lo,hj0,↓reduceIte,hi,hnext,↓reduceDIte,hnextj]
      omega
    obtain ⟨e,he⟩ := hAdj (hi i) (lo j) hConsecutive
    exact ⟨e,v (hi i),⟨hi i,⟨(hLo i).trans (hHi i),le_rfl⟩,rfl⟩,
      v (lo j),⟨lo j,⟨le_rfl,(hLo j).trans (hHi j)⟩,rfl⟩,he⟩
  refine ⟨C,hCsub,?_,?_,hCD,?_,?_,?_⟩
  · rintro i x ⟨j,_,rfl⟩
    exact hV j
  · intro i
    exact graphConnected_induce_index_interval v hAdj (lo i) (hi i) ((hLo i).trans (hHi i))
  · have hLoZero : lo ⟨0,hδ⟩ = ⟨0,hN⟩ := by simp only [lo,↓reduceIte]
    exact ⟨lo ⟨0,hδ⟩,⟨le_rfl,(hLo _).trans (hHi _)⟩, congrArg v hLoZero⟩
  · intro i
    exact ⟨t i,⟨hLo i,hHi i⟩,rfl⟩
  · intro i j hij
    rcases pathGraph_adj.mp hij with h | h
    · exact hForward i j h
    · obtain ⟨e,x,hx,y,hy,he⟩ := hForward j i h
      exact ⟨e,y,hy,x,hx,he.symm⟩

end GraphMinor.GM01
