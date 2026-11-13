module

public import GraphMinor.GM01.SubdivisionSupport
public import GraphMinor.GM01.CombShifts
public import GraphMinor.GM01.CombSpineCuts

/-!
# Segments and ends of a subdivided comb

Graph Minors I, page 58, defines the first end of `D` using its first
two cells and the path joining them, and defines the second end using
the last two cells. We select these supports by the consecutive-comb
embedding. The spine index of a shifted vertex records its interval,
so nonoverlapping intervals select disjoint source vertices and hence
disjoint subdivision supports.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- A consecutive segment of a subdivided comb, including all its
binary copies and all replacing paths of its internal source edges.
The two ends on page 58 of Graph Minors I are segments of length two. -/
def combSegmentSupport {α β : Type*} {γ L m : ℕ}
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (offset : ℕ) (hbound : offset + m ≤ L) : Set α :=
  subdivisionEmbeddingSupport (combShiftEmbedding offset hbound)
    (combShiftEmbedding_adj offset hbound) c P

/-- The spine index of a shifted source vertex shifts by the same
amount, including vertices in attached binary copies. -/
theorem combShiftEmbedding_spineIndex {γ L m : ℕ} (offset : ℕ) (hbound : offset + m ≤ L)
    (v : (pathComb γ m).verts) :
    (pathCombSpineIndex (combShiftEmbedding offset hbound v).val).val =
      offset + (pathCombSpineIndex v.val).val := by
  obtain ⟨v, hv⟩ := v
  cases v <;> rfl

/-- Nonoverlapping intervals select disjoint source vertices. -/
theorem disjoint_combShiftEmbedding_ranges {γ L m m' : ℕ} (offset offset' : ℕ)
    (hbound : offset + m ≤ L) (hbound' : offset' + m' ≤ L) (hgap : offset + m ≤ offset') :
    Disjoint (range (combShiftEmbedding (γ := γ) offset hbound))
      (range (combShiftEmbedding (γ := γ) offset' hbound')) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨v, hv⟩ ⟨w, hw⟩
  have heq := congrArg (fun z : (pathComb γ L).verts ↦ (pathCombSpineIndex z.val).val)
    (hv.trans hw.symm)
  rw [combShiftEmbedding_spineIndex, combShiftEmbedding_spineIndex] at heq
  have hvBound := (pathCombSpineIndex v.val).isLt
  omega

/-- Nonoverlapping consecutive comb segments have disjoint supports
in the represented subdivision. -/
theorem disjoint_combSegmentSupports {α β : Type*} {γ L m m' : ℕ}
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (offset offset' : ℕ) (hbound : offset + m ≤ L) (hbound' : offset' + m' ≤ L)
    (hgap : offset + m ≤ offset') :
    Disjoint (combSegmentSupport c P offset hbound) (combSegmentSupport c P offset' hbound') := by
  exact disjoint_subdivisionEmbeddingSupports _ _ _ _
    (disjoint_combShiftEmbedding_ranges offset offset' hbound hbound' hgap) hc P hRanges hInter

/-- The first end of `D` as defined before GM01 (4.9), page 58. -/
def combFirstEndSupport {α β : Type*} {γ L : ℕ} (hL : 2 ≤ L)
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β) : Set α :=
  combSegmentSupport c P 0 (by omega : 0 + 2 ≤ L)

/-- The second end of `D` as defined before GM01 (4.9), page 58. -/
def combSecondEndSupport {α β : Type*} {γ L : ℕ} (hL : 2 ≤ L)
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β) : Set α :=
  combSegmentSupport c P (L - 2) (by omega : L - 2 + 2 ≤ L)

/-- The two ends used in GM01 (4.9) and (4.13) are disjoint when the
comb has at least four cells, including a path comb of height zero. -/
theorem disjoint_comb_ends {α β : Type*} {γ L : ℕ} (hL : 4 ≤ L)
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c) :
    Disjoint (combFirstEndSupport (by omega) c P) (combSecondEndSupport (by omega) c P) := by
  exact disjoint_combSegmentSupports hc P hRanges hInter 0 (L - 2) _ _ (by omega)

end GraphMinor.GM01
