module

public import GraphMinor.GM01.CombShifts
public import GraphMinor.GM01.CombSpineCuts
public import GraphMinor.GM01.SelectedBoundaryPath
import Lean.Elab.Tactic.Omega

/-!
# The boundary attachment into the skipped cells

The skipped two-cell source in Graph Minors I, (4.1), page 55, begins
just after an earlier spine cut. The replacing path of the edge from
that cut to the first retained spine vertex meets the selected support
only at the first centre. Its earlier source end is outside the shifted
source, so the proved boundary-intersection lemma applies.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The boundary path from the preceding spine centre attaches to the
two-cell subdivision only at its first centre. This is the second arm
attachment used in the contraction of GM01 (4.1), page 55. -/
theorem exists_comb_boundary_attachment {α β : Type*} {γ L : ℕ}
    {N : Graph α β} {c : (pathComb γ L).verts → α} (hc : Injective c)
    (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (offset : ℕ) (hpos : 0 < offset) (hbound : offset + 2 ≤ L) :
    ∃ boundary : (pathComb γ L).coe.edgeSet,
      boundary.val = s(
        (⟨Sum.inl ⟨offset - 1, by omega⟩, pathComb_spine_mem γ L _⟩ : (pathComb γ L).verts),
        combShiftEmbedding offset hbound (rootedPathComb γ 2 (by decide)).root) ∧
      IsGraphPathWithEnds N (P boundary)
        (c ⟨Sum.inl ⟨offset - 1, by omega⟩, pathComb_spine_mem γ L _⟩)
        (c (combShiftEmbedding offset hbound (rootedPathComb γ 2 (by decide)).root)) ∧
      V(P boundary) ∩ (range (fun v : (pathComb γ 2).verts ↦ c (combShiftEmbedding offset hbound v)) ∪
        ⋃ e : (pathComb γ 2).coe.edgeSet, V(P (combShiftEdges offset hbound e))) =
        {c (combShiftEmbedding offset hbound (rootedPathComb γ 2 (by decide)).root)} := by
  let f := combShiftEmbedding (γ := γ) offset hbound
  have hf : ∀ {a b : (pathComb γ 2).verts}, (pathComb γ 2).coe.Adj a b →
      (pathComb γ L).coe.Adj (f a) (f b) := combShiftEmbedding_adj offset hbound
  let root := (rootedPathComb γ 2 (by decide)).root
  let a : (pathComb γ L).verts := ⟨Sum.inl ⟨offset - 1, by omega⟩, pathComb_spine_mem γ L _⟩
  have ha : a ∉ range f := by
    rintro ⟨v, hv⟩
    have hval := congrArg (fun z : (pathComb γ L).verts ↦ (pathCombSpineIndex z.val).val) hv
    have hindex : (pathCombSpineIndex (f v).val).val = offset + (pathCombSpineIndex v.val).val := by
      obtain ⟨v, hv⟩ := v
      cases v <;> rfl
    change (pathCombSpineIndex (f v).val).val = offset - 1 at hval
    rw [hindex] at hval
    omega
  have hadj : (pathComb γ L).coe.Adj a (f root) := by
    apply pathComb_spine_adj (γ := γ)
    apply pathGraph_adj.mpr
    exact Or.inl (by change offset - 1 + 1 = offset + 0; omega)
  let boundary : (pathComb γ L).coe.edgeSet := ⟨s(a,f root), hadj⟩
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  obtain ⟨a', b', he, hP, _⟩ := hPaths boundary
  have hpair : s(a,f root) = s(a',b') := he
  have hPath : IsGraphPathWithEnds N (P boundary) (c a) (c (f root)) := by
    rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hP
    · exact hP.symm
  exact ⟨boundary, rfl, hPath,
    selected_subdivision_boundary_intersection f hf hc P hRanges hInter root a ha boundary rfl⟩

end GraphMinor.GM01
