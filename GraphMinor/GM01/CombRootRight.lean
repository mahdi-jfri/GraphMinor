module

public import GraphMinor.GM01.CombShifts
public import GraphMinor.GM01.CombCells
import GraphMinor.GM01.RootedPathAttachment
import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.Basic

/-!
# A rooted subcomb to the right of an arbitrary root

For the tail in Graph Minors I, (4.1), page 55, suppose enough spine
vertices remain to the right of the cell containing the target root.
Embed a consecutive subcomb there. Within the unused root cell, join
the target root to its spine vertex and then the first retained spine
vertex. This path avoids every retained branch except its root branch,
so adjoining it gives the required rooted comb.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph GraphMinor.GM09

/-- A long enough right-hand interval supplies a rooted subcomb from
any vertex in the preceding cell. The root path stays in that cell
until its final edge to the retained interval. -/
theorem rootedPathComb_to_right {γ m N : ℕ} (hm : 0 < m)
    (v : (pathComb γ N).verts)
    (hbound : (pathCombSpineIndex v.val).val + 1 + m ≤ N) :
    HasRootedMinor (rootedPathComb γ m hm)
      (⟨toGraph (pathComb γ N), v⟩ : RootedGraph (PathCombVertex N) (Sym2 (PathCombVertex N))) := by
  let r := pathCombSpineIndex v.val
  let offset := r.val + 1
  let M := rootedCombShiftModel (γ := γ) hm offset hbound
  let target := combShiftVertex offset hbound (rootedPathComb γ m hm).root.val
  let C := combCell γ N r
  let U := C ∪ {target}
  let G := toGraph (pathComb γ N)
  have hvC : v.val ∈ C := ⟨v.property, rfl⟩
  have htarget : target ∈ V(G) := combShiftVertex_mem offset hbound
    (rootedPathComb γ m hm).root.property
  have hU : U ⊆ V(G) := by
    intro x hx
    rcases hx with hx | hx
    · exact hx.1
    · exact hx ▸ htarget
  have hCellU : G.induce C ≤ G.induce U := by
    refine ⟨subset_union_left, ?_⟩
    intro e x y he
    exact ⟨he.1, Or.inl he.2.1, Or.inl he.2.2⟩
  have hreach : Relation.ReflTransGen (G.induce U).Adj v.val (Sum.inl r) :=
    Relation.ReflTransGen.mono
      (fun _ _ h ↦ by obtain ⟨e, he⟩ := h; exact ⟨e, he.mono hCellU⟩)
      v.val (Sum.inl r) ((combCell_connected γ N r).2 v.val hvC
        (Sum.inl r) (combCell_spine_mem γ N r))
  have hedge : (G.induce U).Adj (Sum.inl r) target := by
    refine ⟨s(Sum.inl r,target), ⟨rfl, ?_⟩,
      Or.inl (combCell_spine_mem γ N r), Or.inr rfl⟩
    apply pathComb_spine_adj
    apply pathGraph_adj.mpr
    exact Or.inl (by change r.val + 1 = offset + 0; rfl)
  obtain ⟨R, hRU⟩ := exists_path_of_adj_reachable (Or.inl hvC)
    (hreach.trans (Relation.ReflTransGen.single hedge))
  have hR : IsGraphPathWithEnds G R v.val target := hRU.mono (G.induce_le hU)
  have hdisj : ∀ w : (pathComb γ m).verts, w ≠ (rootedPathComb γ m hm).root →
      Disjoint (M.branch w) V(R) := by
    intro w hw
    apply Set.disjoint_left.mpr
    intro x hx hxR
    rw [rootedCombShiftModel_branch] at hx
    have hxeq : x = combShiftVertex offset hbound w.val := hx
    subst x
    have hxU := hRU.le.vertexSet_mono hxR
    rcases hxU with hxC | hxTarget
    · have hindex := hxC.2
      have hval := congrArg Fin.val hindex
      have hshift : (pathCombSpineIndex (combShiftVertex offset hbound w.val)).val =
          offset + (pathCombSpineIndex w.val).val := by
        obtain ⟨word, hword⟩ := w
        cases word <;> rfl
      rw [hshift] at hval
      dsimp only [offset] at hval
      omega
    · have heq : combShiftVertex offset hbound w.val =
          combShiftVertex offset hbound (rootedPathComb γ m hm).root.val := hxTarget
      exact hw (Subtype.ext (combShiftVertex_injective offset hbound heq))
  let L := M.attachRootPathOfDisjointBranches le_rfl v.val hR hdisj
  exact ⟨L.mono (subgraphUnion_le le_rfl hR.le) rfl⟩

end GraphMinor.GM01
