module

public import GraphMinor.GM06.Alg57CurrentCutCopyUnique

/-!
# Injective vertex labels on the selected cut face

In VI (5.7), page 133, copied vertex slots project to the actual
vertices of the current drawing. Projection is injective among the
slots visited by a selected face when there are at least two paths:
old live labels are injective, and that face cannot visit both
copies of a single old vertex.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

namespace GM06CurrentDrawingRep
variable {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
  {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L)
include rep

/-- Project a bounded copied vertex slot to its actual old point. -/
@[expose] def cutVertexPoint (v : Fin (2 * x.vertexCount)) : ClosedCylinder :=
  rep.vertex ⟨v.val / 2, by have hv := v.isLt; omega⟩

/-- The actual points of two vertex slots visited by the selected
cut face are equal only when those copied slots are equal. -/
theorem cut_iterate_vertex_inj (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (i : Fin k) (n₁ n₂ : ℕ) (u w : Fin (2 * x.vertexCount))
    (hu : (dartMatePerm.trans (gm06RotationPermutation (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations)).symm)^[n₁]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∈
      (gm06SplitRotationRows (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
        x.linkage x.innerCuff x.outerCuff) x.rotations).getD u.val [])
    (hw : (dartMatePerm.trans (gm06RotationPermutation (gm06SplitRotationRows
      (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints x.linkage
        x.innerCuff x.outerCuff) x.rotations)).symm)^[n₂]
      (gm06CutDart (2 * (rep.tagged.length + i.val) + 1) 0) ∈
      (gm06SplitRotationRows (gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
        x.linkage x.innerCuff x.outerCuff) x.rotations).getD w.val [])
    (hpoint : rep.cutVertexPoint u = rep.cutVertexPoint w) : u = w := by
  let a : Fin x.vertexCount := ⟨u.val / 2, by have hh := u.isLt; omega⟩
  let b : Fin x.vertexCount := ⟨w.val / 2, by have hh := w.isLt; omega⟩
  have ha : a ∈ rep.live := rep.live_of_mem_row
    (splitRows_project_mem _ x.rotations u.val _ hu)
  have hb : b ∈ rep.live := rep.live_of_mem_row
    (splitRows_project_mem _ x.rotations w.val _ hw)
  have hab : a = b := rep.vertex_inj ha hb hpoint
  have hhalf : u.val / 2 = w.val / 2 := congrArg Fin.val hab
  by_contra hne
  have hneval : u.val ≠ w.val := fun h => hne (Fin.ext h)
  have hcases :
      (u.val = gm06CutVertex a.val true ∧ w.val = gm06CutVertex a.val false) ∨
      (w.val = gm06CutVertex a.val true ∧ u.val = gm06CutVertex a.val false) := by
    simp only [gm06CutVertex, Bool.not_true, Bool.not_false, Bool.toNat_false,
      Bool.toNat_true, Nat.add_zero]
    dsimp only [a]
    omega
  rcases hcases with ⟨heu, hew⟩ | ⟨hew, heu⟩
  · exact rep.cut_iterates_not_both_copies hk hG i n₁ n₂ a (heu ▸ hu) (hew ▸ hw)
  · exact rep.cut_iterates_not_both_copies hk hG i n₂ n₁ a (hew ▸ hw) (heu ▸ hu)

end GM06CurrentDrawingRep
end GraphMinor.GM06
