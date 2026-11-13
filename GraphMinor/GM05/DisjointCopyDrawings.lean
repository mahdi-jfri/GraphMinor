module

public import GraphMinor.GM05.GraphCopies
public import GraphMinor.Surface.Defs
import GraphMinor.GM05.CopySubgraphs
import GraphMinor.GM05.DrawingDisjointness
import GraphMinor.GM09.DiscDrawing
import GraphMinor.Planar.Defs

/-!
# Drawing the individual disjoint copies

Restrict a drawing of the copy graph to each tagged copy, then rename
its vertices and edges by the tagging isomorphism. Different copies
have disjoint geometric vertex sets because the original drawing's
vertex map is injective. Their full supports are therefore disjoint.
This is the last copy-drawing step used in GM V, (8.14).
-/

public section
namespace GraphMinor.GM05
open Set Graph Surface
universe u v w

/-- A drawing of disjoint graph copies gives pairwise disjoint graph
drawings of the original graph. -/
theorem disjoint_drawings_of_graphCopies {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S] [T1Space S] {H : Graph α β} {k : ℕ}
    (Γ : GraphDrawing (graphCopies k H) S) :
    ∃ Δ : Fin k → GraphDrawing H S,Pairwise (fun i j ↦ Disjoint (Δ i).drawing.U (Δ j).drawing.U) := by
  classical
  choose A hA hVA hEA hIso using exists_single_copy_subgraph k H
  let φ (i : Fin k) : Iso H (A i) := (hIso i).some
  have hex : ∀ i,∃ Γi : GraphDrawing (A i) S,Γi.drawing.IsSubdrawing Γ.drawing ∧
      ∀ v : V(A i),(Γi.iso.vertexEquiv v).val=
        (Γ.iso.vertexEquiv ⟨v.val,(hA i).vertexSet_mono v.prop⟩).val := by
    intro i
    obtain ⟨Γi,-,-,hsub,hmap,-,-,-⟩ := GM09.GraphDrawing.ofSubgraph Γ (hA i)
    exact ⟨Γi,hsub,hmap⟩
  choose Γi hΓsub hΓmap using hex
  let Δ : Fin k → GraphDrawing H S := fun i ↦ GraphDrawing.ofIso (φ i) (Γi i)
  refine ⟨Δ,?_⟩
  intro i j hij
  change Disjoint (Γi i).drawing.U (Γi j).drawing.U
  apply subdrawings_disjoint_of_vertices (hΓsub i) (hΓsub j)
  apply disjoint_left.mpr
  intro z hzi hzj
  let x := (Γi i).iso.vertexEquiv.symm ⟨z,hzi⟩
  let y := (Γi j).iso.vertexEquiv.symm ⟨z,hzj⟩
  have hxi : (Γ.iso.vertexEquiv ⟨x.val,(hA i).vertexSet_mono x.prop⟩).val=z :=
    (hΓmap i x).symm.trans (congrArg Subtype.val ((Γi i).iso.vertexEquiv.apply_symm_apply ⟨z,hzi⟩))
  have hyj : (Γ.iso.vertexEquiv ⟨y.val,(hA j).vertexSet_mono y.prop⟩).val=z :=
    (hΓmap j y).symm.trans (congrArg Subtype.val ((Γi j).iso.vertexEquiv.apply_symm_apply ⟨z,hzj⟩))
  have hxy := Γ.iso.vertexEquiv.injective (Subtype.ext (hxi.trans hyj.symm))
  have htags : x.val.1=y.val.1 := congrArg (fun v : V(graphCopies k H) ↦ v.val.1) hxy
  have hx : x.val∈{i}×ˢV(H) := by simpa only [hVA i] using x.prop
  have hy : y.val∈{j}×ˢV(H) := by simpa only [hVA j] using y.prop
  exact hij (hx.1.symm.trans (htags.trans hy.1))

end GraphMinor.GM05
