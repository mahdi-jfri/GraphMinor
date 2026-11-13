module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Minor
import GraphMinor.GM08.Section4
import GraphMinor.GM08.Section11Transport

/-!
# Pulling boundary-rooted minors back to abstract grafts

The isomorphism in a graft drawing identifies its roots with the boundary
vertices. Simulations of the drawn graphs can therefore be pulled back to
the abstract graphs, preserving the root condition. This completes the
minor-to-simulation conversion used in VIII (18.1).
-/

public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- A graft drawing identifies the roots with the boundary vertices. -/
theorem ncard_roots_eq_boundary_vertices {S : Type w} [TopologicalSpace S] [T1Space S]
    {α : Type u} {β : Type v} {X : Graft α β} (D : GraftDrawing X.G X.T S) :
    X.T.ncard = (D.drawing.V ∩ bd S).ncard := by
  let f : X.T ≃ ↑(D.drawing.V ∩ bd S) := {
    toFun := fun x => ⟨(D.iso.vertexEquiv ⟨x.1, X.T_subset x.2⟩).1,
      (D.iso.vertexEquiv ⟨x.1, X.T_subset x.2⟩).2,
      (D.mem_bd_iff x.1 (X.T_subset x.2)).mpr x.2⟩
    invFun := fun z => ⟨(D.iso.vertexEquiv.symm ⟨z.1, z.2.1⟩).1,
      (D.mem_bd_iff _ (D.iso.vertexEquiv.symm ⟨z.1, z.2.1⟩).2).mp (by
        change (D.iso.vertexEquiv (D.iso.vertexEquiv.symm ⟨z.1, z.2.1⟩)).1 ∈ bd S
        rw [D.iso.vertexEquiv.apply_symm_apply]
        exact z.2.2)⟩
    left_inv := fun x => by
      apply Subtype.ext
      change (D.iso.vertexEquiv.symm (D.iso.vertexEquiv ⟨x.1, X.T_subset x.2⟩)).1 = x.1
      rw [D.iso.vertexEquiv.symm_apply_apply]
    right_inv := fun z => by
      apply Subtype.ext
      change (D.iso.vertexEquiv (D.iso.vertexEquiv.symm ⟨z.1, z.2.1⟩)).1 = z.1
      rw [D.iso.vertexEquiv.apply_symm_apply] }
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr f

/-- A graft drawing preserves the number of vertices. -/
theorem ncard_drawing_vertices_eq {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {X : Graft α β} (D : GraftDrawing X.G X.T S) :
    D.drawing.V.ncard = V(X.G).ncard := by
  change V(D.drawing.toGraph).ncard = V(X.G).ncard
  simpa only [Nat.card_coe_set_eq] using (Nat.card_congr D.iso.vertexEquiv).symm

/-- A graft drawing preserves the number of edges. -/
theorem ncard_drawing_edges_eq {S : Type w} [TopologicalSpace S]
    {α : Type u} {β : Type v} {X : Graft α β} (D : GraftDrawing X.G X.T S) :
    D.drawing.E.ncard = E(X.G).ncard := by
  change E(D.drawing.toGraph).ncard = E(X.G).ncard
  simpa only [Nat.card_coe_set_eq] using (Nat.card_congr D.iso.edgeEquiv).symm

/-- A boundary-rooted minor between drawings of grafts gives a simulation
of the abstract grafts, as required in VIII (18.1). Both grafts use the same
ambient vertex and edge types, so the unused edges can retain their labels. -/
theorem isGraftSimulatedIn_of_drawn_boundaryRootedMinor {S : Type w}
    [TopologicalSpace S] [T1Space S] [Nonempty S]
    {α : Type u} {β : Type v} {Y X : Graft α β}
    (DY : GraftDrawing Y.G Y.T S) (DX : GraftDrawing X.G X.T S)
    {H G : GM07.SurfaceDigraph S} (hH : H.G = DY.drawing) (hG : G.G = DX.drawing)
    (hminor : GM07.IsBoundaryRootedMinor H G) : IsGraftSimulatedIn Y X := by
  classical
  obtain ⟨ηv, ηe, hm, hroot⟩ := isGraphSimulatedIn_of_boundaryRootedMinor hminor
  have hm' : IsGraphSimulation DY.drawing.toGraph DX.drawing.toGraph ηv ηe := by
    simpa only [hH, hG] using hm
  have hm₁ := isGraphSimulation_comp DY.iso.isGraphBij.isMinorModel hm'
  have hm₂ := hm₁.pullHost DX.iso.isGraphBij id
  refine ⟨_, _, hm₂, ?_, ?_⟩
  · rw [ncard_roots_eq_boundary_vertices DX, ncard_roots_eq_boundary_vertices DY]
    exact congrArg Set.ncard (by simpa only [hH, hG] using hminor.1.symm)
  · intro y hy
    let z : V(DY.drawing.toGraph) := DY.iso.vertexEquiv ⟨y, Y.T_subset hy⟩
    have hzbd : z.1 ∈ H.G.V ∩ bd S := by
      rw [hH]
      exact ⟨z.2, (DY.mem_bd_iff y (Y.T_subset hy)).mpr hy⟩
    have hzG : z.1 ∈ V(DX.drawing.toGraph) := by
      change z.1 ∈ DX.drawing.V
      have hz := hminor.1.subset hzbd
      simpa only [hG] using hz.1
    let x : V(X.G) := DX.iso.vertexEquiv.symm ⟨z.1, hzG⟩
    have hxz : DX.iso.fv x.1 = z.1 := by
      rw [DX.iso.fv_of_mem x.2]
      exact congrArg Subtype.val (DX.iso.vertexEquiv.apply_symm_apply ⟨z.1, hzG⟩)
    have hyz : DY.iso.fv y = z.1 := DY.iso.fv_of_mem (Y.T_subset hy)
    refine ⟨x.1, ?_, (DX.mem_bd_iff x.1 x.2).mp ?_⟩
    · change x.1 ∈ V(X.G) ∧ DX.iso.fv x.1 ∈ ⋃ z' ∈ {DY.iso.fv y}, ηv z'
      rw [hxz, hyz]
      exact ⟨x.2, mem_biUnion (mem_singleton _) (hroot z.1 hzbd)⟩
    · change (DX.iso.vertexEquiv x).1 ∈ bd S
      rw [← DX.iso.fv_of_mem x.2, hxz]
      exact hzbd.2

end GraphMinor.GM08
