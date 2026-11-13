module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM08.Section18ClosedSchism
import GraphMinor.GM08.Section18Orient
import GraphMinor.GM07.Section9CoreProved

/-!
# VIII (18.1) for graft drawings on a closed surface

Orient the drawings and apply VII (9.2), the closed-surface form of VII
(9.1). A large value of alpha gives a simulation of the abstract grafts.
Otherwise a normal schism attains alpha and has the required bounded size.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- The closed-surface case of Graph Minors VIII (18.1), pages 285–286,
for drawings of abstract grafts. A model of the closed surface is supplied
explicitly. The cuff alternatives are empty in this case. -/
theorem Proofs.theorem_18_1_closed {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (a b : ℕ) (hab : 1 ≤ a + b)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) {α : Type u} {β : Type v}
    (Y : Graft α β) (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      ∃ F : Set S, GM07.IsSchism F ∧ DX.drawing.IsNormal F ∧
        (DX.drawing.V ∩ F).ncard ≤ N := by
  obtain ⟨H, hH⟩ := exists_surfaceDigraph_for_surface_reduction DY.drawing
  obtain ⟨N, hN⟩ := GM07.theorem_9_2_proof hS.isSurface a b hab he H
  refine ⟨N, fun X DX => ?_⟩
  obtain ⟨G, hG⟩ := exists_surfaceDigraph_for_surface_reduction DX.drawing
  by_cases hlarge : N ≤ GM07.alpha G.G
  · exact Or.inl (isGraftSimulatedIn_of_drawn_boundaryRootedMinor DY DX hH hG (hN G hlarge).2)
  · obtain ⟨F, hF, hnF, hcount⟩ := exists_normal_schism_at_alpha_of_closed hS hns G.G
    refine Or.inr ⟨F, hF, ?_, ?_⟩
    · simpa only [hG] using hnF
    · rw [← hG, inter_comm, hcount]
      exact Nat.le_of_lt (Nat.lt_of_not_ge hlarge)

end GraphMinor.GM08
