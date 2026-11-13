module

public import GraphMinor.GM08.Section18Minor
import GraphMinor.GM08.Section18ClosedSchism
import GraphMinor.GM07.Section9CoreProved

/-!
# The closed-surface alternatives in VIII (18.1)

VII (9.1), in its closed-surface form (9.2), gives a boundary-rooted minor
when alpha is large. Otherwise a normal schism attains alpha. This proves
the two alternatives for the grafts represented by surface digraphs on a
closed non-sphere surface.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- The closed-surface case of VIII (18.1), pages 285–286, for the grafts
represented by surface digraphs. Cuff alternatives are absent because the
surface is closed. VII (9.2) is itself the closed-surface application of
VII (9.1) used by the paper. -/
theorem Proofs.theorem_18_1_closed_model {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (a b : ℕ) (hab : 1 ≤ a + b)
    (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) (H : GM07.SurfaceDigraph S) :
    ∃ N : ℕ, ∀ G : GM07.SurfaceDigraph S,
      IsGraftSimulatedIn (boundaryGraft H.G) (boundaryGraft G.G) ∨
      ∃ F : Set S, GM07.IsSchism F ∧ G.G.IsNormal F ∧ (G.G.V ∩ F).ncard ≤ N := by
  have : T2Space S := hS.2.1
  obtain ⟨N, hN⟩ := GM07.theorem_9_2_proof hS.isSurface a b hab he H
  refine ⟨N, fun G => ?_⟩
  by_cases hlarge : N ≤ GM07.alpha G.G
  · exact Or.inl (isGraftSimulatedIn_boundaryGraft_of_boundaryRootedMinor (hN G hlarge).2)
  · obtain ⟨F, hF, hnF, hcount⟩ := exists_normal_schism_at_alpha_of_closed hS hns G.G
    refine Or.inr ⟨F, hF, hnF, ?_⟩
    rw [inter_comm, hcount]
    exact Nat.le_of_lt (Nat.lt_of_not_ge hlarge)

end GraphMinor.GM08
