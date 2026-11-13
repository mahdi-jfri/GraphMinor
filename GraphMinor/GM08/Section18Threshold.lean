module

public import GraphMinor.GM08.Section18Minor
import GraphMinor.GM07.Section9CoreProved

/-!
# The threshold supplied by VII (9.1)

For a fixed proper digraph on a model surface, VII (9.1) supplies a bound
such that a boundary-linked digraph with the same boundary vertices and
larger alpha simulates the fixed graft. This is the numerical part of
VIII (18.1); aligning the boundary vertices and producing a small schism
are separate steps.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- The large-alpha alternative in the application of VII (9.1) to
VIII (18.1), page 285. Boundary vertices are already aligned here. -/
theorem exists_simulation_threshold_of_aligned_boundary {S : Type w}
    [TopologicalSpace S] [T1Space S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 * a + 3 * b + c ≥ 3)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (H : GM07.SurfaceDigraph S) (hH : H.IsProper) :
    ∃ N : ℕ, ∀ G : GM07.SurfaceDigraph S, G.IsProper →
      G.G.V ∩ bd S = H.G.V ∩ bd S → GM07.IsBoundaryLinked G.G →
      N ≤ GM07.alpha G.G → IsGraftSimulatedIn (boundaryGraft H.G) (boundaryGraft G.G) := by
  let k := 4 * H.G.E.ncard + 4 * GM07.numInternalIsolatedVertices H.G +
    (H.G.V ∩ bd S).ncard + 2 * c + 2
  let c₀ := c + H.G.E.ncard + GM07.numInternalIsolatedVertices H.G + 1
  refine ⟨42 * k * 5 ^ (GM07.numInternalIsolatedVertices H.G + H.G.E.ncard) *
    GM07.vModel a b c₀ k, ?_⟩
  intro G hG hbd hBL hα
  apply isGraftSimulatedIn_boundaryGraft_of_boundaryRootedMinor
  apply GM07.theorem_9_1_proof hS a b c h3 he H hH k c₀
  · dsimp only [k]
    omega
  · exact le_rfl
  · exact hG
  · exact hbd
  · exact hBL
  · exact hα

end GraphMinor.GM08
