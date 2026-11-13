module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM08.Section18Orient
import GraphMinor.GM07.Section9CoreProved

/-!
# A threshold independent of boundary positions

In VIII (18.1), the target drawing is moved to align its boundary vertices
with the host. VII (9.1) uses only the target's edge count, boundary vertex
count and internal isolated vertex count. Bound the last count by its
vertex count. The resulting threshold depends on the abstract target graft
and the surface, so the boundary alignment does not change it.
-/

public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- A single threshold works for every drawing of a fixed target graft on
the model surface, once the boundary vertices are aligned. This discharges
the uniform numerical choice needed in VIII (18.1), page 285. -/
theorem exists_uniform_simulation_threshold {S : Type w}
    [TopologicalSpace S] [T1Space S] [Nonempty S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {α : Type u} {β : Type v} (Y : Graft α β) :
    ∃ N : ℕ, ∀ (DY : GraftDrawing Y.G Y.T S) (X : Graft α β)
      (DX : GraftDrawing X.G X.T S) (G : GM07.SurfaceDigraph S),
      G.G = DX.drawing → DX.drawing.V ∩ bd S = DY.drawing.V ∩ bd S →
      GM07.IsBoundaryLinked DX.drawing → N ≤ GM07.alpha DX.drawing →
      IsGraftSimulatedIn Y X := by
  let k := 4 * E(Y.G).ncard + 4 * V(Y.G).ncard + Y.index + 2 * c + 2
  let c₀ := c + E(Y.G).ncard + V(Y.G).ncard + 1
  let N := 42 * k * 5 ^ (V(Y.G).ncard + E(Y.G).ncard) * GM07.vModel a b c₀ k
  refine ⟨N, ?_⟩
  intro DY X DX G hG hbd hBL hα
  obtain ⟨H, hH⟩ := exists_surfaceDigraph_for_surface_reduction DY.drawing
  have hE : H.G.E.ncard = E(Y.G).ncard := by
    rw [hH]
    exact ncard_drawing_edges_eq DY
  have hV : H.G.V.ncard = V(Y.G).ncard := by
    rw [hH]
    exact ncard_drawing_vertices_eq DY
  have hg : GM07.numInternalIsolatedVertices H.G ≤ V(Y.G).ncard := by
    rw [← hV]
    exact ncard_le_ncard (fun _ hx => hx.1.1) H.G.finite_V
  have hb : (H.G.V ∩ bd S).ncard = Y.index := by
    rw [hH]
    exact (ncard_roots_eq_boundary_vertices DY).symm
  have hpow : 5 ^ (GM07.numInternalIsolatedVertices H.G + H.G.E.ncard) ≤
      5 ^ (V(Y.G).ncard + E(Y.G).ncard) :=
    pow_le_pow_right₀ (by decide) (by omega)
  have hbound : 42 * k * 5 ^ (GM07.numInternalIsolatedVertices H.G + H.G.E.ncard) *
      GM07.vModel a b c₀ k ≤ N :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hpow)
  have hk : 2 * k ≥ 4 * H.G.E.ncard + 4 * GM07.numInternalIsolatedVertices H.G +
      (H.G.V ∩ bd S).ncard + 2 * c + 2 := by
    rw [hE, hb]
    dsimp only [k]
    omega
  have hc₀ : c₀ ≥ c + H.G.E.ncard + GM07.numInternalIsolatedVertices H.G + 1 := by
    rw [hE]
    dsimp only [c₀]
    omega
  have hHproper : H.IsProper := by
    change H.G.IsProper
    rw [hH]
    exact DY.isProper
  have hGproper : G.IsProper := by
    change G.G.IsProper
    rw [hG]
    exact DX.isProper
  have hbd' : G.G.V ∩ bd S = H.G.V ∩ bd S := by rw [hG, hH]; exact hbd
  have hBL' : GM07.IsBoundaryLinked G.G := by rw [hG]; exact hBL
  have hα' : 42 * k * 5 ^ (GM07.numInternalIsolatedVertices H.G + H.G.E.ncard) *
      GM07.vModel a b c₀ k ≤ GM07.alpha G.G := by
    rw [hG]
    exact hbound.trans hα
  have hminor := GM07.theorem_9_1_proof hS a b c h3 he H hHproper k c₀ hk hc₀ G hGproper hbd' hBL' hα'
  exact isGraftSimulatedIn_of_drawn_boundaryRootedMinor DY DX hH hG hminor

end GraphMinor.GM08
