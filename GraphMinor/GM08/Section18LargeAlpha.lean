module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18UniformThreshold
import GraphMinor.GM08.Section18Align
import GraphMinor.GM08.Section18Orient

/-!
# The large-alpha part of VIII (18.1)

Equal cuff counts let us move the target drawing so that its boundary
vertices agree with the host's. The uniform threshold then applies VII
(9.1). Consequently a host which does not simulate the target has unequal
cuff counts, a smaller surrounding circle, or small alpha. The schism
extraction still has to turn the last two cases into the printed alternatives.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- The large-alpha simulation step in VIII (18.1), page 285, with equal
counts on cuffs rather than already aligned boundary vertices. -/
theorem exists_simulation_threshold_of_cuff_counts {S : Type w}
    [TopologicalSpace S] [T1Space S] [Nonempty S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      (∀ C ∈ cuffs S, (DY.drawing.V ∩ C).ncard = (DX.drawing.V ∩ C).ncard) →
      GM07.IsBoundaryLinked DX.drawing → N ≤ GM07.alpha DX.drawing → IsGraftSimulatedIn Y X := by
  obtain ⟨N, hN⟩ := exists_uniform_simulation_threshold hS a b c h3 he Y
  refine ⟨N, fun X DX hcounts hBL hα => ?_⟩
  obtain ⟨DY', hbd⟩ := exists_graftDrawing_aligned_boundary hS DY DX hcounts
  obtain ⟨G, hG⟩ := exists_surfaceDigraph_for_surface_reduction DX.drawing
  exact hN DY' X DX G hG hbd.symm hBL hα

/-- The reduction supplied by VII (9.1) before the schism discussion of
VII Section 8 is applied in VIII (18.1). The surrounding circle here may
meet other cuffs; the printed alternative (iv) requires a further extraction. -/
theorem exists_simulation_or_cuff_count_or_small_alpha {S : Type w}
    [TopologicalSpace S] [T1Space S] [Nonempty S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      (∃ C ∈ cuffs S, ∃ F : Set S, DX.drawing.IsNormal F ∧ IsOArc F ∧ GM07.SurroundsCuff F C ∧
        (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard) ∨
      GM07.alpha DX.drawing < N := by
  classical
  obtain ⟨N, hN⟩ := exists_simulation_threshold_of_cuff_counts hS a b c h3 he DY
  refine ⟨N, fun X DX => ?_⟩
  by_cases hcounts : ∀ C ∈ cuffs S, (DY.drawing.V ∩ C).ncard = (DX.drawing.V ∩ C).ncard
  · by_cases hBL : GM07.IsBoundaryLinked DX.drawing
    · by_cases hα : N ≤ GM07.alpha DX.drawing
      · exact Or.inl (hN X DX hcounts hBL hα)
      · exact Or.inr (Or.inr (Or.inr (Nat.lt_of_not_ge hα)))
    · have hfail : ¬ ∀ C ∈ cuffs S, ∀ F : Set S, DX.drawing.IsNormal F → IsOArc F →
          GM07.SurroundsCuff F C → (DX.drawing.V ∩ C).ncard ≤ (DX.drawing.V ∩ F).ncard :=
        fun hall => hBL ⟨DX.isProper, hall⟩
      push Not at hfail
      obtain ⟨C, hC, F, hnF, hF, hsF, hlt⟩ := hfail
      exact Or.inr (Or.inr (Or.inl ⟨C, hC, F, hnF, hF, hsF, hlt⟩))
  · push Not at hcounts
    obtain ⟨C, hC, hne⟩ := hcounts
    exact Or.inr (Or.inl ⟨C, hC, Ne.symm hne⟩)

end GraphMinor.GM08
