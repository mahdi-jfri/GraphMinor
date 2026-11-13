module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18LargeAlpha
import GraphMinor.GM08.Section18Surrounding
import GraphMinor.GM08.Section18Align
import GraphMinor.GM08.Section18Drawing
import GraphMinor.GM08.Section18Minimum

/-!
# Reducing VIII (18.1) to small alpha

Enlarge the uniform threshold to exceed twice the root count. Equal cuff
counts identify the host's boundary vertex count with that root count.
Thus large alpha gives either a simulation or precisely the surrounding
circle in alternative (iv), including its boundary restriction.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u v w

/-- The alternatives of VIII (18.1), pages 285–286, before small alpha is
replaced by a bounded normal schism. All other printed alternatives,
including the boundary restriction in (iv), are established here. -/
theorem exists_simulation_or_cuff_count_or_surrounding_or_small_alpha {S : Type w}
    [TopologicalSpace S] [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      (∃ C ∈ cuffs S, ∃ F : Set S, DX.drawing.IsNormal F ∧ IsOArc F ∧ GM07.SurroundsCuff F C ∧
        F ∩ bd S ⊆ C ∧ (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard) ∨
      GM07.alpha DX.drawing < N := by
  classical
  obtain ⟨N₀, hN₀⟩ := exists_simulation_or_cuff_count_or_small_alpha hS a b c h3 he DY
  let N := max N₀ (2 * Y.index + 1)
  refine ⟨N, fun X DX => ?_⟩
  by_cases hcounts : ∀ C ∈ cuffs S, (DY.drawing.V ∩ C).ncard = (DX.drawing.V ∩ C).ncard
  · by_cases hsmall : GM07.alpha DX.drawing < N
    · exact Or.inr (Or.inr (Or.inr hsmall))
    · have hlarge : N ≤ GM07.alpha DX.drawing := Nat.le_of_not_gt hsmall
      have hN₀le : N₀ ≤ N := le_max_left _ _
      have hrootle : 2 * Y.index + 1 ≤ N := le_max_right _ _
      obtain ⟨DY', hbd⟩ := exists_graftDrawing_aligned_boundary hS DY DX hcounts
      have hroot : (DX.drawing.V ∩ bd S).ncard = Y.index := by
        rw [← hbd]
        exact (ncard_roots_eq_boundary_vertices DY').symm
      rcases hN₀ X DX with hsim | hdiff | hsurround | hαsmall
      · exact Or.inl hsim
      · obtain ⟨C, hC, hne⟩ := hdiff
        exact (hne (hcounts C hC).symm).elim
      · obtain ⟨C, hC, F, hnF, hF, hsF, hlt⟩ := hsurround
        have hα : 2 * (DX.drawing.V ∩ bd S).ncard < GM07.alpha DX.drawing := by
          rw [hroot]
          omega
        have hsub := surrounding_circle_inter_boundary_subset hS a b c h3 he hncyl
          DX.drawing DX.isProper hα hC hF hnF hsF hlt
        exact Or.inr (Or.inr (Or.inl ⟨C, hC, F, hnF, hF, hsF, hsub, hlt⟩))
      · exact (Nat.not_lt_of_ge (hN₀le.trans hlarge) hαsmall).elim
  · push Not at hcounts
    obtain ⟨C, hC, hne⟩ := hcounts
    exact Or.inr (Or.inl ⟨C, hC, Ne.symm hne⟩)

/-- All alternatives of VIII (18.1), with the small-alpha alternative
expressed by a bounded normal schismatic set. The remaining geometric
step is to replace this set by one of the six printed schism shapes. -/
theorem exists_simulation_or_cuff_count_or_surrounding_or_schismatic {S : Type w}
    [TopologicalSpace S] [T1Space S] [ConnectedSpace S] (hS : IsSurface S)
    (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    {α : Type u} {β : Type v} {Y : Graft α β} (DY : GraftDrawing Y.G Y.T S) :
    ∃ N : ℕ, ∀ (X : Graft α β) (DX : GraftDrawing X.G X.T S),
      IsGraftSimulatedIn Y X ∨
      (∃ C ∈ cuffs S, (DX.drawing.V ∩ C).ncard ≠ (DY.drawing.V ∩ C).ncard) ∨
      (∃ C ∈ cuffs S, ∃ F : Set S, DX.drawing.IsNormal F ∧ IsOArc F ∧ GM07.SurroundsCuff F C ∧
        F ∩ bd S ⊆ C ∧ (DX.drawing.V ∩ F).ncard < (DX.drawing.V ∩ C).ncard) ∨
      (∃ F : Set S, GM07.IsSchismatic F ∧ DX.drawing.IsNormal F ∧
        (DX.drawing.V ∩ F).ncard < N) := by
  obtain ⟨N, hN⟩ := exists_simulation_or_cuff_count_or_surrounding_or_small_alpha
    hS a b c h3 he hncyl DY
  refine ⟨N, fun X DX => ?_⟩
  rcases hN X DX with hsim | hcount | hsur | hsmall
  · exact Or.inl hsim
  · exact Or.inr (Or.inl hcount)
  · exact Or.inr (Or.inr (Or.inl hsur))
  · obtain ⟨F, hF, hnF, hcard⟩ := exists_normal_schismatic_at_alpha hS h3 he hncyl
      DX.drawing DX.isProper
    exact Or.inr (Or.inr (Or.inr ⟨F, hF, hnF, by rw [inter_comm, hcard]; exact hsmall⟩))

end GraphMinor.GM08
