module

public import GraphMinor.GM12.Section3AlphaEmptyClasses
public import GraphMinor.GM12.Section3ModelComplexity

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# A uniform alpha threshold for the connecting subdrawings

The application of VII in XII (3.1), page 245, chooses its threshold
from the fixed surface, the number of deleted discs and the boundary
vertex bound. The punctured surface has fixed model parameters, so
VII's numerical threshold is independent of the drawing and of the
disc placement. The alpha estimate is the remaining input here.
-/

public section

namespace GraphMinor.GM12

open Set Surface

universe u

/-- Explicit alpha threshold in the application of VII (7.5) for XII (3.1),
parameterized by an upper bound `V` on `GM07.vModel`. -/
@[expose] def uniformAlphaBound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b t z : ℕ) : ℕ :=
  42 * (z + t + 1) * V a b (t + 1) (z + t + 1)

/-- Explicit version of `exists_uniform_connecting_alpha_threshold`, parameterized by
an upper bound `V` on `GM07.vModel` and closed surface model parameters `(a, b)`. -/
theorem exists_uniform_connecting_alpha_threshold_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0))
    (t z : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∀ (Γ : Drawing S) (Δ : Fin t → Set S)
      (hΔ : ∀ i, IsClosedDisc (Δ i))
      (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
      (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
      (p : ℕ) (Zs : Fin p → Set S),
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) →
      IsTopologicallyFeasible Δ Zs →
      (∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
        ∀ D : Set S, IsClosedDisc D → discBd D = F →
        ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
          (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      uniformAlphaBound V a b t z ≤ GM07.alpha (drawingInSubspace Γ (discComplement Δ)
        (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  obtain ⟨e⟩ := he
  have hcomplex := model_complexity_of_not_sphere_or_three_discs e hcase
  intro Γ Δ hΔ hd ha p Zs hcover hdisZ hfeasible hbound hcount hα
  have hmodel : Nonempty (discComplement Δ ≃ₜ SurfaceModel a b t) :=
    Eq.mp (congrArg
      (fun n => Nonempty (discComplement Δ ≃ₜ SurfaceModel a b n)) (Nat.card_fin t))
      (discComplement_model_of_closed_model hS Δ hΔ hd e)
  have hα' : 42 * (z + t + 1) * GM07.vModel a b (t + 1) (z + t + 1) ≤
      GM07.alpha (drawingInSubspace Γ (discComplement Δ)
        (drawing_support_subset_discComplement hS Γ Δ hΔ hd ha)) :=
    (Nat.mul_le_mul_left _ (hV a b (t + 1) (z + t + 1))).trans hα
  exact connecting_subdrawings_of_alpha_bound_allowing_empty hS Γ Δ hΔ hd ha Zs
    hcover hdisZ hfeasible hbound a b t z hcomplex hmodel hcount hα'

/-- The uniform numerical choice in the application of VII (7.5) for
XII (3.1). All model, complexity, forest and boundary-linkage requirements
are discharged. Only the alpha bound remains as a hypothesis. -/
theorem exists_uniform_connecting_alpha_threshold
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) (hcase : ¬ IsSphere S ∨ 3 ≤ t) :
    ∃ N : ℕ, ∀ (Γ : Drawing S) (Δ : Fin t → Set S)
      (hΔ : ∀ i, IsClosedDisc (Δ i))
      (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
      (havoid : ∀ i, Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i))
      (p : ℕ) (Zs : Fin p → Set S),
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) →
      IsTopologicallyFeasible Δ Zs →
      (∀ F : Set S, Γ.IsNormal F → IsOArc F → F ⊆ discComplement Δ →
        ∀ D : Set S, IsClosedDisc D → discBd D = F →
        ∀ i, (∀ j, Δ j ⊆ D ↔ j = i) →
          (Γ.V ∩ discBd (Δ i)).ncard ≤ (Γ.V ∩ F).ncard) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      N ≤ GM07.alpha (drawingInSubspace Γ (discComplement Δ)
        (drawing_support_subset_discComplement hS Γ Δ hΔ hdisj havoid)) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  obtain ⟨a, b, he⟩ := exists_closed_surface_model hS
  exact ⟨uniformAlphaBound GM07.vModel a b t z,
    exists_uniform_connecting_alpha_threshold_explicit GM07.vModel (fun _ _ _ _ => le_rfl)
      hS he t z hcase⟩

end GraphMinor.GM12
