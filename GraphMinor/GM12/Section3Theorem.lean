module

public import GraphMinor.GM12.Section3SeparatedMetric
public import GraphMinor.GM12.Section3TwoDiscs
public import GraphMinor.GM12.Section3OneDisc
import GraphMinor.GM12.Section3EmptyClasses
import GraphMinor.GM12.Section3DiscRegion
import Mathlib.Tactic.IntervalCases

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# Graph Minors XII, (3.2)

For a nonspherical surface or at least three prescribed discs, the
five geometric checks give (3.1). For two discs, choose a separated
intermediate region and add an empty-boundary disc away from the
feasibility forest. For one disc on the sphere, freeness gives the
normal-chord inequality and VI (3.6) gives the connections. With no
discs, the prescribed vertex set is empty. These are the cases of
the proof on pages 246--248.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

universe u

/-- Explicit threshold for Graph Minors XII, (3.2), parameterized by an upper bound `V` on
`GM07.vModel` and closed surface model parameters `(a, b)`. -/
@[expose] def theorem_3_2_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b t z : ℕ) : ℕ :=
  max (theorem_3_2_sep_bound V a b t z) (theorem_3_2_two_discs_bound V a b z)

theorem one_le_theorem_3_2_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b t z : ℕ) :
    1 ≤ theorem_3_2_bound V a b t z :=
  (Nat.succ_le_succ (Nat.zero_le _)).trans (le_max_left _ _)

/-- Graph Minors XII, (3.2), pages 245--248, with an explicit threshold
`theorem_3_2_bound V a b t z`. -/
theorem theorem_3_2_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a b : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a b 0)) (t z : ℕ) :
    ∀ (Δ : Fin t → Set S) (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (p : ℕ) (Zs : Fin p → Set S),
      (∀ i, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) →
      Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → IsTopologicallyFeasible Δ Zs →
      theorem_3_2_bound V a b t z ≤ θ → HasTangleMetric Γ θ T d →
      (∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ Δ i).Nonempty →
        ∀ rj ∈ Γ.R, (rj ∩ Δ j).Nonempty → theorem_3_2_bound V a b t z ≤ d ri rj) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i))) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  by_cases hcase : ¬ IsSphere S ∨ 3 ≤ t
  · intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeas horder hm hsep hfree
    exact theorem_3_2_separated_metric_explicit V hV hS he t z hcase
      Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeas
      ((le_max_left _ _).trans horder) hm
      (fun i j hij ri hri hriD rj hrj hrjD =>
        (le_max_left _ _).trans (hsep i j hij ri hri hriD rj hrj hrjD))
      hfree
  · have hs : IsSphere S := by
      by_contra hn
      exact hcase (Or.inl hn)
    have ht : t ≤ 2 := by
      by_contra hn
      exact hcase (Or.inr (by omega))
    interval_cases t
    · intro Δ Γ θ T d p Zs _ _ _ hcover _ _ _ _ _ _
      have hZ : discBoundaryVertices Γ Δ = ∅ := by simp [discBoundaryVertices]
      rw [hZ] at hcover ⊢
      exact hasConnectingSubdrawings_of_empty_union Γ Zs hcover
    · intro Δ Γ θ T d p Zs hΔ _ _ hcover hdisZ hfeas _ hm _ hfree
      exact theorem_3_2_one_disc hS hs Γ hm.1.2.1 Δ (fun i => (hΔ i).1)
        (fun i => (hΔ i).2) Zs hcover hdisZ hfeas (hfree 0)
    · have htwo := theorem_3_2_two_discs_explicit V hV hS he z
      intro Δ Γ θ T d p Zs hΔ hdis hcount hcover hdisZ hfeas horder hm hsep hfree
      have hreg : ∀ i, ∃ r ∈ Γ.R, (r ∩ Δ i).Nonempty := by
        intro i
        obtain ⟨r, hr, hInt, _, _⟩ := exists_unique_region_meeting_disc hS (hΔ i).1 (hΔ i).2
        obtain ⟨x, hx⟩ := (hΔ i).1.nonempty_discInt
        exact ⟨r, hr, x, hInt hx, hx.1⟩
      choose r hr hrΔ using hreg
      exact htwo Γ θ T d Δ r p Zs hm ((le_max_right _ _).trans horder)
        (fun i => (hΔ i).1) hdis (fun i => (hΔ i).2) hr hrΔ
        (fun i j hij =>
          (le_max_right _ _).trans (hsep i j hij (r i) (hr i) (hrΔ i) (r j) (hr j) (hrΔ j)))
        hfree hcount hcover hdisZ hfeas

/-- Graph Minors XII, (3.2), pages 245--248. A uniform separation
threshold for the prescribed regions and free boundary vertices
ensures disjoint connected subdrawings realizing every topologically
feasible boundary partition. -/
theorem theorem_3_2_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (t z : ℕ) :
    ∃ η : ℕ, 1 ≤ η ∧ ∀ (Δ : Fin t → Set S) (Γ : Drawing S) (θ : ℕ)
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ) (p : ℕ) (Zs : Fin p → Set S),
      (∀ i, IsClosedDisc (Δ i) ∧ Γ.U ∩ Δ i = Γ.V ∩ discBd (Δ i)) →
      Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
      (discBoundaryVertices Γ Δ).ncard ≤ z →
      (⋃ j, Zs j) = discBoundaryVertices Γ Δ →
      (∀ i j, i ≠ j → Disjoint (Zs i) (Zs j)) → IsTopologicallyFeasible Δ Zs →
      η ≤ θ → HasTangleMetric Γ θ T d →
      (∀ i j, i ≠ j → ∀ ri ∈ Γ.R, (ri ∩ Δ i).Nonempty →
        ∀ rj ∈ Γ.R, (rj ∩ Δ j).Nonempty → η ≤ d ri rj) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ (Γ.V ∩ discBd (Δ i))) →
      HasConnectingSubdrawings Γ (discBoundaryVertices Γ Δ) Zs := by
  obtain ⟨a, b, he⟩ := exists_closed_surface_model hS
  exact ⟨theorem_3_2_bound GM07.vModel a b t z, one_le_theorem_3_2_bound _ a b t z,
    theorem_3_2_explicit GM07.vModel (fun _ _ _ _ => le_rfl) hS he t z⟩

end GraphMinor.GM12
