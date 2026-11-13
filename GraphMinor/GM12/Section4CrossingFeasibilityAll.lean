module

public import GraphMinor.GM12.Section4CrossingFeasibilityUniverses
public import GraphMinor.GM12.Section4FourBoundaryParameters

/-!
# Feasibility for four-point prescriptions in arbitrary universes

Graph Minors XII, (4.5), claim (1), page 253, prescribes only
a four-point set on each disc boundary. Order the marks using
a circle parametrization and apply the ordered feasibility
construction. All partition classes, witness discs, and
opposite-pair equations are conclusions of the theorem.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph

/-- Graph Minors XII, (4.5), claim (1), page 253, in arbitrary
surface universes and for arbitrary four-point boundary sets. The source graph and crossing count
are fixed before the prescribed discs and marks are supplied.
The construction works for `p ≥ 4`; the paper uses `p ≥ 5`. -/
theorem theorem_4_5_claim_1_univ {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {p : ℕ} (hp : 4 ≤ p) :
    ∃ (W E : Type) (L : Graph W E) (κ : E × Bool → W) (t : ℕ) (σ : Fin t × Bool ≃ E),
      Finite W ∧ Finite E ∧ IsIsoMinor (GM16.completeGraph p) L ∧
      L.vertexSet = univ ∧ L.edgeSet = univ ∧
      (∀ e, L.IsLink e (κ (e, false)) (κ (e, true))) ∧
      (∀ e, κ (e, false) ≠ κ (e, true)) ∧ 2 ≤ t ∧
      (∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
        κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w) ∧
      ∀ (Δ N : Fin t → Set S), (∀ i, IsClosedDisc (Δ i)) →
        Pairwise (fun i j => Disjoint (Δ i) (Δ j)) →
        (∀ i, N i ⊆ discBd (Δ i)) → (∀ i, (N i).Finite) → (∀ i, (N i).ncard = 4) →
        ∃ (ends : E × Bool → S) (B : W → Set S) (q : Fin t → Circle → S) (β : Fin t → Fin 4 → ℝ),
          Function.Injective ends ∧ (∀ w, IsClosedDisc (B w)) ∧
          Pairwise (fun w z => Disjoint (B w) (B z)) ∧
          (∀ w, B w ∩ (⋃ i, Δ i) = edgeEndClass ends κ w) ∧
          (∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (Δ i)) ∧
          (∀ i, StrictMono (β i) ∧ (∀ j, β i j ∈ Ico 0 1) ∧
            N i = range (fun j => q i (ee (β i j)))) ∧
          (∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) =
            {q i (ee (β i 0)), q i (ee (β i 2))}) ∧
          (∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) =
            {q i (ee (β i 1)), q i (ee (β i 3))}) := by
  obtain ⟨W, E, L, κ, t, σ, hW, hE, hminor, hLV, hLE, hlink, hκne, ht, htwo, hmain⟩ :=
    theorem_4_5_claim_1_ordered_univ hS hp
  refine ⟨W, E, L, κ, t, σ, hW, hE, hminor, hLV, hLE, hlink, hκne, ht, htwo, ?_⟩
  intro Δ N hΔ hΔΔ hN hNfin hNcard
  have hparams : ∀ i, ∃ (q : Circle → S) (b : Fin 4 → ℝ), Continuous q ∧ Function.Injective q ∧
      range q = discBd (Δ i) ∧ StrictMono b ∧ (∀ j, b j ∈ Ico 0 1) ∧
      N i = range (fun j => q (ee (b j))) := fun i =>
    exists_four_boundary_parameters (hΔ i) (hN i) (hNfin i) (hNcard i)
  choose q β hqc hqi hqr hβ hβ01 hNrepr using hparams
  have hq : ∀ i, Continuous (q i) ∧ Function.Injective (q i) ∧ range (q i) = discBd (Δ i) :=
    fun i => ⟨hqc i, hqi i, hqr i⟩
  obtain ⟨ends, B, hinj, hB, hBB, hcontact, h0, h1⟩ := hmain Δ q β hΔ hΔΔ hq hβ hβ01
  exact ⟨ends, B, q, β, hinj, hB, hBB, hcontact, hq,
    (fun i => ⟨hβ i, hβ01 i, hNrepr i⟩), h0, h1⟩

end GraphMinor.GM12
