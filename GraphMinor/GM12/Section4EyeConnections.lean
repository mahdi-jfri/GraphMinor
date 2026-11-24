module

public import GraphMinor.GM12.Cited
public import GraphMinor.GM12.Defs
public import GraphMinor.GM12.Section4EndPartition
public import GraphMinor.GM16.Defs
public import GraphMinor.GM14.Defs
public import GraphMinor.GM12.Section4DiscConnections
import GraphMinor.GM12.Section4CrossingFeasibilityUniverses
import GraphMinor.GM12.Section4OrderedEyeContactFamily
import GraphMinor.GM12.Section4FourContactBoundary
import GraphMinor.GM12.Section4CrossingEndClasses
import GraphMinor.GM12.Section2NonemptyEdges

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# The endpoint connections for XII (4.5)

Choose the source subdivision and the threshold in (3.2),
with four marks per crossing. For the prescribed eye regions,
construct the ordered contact discs, apply claim (1), and then
apply (3.2) to its endpoint classes. All source geometry and
feasibility are proved before this application. The resulting
connected subdrawings contain the assigned ends of the two
external paths at each eye.
-/

public section

namespace GraphMinor.GM12

open Set Surface Graph GM14

universe u

/-- Explicit eye-count upper bound for Graph Minors XII, (4.5), when `4 ≤ p`. -/
@[expose] def theorem_4_5_large_kBound (p : ℕ) : ℕ :=
  (p * (p - 1) / 2) ^ 2

/-- Explicit distance/order threshold for Graph Minors XII, (4.5), when `4 ≤ p`. -/
@[expose] def theorem_4_5_large_NBound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b p : ℕ) : ℕ :=
  let kMax := theorem_4_5_large_kBound p
  max ((Finset.range (kMax + 1)).sup fun t => theorem_3_2_bound V a b t (4 * t))
    (2 * (p + 2 * kMax) + 3)

/-- Explicit version of `exists_eye_connections`, using `theorem_4_5_large_NBound V a b p`
and bounding `t ≤ theorem_4_5_large_kBound p`. -/
theorem exists_eye_connections_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a₀ b₀ : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a₀ b₀ 0))
    {p : ℕ} (hp : 4 ≤ p) :
    ∃ (W E : Type) (L : Graph W E) (κ : E × Bool → W) (t : ℕ)
      (σ : Fin t × Bool ≃ E),
      Finite W ∧ Finite E ∧ IsIsoMinor (GM16.completeGraph p) L ∧
      (∀ e, L.IsLink e (κ (e, false)) (κ (e, true))) ∧
      (∀ e, κ (e, false) ≠ κ (e, true)) ∧ 2 ≤ t ∧ t ≤ theorem_4_5_large_kBound p ∧
      2 * Nat.card W + 3 ≤ theorem_4_5_large_NBound V a₀ b₀ p ∧
      (∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
        κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w) ∧
      ∀ (Γ : Drawing S) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (δ : Set S → Set S → ℕ) (r : Fin t → Set S) (C : Fin t → Drawing S)
        (a b c d : Fin t → S),
      Γ.IsTwoCell → HasTangleMetric Γ θ T δ → theorem_4_5_large_NBound V a₀ b₀ p ≤ θ →
      (∀ i, r i ∈ Γ.R) → Function.Injective r →
      (∀ i j, i ≠ j → theorem_4_5_large_NBound V a₀ b₀ p ≤ δ (r i) (r j)) →
      (∀ i, (C i).IsCircuit) → (∀ i, (C i).IsSubdrawing Γ) →
      (∀ i, (C i).U = subBd (r i)) →
      (∀ i, a i ∈ (C i).V ∧ b i ∈ (C i).V ∧ c i ∈ (C i).V ∧ d i ∈ (C i).V) →
      (∀ i, OccurInCircuitOrder (C i) (a i) (b i) (c i) (d i)) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ {a i, b i, c i, d i}) →
      ∃ (ends : E × Bool → S) (H : W → Drawing S),
        Function.Injective ends ∧ (∀ q, ends q ∈ Γ.V) ∧
        (∀ i b c, ends (σ (i, b), c) ∈ closure (r i)) ∧
        (∀ w, (H w).IsSubdrawing Γ) ∧ (∀ w, IsConnectedDrawing (H w)) ∧
        Pairwise (fun v w => Disjoint (H v).V (H w).V) ∧
        (∀ w, (H w).V ∩ range ends = edgeEndClass ends κ w) ∧
        (∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) = {a i, c i}) ∧
        (∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) = {b i, d i}) := by
  classical
  obtain ⟨W, E, L, κ, t, σ, hW, hE, hminor, hLV, hLE, hlink, hκne, ht, htle, hWle, htwo, hsource⟩ :=
    theorem_4_5_claim_1_ordered_univ_bounded hS hp
  let : Finite W := hW
  let : Fintype W := Fintype.ofFinite W
  have hconnect := exists_threshold_for_disc_connections_explicit V hV hS he t (4 * t) (W := W)
  set N := theorem_4_5_large_NBound V a₀ b₀ p
  have hη_le : theorem_3_2_bound V a₀ b₀ t (4 * t) ≤ N := by
    have ht_mem : t ∈ Finset.range (theorem_4_5_large_kBound p + 1) :=
      Finset.mem_range.mpr (Nat.lt_succ_of_le htle)
    exact (Finset.le_sup (f := fun t => theorem_3_2_bound V a₀ b₀ t (4 * t)) ht_mem).trans
      (le_max_left _ _)
  have hNW : 2 * Nat.card W + 3 ≤ N :=
    (by dsimp only [theorem_4_5_large_kBound]; omega :
      2 * Nat.card W + 3 ≤ 2 * (p + 2 * theorem_4_5_large_kBound p) + 3).trans
      (le_max_right _ _)
  refine ⟨W, E, L, κ, t, σ, hW, hE, hminor, hlink, hκne, ht, htle, hNW, htwo, ?_⟩
  intro Γ θ T δ r C a b c d hcell hm hθ hr hri hfar hC hCG hCr hmarks horder hfree
  have hN3 : 3 ≤ N := by omega
  have hEΓ : Γ.E.Nonempty := edges_nonempty_of_tangle_order_two hm.1.2.1 (by omega)
  obtain ⟨D, q, β, hD, hDD, hDN, hq, hβ, hβ01, hqmarks⟩ :=
    exists_ordered_eye_contact_family hS hcell hm hEΓ ht r C a b c d hr hri
      (fun i j hij => hN3.trans (hfar i j hij)) hC hCG hCr hmarks horder
  obtain ⟨ends, B, hinj, hB, hBB, hcontact, hp0, hp1⟩ := hsource D q β hD hDD hq hβ hβ01
  have hp0' : ∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) = {a i, c i} := by
    intro i
    rw [hp0 i, (hqmarks i).1, (hqmarks i).2.2.1]
  have hp1' : ∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) = {b i, d i} := by
    intro i
    rw [hp1 i, (hqmarks i).2.1, (hqmarks i).2.2.2]
  let M : Fin t → Set S := fun i => {a i, b i, c i, d i}
  have hMV : ∀ i, M i ⊆ Γ.V := by
    intro i x hx
    rcases hx with rfl | rfl | rfl | hx
    · exact (hCG i).1 (hmarks i).1
    · exact (hCG i).1 (hmarks i).2.1
    · exact (hCG i).1 (hmarks i).2.2.1
    · exact (mem_singleton_iff.mp hx) ▸ (hCG i).1 (hmarks i).2.2.2
  have hnorm := fun i => normal_disc_of_exact_boundary_contacts (hDN i).2.1 (hMV i) (hDN i).2.2
  have hbd : ∀ i, Γ.V ∩ discBd (D i) = M i := fun i => (hnorm i).2
  have hrange : range ends = ⋃ i, M i := by
    have hh := range_ends_eq_crossing_marks σ ends (fun i => ![a i, b i, c i, d i]) hp0' hp1'
    have hvec : ∀ i, range ![a i, b i, c i, d i] = M i := by
      intro i
      ext x
      simp [M, or_comm, or_left_comm]
    simpa only [hvec] using hh
  have hZ : discBoundaryVertices Γ D = range ends := by
    simp only [discBoundaryVertices, hbd, hrange]
  have hendM : ∀ i b c, ends (σ (i, b), c) ∈ M i := by
    intro i b' c'
    have hh : ends (σ (i, b'), c') ∈
        ({ends (σ (i, b'), false), ends (σ (i, b'), true)} : Set S) := by cases c' <;> simp
    cases b'
    · rw [hp0' i] at hh
      rcases hh with hh | hh
      · rw [hh]; simp [M]
      · rw [mem_singleton_iff.mp hh]; simp [M]
    · rw [hp1' i] at hh
      rcases hh with hh | hh
      · rw [hh]; simp [M]
      · rw [mem_singleton_iff.mp hh]; simp [M]
  have hends : ∀ z, ends z ∈ Γ.V := by
    rintro ⟨e, c'⟩
    obtain ⟨⟨i, b'⟩, rfl⟩ := σ.surjective e
    exact hMV i (hendM i b' c')
  have hinc : ∀ i b c, ends (σ (i, b), c) ∈ closure (r i) := by
    intro i b' c'
    have hmD := (hDN i).2.2 (hendM i b' c')
    exact (hDN i).1 (discBd_subset _ hmD)
  obtain ⟨H, hHs, hHc, hHH, hHZ⟩ := hconnect Γ θ T δ D r (edgeEndClass ends κ)
    (fun i => ⟨hD i, (hnorm i).1⟩) hDD
    (discBoundaryVertices_ncard_le_four D a b c d hbd)
    ((iUnion_edgeEndClass ends κ).trans hZ.symm)
    (fun v w hvw => disjoint_edgeEndClass ends κ hinj hvw)
    ⟨B, hB, hBB, hcontact⟩ (hη_le.trans hθ) hm
    (fun i => ⟨hr i, (hDN i).1⟩)
    (fun i j hij => hη_le.trans (hfar i j hij))
    (fun i => hbd i ▸ hfree i)
  refine ⟨ends, H, hinj, hends, hinc, hHs, hHc, hHH, ?_, hp0', hp1'⟩
  intro w
  simpa only [hZ] using hHZ w

/-- The endpoint-connection construction following claim (1) in
XII (4.5), page 253. Its only statement hypotheses are the cited
VII (7.5), (5.1), and (5.5). -/
theorem exists_eye_connections
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {p : ℕ} (hp : 4 ≤ p) :
    ∃ (W E : Type) (L : Graph W E) (κ : E × Bool → W) (t : ℕ)
      (σ : Fin t × Bool ≃ E) (N : ℕ),
      Finite W ∧ Finite E ∧ IsIsoMinor (GM16.completeGraph p) L ∧
      (∀ e, L.IsLink e (κ (e, false)) (κ (e, true))) ∧
      (∀ e, κ (e, false) ≠ κ (e, true)) ∧ 2 ≤ t ∧ 2 * Nat.card W + 3 ≤ N ∧
      (∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
        κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w) ∧
      ∀ (Γ : Drawing S) (θ : ℕ)
        (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (δ : Set S → Set S → ℕ) (r : Fin t → Set S) (C : Fin t → Drawing S)
        (a b c d : Fin t → S),
      Γ.IsTwoCell → HasTangleMetric Γ θ T δ → N ≤ θ →
      (∀ i, r i ∈ Γ.R) → Function.Injective r →
      (∀ i j, i ≠ j → N ≤ δ (r i) (r j)) →
      (∀ i, (C i).IsCircuit) → (∀ i, (C i).IsSubdrawing Γ) →
      (∀ i, (C i).U = subBd (r i)) →
      (∀ i, a i ∈ (C i).V ∧ b i ∈ (C i).V ∧ c i ∈ (C i).V ∧ d i ∈ (C i).V) →
      (∀ i, OccurInCircuitOrder (C i) (a i) (b i) (c i) (d i)) →
      (∀ i, GM10.IsFreeSet Γ.toHypergraph T θ {a i, b i, c i, d i}) →
      ∃ (ends : E × Bool → S) (H : W → Drawing S),
        Function.Injective ends ∧ (∀ q, ends q ∈ Γ.V) ∧
        (∀ i b c, ends (σ (i, b), c) ∈ closure (r i)) ∧
        (∀ w, (H w).IsSubdrawing Γ) ∧ (∀ w, IsConnectedDrawing (H w)) ∧
        Pairwise (fun v w => Disjoint (H v).V (H w).V) ∧
        (∀ w, (H w).V ∩ range ends = edgeEndClass ends κ w) ∧
        (∀ i, ({ends (σ (i, false), false), ends (σ (i, false), true)} : Set S) = {a i, c i}) ∧
        (∀ i, ({ends (σ (i, true), false), ends (σ (i, true), true)} : Set S) = {b i, d i}) := by
  obtain ⟨a₀, b₀, he⟩ := exists_closed_surface_model hS
  obtain ⟨W, E, L, κ, t, σ, hW, hE, hmin, hlink, hκne, ht, _, hNW, htwo, hmain⟩ :=
    exists_eye_connections_explicit GM07.vModel (fun _ _ _ _ => le_rfl) hS he hp
  exact ⟨W, E, L, κ, t, σ, theorem_4_5_large_NBound GM07.vModel a₀ b₀ p,
    hW, hE, hmin, hlink, hκne, ht, hNW, htwo, hmain⟩

end GraphMinor.GM12
