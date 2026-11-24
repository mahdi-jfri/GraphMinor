module

public import GraphMinor.GM12.Defs
public import GraphMinor.GM12.Induced
public import GraphMinor.GM12.Cited
public import GraphMinor.Surface.Defs
public import GraphMinor.GM12.Section4FeasibleControl
import GraphMinor.GM12.Section4NormalizedTarget
import GraphMinor.GM12.Section4TargetOrientation
import GraphMinor.GM12.Section4TopologicalFeasibility
import GraphMinor.GM12.Section3GeometricReduction
import GraphMinor.GM12.Section4FreeEdgeDiscs
import GraphMinor.GM12.Section4Monotone

import GraphMinor.GM07.Section7
import GraphMinor.GM07.Bridge

/-!
# Graph Minors XII (4.3): controlling a drawable minor

Replace the drawable target by a loopless drawable graph with two
incident edges at every vertex. Select widely separated free edges
of the host drawing and empty discs around them. The source target
drawing and the marked-disc homeomorphism prove topological
feasibility. Apply (3.2), verify control using (4.1), and pass back
to the original target by (4.2).
-/

public section

namespace GraphMinor.GM12

open Set Surface GM14

universe u

/-- A drawing gives the same incidence hypergraph through its graph representation. -/
theorem drawing_hypergraph_eq_ofGraph
    {S : Type*} [TopologicalSpace S] (Γ : Drawing S) :
    Γ.toHypergraph = Hypergraph.ofGraph Γ.toGraph Γ.finite_V Γ.finite_edges := by
  refine Hypergraph.ext (x := Γ.toHypergraph)
    (y := Hypergraph.ofGraph Γ.toGraph Γ.finite_V Γ.finite_edges) ?_ ?_ ?_
  · rfl
  · rfl
  funext e v
  apply propext
  change (e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e) ↔ ∃ w, Γ.toGraph.IsLink e v w
  constructor
  · intro h
    obtain ⟨x, y, hxy⟩ := Γ.toGraph.exists_isLink_of_mem_edgeSet h.1
    have hv : v ∈ ({x, y} : Set S) := hxy.2.2.2 ▸ (show v ∈ closure e ∩ Γ.V from ⟨h.2.2, h.2.1⟩)
    rcases hv with hv | hv
    · subst v
      exact ⟨y, hxy⟩
    · have heq := Set.mem_singleton_iff.mp hv
      subst v
      exact ⟨x, hxy.symm⟩
  · rintro ⟨w, he, hv, hw, hcap⟩
    exact ⟨he, hv, ((hcap.symm).subset (by simp)).1⟩

/-- Explicit threshold for Graph Minors XII, (4.3), depending only on an upper bound `V` on
`GM07.vModel`, the closed surface model `(a, b)`, and upper bounds `(vB, eB)` on the target
graph's vertex and edge counts. -/
@[expose] def theorem_4_3_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b vB eB : ℕ) : ℕ :=
  (Finset.range (4 * vB + 4 * eB + 1)).sup fun t =>
    let k := feasibleControlBound V a b (3 * vB + eB) t
    max k (5 + t * (k + 7))

theorem one_le_theorem_4_3_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (a b vB eB : ℕ) :
    1 ≤ theorem_4_3_bound V a b vB eB := by
  have h0 : (0 : ℕ) ∈ Finset.range (4 * vB + 4 * eB + 1) :=
    Finset.mem_range.mpr (Nat.succ_pos _)
  have h1 : 1 ≤ feasibleControlBound V a b (3 * vB + eB) 0 :=
    (one_le_theorem_3_2_bound V a b 0 0).trans (le_max_left _ _)
  exact h1.trans ((le_max_left _ _).trans (Finset.le_sup (f := fun t =>
    let k := feasibleControlBound V a b (3 * vB + eB) t
    max k (5 + t * (k + 7))) h0))

/-- Graph Minors XII (4.3), pages 249--251, for the drawing itself, with an explicit threshold
`theorem_4_3_bound V a b vB eB`. -/
theorem theorem_4_3_drawing_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {a₀ b₀ : ℕ} (he : Nonempty (S ≃ₜ SurfaceModel a₀ b₀ 0))
    {α β : Type*} {L : Graph α β} (D : GraphDrawing L S) {vB eB : ℕ}
    (hvB : L.vertexSet.ncard ≤ vB) (heB : L.edgeSet.ncard ≤ eB) :
    ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d : Set S → Set S → ℕ),
      HasTangleMetric Γ θ T d → theorem_4_3_bound V a₀ b₀ vB eB ≤ θ →
      ControlsMinor Γ.toHypergraph θ T L := by
  obtain ⟨p, t, K, DK, hp_le, ht_le, hKV, hKE, hminor, hloop, htwo⟩ :=
    exists_normalized_target_replacement_bounded hS D
  obtain ⟨κ, hassign, hslots⟩ := exists_target_end_assignment K hKE hloop htwo
  have hl : ∀ i, K.IsLink i (κ (i, true)) (κ (i, false)) := by
    intro i
    obtain ⟨v, w, h⟩ := K.exists_isLink_of_mem_edgeSet (hKE ▸ mem_univ i)
    rcases hassign i v w h with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · rw [hv, hw]; exact h
    · rw [hv, hw]; exact h.symm
  have hne : ∀ i, κ (i, true) ≠ κ (i, false) := by
    intro i heq
    exact hloop i (κ (i, false)) (heq ▸ hl i)
  have hcontrol := exists_threshold_for_control_from_feasible_discs_explicit V hV hS he
    K κ hloop hassign hslots
  set k := feasibleControlBound V a₀ b₀ p t
  have hk : 1 ≤ k := (one_le_theorem_3_2_bound V a₀ b₀ t (2 * t)).trans (le_max_left _ _)
  have hk_le : k ≤ feasibleControlBound V a₀ b₀ (3 * vB + eB) t :=
    max_le_max_left _ (by omega)
  have ht_mem : t ∈ Finset.range (4 * vB + 4 * eB + 1) :=
    Finset.mem_range.mpr (by omega)
  have hN_le : max k (5 + t * (k + 7)) ≤ theorem_4_3_bound V a₀ b₀ vB eB := by
    have hstep : max k (5 + t * (k + 7)) ≤
        max (feasibleControlBound V a₀ b₀ (3 * vB + eB) t)
          (5 + t * (feasibleControlBound V a₀ b₀ (3 * vB + eB) t + 7)) :=
      max_le_max hk_le (Nat.add_le_add_left (Nat.mul_le_mul_left t (Nat.add_le_add_right hk_le 7)) 5)
    exact hstep.trans (Finset.le_sup (f := fun t =>
      let k := feasibleControlBound V a₀ b₀ (3 * vB + eB) t
      max k (5 + t * (k + 7))) ht_mem)
  intro Γ θ T d hm hN
  have hN' : max k (5 + t * (k + 7)) ≤ θ := hN_le.trans hN
  have hkθ : k ≤ θ := (le_max_left _ _).trans hN'
  obtain ⟨f, a, b, Δ, r, hdata, hdisj, hreg, hsep⟩ :=
    exists_spaced_free_edge_discs hS hm hk ((le_max_right _ _).trans hN')
  have hfeas := topologicallyFeasible_of_drawn_target hS K hKV hKE DK κ hl hne Δ a b
    (fun i => ⟨(hdata i).2.2.1, (hdata i).2.1, (hdata i).2.2.2.2.1⟩) hdisj
  have hc : ControlsMinor Γ.toHypergraph θ T K := hcontrol Γ θ T d f a b Δ r hm hkθ
    (fun i => ⟨(hdata i).1, (hdata i).2.1⟩)
    (fun i => ⟨(hdata i).2.2.1, (hdata i).2.2.2.2.2.1,
      (hdata i).2.2.2.2.2.1.symm.trans (hdata i).2.2.2.1⟩)
    hdisj hsep (fun i => ⟨(hdata i).2.2.2.2.2.2.2.1, (hdata i).2.2.2.2.2.2.2.2.2⟩)
    hreg (fun i => (hdata i).2.2.2.2.2.2.1) hfeas
  have heq := drawing_hypergraph_eq_ofGraph Γ
  rw [heq] at hc
  have hfinal := theorem_4_2_proof (G := Γ.toGraph) Γ.finite_V Γ.finite_edges
    (Set.toFinite _) (Set.toFinite _) hminor hc
  rwa [← heq] at hfinal

/-- Graph Minors XII (4.3), pages 249--251, for the drawing itself.
The threshold is enlarged by taking a maximum with the connection
threshold, also covering an edgeless target. The only statement
hypotheses are the cited VII (7.5), (5.1), and (5.5). -/
theorem theorem_4_3_drawing
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {α β : Type*} {L : Graph α β} (D : GraphDrawing L S) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ),
      HasTangleMetric Γ θ T d → N ≤ θ → ControlsMinor Γ.toHypergraph θ T L := by
  obtain ⟨a₀, b₀, he⟩ := exists_closed_surface_model hS
  exact ⟨theorem_4_3_bound GM07.vModel a₀ b₀ L.vertexSet.ncard L.edgeSet.ncard,
    one_le_theorem_4_3_bound _ a₀ b₀ _ _,
    theorem_4_3_drawing_explicit GM07.vModel (fun _ _ _ _ => le_rfl) hS he D le_rfl le_rfl⟩

/-- Graph Minors XII (4.3), pages 249--251. The tangle induced in
an overgraph controls every drawable target once its order exceeds
the threshold. The overgraph is written as a hypergraph with the
same vertex and edge labels as the drawing. -/
theorem theorem_4_3_proof
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {α β : Type*} {L : Graph α β} (D : GraphDrawing L S) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ (Γ : Drawing S) (θ : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ) (G : Hypergraph S (Set S)),
      HasTangleMetric Γ θ T d → N ≤ θ → Γ.toHypergraph ≤ G →
      ControlsMinor G θ (inducedBySubgraph G Γ.toHypergraph θ T) L := by
  obtain ⟨N, hN, hdraw⟩ := theorem_4_3_drawing hS D
  refine ⟨N, hN, ?_⟩
  intro Γ θ T d G hm hθ hΓG
  exact controlsMinor_inducedBySubgraph hΓG (hdraw Γ θ T d hm hθ)

end GraphMinor.GM12
