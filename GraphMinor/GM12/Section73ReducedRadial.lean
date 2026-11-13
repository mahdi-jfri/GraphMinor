module

public import GraphMinor.GM12.Section73VertexReduction
public import GraphMinor.GM12.Section73NoParallel
import GraphMinor.GM11.RadialExists
import GraphMinor.GM11.Section64

/-!
# A radial drawing with distinct neighbours at the deleted vertex

This closes the preprocessing needed to correct the parallel-edge
claim in XII (7.3), page 261. The finite selected-disc reduction keeps
the deleted drawing and does not decrease shared-atom distances.
Choose a radial drawing of the reduced drawing. The corrected
parallel-spoke lemma makes all neighbours at the deleted vertex
distinct, so its incident edges form the star to be contracted.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14 Hypergraph

/-- Before the radial contraction in XII (7.3), page 261, one may
reduce to a radial drawing with no parallel edges at the deleted
vertex, preserving the deleted drawing and all shared-atom lower
bounds. This includes the preprocessing that the printed proof omits. -/
theorem exists_reduced_radial_at_vertex
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell) :
    ∃ (Γ₀ K : Drawing S) (T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d₀ : Set S → Set S → ℕ),
      Γ₀.IsSubdrawing Γ ∧ v ∈ Γ₀.V ∧ deleteVertices Γ₀ {v} = deleteVertices Γ {v} ∧
      HasTangleMetric Γ₀ θ T₀ d₀ ∧
      (∀ a ∈ Γ.A ∩ Γ₀.A, ∀ b ∈ Γ.A ∩ Γ₀.A, d a b ≤ d₀ a b) ∧
      (PaintingOrDrawing.drawing Γ₀).IsRadialDrawing K ∧
      (∀ e ∈ K.E, ∀ f ∈ K.E, ∀ u : S,
        K.toGraph.IsLink e v u → K.toGraph.IsLink f v u → e = f) := by
  obtain ⟨Γ₀, T₀, d₀, hΓ₀, hv₀, hdelete, hd₀, hcomp, hno⟩ :=
    exists_vertex_reduction hS hθ hd hv htwo
  obtain ⟨K, hK⟩ := exists_radialDrawing hS hd₀.1.1
  have htwo₀ : (PaintingOrDrawing.drawing (deleteVertices Γ₀ {v})).IsTwoCell := by
    rw [hdelete]
    exact htwo
  refine ⟨Γ₀, K, T₀, d₀, hΓ₀, hv₀, hdelete, hd₀, hcomp, hK, ?_⟩
  intro e he f hf u hel hfl
  by_contra hef
  have huK : u ∈ K.V := hel.2.2.1
  have hun : u ∉ Γ₀.V := (bipartite_of_preRadial hK.2.1 e v u hel).mp hv₀
  obtain ⟨r, hr, hur⟩ := hK.2.1.2.2.2.1 u ⟨huK, hun⟩
  exact no_parallel_spokes_of_no_selected_edge_inside hS hθ hd₀.1 hK.2.1 hv₀ htwo₀ hno
    he hf hef hr hur huK hel.2.2.2 hfl.2.2.2

end GraphMinor.GM12
