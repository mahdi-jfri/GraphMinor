module

public import GraphMinor.GM12.Section73DerivedContraction
public import GraphMinor.GM12.Section73VertexReduction
import GraphMinor.GM12.Section73NoParallel
import GraphMinor.GM12.Section73OrderOne
import GraphMinor.GM12.Section77
import GraphMinor.GM11.RadialBasics
import GraphMinor.GM07.Section3

/-!
# Existence of a metric after vertex deletion

The existence part of XII (7.3), page 261, follows by first
removing selected one-vertex discs that contain edges. This keeps
the deleted drawing fixed. Its reduced radial drawing has distinct
neighbours at the deleted vertex, so the star contraction constructs
a respectful tangle and its metric. Order two uses the order-one
construction directly.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

/-- The existence part of XII (7.3), page 261: a two-cell vertex
deletion has a respectful tangle and metric of order one less. The
distance comparisons are separate assertions of (7.3). -/
theorem exists_metric_after_vertex_deletion
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hθ : 2 ≤ θ) (hd : HasTangleMetric Γ θ T d)
    {v : S} (hv : v ∈ Γ.V)
    (htwo : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsTwoCell) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ), HasTangleMetric (deleteVertices Γ {v}) (θ - 1) T' d' := by
  by_cases hθtwo : θ = 2
  · subst θ
    have ht := theorem_7_3_tangle (by decide : 2 ≤ 2) hd.1.2.1 hv
    obtain ⟨d', hd'⟩ := exists_metric_order_one hS htwo ht
    exact ⟨_, d', hd'⟩
  have hθthree : 3 ≤ θ := by omega
  obtain ⟨Γ₀, T₀, d₀, _, hv₀, hdelete, hd₀, _, hno⟩ :=
    exists_vertex_reduction hS hθ hd hv htwo
  have htwo₀ : (PaintingOrDrawing.drawing (deleteVertices Γ₀ {v})).IsTwoCell :=
    hdelete.symm ▸ htwo
  obtain ⟨K, ins, hK, hins, _⟩ := hd₀.2
  have hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g := by
    intro e he g hg u hel hgl
    by_contra heg
    have huK : u ∈ K.V := hel.2.2.1
    have hun : u ∉ Γ₀.V := (bipartite_of_preRadial hK.2.1 e v u hel).mp hv₀
    obtain ⟨r, hr, hur⟩ := hK.2.1.2.2.2.1 u ⟨huK, hun⟩
    exact no_parallel_spokes_of_no_selected_edge_inside hS hθ hd₀.1 hK.2.1 hv₀ htwo₀ hno
      he hg heg hr hur huK hel.2.2.2 hgl.2.2.2
  have hE : Γ₀.E.Nonempty := edgeSet_nonempty_of_isTangle_of_two_le hd₀.1.2.1 hθ
  have ht' := theorem_7_3_tangle hθ hd₀.1.2.1 hv₀
  have hE' : (deleteVertices Γ₀ {v}).E.Nonempty :=
    edgeSet_nonempty_of_isTangle_of_two_le ht' (by omega)
  have hvnot : v ∉ (deleteVertices Γ₀ {v}).U := by
    intro hvU
    have hvV := (isSubdrawing_U_inter_V (deleteVertices_isSubdrawing Γ₀ {v})).subset ⟨hvU, hv₀⟩
    exact ((deleteVertices_V Γ₀ {v}).subset hvV).2 rfl
  obtain ⟨r', hr', hvr'⟩ := exists_region_of_notMem hvnot
  obtain ⟨_, _, J, ins', _, _, _, _, _, _, _, _, _, hJ, hresp, hins', _⟩ :=
    exists_derivedSlope_after_radial_star_contraction hS hθ hd₀.1 hins hK hE hv₀ htwo₀ hE'
      hunique hr' hvr'
  have hm : HasTangleMetric (deleteVertices Γ₀ {v}) (θ - 1)
      (deleteVerticesTangle Γ₀.toHypergraph {v} T₀ θ)
      (tangleMetric (deleteVertices Γ₀ {v}) J ins' (θ - 1)) :=
    ⟨hresp, J, ins', hJ, hins', fun _ _ _ _ => rfl⟩
  exact ⟨_, _, hdelete ▸ hm⟩

end GraphMinor.GM12
