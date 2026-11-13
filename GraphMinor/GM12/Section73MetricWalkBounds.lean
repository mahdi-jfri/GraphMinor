module

public import GraphMinor.GM12.Section73WalkInside
import GraphMinor.GM12.Section73HubInside
import GraphMinor.GM12.Section73WalkLiftEdges
import GraphMinor.GM12.Section4WalkMetric
import GraphMinor.GM14.Section7a

/-!
# Metric bounds from a chosen new walk

For XII (7.3), page 262, lift a short new walk. Its length grows
by twice the number of merged-hub visits. The proved inside
containment transfers intersections with atoms outside the merged
region. The separate hub assertion transfers the deleted vertex
when the new inside contains the region hub. The definition of
the old radial metric now bounds its distance by half the lifted
length. Selecting new walks with the visit bounds is a separate
use of XI (9.2).
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM10 GM14 Hypergraph

/-- The walk inequality used in XII (7.3)(i), page 262. For atoms
outside the merged region, half the lifted walk length bounds the
old metric. The hub-visit count is recorded without an assumed
metric-witness selection step. -/
theorem two_mul_metric_le_lifted_walk_length
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    {v : S} {ins ins' : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hins' : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins')
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J)
    {B : Set S} (hB : IsClosedDisc B) (hBr : B ⊆ r')
    (hAB : ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ⊆ discInt B)
    (hfixB : ∀ x ∉ discInt B, f x = x)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {a₀ b₀ : Set S} (ha : a₀ ∈ Γ.A) (hb : b₀ ∈ Γ.A)
    (haDis : Disjoint a₀ r') (hbDis : Disjoint b₀ r')
    {a : S} (W : GraphWalk J.toGraph a a)
    (hWshort : W.length < 2 * (θ - 1))
    (hliftshort : W.length + 2 * walkVertexCount v W < 2 * θ)
    (haMeet : (a₀ ∩ insWalk ins' J W).Nonempty)
    (hbMeet : (b₀ ∩ insWalk ins' J W).Nonempty) :
    2 * tangleMetric Γ K ins θ a₀ b₀ ≤ W.length + 2 * walkVertexCount v W := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨W', hlen, _, hpoints, hedges⟩ := exists_closed_walk_lift_with_edges hS hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV hJE hJ.2.1 hunique W
  have hshort : W'.length < 2 * θ := hlen ▸ hliftshort
  have hinside := theorem_7_3_claim_1_short_walk hS hθ hT hins hins' hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV hJE hJ hB hBr hAB hfixB W W' hWshort hpoints hedges
  have transfer : ∀ z : Set S, Disjoint z r' → (z ∩ insWalk ins' J W).Nonempty →
      (z ∩ insWalk ins K W').Nonempty := by
    intro z hz hmeet
    obtain ⟨x, hxz, hxInside⟩ := hmeet
    exact ⟨x, hxz, (hinside hxInside).resolve_right (fun hxr => disjoint_left.mp hz hxz hxr)⟩
  obtain ⟨a', hca, _⟩ := existsUnique_correspondingAtom' hK ha
  obtain ⟨b', hcb, _⟩ := existsUnique_correspondingAtom' hK hb
  have haW : a' ⊆ insWalk ins K W' :=
    (corresponding_atom_subset_iff hS hK hins hca W' hshort).mpr (transfer a₀ haDis haMeet)
  have hbW : b' ⊆ insWalk ins K W' :=
    (corresponding_atom_subset_iff hS hK hins hcb W' hshort).mpr (transfer b₀ hbDis hbMeet)
  have hbound := two_mul_tangleMetric_le_walk_length hK hca hcb W' hshort haW hbW
  exact hlen ▸ hbound

/-- The walk inequality used in XII (7.3)(ii), page 262. If the
new inside contains the merged hub, the old inside contains the
deleted vertex, so the same lifted-length bound applies. -/
theorem two_mul_metric_to_deleted_vertex_le_lifted_walk_length
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hθ : 2 ≤ θ) (hT : IsTangle Γ.toHypergraph θ T)
    {v : S} {ins ins' : Drawing S → Set S}
    (hins : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hins' : IsDerivedSlope (PaintingOrDrawing.drawing (deleteVertices Γ {v})) J (θ - 1)
      (deleteVerticesTangle Γ.toHypergraph {v} T θ) ins')
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J)
    {B : Set S} (hB : IsClosedDisc B) (hBr : B ⊆ r')
    (hAB : ({v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ⊆ discInt B)
    (hfixB : ∀ x ∉ discInt B, f x = x)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {a₀ : Set S} (ha : a₀ ∈ Γ.A) (haDis : Disjoint a₀ r')
    {a : S} (W : GraphWalk J.toGraph a a)
    (hWshort : W.length < 2 * (θ - 1))
    (hliftshort : W.length + 2 * walkVertexCount v W < 2 * θ)
    (haMeet : (a₀ ∩ insWalk ins' J W).Nonempty) (hvInside : v ∈ insWalk ins' J W) :
    2 * tangleMetric Γ K ins θ a₀ {v} ≤ W.length + 2 * walkVertexCount v W := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨W', hlen, _, hpoints, hedges⟩ := exists_closed_walk_lift_with_edges hS hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV hJE hJ.2.1 hunique W
  have hshort : W'.length < 2 * θ := hlen ▸ hliftshort
  have hinside := theorem_7_3_claim_1_short_walk hS hθ hT hins hins' hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV hJE hJ hB hBr hAB hfixB W W' hWshort hpoints hedges
  have hvOld := hub_mem_inside_lifted_walk hS hθ hT hins hins' hK hE hv hr' hvr'
    f hfix hcollapse hfibre hJV hJE hJ W W' hWshort hpoints hedges hvInside
  obtain ⟨a', hca, _⟩ := existsUnique_correspondingAtom' hK ha
  have hcv : IsCorrespondingAtom Γ K {v} {v} :=
    ⟨Or.inl (Or.inl ⟨v, hv, rfl⟩), Or.inl (Or.inl ⟨v, hK.2.1.2.1 hv, rfl⟩),
      Or.inl ⟨v, hv, rfl, rfl⟩⟩
  obtain ⟨x, hxa, hxInside⟩ := haMeet
  have haOld : (a₀ ∩ insWalk ins K W').Nonempty :=
    ⟨x, hxa, (hinside hxInside).resolve_right (fun hxr => disjoint_left.mp haDis hxa hxr)⟩
  have haW : a' ⊆ insWalk ins K W' :=
    (corresponding_atom_subset_iff hS hK hins hca W' hshort).mpr haOld
  have hvW : ({v} : Set S) ⊆ insWalk ins K W' := singleton_subset_iff.mpr hvOld
  have hbound := two_mul_tangleMetric_le_walk_length hK hca hcv W' hshort haW hvW
  exact hlen ▸ hbound

end GraphMinor.GM12
