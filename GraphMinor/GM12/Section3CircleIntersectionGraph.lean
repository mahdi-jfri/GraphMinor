module

public import GraphMinor.Surface.SurfaceGraph

/-!
# Circle intersections inside a finite graph

For the finite graph reduction used by XII (3.1), page 245, a circle
contains each edge it meets away from the vertices. Thus the intersection
of two circles in a finite graph is itself a finite graph: retain the
common vertices and the edges included in both circles. This supplies
finite edge data even when the original circles had an arbitrary
intersection before the homotopy-preserving reduction.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The intersection of two circles in a finite graph is the carrier
of the graph formed by their common vertices and common whole edges. -/
theorem isGraph_circle_intersection
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hG : IsGraph V E)
    {F A : Set S} (hF : IsOArc F) (hA : IsOArc A)
    (hFG : F ⊆ gr V E) (hAG : A ⊆ gr V E) :
    IsGraph (V ∩ (F ∩ A)) {e ∈ E | e ⊆ F ∧ e ⊆ A} ∧
      gr (V ∩ (F ∩ A)) {e ∈ E | e ⊆ F ∧ e ⊆ A} = F ∩ A := by
  constructor
  · refine ⟨hG.fin.subset inter_subset_left,
      hG.fine.subset (fun _ he => he.1), ?_, ?_⟩
    · intro e he
      obtain ⟨u, v, huv, hL, hends⟩ := hG.edge e he.1
      refine ⟨u, v, huv, hL, ?_⟩
      have hu : u ∈ e ∩ V := hends.symm ▸ (by simp)
      have hv : v ∈ e ∩ V := hends.symm ▸ (by simp)
      ext x
      constructor
      · rintro ⟨hxe, hxV, _⟩
        exact hends ▸ (show x ∈ e ∩ V from ⟨hxe, hxV⟩)
      · intro hx
        have hxeV : x ∈ e ∩ V := hends.symm ▸ hx
        exact ⟨hxeV.1, hxeV.2, he.2.1 hxeV.1, he.2.2 hxeV.1⟩
    · intro e he f hf hne x hx
      exact ⟨hG.disj e he.1 f hf.1 hne hx, he.2.1 hx.1, he.2.2 hx.1⟩
  · ext x
    constructor
    · rintro (hx | ⟨e, he, hxe⟩)
      · exact hx.2
      · exact ⟨he.2.1 hxe, he.2.2 hxe⟩
    · intro hx
      by_cases hxV : x ∈ V
      · exact Or.inl ⟨hxV, hx⟩
      · obtain hxV' | ⟨e, he, hxe⟩ := hFG hx.1
        · exact (hxV hxV').elim
        · have heF : e ⊆ F := by
            rcases hG.edge_or hF hFG he with hs | hd
            · exact hs
            · exact (Set.disjoint_left.mp hd ⟨hxe, hxV⟩ hx.1).elim
          have heA : e ⊆ A := by
            rcases hG.edge_or hA hAG he with hs | hd
            · exact hs
            · exact (Set.disjoint_left.mp hd ⟨hxe, hxV⟩ hx.2).elim
          exact Or.inr ⟨e, ⟨he, heF, heA⟩, hxe⟩

/-- A finite graph carrier is a finite union of preconnected sets:
each edge is an interval image and each remaining vertex is a singleton. -/
theorem finConn_gr_of_isGraph
    {S : Type*} [TopologicalSpace S]
    {V : Set S} {E : Set (Set S)} (hG : IsGraph V E) : FinConn (gr V E) := by
  refine ⟨E ∪ (fun x : S => ({x} : Set S)) '' V,
    hG.fine.union (hG.fin.image _), ?_, ?_⟩
  · rintro J (hJ | ⟨x, _, rfl⟩)
    · obtain ⟨u, v, _, hL, _⟩ := hG.edge J hJ
      obtain ⟨e, _, _⟩ := hL
      have heq : range (fun t : unitInterval => (e t).val) = J := by
        ext x
        constructor
        · rintro ⟨t, rfl⟩
          exact (e t).property
        · intro hx
          exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
      rw [← heq]
      exact (isConnected_range (continuous_subtype_val.comp e.continuous)).isPreconnected
    · exact isPreconnected_singleton
  · ext x
    constructor
    · rintro ⟨J, hJ | ⟨y, hy, rfl⟩, hx⟩
      · exact Or.inr ⟨J, hJ, hx⟩
      · exact Or.inl ((mem_singleton_iff.mp hx) ▸ hy)
    · rintro (hx | ⟨J, hJ, hx⟩)
      · exact ⟨{x}, Or.inr ⟨x, hx, rfl⟩, rfl⟩
      · exact ⟨J, Or.inl hJ, hx⟩

/-- Two circles in one finite graph meet in finitely many connected
pieces, by their common-edge graph presentation. -/
theorem finConn_circle_intersection_of_isGraph
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hG : IsGraph V E)
    {F A : Set S} (hF : IsOArc F) (hA : IsOArc A)
    (hFG : F ⊆ gr V E) (hAG : A ⊆ gr V E) : FinConn (F ∩ A) := by
  obtain ⟨hI, heq⟩ := isGraph_circle_intersection hG hF hA hFG hAG
  exact heq ▸ finConn_gr_of_isGraph hI

end GraphMinor.GM12
