module

public import GraphMinor.GM12.Section3HomotopicGraphExtension
import GraphMinor.Surface.DiscGrow

/-!
# A finite graph retaining two meeting circles' homotopies

For the remaining circle-intersection case in VII Section 8, used by
XII (3.1), page 245, split the second circle into two injective paths
starting on the first circle. Extend a finite graph for the first
circle by these paths in turn, preserving their homotopies. The result
is connected, stays in the original union, and contains both rerouted
paths. No finiteness of the original circle intersection is assumed.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Two meeting circles have a connected finite graph inside their
union which contains the first circle and fixed-end reroutings of the
two arcs of the second circle. Both original path homotopies are kept. -/
theorem exists_finite_graph_of_meeting_circles_with_homotopic_paths
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsSurface S)
    {F A : Set S} (hF : IsOArc F) (hA : IsOArc A) (hmeet : (F ∩ A).Nonempty) :
    ∃ (V : Set S) (E : Set (Set S)) (x y : S) (p q r s : Path x y),
      IsGraph V E ∧ IsConnected (gr V E) ∧ x ≠ y ∧ IsTwoArcs p q ∧
      range p ∪ range q = A ∧ p.Homotopic r ∧ q.Homotopic s ∧
      F ⊆ gr V E ∧ range r ∪ range s ⊆ gr V E ∧ gr V E ⊆ F ∪ A := by
  obtain ⟨x, hxF, hxA⟩ := hmeet
  obtain ⟨y, hyA, hyx⟩ := hA.exists_ne x
  have hxy : x ≠ y := Ne.symm hyx
  obtain ⟨f, g, hfg, hf0, hf1, hfgA⟩ := hA.exists_arcs hxA hyA hxy
  let p : Path x y := {
    toFun := f
    continuous_toFun := hfg.arc_left.1
    source' := hf0
    target' := hf1 }
  let q : Path x y := {
    toFun := g
    continuous_toFun := hfg.arc_right.1
    source' := hfg.zero.trans hf0
    target' := hfg.one.trans hf1 }
  have hzero : gr (∅ : Set S) ∅ = ∅ := by simp [gr]
  have hfin : FinConn (F \ gr (∅ : Set S) ∅) := by
    rw [hzero, sdiff_empty]
    exact finConn_of_isPreconnected hF.isPreconnected
  obtain ⟨V₀, E₀, _, hG₀, hgr₀, _⟩ := isGraph_empty.add_curve hF hfin
  rw [hzero, empty_union] at hgr₀
  have hxG₀ : x ∈ gr V₀ E₀ := hgr₀.symm ▸ hxF
  obtain ⟨V₁, E₁, r, _, hG₁, hpr, hgr₁, hsub₁⟩ :=
    exists_graph_add_homotopic_arc hS hG₀ p hfg.arc_left.2 hxG₀
  have hxG₁ : x ∈ gr V₁ E₁ := hgr₁.symm ▸ Or.inl hxG₀
  obtain ⟨V₂, E₂, s, _, hG₂, hqs, hgr₂, hsub₂⟩ :=
    exists_graph_add_homotopic_arc hS hG₁ q hfg.arc_right.2 hxG₁
  have hFconn : IsConnected F := ⟨⟨x, hxF⟩, hF.isPreconnected⟩
  have hconn₁ : IsConnected (gr V₁ E₁) := by
    rw [hgr₁, hgr₀]
    exact hFconn.union ⟨x, hxF, ⟨0, r.source⟩⟩ (isConnected_range r.continuous)
  have hconn₂ : IsConnected (gr V₂ E₂) := by
    rw [hgr₂]
    exact hconn₁.union ⟨x, hxG₁, ⟨0, s.source⟩⟩ (isConnected_range s.continuous)
  have hFsub : F ⊆ gr V₂ E₂ := by
    rw [hgr₂, hgr₁, hgr₀]
    exact subset_union_left.trans subset_union_left
  have hrsub : range r ∪ range s ⊆ gr V₂ E₂ := by
    rw [hgr₂, hgr₁]
    exact union_subset (subset_union_right.trans subset_union_left) subset_union_right
  refine ⟨V₂, E₂, x, y, p, q, r, s, hG₂, hconn₂, hxy, hfg, hfgA, hpr, hqs, hFsub, hrsub, ?_⟩
  intro z hz
  rcases hsub₂ hz with hz₁ | hzq
  · rcases hsub₁ hz₁ with hz₀ | hzp
    · exact Or.inl (hgr₀ ▸ hz₀)
    · exact Or.inr (hfgA ▸ Or.inl hzp)
  · exact Or.inr (hfgA ▸ Or.inr hzq)

end GraphMinor.GM12
