module

import GraphMinor.GM12.Section75Proof

/-!
# Least cases for the order 2 step of XII (7.5)

* A triangle has no tangle of order 3. This is `false_of_cover_of_edge` in its least case: `G \ v` is one
  edge `g`, its two sides are its two ends, and each of the three sides has one edge of the triangle. In
  (7.5) this is the case where `Γ₂` is one edge and `Γ₃` is one loop, and it shows why the order 3 tangle
  in `Γ₁` excludes a loop of `Γ₃` with no small side.
* `theorem_7_5` at `θ = 3` gives a tangle of order 1.
-/

namespace GraphMinor.GM12Examples

open Set GraphMinor GraphMinor.Hypergraph GraphMinor.GM10 GraphMinor.GM12 GraphMinor.GM14

/-- The triangle on `Fin 3`. The edge `e` is opposite the vertex `e`. -/
def triangle : Hypergraph (Fin 3) (Fin 3) where
  vertexSet := univ
  edgeSet := univ
  Inc e w := w ≠ e
  vertex_mem_of_inc _ _ _ := mem_univ _
  edge_mem_of_inc _ _ _ := mem_univ _
  vertexSet_finite := finite_univ
  edgeSet_finite := finite_univ

theorem triangle_isGraph : triangle.IsGraph := by
  intro e _
  have hends : triangle.ends e = ((Finset.univ.filter fun w => w ≠ e : Finset (Fin 3)) : Set (Fin 3)) := by
    ext w
    simp [Hypergraph.ends, triangle]
  have h₁ : ∀ e : Fin 3, (Finset.univ.filter fun w => w ≠ e : Finset (Fin 3)).Nonempty := by decide
  have h₂ : ∀ e : Fin 3, (Finset.univ.filter fun w => w ≠ e : Finset (Fin 3)).card ≤ 2 := by decide
  rw [hends, ncard_coe_finset]
  exact ⟨Finset.coe_nonempty.mpr (h₁ e), h₂ e⟩

/-- The vertex `w` of `G`, with no edges, is a small side when `G` has a tangle of order 2 and `w` is not
all of `G`. -/
theorem vertex_small {G : Hypergraph (Fin 3) (Fin 3)} {T : Set (Hypergraph (Fin 3) (Fin 3) ×
    Hypergraph (Fin 3) (Fin 3))} (hT : IsTangle G 2 T) {w : Fin 3} (hw : w ∈ G.vertexSet) :
    (vertexHypergraph w, G) ∈ T := by
  have hle : (vertexHypergraph w : Hypergraph (Fin 3) (Fin 3)) ≤ G :=
    ⟨singleton_subset_iff.mpr hw, empty_subset _, fun _ h => absurd h (notMem_empty _)⟩
  have hsep : G.IsSeparation (vertexHypergraph w) G := by
    refine ⟨hle, le_refl G, ?_, ?_⟩
    · refine Hypergraph.ext (union_eq_right.mpr (singleton_subset_iff.mpr hw)) (empty_union _) ?_
      funext e x
      exact false_or _
    · exact empty_inter _
  have hord : separationOrder (vertexHypergraph w) G < 2 := by
    have hsub : (vertexHypergraph w ∩ G).vertexSet ⊆ {w} := inter_subset_left
    have := ncard_le_ncard hsub (finite_singleton w)
    rw [ncard_singleton] at this
    unfold separationOrder
    omega
  exact (hT.axiom1 hsep hord).resolve_right fun h => hT.axiom3 h rfl

/-- A triangle has no tangle of order 3. -/
theorem triangle_no_tangle (T : Set (Hypergraph (Fin 3) (Fin 3) × Hypergraph (Fin 3) (Fin 3)))
    (hT : IsTangle triangle 3 T) : False := by
  have hT' : IsTangle (triangle.deleteVertices {0}) 2 (deleteVerticesTangle triangle {0} T 3) := by
    simpa using GraphMinor.GM10.theorem_8_5_proof triangle_isGraph hT (W := {0}) (subset_univ _) (by simp)
  have hmem : ∀ w : Fin 3, w ≠ 0 → (vertexHypergraph w, triangle.deleteVertices {0}) ∈
      deleteVerticesTangle triangle {0} T 3 := fun w hw =>
    vertex_small hT' ⟨mem_univ _, hw⟩
  refine false_of_cover_of_edge triangle_isGraph hT (mem_univ 0) hT' (hmem 1 (by decide))
    (hmem 2 (by decide)) (g := 0) (mem_univ _) ?_ ?_
  · intro w _ hw
    revert hw
    fin_cases w <;> simp [vertexHypergraph]
  · intro f _ hf hg
    refine absurd ?_ hf
    change (0 : Fin 3) ≠ f
    exact fun h => hg h.symm

/-- `theorem_7_5` at `θ = 3`, the least order. -/
example {S : Type} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] (hS : Surface.IsClosedSurface S)
    (Γ : Surface.Drawing S) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (r : Set S) (hd : HasTangleMetric Γ 3 T d) (hr : r ∈ Γ.R) :
    ∃ (Γ' : Surface.Drawing S) (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r' : Set S), HasTangleMetric Γ' 1 T' d' ∧ r' ∈ Γ'.R ∧ r ⊆ r' := by
  obtain ⟨Γ', T', d', r', -, -, h, hr', hrr', -⟩ := theorem_7_5_proof S hS Γ 3 T d r le_rfl hd hr
  exact ⟨Γ', T', d', r', h, hr', hrr'⟩

end GraphMinor.GM12Examples
