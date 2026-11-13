module

public import GraphMinor.GM08.Section11Side

/-!
# The cells of a derived portrait

Let `P` be a `Q_{k-1}`-portrait derived from `(G, τ)` via `Γ` and a foundation `F_1, …, F_t`
(Graph Minors VIII, Section 11, page 272). Its cells are of two kinds, told apart by their labels.

* A cell labelled `(G_i, ψ_i)` is `Σ_i \ N'`. Its closure is `Σ_i`, its ends are `V(Γ) ∩ F_i`, and
  `G_i` is the part of `G` drawn in `Σ_i` (`IsDerivedPortraitVia.ring_cell`).
* A cell labelled `*` contains a unique edge `e` of `Γ_0`, and its ends are the ends of `e`
  (`IsDerivedPortraitVia.edge_cell`).
-/

public section

namespace GraphMinor
namespace GM08

open Set Topology Surface Graph

universe u u' v'

variable {S : Type u} [TopologicalSpace S] {α : Type u'} {β : Type v'}

/-- `R` is the part `(G_i, ψ_i)` of `(G, τ)` drawn in the disc `Σ_i = F_i ∪ ins F_i`, rooted by the
list `μ` of the vertices on `F_i`. -/
@[expose] def IsRingGraph (X : RootedGraph α β) (gd : GraftDrawing X.G X.toGraft.T S) (F : Set S)
    (R : RootedGraph α β) (μ : List S) : Prop :=
  R.G ≤ X.G ∧
  V(R.G) = {v : α | ∃ hv : v ∈ V(X.G),
    (gd.iso.vertexEquiv ⟨v, hv⟩).1 ∈ gd.drawing.V ∩ (F ∪ insideSet F)} ∧
  E(R.G) = {e : β | ∃ he : e ∈ E(X.G),
    (gd.iso.edgeEquiv ⟨e, he⟩).1 ∈ edgesInsideOArc gd.drawing univ F} ∧
  μ.Nodup ∧ {x : S | x ∈ μ} = gd.drawing.V ∩ F ∧ R.τ.length = μ.length ∧
  ∀ (n : ℕ) (hn : n < R.τ.length) (hn' : n < μ.length),
    ∃ hv : R.τ[n] ∈ V(X.G), (gd.iso.vertexEquiv ⟨R.τ[n], hv⟩).1 = μ[n]

variable {k : ℕ} {X : RootedGraph α β} {gd : GraftDrawing X.G X.toGraft.T S} {t : ℕ}
  {F : Fin t → Set S} {P : QPortrait (QKElem α β S ((k : ℤ) - 1)) S}

theorem IsDerivedPortraitVia.foundation (hP : IsDerivedPortraitVia X gd F P) :
    IsFoundation gd.drawing univ F :=
  hP.2.2.2.1

theorem IsDerivedPortraitVia.nodes (hP : IsDerivedPortraitVia X gd F P) :
    P.painting.N = ringNodes gd.drawing F := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hN, -⟩ := hP
  exact hN

/-- The roots of `(G, τ)` are drawn at the list `α` of the portrait. -/
theorem IsDerivedPortraitVia.roots (hP : IsDerivedPortraitVia X gd F P) :
    P.α.length = X.τ.length ∧ ∀ (n : ℕ) (hn : n < X.τ.length) (hn' : n < P.α.length),
      (gd.iso.vertexEquiv ⟨X.τ[n], X.τ_subset _ (List.getElem_mem _)⟩).1 = P.α[n] :=
  ⟨hP.2.2.2.2.1, hP.2.2.2.2.2.1⟩

/-- The cells of `P` are pairwise equal or disjoint, and they miss `N'`. -/
theorem IsDerivedPortraitVia.cells_disjoint {c c' : Set S} (hc : c ∈ P.painting.cells)
    (hc' : c' ∈ P.painting.cells) : c = c' ∨ Disjoint c c' :=
  eq_or_disjoint_of_mem_componentsIn hc hc'

theorem PaintingInDisc.cell_subset {Pt : PaintingInDisc S} {c : Set S} (hc : c ∈ Pt.cells) :
    c ⊆ Pt.U \ Pt.N := by
  obtain ⟨x, -, rfl⟩ := hc
  exact connectedComponentIn_subset _ _

/-- A cell labelled `(G_i, ψ_i)` is `Σ_i \ N'`. -/
theorem IsDerivedPortraitVia.ring_cell (hP : IsDerivedPortraitVia X gd F P) {c : Set S}
    (hc : c ∈ P.painting.cells) {y : discRootedClassA (α := α) (β := β) S ((k : ℤ) - 1)}
    (hy : P.φ c = some y) :
    ∃ i, c = (F i ∪ insideSet (F i)) \ ringNodes gd.drawing F ∧
      closure c = F i ∪ insideSet (F i) ∧ IsRingGraph X gd (F i) y.1 (P.μ c) := by
  obtain ⟨-, -, -, -, -, -, α_ring, G_sub, hG_sub, D_edge, hring, -, -, -, hcells, hdisc,
    hedge'⟩ := hP
  rw [hcells] at hc
  rcases hc with ⟨i, rfl⟩ | ⟨e, he, rfl⟩
  · refine ⟨i, rfl, (hdisc i).1, ?_⟩
    have hφ := (hdisc i).2.2
    rw [hφ] at hy
    cases hy
    obtain ⟨hnd, hset, hle, hV, hE, hlen, hroot⟩ := hring i
    rw [(hdisc i).2.1]
    exact ⟨hle, hV, hE, hnd, hset, hlen, hroot⟩
  · rw [(hedge' e he).2] at hy
    cases hy

/-- Each ring gives a cell labelled by its part of `(G, τ)`. -/
theorem IsDerivedPortraitVia.ring_cell_mem (hP : IsDerivedPortraitVia X gd F P) (i : Fin t) :
    (F i ∪ insideSet (F i)) \ ringNodes gd.drawing F ∈ P.painting.cells ∧
      closure ((F i ∪ insideSet (F i)) \ ringNodes gd.drawing F) = F i ∪ insideSet (F i) ∧
      ∃ y, P.φ ((F i ∪ insideSet (F i)) \ ringNodes gd.drawing F) = some y := by
  obtain ⟨-, -, -, -, -, -, α_ring, G_sub, hG_sub, D_edge, -, -, -, -, hcells, hdisc, -⟩ := hP
  refine ⟨?_, (hdisc i).1, _, (hdisc i).2.2⟩
  rw [hcells]
  exact Or.inl ⟨i, rfl⟩

/-- A cell labelled `*` contains a unique edge `e` of `Γ_0`, and its ends are the ends of `e`. -/
theorem IsDerivedPortraitVia.edge_cell (hS : IsClosedDisc (univ : Set S))
    (hP : IsDerivedPortraitVia X gd F P) {c : Set S}
    (hc : c ∈ P.painting.cells) (hy : P.φ c = none) :
    ∃ e ∈ ringEdges gd.drawing F, e ⊆ c ∧ closure c ∩ gd.drawing.U = closure e ∧
      closure c \ c = closure e ∩ gd.drawing.V := by
  have hF := hP.foundation
  obtain ⟨-, -, -, -, -, -, α_ring, G_sub, hG_sub, D_edge, -, hedge, hN, -, hcells, hdisc,
    hedge'⟩ := hP
  rw [hcells] at hc
  rcases hc with ⟨i, rfl⟩ | ⟨e, he, rfl⟩
  · rw [(hdisc i).2.2] at hy
    cases hy
  · obtain ⟨-, heD, hDU, -, -⟩ := hedge e he
    have hcl := (hedge' e he).1
    refine ⟨e, he, fun x hx => ⟨heD hx, fun hxN => ?_⟩, ?_, ?_⟩
    · exact (he.1.2.1 hx).2 hxN.1
    · rw [hcl]; exact hDU
    · rw [hcl]
      ext x
      constructor
      · rintro ⟨hxD, hxc⟩
        have hxN : x ∈ ringNodes gd.drawing F := by
          by_contra h
          exact hxc ⟨hxD, h⟩
        refine ⟨?_, hxN.1⟩
        rw [← hDU]
        exact ⟨hxD, gd.drawing.V_subset_U hxN.1⟩
      · rintro ⟨hxe, hxV⟩
        have hxD : x ∈ D_edge e := (hDU.symm ▸ hxe : x ∈ D_edge e ∩ gd.drawing.U).1
        exact ⟨hxD, fun h => h.2 (hF.ends_subset_nodes hS he ⟨hxe, hxV⟩)⟩

/-- Each edge of `Γ_0` lies in a cell labelled `*`. -/
theorem IsDerivedPortraitVia.edge_cell_mem (hP : IsDerivedPortraitVia X gd F P) {e : Set S}
    (he : e ∈ ringEdges gd.drawing F) :
    ∃ c ∈ P.painting.cells, P.φ c = none ∧ e ⊆ c := by
  obtain ⟨-, -, -, -, -, -, α_ring, G_sub, hG_sub, D_edge, -, hedge, hN, -, hcells, hdisc,
    hedge'⟩ := hP
  refine ⟨D_edge e \ ringNodes gd.drawing F, ?_, (hedge' e he).2, fun x hx =>
    ⟨(hedge e he).2.1 hx, fun hxN => (he.1.2.1 hx).2 hxN.1⟩⟩
  rw [hcells]
  exact Or.inr ⟨e, he, rfl⟩

/-- An edge of `Γ` in a cell labelled `*` is the edge of that cell. -/
theorem eq_of_subset_closure_inter {Γ : Drawing S} {c e₁ e₂ : Set S} (he₁ : e₁ ∈ Γ.E)
    (he₂ : e₂ ∈ Γ.E) (h₁ : e₁ ⊆ c) (h₂ : closure c ∩ Γ.U = closure e₂) : e₁ = e₂ := by
  obtain ⟨x, hx⟩ := he₁.1
  have hx2 : x ∈ closure e₂ := by
    rw [← h₂]
    exact ⟨subset_closure (h₁ hx), (he₁.2.1 hx).1⟩
  have hx3 : x ∈ e₂ := by
    rw [← Γ.closure_diff_V he₂]
    exact ⟨hx2, (he₁.2.1 hx).2⟩
  exact Γ.edge_eq_of_mem he₁ he₂ hx hx3

end GM08
end GraphMinor
