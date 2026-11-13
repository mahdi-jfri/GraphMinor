module

public import GraphMinor.Compute.Algorithm99TransportSociety

/-!
# Transport of rural societies, rural divisions and branch-decompositions

A society is rural (Graph Minors IX, Section 1, page 42; Section 2, page 45) if its graph has a
drawing in a closed disc with the vertices of `Ω̄` on the boundary, in the order of `Ω`. A division
`𝒜` of a society is rural (Graph Minors XIII, Section 8, page 96) if the bipartite graph of
members and boundary vertices gives a rural society. Step (5) of Algorithm (9.9) needs this notion
in the labels of `G`, and finds it in the labels of the renumbered `G_i`.

A drawing of `G` is also a drawing of the renamed graph: the drawing is the same, and only the
isomorphism to its abstract graph changes (`relabelGraphDrawing`). The point that represents a
renamed vertex `f v` is the point that represented `v` (`graphDrawingVertexSet_relabelGraphDrawing`).
So a rural neighborhood renames to a rural neighborhood (`Neighborhood.IsRural.relabel`), and a
rural society to a rural society (`Society.IsRuralSociety.relabel`).

For a division, the bipartite graph of the renamed division is the renaming of the bipartite graph,
along `A ↦ relabelGraph f g A` on members and `f` on vertices (`divisionBipartiteGraph_relabelSociety`).
This gives `IsRuralDivision.relabel`.

Last, a branch-decomposition `(T, τ)` of `A` gives the branch-decomposition `(T, τ')` of the
renamed graph, for every `τ'` with `τ' (g e) = τ e`, of the same width
(`isGraphBranchDecomposition_relabelGraph_iff`, `graphBranchDecompWidth_relabelGraph`).
-/

@[expose] public section

namespace GraphMinor.Transport

open Graph Function Set GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM14 GraphMinor.GM13

universe u u' v v' w

variable {α : Type u} {α' : Type u'} {β : Type v} {β' : Type v'}
variable (f : α ↪ α') (g : β ↪ β')

/-! ### Drawings -/

private theorem image_symm_apply_mk {γ γ' : Type*} (k : γ ↪ γ') (s : Set γ) (x : γ) (hx : x ∈ s)
    (h : k x ∈ k '' s) : (Equiv.Set.image k s k.injective).symm ⟨k x, h⟩ = ⟨x, hx⟩ :=
  (Equiv.symm_apply_eq _).2 rfl

/-- A drawing of `G` seen as a drawing of the renamed graph. -/
noncomputable def relabelGraphDrawing {S : Type w} [TopologicalSpace S] {G : Graph α β}
    (Γ : GraphDrawing G S) : GraphDrawing (relabelGraph f g G) S where
  drawing := Γ.drawing
  iso :=
    { vertexEquiv := (Equiv.Set.image f V(G) f.injective).symm.trans Γ.iso.vertexEquiv
      edgeEquiv := (Equiv.Set.image g E(G) g.injective).symm.trans Γ.iso.edgeEquiv
      isLink_iff := by
        rintro ⟨_, e, he, rfl⟩ ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩
        convert (relabelGraph_isLink_apply f g).trans
          (Γ.iso.isLink_iff ⟨e, he⟩ ⟨x, hx⟩ ⟨y, hy⟩) using 3 <;>
        first
          | exact congrArg Γ.iso.edgeEquiv (image_symm_apply_mk g _ e he _)
          | exact congrArg Γ.iso.vertexEquiv (image_symm_apply_mk f _ x hx _)
          | exact congrArg Γ.iso.vertexEquiv (image_symm_apply_mk f _ y hy _) }

@[simp]
theorem relabelGraphDrawing_drawing {S : Type w} [TopologicalSpace S] {G : Graph α β}
    (Γ : GraphDrawing G S) : (relabelGraphDrawing f g Γ).drawing = Γ.drawing := rfl

theorem graphDrawingVertexSet_relabelGraphDrawing {S : Type w} [TopologicalSpace S]
    {G : Graph α β} (Γ : GraphDrawing G S) (x : α) :
    graphDrawingVertexSet (relabelGraphDrawing f g Γ) (f x) = graphDrawingVertexSet Γ x := by
  unfold graphDrawingVertexSet
  ext p
  constructor
  · rintro ⟨hx, rfl⟩
    have hx' : x ∈ V(G) := (mem_vertexSet_relabelGraph_apply f g).1 hx
    refine ⟨hx', ?_⟩
    change _ = (Γ.iso.vertexEquiv ((Equiv.Set.image f V(G) f.injective).symm ⟨f x, hx⟩)).1
    congr 2
    exact ((Equiv.symm_apply_eq _).2 rfl).symm
  · rintro ⟨hx, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    change (Γ.iso.vertexEquiv ((Equiv.Set.image f V(G) f.injective).symm ⟨f x, _⟩)).1 = _
    congr 2
    exact (Equiv.symm_apply_eq _).2 rfl

theorem drawingAgreesWithOArcHomeo_relabel {S : Type w} [TopologicalSpace S] {G : Graph α β}
    (Γ : GraphDrawing G S) (Ω : CyclicPerm α) (C : Set S) (φ : Circle ≃ₜ C)
    (h : DrawingAgreesWithOArcHomeo Γ Ω C φ) :
    DrawingAgreesWithOArcHomeo (relabelGraphDrawing f g Γ) (relabelCyclicPerm f Ω) C φ := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [graphDrawingVertexSet_relabelGraphDrawing]
    exact h.1 x hx
  · intro v₁ v₂ v₃ hc
    obtain ⟨w₁, w₂, w₃, rfl, rfl, rfl, hc'⟩ := exists_of_isClockwise3_relabelCyclicPerm f Ω hc
    simp only [graphDrawingVertexSet_relabelGraphDrawing]
    exact h.2 w₁ w₂ w₃ hc'

/-- A rural neighborhood renames to a rural neighborhood. -/
theorem Neighborhood.IsRural.relabel {N : Neighborhood α β} (h : N.IsRural)
    (hV : V(relabelGraph f g N.G).Finite) (hE : E(relabelGraph f g N.G).Finite)
    (hb : (relabelCyclicPerm f N.Ω).bar ⊆ V(relabelGraph f g N.G))
    (hb₀ : (relabelCyclicPerm f N.Ω₀).bar ⊆ V(relabelGraph f g N.G)) :
    (Neighborhood.mk (relabelGraph f g N.G) (relabelCyclicPerm f N.Ω) (relabelCyclicPerm f N.Ω₀)
      hV hE hb hb₀).IsRural := by
  obtain ⟨Γ, Δ, Δ₀, hΔ, hsub, hU, hbd, hbd₀, ⟨φ, hφ, hag⟩, hinner⟩ := h
  refine ⟨relabelGraphDrawing f g Γ, Δ, Δ₀, hΔ, hsub, hU, ?_, ?_, ⟨φ, hφ, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [graphDrawingVertexSet_relabelGraphDrawing, relabelCyclicPerm_bar,
      f.injective.mem_set_image]
    exact hbd x hx
  · rintro _ ⟨x, hx, rfl⟩
    rw [graphDrawingVertexSet_relabelGraphDrawing, relabelCyclicPerm_bar,
      f.injective.mem_set_image]
    exact hbd₀ x hx
  · exact drawingAgreesWithOArcHomeo_relabel f g Γ N.Ω _ φ hag
  · rcases hinner with ⟨h₁, h₂⟩ | ⟨h₁, φ₀, hφ₀, hag₀⟩
    · refine Or.inl ⟨h₁, ?_⟩
      change f '' N.Ω₀.bar = ∅
      rw [h₂, Set.image_empty]
    · exact Or.inr ⟨h₁, φ₀, hφ₀, drawingAgreesWithOArcHomeo_relabel f g Γ N.Ω₀ _ φ₀ hag₀⟩

/-- A society whose graph and cyclic order are renamings of those of a rural society is rural. -/
theorem Society.IsRuralSociety.relabel {S₀ : Society α β} {S₁ : Society α' β'}
    (hG : S₁.G = relabelGraph f g S₀.G) (hΩ : S₁.Ω = relabelCyclicPerm f S₀.Ω)
    (h : S₀.IsRuralSociety) : S₁.IsRuralSociety := by
  obtain ⟨Ω₀, h₀, hempty, hN⟩ := h
  obtain ⟨G₁, Ω₁, hV₁, hE₁, hb₁⟩ := S₁
  simp only at hG hΩ
  subst hG hΩ
  refine ⟨relabelCyclicPerm f Ω₀, Set.image_mono h₀, by rw [relabelCyclicPerm_bar, hempty,
    Set.image_empty], ?_⟩
  exact Neighborhood.IsRural.relabel f g hN _ _ _ _

/-! ### The bipartite graph of a division -/

/-- Renaming of graphs, as an embedding. -/
def relabelGraphEmb : Graph α β ↪ Graph α' β' :=
  ⟨relabelGraph f g, relabelGraph_injective f g⟩

@[simp] theorem relabelGraphEmb_apply (A : Graph α β) :
    relabelGraphEmb f g A = relabelGraph f g A := rfl

/-- The vertex renaming of the bipartite graph: members by `relabelGraph f g`, vertices by `f`. -/
def bipartiteVertexEmb : Graph α β ⊕ α ↪ Graph α' β' ⊕ α' :=
  (relabelGraphEmb f g).sumMap f

/-- The edge renaming of the bipartite graph. -/
def bipartiteEdgeEmb : Graph α β × α ↪ Graph α' β' × α' :=
  (relabelGraphEmb f g).prodMap f

/-- The bipartite graph of a renamed division is the renamed bipartite graph. -/
theorem divisionBipartiteGraph_relabelSociety (S : Society α β) (𝒜 : Set (Graph α β)) :
    divisionBipartiteGraph (relabelSociety f g S) (relabelGraph f g '' 𝒜) =
      relabelGraph (bipartiteVertexEmb f g) (bipartiteEdgeEmb f g)
        (divisionBipartiteGraph S 𝒜) := by
  refine Graph.ext ?_ ?_
  · change Sum.inl '' (relabelGraph f g '' 𝒜) ∪
        Sum.inr '' (divTotalBoundary (relabelSociety f g S) (relabelGraph f g '' 𝒜) ∪
          f '' S.Ω.bar) =
      bipartiteVertexEmb f g '' (Sum.inl '' 𝒜 ∪ Sum.inr '' (divTotalBoundary S 𝒜 ∪ S.Ω.bar))
    rw [divTotalBoundary_relabelSociety]
    simp only [Set.image_union, Set.image_image]
    rfl
  · rintro ⟨A', a'⟩ x' y'
    constructor
    · rintro ⟨⟨A, hA, rfl⟩, hb, hxy⟩
      rw [divBoundary_relabelSociety] at hb
      obtain ⟨a, ha, rfl⟩ := hb
      refine ⟨(A, a), ?_⟩
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Sum.inl A, Sum.inr a, ⟨hA, ha, Or.inl ⟨rfl, rfl⟩⟩, rfl, rfl, rfl⟩
      · exact ⟨Sum.inr a, Sum.inl A, ⟨hA, ha, Or.inr ⟨rfl, rfl⟩⟩, rfl, rfl, rfl⟩
    · rintro ⟨⟨A, a⟩, x, y, ⟨hA, ha, hxy⟩, hp, rfl, rfl⟩
      simp only [bipartiteEdgeEmb, Embedding.coe_prodMap, Prod.map, relabelGraphEmb_apply,
        Prod.mk.injEq] at hp
      obtain ⟨rfl, rfl⟩ := hp
      refine ⟨⟨A, hA, rfl⟩, ?_, ?_⟩
      · rw [divBoundary_relabelSociety]
        exact ⟨a, ha, rfl⟩
      · rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩

open Classical in
/-- The cyclic order lifted to the bipartite graph commutes with renaming. -/
theorem liftCyclicPermInr_relabelCyclicPerm (Ω : CyclicPerm α) :
    liftCyclicPermInr (γ := Graph α' β') (relabelCyclicPerm f Ω) =
      relabelCyclicPerm (bipartiteVertexEmb f g) (liftCyclicPermInr (γ := Graph α β) Ω) := by
  refine cyclicPerm_ext ?_ ?_
  · change Sum.inr '' (f '' Ω.bar) = bipartiteVertexEmb f g '' (Sum.inr '' Ω.bar)
    rw [Set.image_image, Set.image_image]
    rfl
  · funext x'
    change _ = relabelPermFun (bipartiteVertexEmb f g) _ x'
    by_cases hx : x' ∈ Set.range (bipartiteVertexEmb f g)
    · obtain ⟨x, rfl⟩ := hx
      rw [relabelPermFun_apply]
      rcases x with A | a
      · rfl
      · change Sum.inr (relabelPermFun f Ω (f a)) = _
        rw [relabelPermFun_apply]
        rfl
    · unfold relabelPermFun
      rw [dite_eq_right_iff.2 (fun h => absurd h hx)]
      rcases x' with A' | a'
      · rfl
      · change Sum.inr (relabelPermFun f Ω a') = Sum.inr a'
        have ha : a' ∉ Set.range f := by
          rintro ⟨a, rfl⟩
          exact hx ⟨Sum.inr a, rfl⟩
        unfold relabelPermFun
        rw [dite_eq_right_iff.2 (fun h => absurd h ha)]

/-- A rural division renames to a rural division of the renamed society. -/
theorem IsRuralDivision.relabel {S : Society α β} {𝒜 : Set (Graph α β)}
    (h : IsRuralDivision S 𝒜) :
    IsRuralDivision (relabelSociety f g S) (relabelGraph f g '' 𝒜) := by
  refine ⟨IsSocietyDivision.relabel f g h.isDivision, h.finite_𝒜.image _, ?_⟩
  obtain ⟨hV, hE, hbar, hR⟩ := h.isRuralBipartite
  have hG := divisionBipartiteGraph_relabelSociety f g S 𝒜
  have hΩ := liftCyclicPermInr_relabelCyclicPerm f g S.Ω
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hG]
    exact hV.image _
  · rw [hG]
    exact hE.image _
  · change (liftCyclicPermInr (relabelCyclicPerm f S.Ω)).bar ⊆ _
    rw [hG, hΩ]
    exact Set.image_mono hbar
  · exact Society.IsRuralSociety.relabel (bipartiteVertexEmb f g) (bipartiteEdgeEmb f g)
      (S₀ := Society.mk (divisionBipartiteGraph S 𝒜) (liftCyclicPermInr S.Ω) hV hE hbar) hG hΩ hR

/-! ### Branch-decompositions -/

theorem bijOn_relabelGraph_iff {ι : Type*} {A : Graph α β} {L : Set ι} {τ : β → ι}
    {τ' : β' → ι} (hτ : ∀ e, τ' (g e) = τ e) :
    Set.BijOn τ' E(relabelGraph f g A) L ↔ Set.BijOn τ E(A) L := by
  rw [edgeSet_relabelGraph]
  constructor
  · rintro ⟨hm, hi, hs⟩
    refine ⟨fun e he => hτ e ▸ hm ⟨e, he, rfl⟩, fun e₁ he₁ e₂ he₂ h => ?_, fun l hl => ?_⟩
    · rw [← hτ, ← hτ] at h
      exact g.injective (hi ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, rfl⟩ h)
    · obtain ⟨_, ⟨e, he, rfl⟩, rfl⟩ := hs hl
      exact ⟨e, he, (hτ e).symm⟩
  · rintro ⟨hm, hi, hs⟩
    refine ⟨?_, ?_, fun l hl => ?_⟩
    · rintro _ ⟨e, he, rfl⟩
      rw [hτ]
      exact hm he
    · rintro _ ⟨e₁, he₁, rfl⟩ _ ⟨e₂, he₂, rfl⟩ h
      rw [hτ, hτ] at h
      rw [hi he₁ he₂ h]
    · obtain ⟨e, he, rfl⟩ := hs hl
      exact ⟨g e, ⟨e, he, rfl⟩, hτ e⟩

/-- `(T, τ')` is a branch-decomposition of the renamed graph if and only if `(T, τ)` is one of
`A`, when `τ' (g e) = τ e` for every edge name `e`. -/
theorem isGraphBranchDecomposition_relabelGraph_iff {ι : Type*} [Fintype ι] {A : Graph α β}
    {T : SimpleGraph ι} {τ : β → ι} {τ' : β' → ι} (hτ : ∀ e, τ' (g e) = τ e) :
    IsGraphBranchDecomposition (relabelGraph f g A) T τ' ↔ IsGraphBranchDecomposition A T τ := by
  constructor
  · rintro ⟨ht, hb⟩
    exact ⟨ht, (bijOn_relabelGraph_iff f g hτ).1 hb⟩
  · rintro ⟨ht, hb⟩
    exact ⟨ht, (bijOn_relabelGraph_iff f g hτ).2 hb⟩

theorem graphBranchEdgeOrder_relabelGraph {ι : Type*} [Fintype ι] {A : Graph α β}
    {T : SimpleGraph ι} {τ : β → ι} {τ' : β' → ι} (hτ : ∀ e, τ' (g e) = τ e) (e : Sym2 ι) :
    graphBranchEdgeOrder (relabelGraph f g A) T τ' e = graphBranchEdgeOrder A T τ e := by
  unfold graphBranchEdgeOrder
  have hset : {v ∈ V(relabelGraph f g A) | ∃ f₁ ∈ E(relabelGraph f g A),
      ∃ f₂ ∈ E(relabelGraph f g A), ¬ (T.deleteEdges {e}).Reachable (τ' f₁) (τ' f₂) ∧
        (relabelGraph f g A).Inc f₁ v ∧ (relabelGraph f g A).Inc f₂ v} =
      f '' {v ∈ V(A) | ∃ f₁ ∈ E(A), ∃ f₂ ∈ E(A),
        ¬ (T.deleteEdges {e}).Reachable (τ f₁) (τ f₂) ∧ A.Inc f₁ v ∧ A.Inc f₂ v} := by
    ext v'
    constructor
    · rintro ⟨⟨v, hv, rfl⟩, _, ⟨e₁, he₁, rfl⟩, _, ⟨e₂, he₂, rfl⟩, hr, hi₁, hi₂⟩
      rw [hτ, hτ] at hr
      exact ⟨v, ⟨hv, e₁, he₁, e₂, he₂, hr, (relabelGraph_inc_apply f g).1 hi₁,
        (relabelGraph_inc_apply f g).1 hi₂⟩, rfl⟩
    · rintro ⟨v, ⟨hv, e₁, he₁, e₂, he₂, hr, hi₁, hi₂⟩, rfl⟩
      refine ⟨⟨v, hv, rfl⟩, g e₁, ⟨e₁, he₁, rfl⟩, g e₂, ⟨e₂, he₂, rfl⟩, ?_,
        (relabelGraph_inc_apply f g).2 hi₁, (relabelGraph_inc_apply f g).2 hi₂⟩
      rw [hτ, hτ]
      exact hr
  rw [hset, Set.ncard_image_of_injective _ f.injective]

/-- The renamed branch-decomposition has the same width. -/
theorem graphBranchDecompWidth_relabelGraph {ι : Type*} [Fintype ι] {A : Graph α β}
    {T : SimpleGraph ι} {τ : β → ι} {τ' : β' → ι} (hτ : ∀ e, τ' (g e) = τ e) :
    graphBranchDecompWidth (relabelGraph f g A) T τ' = graphBranchDecompWidth A T τ := by
  unfold graphBranchDecompWidth
  congr 1
  ext k
  simp only [Set.mem_image, graphBranchEdgeOrder_relabelGraph f g hτ]

theorem ncard_edgeSet_relabelGraph (A : Graph α β) :
    E(relabelGraph f g A).ncard = E(A).ncard :=
  Set.ncard_image_of_injective _ g.injective

end GraphMinor.Transport
