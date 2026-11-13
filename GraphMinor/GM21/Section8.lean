module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.CuffSpaces
public import GraphMinor.GM21.Parallel
import GraphMinor.GM21.Section7ThreeProof
public import GraphMinor.GM21.Section3
public import GraphMinor.GM17.Section4
import GraphMinor.GM21.Section2

/-!
# Graph Minors XXI, Section 8: Pseudo-presentations

Formalization of Section 8 (pages 32–37 of the preprint) of
N. Robertson and P. D. Seymour,
*Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616.

Proves:
- `theorem_8_1` (Graph Minors XXI, (8.1)): every disjointed pseudo-presentation of `G` in `Σ`
  yields a presentation of `G` in `Σ` with `H_j = μ(F_j^*)`.
- `theorem_8_2` (Graph Minors XXI, (8.2)): splitting a shared boundary-unit vertex `v` in a
  pseudo-presentation of `G` yields a pseudo-presentation of `G'`.
- `theorem_8_3` (Graph Minors XXI, (8.3)): if the pseudo-presentation in `(8.2)` has depth `≤ q`
  and surrounds a tangle of order `θ ≥ 2q + 3`, then the split pseudo-presentation surrounds a
  tangle in `G'` of order `θ - 1`.
- `theorem_8_4` (Graph Minors XXI, (8.4)): for every surface `Σ` and integers `p, r ≥ 0` and
  `q ≥ 1`, there exists `θ ≥ 1` such that if `G` has a pseudo-presentation in `Σ` of depth `≤ q`
  and defect `≤ r` surrounding a tangle of order `≥ θ`, then `G` has no vital `p`-linkage.
  Here it is `theorem_8_4_of_infinite`, for an infinite type of vertices; `theorem_8_4_proof` in
  `GraphMinor.GM21.Section8Free` removes this hypothesis.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Classical Hypergraph GraphMinor.Surface GraphMinor.GM10
open GraphMinor.GM17
open GraphMinor.GM19 (cuffPoint)

set_option linter.deprecated false

universe u v w

/-! ## Section 1: Basic properties of `supportGraph` and proof of (8.1) -/

section SupportGraphLemmas

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β}
  {r : ℕ} {F_star : Fin r → Set S}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}

/-- In a pseudo-presentation, `supportGraph G Γ μ (F_star j)` is a subhypergraph of `G`. -/
theorem supportGraph_le_of_isPseudoPresentation
    (hp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (j : Fin r) :
    supportGraph G Γ μ (F_star j) ≤ G where
  vertexSet_subset := inter_subset_left
  edgeSet_subset := inter_subset_left
  ends_eq e he := by
    ext v
    simp only [Hypergraph.ends, mem_ofPred_eq, supportGraph]
    refine ⟨?_, fun h => h.1⟩
    intro hincG
    refine ⟨hincG, ?_⟩
    rcases he.2 with h_space | h_vert
    · rw [mem_iUnion₂] at h_space
      rcases h_space with ⟨s, ⟨hs, hsF⟩, hes⟩
      exact Or.inl ⟨s, hs, hsF, (GM10.inc_iff_of_le (hp.μ_space j s hs hsF) hes).2 hincG⟩
    · rw [mem_iUnion₂] at h_vert
      rcases h_vert with ⟨u, hu, heu⟩
      rw [(hp.μ_vertex j u hu).2.1] at heu
      exact heu.elim

/-- In a pseudo-presentation, a vertex `v` belongs to `(supportGraph G Γ μ (F_star j)).vertexSet`
if and only if `v ∈ (μ (.space s)).vertexSet` for some space `s ⊆ F_star j` or
`v ∈ (μ (.vertex u)).vertexSet` for some `u ∈ Γ.V ∩ F_star j`. -/
theorem mem_supportGraph_vertexSet_iff
    (hp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (j : Fin r) {v : α} :
    v ∈ (supportGraph G Γ μ (F_star j)).vertexSet ↔
      (∃ s ∈ drawingSpaces Γ, s ⊆ F_star j ∧ v ∈ (μ (.space s)).vertexSet) ∨
      (∃ u ∈ Γ.V ∩ F_star j, v ∈ (μ (.vertex u)).vertexSet) := by
  simp only [supportGraph, mem_inter_iff, mem_union, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨_, h⟩
    rcases h with ⟨s, ⟨hs, hsF⟩, hv⟩ | ⟨u, hu, hv⟩
    · exact Or.inl ⟨s, hs, hsF, hv⟩
    · exact Or.inr ⟨u, hu, hv⟩
  · rintro (⟨s, hs, hsF, hv⟩ | ⟨u, hu, hv⟩)
    · exact ⟨(hp.μ_space j s hs hsF).vertexSet_subset hv, Or.inl ⟨s, ⟨hs, hsF⟩, hv⟩⟩
    · exact ⟨(hp.μ_vertex j u hu).1.vertexSet_subset hv, Or.inr ⟨u, hu, hv⟩⟩

/-- In a pseudo-presentation, an edge `e` belongs to `(supportGraph G Γ μ (F_star j)).edgeSet`
if and only if `e ∈ (μ (.space s)).edgeSet` for some space `s ⊆ F_star j`. -/
theorem mem_supportGraph_edgeSet_iff
    (hp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (j : Fin r) {e : β} :
    e ∈ (supportGraph G Γ μ (F_star j)).edgeSet ↔
      ∃ s ∈ drawingSpaces Γ, s ⊆ F_star j ∧ e ∈ (μ (.space s)).edgeSet := by
  simp only [supportGraph, mem_inter_iff, mem_union, mem_iUnion, mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨_, ⟨s, ⟨hs, hsF⟩, he⟩ | ⟨u, hu, he⟩⟩
    · exact ⟨s, hs, hsF, he⟩
    · rw [(hp.μ_vertex j u hu).2.1] at he
      exact he.elim
  · rintro ⟨s, hs, hsF, he⟩
    exact ⟨(hp.μ_space j s hs hsF).edgeSet_subset he, Or.inl ⟨s, ⟨hs, hsF⟩, he⟩⟩

/-- In a pseudo-presentation, `μ (.vertex u) ≤ supportGraph G Γ μ (F_star j)` for every
`u ∈ Γ.V ∩ F_star j`. -/
theorem μ_vertex_le_supportGraph
    (hp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (j : Fin r)
    {u : S} (hu : u ∈ Γ.V ∩ F_star j) :
    μ (.vertex u) ≤ supportGraph G Γ μ (F_star j) := by
  rw [GM10.le_iff_of_le (hp.μ_vertex j u hu).1 (supportGraph_le_of_isPseudoPresentation hp j)]
  refine ⟨fun v hv => (mem_supportGraph_vertexSet_iff hp j).2 (Or.inr ⟨u, hu, hv⟩), ?_⟩
  rw [(hp.μ_vertex j u hu).2.1]
  exact empty_subset _

/-- In a pseudo-presentation, `μ (.space s) ≤ supportGraph G Γ μ (F_star j)` for every
`s ∈ drawingSpaces Γ` with `s ⊆ F_star j`. -/
theorem μ_space_le_supportGraph
    (hp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (j : Fin r)
    {s : Set S} (hs : s ∈ drawingSpaces Γ) (hsF : s ⊆ F_star j) :
    μ (.space s) ≤ supportGraph G Γ μ (F_star j) := by
  rw [GM10.le_iff_of_le (hp.μ_space j s hs hsF) (supportGraph_le_of_isPseudoPresentation hp j)]
  exact ⟨fun v hv => (mem_supportGraph_vertexSet_iff hp j).2 (Or.inl ⟨s, hs, hsF, hv⟩),
         fun e he => (mem_supportGraph_edgeSet_iff hp j).2 ⟨s, hs, hsF, he⟩⟩

/-- In a pseudo-presentation, `(supportGraph G Γ μ (F_star j)).vertexSet ∩ Γ_sub.vertexSet =
ιV '' (Γ.V ∩ F_star j)`. -/
theorem supportGraph_vertexSet_inter_drawing
    (hp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (j : Fin r) :
    (supportGraph G Γ μ (F_star j)).vertexSet ∩ Γ_sub.vertexSet = ιV '' (Γ.V ∩ F_star j) := by
  ext v
  simp only [mem_inter_iff, mem_supportGraph_vertexSet_iff hp j, mem_image]
  constructor
  · rintro ⟨⟨s, hs, hsF, hvs⟩ | ⟨u, hu, hvu⟩, hvΓ⟩
    · obtain ⟨u₁, u₂, hs_ends⟩ :=
        exists_spaceHasEnds_of_mem_drawingSpaces hp.is_surface hp.cuff_vertices_ge_two hs
      have hv_ends : v ∈ ({ιV u₁, ιV u₂} : Set α) := by
        rw [← (hp.p2_space j s hs u₁ u₂ hsF hs_ends).1]
        exact ⟨hvs, hvΓ⟩
      have hcl_sub : closure s ⊆ F_star j :=
        closure_minimal hsF (isClosed_of_isSupportOfDrawing hp.is_surface (hp.supports_isSupport j))
      rw [hs_ends.2.2.2.2.2] at hcl_sub
      rcases hv_ends with rfl | rfl
      · exact ⟨u₁, ⟨hs_ends.2.1.1, hcl_sub (Or.inr (Or.inl rfl))⟩, rfl⟩
      · exact ⟨u₂, ⟨hs_ends.2.2.1.1, hcl_sub (Or.inr (Or.inr rfl))⟩, rfl⟩
    · have hv_eq : v ∈ ({ιV u} : Set α) := by
        rw [← (hp.μ_vertex j u hu).2.2.2]
        exact ⟨hvu, hvΓ⟩
      rw [mem_singleton_iff] at hv_eq
      exact ⟨u, hu, hv_eq.symm⟩
  · rintro ⟨u, hu, rfl⟩
    have hmem : ιV u ∈ (μ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet := by
      rw [(hp.μ_vertex j u hu).2.2.2]
      exact mem_singleton (ιV u)
    exact ⟨Or.inr ⟨u, hu, hmem.1⟩, hmem.2⟩

/-- In a pseudo-presentation, `(supportGraph G Γ μ (F_star j)).edgeSet` is disjoint from
`Γ_sub.edgeSet`. -/
theorem supportGraph_edgeSet_disjoint_drawing
    (hp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) (j : Fin r) :
    Disjoint (supportGraph G Γ μ (F_star j)).edgeSet Γ_sub.edgeSet := by
  rw [disjoint_iff_inter_eq_empty]
  ext e
  simp only [mem_inter_iff, mem_supportGraph_edgeSet_iff hp j, mem_empty_iff_false, iff_false,
    not_and]
  rintro ⟨s, hs, hsF, hes⟩ heΓ
  exact Set.disjoint_left.mp (hp.p1_edge_disjoint_drawing j s hs hsF) heΓ hes

/-- In a disjointed pseudo-presentation, the graphs `supportGraph G Γ μ (F_star j)` are pairwise
vertex-disjoint (`(V1)` in the proof of `(8.1)`). -/
theorem supportGraph_pairwise_disjoint_of_isDisjointed
    (hpp : IsDisjointedPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    Pairwise (fun i j : Fin r =>
      Disjoint (supportGraph G Γ μ (F_star i)).vertexSet
        (supportGraph G Γ μ (F_star j)).vertexSet) := by
  have hp := hpp.1
  have : T2Space S := hp.is_surface.2.1
  intro j₁ j₂ hj₁₂
  rw [disjoint_iff_inter_eq_empty]
  ext v
  simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
  intro hv₁ hv₂
  have hx₁_ex : ∃ x₁ : BoundaryUnit S,
      x₁.InSet (F_star j₁) ∧ x₁.toSet.Nonempty ∧ v ∈ (μ x₁).vertexSet := by
    rcases (mem_supportGraph_vertexSet_iff hp j₁).1 hv₁ with ⟨s, hs, hsF, hvs⟩ | ⟨u, hu, hvu⟩
    · exact ⟨.space s, hsF, (isConnected_of_mem_drawingSpaces hs).nonempty, hvs⟩
    · exact ⟨.vertex u, hu.2, singleton_nonempty u, hvu⟩
  have hx₂_ex : ∃ x₂ : BoundaryUnit S,
      x₂.InSet (F_star j₂) ∧ x₂.toSet.Nonempty ∧ v ∈ (μ x₂).vertexSet := by
    rcases (mem_supportGraph_vertexSet_iff hp j₂).1 hv₂ with ⟨s, hs, hsF, hvs⟩ | ⟨u, hu, hvu⟩
    · exact ⟨.space s, hsF, (isConnected_of_mem_drawingSpaces hs).nonempty, hvs⟩
    · exact ⟨.vertex u, hu.2, singleton_nonempty u, hvu⟩
  rcases hx₁_ex with ⟨x₁, hx₁_F, hx₁_ne, hv_x₁⟩
  rcases hx₂_ex with ⟨x₂, hx₂_F, hx₂_ne, hv_x₂⟩
  obtain ⟨C₁, hC₁, hF₁C₁, _⟩ :=
    exists_cuff_of_isSupportOfDrawing (hp.supports_isSupport j₁)
  obtain ⟨C₂, hC₂, hF₂C₂, _⟩ :=
    exists_cuff_of_isSupportOfDrawing (hp.supports_isSupport j₂)
  have hx₁_C₁ : x₁.InSet C₁ := by
    cases x₁ with
    | vertex u => exact hF₁C₁ hx₁_F
    | space s => exact hx₁_F.trans hF₁C₁
  have hx₂_C₂ : x₂.InSet C₂ := by
    cases x₂ with
    | vertex u => exact hF₂C₂ hx₂_F
    | space s => exact hx₂_F.trans hF₂C₂
  have hC_eq : C₁ = C₂ := by
    by_contra hne
    exact Set.disjoint_left.mp
      (hp.p1_diff_cuff_disjoint C₁ hC₁ C₂ hC₂ hne x₁ x₂ hx₁_C₁ hx₂_C₂) hv_x₁ hv_x₂
  subst hC_eq
  obtain ⟨s_r, s_l, a_r, b_r, a_l, b_l, hs_r_C, hs_l_C, hs_r_ends, hs_l_ends,
      hs_r_uncov, hs_l_uncov, h_sep, _⟩ :=
    exists_adjacent_uncovered_spaces_of_support hp.is_surface hp.cuff_vertices_ge_two
      hp.supports_isSupport hp.supports_disjoint j₁ hC₁ hF₁C₁
  have hdisj_r : Disjoint (μ (.vertex a_r)).vertexSet (μ (.vertex b_r)).vertexSet :=
    hpp.2 s_r hs_r_ends.1 a_r b_r hs_r_ends hs_r_uncov
  have hdisj_l : Disjoint (μ (.vertex a_l)).vertexSet (μ (.vertex b_l)).vertexSet :=
    hpp.2 s_l hs_l_ends.1 a_l b_l hs_l_ends hs_l_uncov
  have hcC₁ : IsClosed C₁ := isClosed_cuff_univ hp.is_surface hC₁
  have hu₁_ex : ∃ u₁ ∈ ({a_r, b_r} : Set S), u₁ ∈ C₁ ∩ Γ.V ∧ v ∉ (μ (.vertex u₁)).vertexSet := by
    have har : a_r ∈ C₁ ∩ Γ.V := by
      have hcl : a_r ∈ closure s_r := by
        rw [hs_r_ends.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
      exact ⟨closure_minimal hs_r_C hcC₁ hcl, hs_r_ends.2.1.1⟩
    have hbr : b_r ∈ C₁ ∩ Γ.V := by
      have hcl : b_r ∈ closure s_r := by
        rw [hs_r_ends.2.2.2.2.2]; exact Or.inr (Or.inr rfl)
      exact ⟨closure_minimal hs_r_C hcC₁ hcl, hs_r_ends.2.2.1.1⟩
    by_cases hvar : v ∈ (μ (.vertex a_r)).vertexSet
    · exact ⟨b_r, Or.inr rfl, hbr, Set.disjoint_left.mp hdisj_r hvar⟩
    · exact ⟨a_r, Or.inl rfl, har, hvar⟩
  have hu₂_ex : ∃ u₂ ∈ ({a_l, b_l} : Set S), u₂ ∈ C₁ ∩ Γ.V ∧ v ∉ (μ (.vertex u₂)).vertexSet := by
    have hal : a_l ∈ C₁ ∩ Γ.V := by
      have hcl : a_l ∈ closure s_l := by
        rw [hs_l_ends.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
      exact ⟨closure_minimal hs_l_C hcC₁ hcl, hs_l_ends.2.1.1⟩
    have hbl : b_l ∈ C₁ ∩ Γ.V := by
      have hcl : b_l ∈ closure s_l := by
        rw [hs_l_ends.2.2.2.2.2]; exact Or.inr (Or.inr rfl)
      exact ⟨closure_minimal hs_l_C hcC₁ hcl, hs_l_ends.2.2.1.1⟩
    by_cases hval : v ∈ (μ (.vertex a_l)).vertexSet
    · exact ⟨b_l, Or.inr rfl, hbl, Set.disjoint_left.mp hdisj_l hval⟩
    · exact ⟨a_l, Or.inl rfl, hal, hval⟩
  rcases hu₁_ex with ⟨u₁, hu₁_pair, hu₁_CV, hv_not_u₁⟩
  rcases hu₂_ex with ⟨u₂, hu₂_pair, hu₂_CV, hv_not_u₂⟩
  have hX₁_sub : x₁.toSet ⊆ F_star j₁ := by
    cases x₁ with
    | vertex u => exact singleton_subset_iff.mpr hx₁_F
    | space s => exact hx₁_F
  have hX₂_sub : x₂.toSet ⊆ F_star j₂ := by
    cases x₂ with
    | vertex u => exact singleton_subset_iff.mpr hx₂_F
    | space s => exact hx₂_F
  have hcl₁_sub : closure x₁.toSet ∩ C₁ ⊆ F_star j₁ :=
    inter_subset_left.trans
      (closure_minimal hX₁_sub (isClosed_of_isSupportOfDrawing hp.is_surface (hp.supports_isSupport j₁)))
  have hcl₂_sub : closure x₂.toSet ∩ C₁ ⊆ F_star j₂ :=
    inter_subset_left.trans
      (closure_minimal hX₂_sub (isClosed_of_isSupportOfDrawing hp.is_surface (hp.supports_isSupport j₂)))
  have hcl₁_ne : (closure x₁.toSet ∩ C₁).Nonempty := by
    rcases hx₁_ne with ⟨z, hz⟩
    exact ⟨z, subset_closure hz, hF₁C₁ (hX₁_sub hz)⟩
  have hcl₂_ne : (closure x₂.toSet ∩ C₁).Nonempty := by
    rcases hx₂_ne with ⟨z, hz⟩
    exact ⟨z, subset_closure hz, hF₂C₂ (hX₂_sub hz)⟩
  have hord : InCuffOrder C₁ x₁.toSet u₁ x₂.toSet u₂ :=
    h_sep j₂ hj₁₂ hF₂C₂ x₁.toSet x₂.toSet hcl₁_ne hcl₁_sub hcl₂_ne hcl₂_sub u₁ hu₁_pair u₂ hu₂_pair
  have hle := hp.p3_order C₁ hC₁ x₁ x₂ u₁ hu₁_CV u₂ hu₂_CV hx₁_C₁ hx₂_C₂ hord
  have hv_union : v ∈ (μ (.vertex u₁) ∪ μ (.vertex u₂)).vertexSet :=
    hle.vertexSet_subset ⟨hv_x₁, hv_x₂⟩
  rcases hv_union with hv_u₁ | hv_u₂
  · exact hv_not_u₁ hv_u₁
  · exact hv_not_u₂ hv_u₂

/-- In a disjointed pseudo-presentation, if `u ∈ F_star j ∩ Γ.V` lies between spaces
`s₁, s₂ ⊆ F_star j`, then `μ (.space s₁) ∩ μ (.space s₂) ≤ μ (.vertex u)` (`(V4)` in the proof of
`(8.1)`). The printed proof ends with $\mu(s_1) \cap \mu(s_2) \subseteq (\mu(a_0) \cap \mu(b_0))
\cap \mu(s_2) = \mu(s_2)$. We prove the corrected form with $\cup$ and $\mu(u)$ (see the correction
to the proof of (8.1) in `corrections/GM21.md`). -/
theorem v4_between_of_isDisjointed
    (hpp : IsDisjointedPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    (j : Fin r) {s₁ s₂ : Set S} {u : S}
    (hbet : LiesBetweenInSupport Γ (F_star j) s₁ s₂ u) :
    μ (.space s₁) ∩ μ (.space s₂) ≤ μ (.vertex u) := by
  have hp := hpp.1
  have : T2Space S := hp.is_surface.2.1
  obtain ⟨C, hC, hFC, _⟩ :=
    exists_cuff_of_isSupportOfDrawing (hp.supports_isSupport j)
  obtain ⟨s_r, _, a_r, b_r, _, _, hs_r_C, _, hs_r_ends, _, hs_r_uncov, _, _, h_bet_ord⟩ :=
    exists_adjacent_uncovered_spaces_of_support hp.is_surface hp.cuff_vertices_ge_two
      hp.supports_isSupport hp.supports_disjoint j hC hFC
  have hs₁ : s₁ ∈ drawingSpaces Γ := hbet.2.1
  have hs₂ : s₂ ∈ drawingSpaces Γ := hbet.2.2.1
  have hs₁F : s₁ ⊆ F_star j := hbet.2.2.2.1
  have hs₂F : s₂ ⊆ F_star j := hbet.2.2.2.2.1
  have hu_VF : u ∈ Γ.V ∩ F_star j := ⟨hbet.1.2, hbet.1.1⟩
  have hu_CV : u ∈ C ∩ Γ.V := ⟨hFC hbet.1.1, hbet.1.2⟩
  have hs₁C : (BoundaryUnit.space s₁).InSet C := hs₁F.trans hFC
  have hs₂C : (BoundaryUnit.space s₂).InSet C := hs₂F.trans hFC
  have hcC : IsClosed C := isClosed_cuff_univ hp.is_surface hC
  have har_CV : a_r ∈ C ∩ Γ.V := by
    have hcl : a_r ∈ closure s_r := by
      rw [hs_r_ends.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
    exact ⟨closure_minimal hs_r_C hcC hcl, hs_r_ends.2.1.1⟩
  have hbr_CV : b_r ∈ C ∩ Γ.V := by
    have hcl : b_r ∈ closure s_r := by
      rw [hs_r_ends.2.2.2.2.2]; exact Or.inr (Or.inr rfl)
    exact ⟨closure_minimal hs_r_C hcC hcl, hs_r_ends.2.2.1.1⟩
  have hle_ar : μ (.space s₁) ∩ μ (.space s₂) ≤ μ (.vertex u) ∪ μ (.vertex a_r) := by
    rcases h_bet_ord s₁ s₂ u hbet a_r (Or.inl rfl) with hord | hord
    · exact hp.p3_order C hC (.space s₁) (.space s₂) u hu_CV a_r har_CV hs₁C hs₂C hord
    · have h := hp.p3_order C hC (.space s₂) (.space s₁) u hu_CV a_r har_CV hs₂C hs₁C hord
      rwa [GM10.inter_comm] at h
  have hle_br : μ (.space s₁) ∩ μ (.space s₂) ≤ μ (.vertex u) ∪ μ (.vertex b_r) := by
    rcases h_bet_ord s₁ s₂ u hbet b_r (Or.inr rfl) with hord | hord
    · exact hp.p3_order C hC (.space s₁) (.space s₂) u hu_CV b_r hbr_CV hs₁C hs₂C hord
    · have h := hp.p3_order C hC (.space s₂) (.space s₁) u hu_CV b_r hbr_CV hs₂C hs₁C hord
      rwa [GM10.inter_comm] at h
  have hdisj_r : Disjoint (μ (.vertex a_r)).vertexSet (μ (.vertex b_r)).vertexSet :=
    hpp.2 s_r hs_r_ends.1 a_r b_r hs_r_ends hs_r_uncov
  have h_inter_le : μ (.space s₁) ∩ μ (.space s₂) ≤ G :=
    GM10.inter_le (hp.μ_space j s₁ hs₁ hs₁F) (hp.μ_space j s₂ hs₂ hs₂F)
  have h_u_le : μ (.vertex u) ≤ G := (hp.μ_vertex j u hu_VF).1
  rw [GM10.le_iff_of_le h_inter_le h_u_le]
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv_ar : v ∈ (μ (.vertex u)).vertexSet ∪ (μ (.vertex a_r)).vertexSet :=
      hle_ar.vertexSet_subset hv
    have hv_br : v ∈ (μ (.vertex u)).vertexSet ∪ (μ (.vertex b_r)).vertexSet :=
      hle_br.vertexSet_subset hv
    rcases hv_ar with hvu | hvar
    · exact hvu
    · rcases hv_br with hvu | hvbr
      · exact hvu
      · exact (Set.disjoint_left.mp hdisj_r hvar hvbr).elim
  · intro e he
    have he_ar : e ∈ (μ (.vertex u)).edgeSet ∪ (μ (.vertex a_r)).edgeSet :=
      hle_ar.edgeSet_subset he
    have har_bd : a_r ∈ Γ.V ∩ bd S := hs_r_ends.2.1
    have har_cov := hp.bd_vertices_covered har_bd
    rw [mem_iUnion] at har_cov
    rcases har_cov with ⟨j_r, hj_r⟩
    rw [(hp.μ_vertex j u hu_VF).2.1, (hp.μ_vertex j_r a_r ⟨har_bd.1, hj_r⟩).2.1,
      Set.union_self] at he_ar
    exact he_ar.elim

/-- **Graph Minors XXI, (8.1)** (page 32 of the preprint):
"Let $\Gamma, F_1^*, \dots, F_r^*, \mu$ be a disjointed pseudo-presentation of a graph $G$ in a
surface $\Sigma$. Then $\Gamma, F_1^*, \dots, F_r^*, \mu(F_1^*), \dots, \mu(F_r^*), \mu$ is a
presentation of $G$ in $\Sigma$." -/
theorem theorem_8_1_proof {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hpp : IsDisjointedPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    IsPresentation G Γ Γ_sub ιV ιE r F_star (fun j => supportGraph G Γ μ (F_star j)) μ q := by
  have hp := hpp.1
  have hV : G.vertexSet =
      (⋃ j : Fin r, (supportGraph G Γ μ (F_star j)).vertexSet) ∪ Γ_sub.vertexSet := by
    rw [hp.p1_union_V, Set.union_comm]
  have hE : G.edgeSet =
      (⋃ j : Fin r, (supportGraph G Γ μ (F_star j)).edgeSet) ∪ Γ_sub.edgeSet := by
    rw [hp.p1_union_E, Set.union_comm]
  refine
    { is_surface := hp.is_surface
      is_connected_surface := hp.is_connected_surface
      is_proper_drawing := hp.is_proper_drawing
      cuff_vertices_ge_two := hp.cuff_vertices_ge_two
      drawing_subgraph := hp.drawing_subgraph
      drawing_iso := hp.drawing_iso
      supports_isSupport := hp.supports_isSupport
      supports_disjoint := hp.supports_disjoint
      bd_vertices_covered := hp.bd_vertices_covered
      v1_sub := supportGraph_le_of_isPseudoPresentation hp
      v1_union_V := hV
      v1_union_E := hE
      v1_disjoint := supportGraph_pairwise_disjoint_of_isDisjointed hpp
      v1_inter_V := supportGraph_vertexSet_inter_drawing hp
      v1_inter_E := supportGraph_edgeSet_disjoint_drawing hp
      q_pos := hp.q_pos
      μ_vertex_sub := fun j u hu =>
        ⟨μ_vertex_le_supportGraph hp j hu, (hp.μ_vertex j u hu).2.1,
         (hp.μ_vertex j u hu).2.2.1, (hp.μ_vertex j u hu).2.2.2⟩
      μ_space_sub := fun j _ hs hsF => μ_space_le_supportGraph hp j hs hsF
      v2_eq := fun _ => rfl
      v3_space := hp.p2_space
      v4_between := fun j _ _ _ hbet => v4_between_of_isDisjointed hpp j hbet }

end SupportGraphLemmas

/-! ## Section 2: Vertex splitting in a pseudo-presentation and proof of (8.2) -/

section PseudoSplit

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- The empty hypergraph on `(α, β)`. -/
def emptyHypergraph (α : Type u) (β : Type v) : Hypergraph α β where
  vertexSet := ∅
  edgeSet := ∅
  Inc _ _ := False
  vertex_mem_of_inc _ _ h := h.elim
  edge_mem_of_inc _ _ h := h.elim
  vertexSet_finite := finite_empty
  edgeSet_finite := finite_empty

@[simp]
theorem emptyHypergraph_vertexSet : (emptyHypergraph α β).vertexSet = ∅ := rfl

@[simp]
theorem emptyHypergraph_edgeSet : (emptyHypergraph α β).edgeSet = ∅ := rfl

theorem emptyHypergraph_le (H : Hypergraph α β) : emptyHypergraph α β ≤ H where
  vertexSet_subset := empty_subset _
  edgeSet_subset := empty_subset _
  ends_eq _ he := he.elim

/-- A `BoundaryUnit S` is a valid unit of `(Γ, F_star)` if it is either `.vertex u` with
`u ∈ Γ.V ∩ bd S` or `.space s` with `s ∈ drawingSpaces Γ` and `s ⊆ F_star j` for some `j : Fin r`
(Graph Minors XXI, Section 8, page 32 of the preprint: "A *unit* is either a vertex in $V(\Gamma)
\cap bd(\Sigma)$ or a space in $F_1^* \cup \dots \cup F_r^*$"). -/
def IsValidUnit (Γ : Drawing S) (r : ℕ) (F_star : Fin r → Set S) (x : BoundaryUnit S) : Prop :=
  (∃ u ∈ Γ.V ∩ bd S, x = .vertex u) ∨
  (∃ s ∈ drawingSpaces Γ, (∃ j : Fin r, s ⊆ F_star j) ∧ x = .space s)

/-- The hypergraph `G'` obtained from `G` by splitting `v` into `v₁, v₂` according to `δ₁, δ₂`
(Graph Minors XXI, Section 2, pages 2–3 of the preprint). -/
def vertexSplitHypergraph (G : Hypergraph α β) (v v₁ v₂ : α) (δ₁ δ₂ : Set β) : Hypergraph α β where
  vertexSet := (G.vertexSet \ {v}) ∪ {v₁, v₂}
  edgeSet := G.edgeSet
  Inc e u :=
    (u ≠ v ∧ u ≠ v₁ ∧ u ≠ v₂ ∧ G.Inc e u) ∨
    (u = v₁ ∧ e ∈ δ₁ ∩ G.edgeSet) ∨
    (u = v₂ ∧ e ∈ δ₂ ∩ G.edgeSet)
  vertex_mem_of_inc := by
    rintro e u (⟨hu_v, _, _, hinc⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩)
    · exact Or.inl ⟨G.vertex_mem_of_inc hinc, hu_v⟩
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  edge_mem_of_inc := by
    rintro e u (⟨_, _, _, hinc⟩ | ⟨_, _, he⟩ | ⟨_, _, he⟩)
    · exact G.edge_mem_of_inc hinc
    · exact he
    · exact he
  vertexSet_finite := (G.vertexSet_finite.sdiff).union ((finite_singleton v₂).insert v₁)
  edgeSet_finite := G.edgeSet_finite

theorem isVertexSplit_vertexSplitHypergraph {G : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hv : v ∈ G.vertexSet) (hv₁ : v₁ ∉ G.vertexSet) (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂)
    (hdisj : Disjoint δ₁ δ₂) (hunion : δ₁ ∪ δ₂ = incidentEdges G v) :
    IsVertexSplit G (vertexSplitHypergraph G v v₁ v₂ δ₁ δ₂) v v₁ v₂ δ₁ δ₂ where
  v_mem := hv
  v₁_not_mem := hv₁
  v₂_not_mem := hv₂
  v₁_ne_v₂ := hne
  δ_disjoint := hdisj
  δ_union := hunion
  vertexSet_eq := rfl
  edgeSet_eq := rfl
  inc_iff e he u hu := by
    simp only [vertexSplitHypergraph] at hu ⊢
    refine or_congr ?_ (or_congr ?_ ?_)
    · refine ⟨fun h => ⟨h.2.1, h.2.2⟩, fun ⟨hu₁, hu₂, hinc⟩ => ⟨?_, hu₁, hu₂, hinc⟩⟩
      rcases hu with ⟨_, huv⟩ | rfl | rfl
      · exact huv
      · exact (hu₁ rfl).elim
      · exact (hu₂ rfl).elim
    · refine and_congr_right fun _ => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      have hsub : δ₁ ⊆ incidentEdges G v := subset_union_left.trans hunion.subset
      exact (hsub h).1
    · refine and_congr_right fun _ => ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      have hsub : δ₂ ⊆ incidentEdges G v := subset_union_right.trans hunion.subset
      exact (hsub h).1

/-- Splitting a vertex preserves `IsGraph`. -/
theorem IsVertexSplit.isGraph {G G' : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hsplit : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hG : G.IsGraph) : G'.IsGraph := by
  intro e he'
  have he : e ∈ G.edgeSet := hsplit.edgeSet_eq ▸ he'
  obtain ⟨hneG, hcardG⟩ := hG e he
  have hends_fin : (G.ends e).Finite :=
    G.vertexSet_finite.subset (fun u hu => G.vertex_mem_of_inc hu)
  have hends_sub : G'.ends e ⊆ (G.ends e \ {v}) ∪
      (if e ∈ δ₁ then {v₁} else ∅) ∪ (if e ∈ δ₂ then {v₂} else ∅) := by
    intro u hu
    have huG' : u ∈ G'.vertexSet := G'.vertex_mem_of_inc hu
    rcases (hsplit.inc_iff e he' u huG').1 hu with ⟨hu₁, hu₂, hincG⟩ | ⟨rfl, he₁⟩ | ⟨rfl, he₂⟩
    · left; left
      refine ⟨hincG, ?_⟩
      rintro (rfl : u = v)
      rw [hsplit.vertexSet_eq] at huG'
      rcases huG' with ⟨_, huv⟩ | rfl | rfl
      · exact huv rfl
      · exact hu₁ rfl
      · exact hu₂ rfl
    · left; right; rw [if_pos he₁]; exact rfl
    · right; rw [if_pos he₂]; exact rfl
  constructor
  · rcases hneG with ⟨w, hw⟩
    by_cases hwv : w = v
    · subst hwv
      have he_inc : e ∈ δ₁ ∪ δ₂ := by
        rw [hsplit.δ_union]; exact ⟨he, hw⟩
      rcases he_inc with he₁ | he₂
      · refine ⟨v₁, (hsplit.inc_iff e he' v₁ ?_).2 (Or.inr (Or.inl ⟨rfl, he₁⟩))⟩
        rw [hsplit.vertexSet_eq]; exact Or.inr (Or.inl rfl)
      · refine ⟨v₂, (hsplit.inc_iff e he' v₂ ?_).2 (Or.inr (Or.inr ⟨rfl, he₂⟩))⟩
        rw [hsplit.vertexSet_eq]; exact Or.inr (Or.inr rfl)
    · have hwG : w ∈ G.vertexSet := G.vertex_mem_of_inc hw
      have hwG' : w ∈ G'.vertexSet := by
        rw [hsplit.vertexSet_eq]; exact Or.inl ⟨hwG, hwv⟩
      refine ⟨w, (hsplit.inc_iff e he' w hwG').2 (Or.inl ⟨?_, ?_, hw⟩)⟩
      · rintro rfl; exact hsplit.v₁_not_mem hwG
      · rintro rfl; exact hsplit.v₂_not_mem hwG
  · by_cases hinc_v : G.Inc e v
    · have he_inc : e ∈ δ₁ ∪ δ₂ := by
        rw [hsplit.δ_union]; exact ⟨he, hinc_v⟩
      have hdiff_ncard : (G.ends e \ {v}).ncard + 1 = (G.ends e).ncard :=
        ncard_sdiff_singleton_add_one hinc_v hends_fin
      rcases he_inc with he₁ | he₂
      · have he₂ : e ∉ δ₂ := Set.disjoint_left.mp hsplit.δ_disjoint he₁
        rw [if_pos he₁, if_neg he₂, union_empty] at hends_sub
        have hfin : ((G.ends e \ {v}) ∪ {v₁}).Finite :=
          hends_fin.sdiff.union (finite_singleton v₁)
        calc (G'.ends e).ncard
            ≤ ((G.ends e \ {v}) ∪ {v₁}).ncard := ncard_le_ncard hends_sub hfin
          _ ≤ (G.ends e \ {v}).ncard + ({v₁} : Set α).ncard := ncard_union_le _ _
          _ = (G.ends e \ {v}).ncard + 1 := by rw [ncard_singleton]
          _ = (G.ends e).ncard := hdiff_ncard
          _ ≤ 2 := hcardG
      · have he₁ : e ∉ δ₁ := Set.disjoint_right.mp hsplit.δ_disjoint he₂
        rw [if_neg he₁, if_pos he₂, union_empty] at hends_sub
        have hfin : ((G.ends e \ {v}) ∪ {v₂}).Finite :=
          hends_fin.sdiff.union (finite_singleton v₂)
        calc (G'.ends e).ncard
            ≤ ((G.ends e \ {v}) ∪ {v₂}).ncard := ncard_le_ncard hends_sub hfin
          _ ≤ (G.ends e \ {v}).ncard + ({v₂} : Set α).ncard := ncard_union_le _ _
          _ = (G.ends e \ {v}).ncard + 1 := by rw [ncard_singleton]
          _ = (G.ends e).ncard := hdiff_ncard
          _ ≤ 2 := hcardG
    · have he_not : e ∉ δ₁ ∪ δ₂ := by
        rw [hsplit.δ_union]
        rintro ⟨_, h⟩
        exact hinc_v h
      have he₁ : e ∉ δ₁ := fun h => he_not (Or.inl h)
      have he₂ : e ∉ δ₂ := fun h => he_not (Or.inr h)
      rw [if_neg he₁, if_neg he₂, union_empty, union_empty] at hends_sub
      exact (ncard_le_ncard (hends_sub.trans sdiff_subset) hends_fin).trans hcardG

/-- Graph Minors XXI, Section 8 (page 34 of the preprint):
"For $i = 1, 2$, and for each subgraph $A$ of $G$ with $v \in V(A)$, let $\sigma_i(A)$ be the
graph with the same set of edges as $A$, and with vertex set $(V(A) \setminus \{v\}) \cup \{v_i\}$,
with the same incidence relation as $A$ except that the edges of $A$ that are incident with $v$ in
$A$ are incident with $v_i$ in $\sigma_i(A)$." -/
def replaceVertex (A : Hypergraph α β) (v v_new : α) : Hypergraph α β where
  vertexSet := (A.vertexSet \ {v}) ∪ {v_new}
  edgeSet := A.edgeSet
  Inc e u := (u ≠ v ∧ u ≠ v_new ∧ A.Inc e u) ∨ (u = v_new ∧ A.Inc e v)
  vertex_mem_of_inc := by
    rintro e u (⟨huv, _, hinc⟩ | ⟨rfl, _⟩)
    · exact Or.inl ⟨A.vertex_mem_of_inc hinc, huv⟩
    · exact Or.inr rfl
  edge_mem_of_inc := by
    rintro e u (⟨_, _, hinc⟩ | ⟨_, hinc⟩)
    · exact A.edge_mem_of_inc hinc
    · exact A.edge_mem_of_inc hinc
  vertexSet_finite := A.vertexSet_finite.sdiff.union (finite_singleton v_new)
  edgeSet_finite := A.edgeSet_finite

@[simp]
theorem replaceVertex_vertexSet (A : Hypergraph α β) (v v_new : α) :
    (replaceVertex A v v_new).vertexSet = (A.vertexSet \ {v}) ∪ {v_new} := rfl

@[simp]
theorem replaceVertex_edgeSet (A : Hypergraph α β) (v v_new : α) :
    (replaceVertex A v v_new).edgeSet = A.edgeSet := rfl

theorem replaceVertex_vertexSet_ncard {A : Hypergraph α β} {v v_new : α}
    (hv : v ∈ A.vertexSet) (hnew : v_new ∉ A.vertexSet) :
    (replaceVertex A v v_new).vertexSet.ncard = A.vertexSet.ncard := by
  have hnot : v_new ∉ A.vertexSet \ {v} := fun h => hnew h.1
  calc (replaceVertex A v v_new).vertexSet.ncard
      = (insert v_new (A.vertexSet \ {v})).ncard := by
        rw [replaceVertex_vertexSet, Set.union_comm, Set.singleton_union]
    _ = (A.vertexSet \ {v}).ncard + 1 :=
        ncard_insert_of_notMem hnot A.vertexSet_finite.sdiff
    _ = A.vertexSet.ncard := ncard_sdiff_singleton_add_one hv A.vertexSet_finite

theorem replaceVertex_mono {A B : Hypergraph α β} {v v_new : α}
    (hAB : A ≤ B) :
    replaceVertex A v v_new ≤ replaceVertex B v v_new where
  vertexSet_subset :=
    union_subset_union (sdiff_subset_sdiff hAB.vertexSet_subset Subset.rfl) Subset.rfl
  edgeSet_subset := hAB.edgeSet_subset
  ends_eq e he := by
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq, replaceVertex]
    rw [GM10.inc_iff_of_le hAB he, GM10.inc_iff_of_le hAB he]

theorem le_replaceVertex_of_not_mem {A B : Hypergraph α β} {v v_new : α}
    (hAB : A ≤ B) (hvA : v ∉ A.vertexSet) (hnew : v_new ∉ A.vertexSet) :
    A ≤ replaceVertex B v v_new where
  vertexSet_subset x hx := Or.inl ⟨hAB.vertexSet_subset hx, fun h => hvA (h ▸ hx)⟩
  edgeSet_subset := hAB.edgeSet_subset
  ends_eq e he := by
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq, replaceVertex]
    constructor
    · rintro (⟨_, _, hincB⟩ | ⟨rfl, hincBv⟩)
      · exact (GM10.inc_iff_of_le hAB he).2 hincB
      · have hincAv : A.Inc e v := (GM10.inc_iff_of_le hAB he).2 hincBv
        exact (hvA (A.vertex_mem_of_inc hincAv)).elim
    · intro hincA
      have huA : u ∈ A.vertexSet := A.vertex_mem_of_inc hincA
      exact Or.inl ⟨fun h => hvA (h ▸ huA), fun h => hnew (h ▸ huA),
        GM10.inc_of_le hAB hincA⟩

theorem le_split_of_not_mem {G G' A : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hsplit : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hA : A ≤ G) (hvA : v ∉ A.vertexSet) :
    A ≤ G' := by
  have hle_del : A ≤ G.deleteVertices {v} := by
    refine ⟨fun x hx => ⟨hA.vertexSet_subset hx, fun h => hvA (h ▸ hx)⟩,
            fun e he => ⟨hA.edgeSet_subset he, ?_⟩,
            fun e he => ?_⟩
    · rintro w (rfl : w = v) hincG
      exact hvA (A.vertex_mem_of_inc ((GM10.inc_iff_of_le hA he).2 hincG))
    · ext u
      simp only [Hypergraph.ends, mem_ofPred_eq, deleteVertices]
      rw [GM10.inc_iff_of_le hA he]
      exact ⟨fun h => h.1, fun h => ⟨h, by
        rintro w (rfl : w = v) hincG
        exact hvA (A.vertex_mem_of_inc ((GM10.inc_iff_of_le hA he).2 hincG))⟩⟩
  exact hle_del.trans (deleteVertex_le_of_isVertexSplit hsplit)

theorem replaceVertex_le_split_left {G G' A : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hsplit : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hA : A ≤ G)
    (hδ₁ : ∀ e ∈ A.edgeSet, A.Inc e v → e ∈ δ₁) :
    replaceVertex A v v₁ ≤ G' where
  vertexSet_subset := by
    rw [hsplit.vertexSet_eq, replaceVertex_vertexSet]
    exact union_subset_union (sdiff_subset_sdiff hA.vertexSet_subset Subset.rfl)
      (singleton_subset_iff.mpr (Or.inl rfl))
  edgeSet_subset := by
    rw [hsplit.edgeSet_eq, replaceVertex_edgeSet]
    exact hA.edgeSet_subset
  ends_eq e he := by
    have heG : e ∈ G.edgeSet := hA.edgeSet_subset he
    have heG' : e ∈ G'.edgeSet := hsplit.edgeSet_eq ▸ heG
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq]
    constructor
    · intro hincG'
      have huG' : u ∈ G'.vertexSet := G'.vertex_mem_of_inc hincG'
      rcases (hsplit.inc_iff e heG' u huG').1 hincG' with ⟨hu₁, hu₂, hincG⟩ | ⟨rfl, he₁⟩ | ⟨rfl, he₂⟩
      · have huv : u ≠ v := by
          rw [hsplit.vertexSet_eq] at huG'
          rcases huG' with ⟨_, huv⟩ | rfl | rfl
          · exact huv
          · exact (hu₁ rfl).elim
          · exact (hu₂ rfl).elim
        exact Or.inl ⟨huv, hu₁, (GM10.inc_iff_of_le hA he).2 hincG⟩
      · have he_inc : e ∈ incidentEdges G v := by
          rw [← hsplit.δ_union]; exact Or.inl he₁
        exact Or.inr ⟨rfl, (GM10.inc_iff_of_le hA he).2 he_inc.2⟩
      · exfalso
        have he_inc : e ∈ incidentEdges G v := by
          rw [← hsplit.δ_union]; exact Or.inr he₂
        have hincAv : A.Inc e v := (GM10.inc_iff_of_le hA he).2 he_inc.2
        exact Set.disjoint_left.mp hsplit.δ_disjoint (hδ₁ e he hincAv) he₂
    · rintro (⟨huv, hu₁, hincA⟩ | ⟨hu_eq, hincAv⟩)
      · have huA : u ∈ A.vertexSet := A.vertex_mem_of_inc hincA
        have huG : u ∈ G.vertexSet := hA.vertexSet_subset huA
        have hu₂ : u ≠ v₂ := fun h => hsplit.v₂_not_mem (h ▸ huG)
        have huG' : u ∈ G'.vertexSet := by
          rw [hsplit.vertexSet_eq]; exact Or.inl ⟨huG, huv⟩
        exact (hsplit.inc_iff e heG' u huG').2 (Or.inl ⟨hu₁, hu₂, GM10.inc_of_le hA hincA⟩)
      · subst u
        have hv₁G' : v₁ ∈ G'.vertexSet := by
          rw [hsplit.vertexSet_eq]; exact Or.inr (Or.inl rfl)
        exact (hsplit.inc_iff e heG' v₁ hv₁G').2 (Or.inr (Or.inl ⟨rfl, hδ₁ e he hincAv⟩))

theorem replaceVertex_le_split_right {G G' A : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hsplit : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hA : A ≤ G)
    (hδ₂ : ∀ e ∈ A.edgeSet, A.Inc e v → e ∈ δ₂) :
    replaceVertex A v v₂ ≤ G' := by
  have hsplit' : IsVertexSplit G G' v v₂ v₁ δ₂ δ₁ :=
    { v_mem := hsplit.v_mem
      v₁_not_mem := hsplit.v₂_not_mem
      v₂_not_mem := hsplit.v₁_not_mem
      v₁_ne_v₂ := hsplit.v₁_ne_v₂.symm
      δ_disjoint := hsplit.δ_disjoint.symm
      δ_union := by rw [Set.union_comm, hsplit.δ_union]
      vertexSet_eq := by rw [pair_comm, hsplit.vertexSet_eq]
      edgeSet_eq := hsplit.edgeSet_eq
      inc_iff := fun e he u hu => by
        rw [hsplit.inc_iff e he u hu]
        tauto }
  exact replaceVertex_le_split_left hsplit' hA hδ₂

/-- When `v_new ∉ A.vertexSet`, `Equiv.swap v v_new` induces a graph isomorphism
`A.skeleton ≃g (replaceVertex A v v_new).skeleton`. -/
noncomputable def replaceVertexSkeletonIso {A : Hypergraph α β} {v v_new : α}
    (hv : v ∈ A.vertexSet) (hnew : v_new ∉ A.vertexSet) :
    A.skeleton ≃g (replaceVertex A v v_new).skeleton where
  toEquiv := Equiv.swap v v_new
  map_rel_iff' := by
    intro x y
    have hvn : v ≠ v_new := fun h => hnew (h ▸ hv)
    have hinc : ∀ (e : β) (z : α),
        (replaceVertex A v v_new).Inc e (Equiv.swap v v_new z) ↔ A.Inc e z := by
      intro e z
      by_cases hzv : z = v
      · subst hzv
        rw [Equiv.swap_apply_left]
        dsimp only [replaceVertex]
        exact ⟨fun h => h.elim (fun h1 => (h1.2.1 rfl).elim) (fun h2 => h2.2),
               fun h => Or.inr ⟨rfl, h⟩⟩
      · by_cases hzn : z = v_new
        · subst hzn
          rw [Equiv.swap_apply_right]
          dsimp only [replaceVertex]
          exact ⟨fun h => h.elim (fun h1 => (h1.1 rfl).elim) (fun h2 => (hvn h2.1).elim),
                 fun h => (hnew (A.vertex_mem_of_inc h)).elim⟩
        · rw [Equiv.swap_apply_of_ne_of_ne hzv hzn]
          dsimp only [replaceVertex]
          exact ⟨fun h => h.elim (fun h1 => h1.2.2) (fun h2 => (hzn h2.1).elim),
                 fun h => Or.inl ⟨hzv, hzn, h⟩⟩
    simp only [Hypergraph.skeleton, (Equiv.swap v v_new).injective.ne_iff]
    exact and_congr_right fun _ => exists_congr fun e => and_congr (hinc e x) (hinc e y)

theorem image_swap_of_subset {A : Hypergraph α β} {v v_new : α}
    (hnew : v_new ∉ A.vertexSet) {X : Set α} (hX : X ⊆ A.vertexSet) :
    (Equiv.swap v v_new) '' X = if v ∈ X then (X \ {v}) ∪ {v_new} else X := by
  split_ifs with hvX
  · ext y
    simp only [mem_image, mem_union, mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨x, hxX, rfl⟩
      by_cases hxv : x = v
      · subst hxv; rw [Equiv.swap_apply_left]; exact Or.inr rfl
      · have hxn : x ≠ v_new := fun h => hnew (h ▸ hX hxX)
        rw [Equiv.swap_apply_of_ne_of_ne hxv hxn]
        exact Or.inl ⟨hxX, hxv⟩
    · rintro (⟨hyX, hyv⟩ | hy_eq)
      · have hyn : y ≠ v_new := fun h => hnew (h ▸ hX hyX)
        exact ⟨y, hyX, Equiv.swap_apply_of_ne_of_ne hyv hyn⟩
      · subst y
        exact ⟨v, hvX, Equiv.swap_apply_left v v_new⟩
  · ext y
    simp only [mem_image]
    constructor
    · rintro ⟨x, hxX, rfl⟩
      have hxv : x ≠ v := fun h => hvX (h ▸ hxX)
      have hxn : x ≠ v_new := fun h => hnew (h ▸ hX hxX)
      rwa [Equiv.swap_apply_of_ne_of_ne hxv hxn]
    · intro hyX
      have hyv : y ≠ v := fun h => hvX (h ▸ hyX)
      have hyn : y ≠ v_new := fun h => hnew (h ▸ hX hyX)
      exact ⟨y, hyX, Equiv.swap_apply_of_ne_of_ne hyv hyn⟩

theorem hasDisjointPaths_of_iso {K K' : SimpleGraph α} (φ : K ≃g K') {X Y : Set α} {k : ℕ}
    (h : HasDisjointPaths K X Y k) :
    HasDisjointPaths K' (φ '' X) (φ '' Y) k := by
  rcases h with ⟨P, hdisj⟩
  refine ⟨fun i =>
    { first := φ (P i).first
      last := φ (P i).last
      walk := (P i).walk.map φ.toHom
      isPath := (P i).isPath.map φ.injective
      first_mem := mem_image_of_mem φ (P i).first_mem
      last_mem := mem_image_of_mem φ (P i).last_mem }, ?_⟩
  intro i j hij
  rw [disjoint_iff_inter_eq_empty]
  ext z
  simp only [mem_inter_iff, mem_ofPred_eq, SimpleGraph.Walk.support_map, List.mem_map,
    mem_empty_iff_false, iff_false, not_and]
  rintro ⟨x, hx, rfl⟩ ⟨y, hy, hy_eq⟩
  have hxy : x = y := (φ.injective hy_eq).symm
  subst hxy
  exact Set.disjoint_left.mp (hdisj hij) hx hy

/-- Given a support `F ⊆ C`, `splitDelta Γ r F_star μ F v` is the set of edges `e` incident with `v`
such that `e ∈ (μ (.space s)).edgeSet` for some space `s ⊆ F ∩ (F_star 0 ∪ ... ∪ F_star (r-1))`
(Graph Minors XXI, Section 8, page 34 of the preprint). -/
def splitDelta (Γ : Drawing S) (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β) (F : Set S) (v : α) : Set β :=
  {e : β | ∃ j : Fin r, ∃ s ∈ drawingSpaces Γ, s ⊆ F_star j ∧ s ⊆ F ∧ (μ (.space s)).Inc e v}

/-- The modified unit map `μ'` obtained by replacing `v` with `v₁` in units in `F₁` and with `v₂`
in units in `F₂` (Graph Minors XXI, Section 8, page 34 of the preprint).
For non-units (`¬ IsValidUnit Γ r F_star x`), `splitMu` returns `emptyHypergraph α β`. The print
writes "if $v \in V(\Gamma) \cap bd(\Sigma)$" and "if $v \in V(\Gamma) \cap F_i$" in the cases for a
vertex $u$, where $u$ is meant. We use $u$ (see the correction to (8.2) and the definition of
$\mu'$ in `corrections/GM21.md`). -/
noncomputable def splitMu (Γ : Drawing S) (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β) (F₁ F₂ : Set S) (v v₁ v₂ : α)
    (x : BoundaryUnit S) : Hypergraph α β :=
  if IsValidUnit Γ r F_star x then
    if v ∈ (μ x).vertexSet then
      if x.InSet F₁ then replaceVertex (μ x) v v₁
      else if x.InSet F₂ then replaceVertex (μ x) v v₂
      else μ x
    else μ x
  else emptyHypergraph α β

/-- Existence of `u_star ∈ Γ.V ∩ C` and the two supports `F₁, F₂ ⊆ C` partitioning `C \ s_star`
in the vertex-splitting construction of Section 8 (page 34 of the preprint). -/
theorem exists_split_data {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) :
    ∃ (u_star : S) (F₁ F₂ : Set S),
      u_star ∈ Γ.V ∩ C ∧ v ∉ (μ (.vertex u_star)).vertexSet ∧
      u_star ≠ u₁ ∧ u_star ≠ u₂ ∧
      F₁ ⊆ C ∧ F₂ ⊆ C ∧
      SupportHasEnds Γ F₁ u₁ u_star ∧
      SupportHasEnds Γ F₂ u₂ u_star ∧
      u₁ ∈ F₁ ∧ u₁ ∉ F₂ ∧ u₂ ∈ F₂ ∧ u₂ ∉ F₁ ∧
      F₁ ∪ F₂ = C \ s_star ∧
      F₁ ∩ F₂ = {u_star} ∧
      Disjoint F₁ s_star ∧ Disjoint F₂ s_star ∧
      (∀ s ∈ drawingSpaces Γ, s ⊆ C → s ≠ s_star →
        (s ⊆ F₁ ∧ closure s ⊆ F₁ ∧ Disjoint s F₂) ∨
        (s ⊆ F₂ ∧ closure s ⊆ F₂ ∧ Disjoint s F₁)) ∧
      (∀ F ∈ ({F₁, F₂} : Set (Set S)),
        ∀ (x₁ x₂ : BoundaryUnit S) (a b : S),
          a ∈ C ∩ Γ.V → b ∈ C ∩ Γ.V →
          ((∃ w ∈ F, x₁ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₁ = .space s)) →
          ((∃ w ∈ F, x₂ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₂ = .space s)) →
          InCuffOrder C x₁.toSet a x₂.toSet b →
          (a ∈ F ∧ InCuffOrder C x₁.toSet a x₂.toSet u_star) ∨
          (b ∈ F ∧ InCuffOrder C x₁.toSet u_star x₂.toSet b)) := by
  have hu_star_ex : ∃ u_star ∈ Γ.V ∩ C, v ∉ (μ (.vertex u_star)).vertexSet := by
    by_contra h_all
    push Not at h_all
    have hv_inter : v ∈ ⋂ u ∈ Γ.V ∩ C, (μ (.vertex u)).vertexSet :=
      mem_iInter₂.mpr h_all
    rw [hpp.p4_inter_null C hC] at hv_inter
    exact hv_inter
  rcases hu_star_ex with ⟨u_star, hu_star, hv_not_ustar⟩
  have hu_star_ne₁ : u_star ≠ u₁ := fun h => hv_not_ustar (h ▸ hv.1)
  have hu_star_ne₂ : u_star ≠ u₂ := fun h => hv_not_ustar (h ▸ hv.2)
  obtain ⟨F₁, F₂, hprops⟩ :=
    exists_split_supports_of_uncovered_space hpp.is_surface hpp.cuff_vertices_ge_two
      hC hs_star hs_star_C hu_star hu_star_ne₁ hu_star_ne₂
  exact ⟨u_star, F₁, F₂, hu_star, hv_not_ustar, hu_star_ne₁, hu_star_ne₂, hprops⟩

/-- The chosen vertex `u^* ∈ Γ.V ∩ C` with `v ∉ V(μ(u^*))` in the vertex-splitting construction. -/
noncomputable def pseudoSplitUStar {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) : S :=
  (exists_split_data hpp hC hs_star hs_star_C hv).choose

/-- The first chosen support `F₁ ⊆ C` (with ends `u₁, u^*`) in the vertex-splitting construction. -/
noncomputable def pseudoSplitSupport₁ {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) : Set S :=
  (exists_split_data hpp hC hs_star hs_star_C hv).choose_spec.choose

/-- The second chosen support `F₂ ⊆ C` (with ends `u₂, u^*`) in the vertex-splitting construction. -/
noncomputable def pseudoSplitSupport₂ {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) : Set S :=
  (exists_split_data hpp hC hs_star hs_star_C hv).choose_spec.choose_spec.choose

/-- Specification of `pseudoSplitUStar`, `pseudoSplitSupport₁`, and `pseudoSplitSupport₂`. -/
theorem pseudoSplit_spec {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) :
    let u_star := pseudoSplitUStar hpp hC hs_star hs_star_C hv
    let F₁ := pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv
    let F₂ := pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv
    u_star ∈ Γ.V ∩ C ∧ v ∉ (μ (.vertex u_star)).vertexSet ∧
    u_star ≠ u₁ ∧ u_star ≠ u₂ ∧
    F₁ ⊆ C ∧ F₂ ⊆ C ∧
    SupportHasEnds Γ F₁ u₁ u_star ∧
    SupportHasEnds Γ F₂ u₂ u_star ∧
    u₁ ∈ F₁ ∧ u₁ ∉ F₂ ∧ u₂ ∈ F₂ ∧ u₂ ∉ F₁ ∧
    F₁ ∪ F₂ = C \ s_star ∧
    F₁ ∩ F₂ = {u_star} ∧
    Disjoint F₁ s_star ∧ Disjoint F₂ s_star ∧
    (∀ s ∈ drawingSpaces Γ, s ⊆ C → s ≠ s_star →
      (s ⊆ F₁ ∧ closure s ⊆ F₁ ∧ Disjoint s F₂) ∨
      (s ⊆ F₂ ∧ closure s ⊆ F₂ ∧ Disjoint s F₁)) ∧
    (∀ F ∈ ({F₁, F₂} : Set (Set S)),
      ∀ (x₁ x₂ : BoundaryUnit S) (a b : S),
        a ∈ C ∩ Γ.V → b ∈ C ∩ Γ.V →
        ((∃ w ∈ F, x₁ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₁ = .space s)) →
        ((∃ w ∈ F, x₂ = .vertex w) ∨ (∃ s ∈ drawingSpaces Γ, s ⊆ F ∧ x₂ = .space s)) →
        InCuffOrder C x₁.toSet a x₂.toSet b →
        (a ∈ F ∧ InCuffOrder C x₁.toSet a x₂.toSet u_star) ∨
        (b ∈ F ∧ InCuffOrder C x₁.toSet u_star x₂.toSet b)) :=
  (exists_split_data hpp hC hs_star hs_star_C hv).choose_spec.choose_spec.choose_spec

/-- The edge set `δ₁` in the vertex-splitting construction of Section 8. -/
noncomputable def pseudoSplitDelta₁ {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) : Set β :=
  splitDelta Γ r F_star μ (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv) v

/-- The edge set `δ₂` in the vertex-splitting construction of Section 8. -/
noncomputable def pseudoSplitDelta₂ {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) : Set β :=
  splitDelta Γ r F_star μ (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv) v

/-- The split graph `G'` in the vertex-splitting construction of Section 8. -/
noncomputable def pseudoSplitGraph {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) (v₁ v₂ : α) : Hypergraph α β :=
  vertexSplitHypergraph G v v₁ v₂
    (pseudoSplitDelta₁ hpp hC hs_star hs_star_C hv)
    (pseudoSplitDelta₂ hpp hC hs_star hs_star_C hv)

/-- The modified unit map `μ'` in the vertex-splitting construction of Section 8. -/
noncomputable def pseudoSplitMu {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) (v₁ v₂ : α) :
    BoundaryUnit S → Hypergraph α β :=
  splitMu Γ r F_star μ
    (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv)
    (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv) v v₁ v₂

/-- Any valid unit `x` in a pseudo-presentation satisfies `μ x ≤ G`. -/
theorem validUnit_le {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {x : BoundaryUnit S} (hx : IsValidUnit Γ r F_star x) :
    μ x ≤ G := by
  rcases hx with ⟨u, hu, rfl⟩ | ⟨s, hs, ⟨j, hsF⟩, rfl⟩
  · have hu_cov := hpp.bd_vertices_covered hu
    rw [mem_iUnion] at hu_cov
    rcases hu_cov with ⟨j, hj⟩
    exact (hpp.μ_vertex j u ⟨hu.1, hj⟩).1
  · exact hpp.μ_space j s hs hsF

/-- In the setup of `(8.2)`, `v ∈ G.vertexSet` and `v ∉ Γ_sub.vertexSet`. -/
theorem v_mem_and_not_mem_drawing {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {s_star : Set S} {u₁ u₂ : S} {v : α}
    (hs_star : SpaceHasEnds Γ s_star u₁ u₂)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet) :
    v ∈ G.vertexSet ∧ v ∉ Γ_sub.vertexSet := by
  have hu₁_cov := hpp.bd_vertices_covered hs_star.2.1
  rw [mem_iUnion] at hu₁_cov
  rcases hu₁_cov with ⟨j₁, hj₁⟩
  have hu₂_cov := hpp.bd_vertices_covered hs_star.2.2.1
  rw [mem_iUnion] at hu₂_cov
  rcases hu₂_cov with ⟨j₂, hj₂⟩
  have hvG : v ∈ G.vertexSet := (hpp.μ_vertex j₁ u₁ ⟨hs_star.2.1.1, hj₁⟩).1.vertexSet_subset hv.1
  refine ⟨hvG, ?_⟩
  intro hvΓ
  have hv₁ : v = ιV u₁ := by
    have : v ∈ (μ (.vertex u₁)).vertexSet ∩ Γ_sub.vertexSet := ⟨hv.1, hvΓ⟩
    rwa [(hpp.μ_vertex j₁ u₁ ⟨hs_star.2.1.1, hj₁⟩).2.2.2, mem_singleton_iff] at this
  have hv₂ : v = ιV u₂ := by
    have : v ∈ (μ (.vertex u₂)).vertexSet ∩ Γ_sub.vertexSet := ⟨hv.2, hvΓ⟩
    rwa [(hpp.μ_vertex j₂ u₂ ⟨hs_star.2.2.1.1, hj₂⟩).2.2.2, mem_singleton_iff] at this
  have hu_eq : u₁ = u₂ := hpp.ιV_injOn hs_star.2.1.1 hs_star.2.2.1.1 (hv₁.symm.trans hv₂)
  exact hs_star.2.2.2.1 hu_eq

/-- Every valid unit `x` with `v ∈ (μ x).vertexSet` lies in `C` and belongs either to `F₁ \ F₂`
or to `F₂ \ F₁`. -/
theorem validUnit_dichotomy_of_v_mem {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet)
    {x : BoundaryUnit S} (hx : IsValidUnit Γ r F_star x) (hvx : v ∈ (μ x).vertexSet) :
    x.InSet C ∧
    ((x.InSet (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv) ∧
      ¬ x.InSet (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv)) ∨
     (x.InSet (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv) ∧
      ¬ x.InSet (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv))) := by
  have : T2Space S := hpp.is_surface.2.1
  obtain ⟨_, hv_not_ustar, _, _, _, _, _, _, _, _, _, _,
    hF_union, hF_inter, _, _, h_space_dichot, _⟩ :=
    pseudoSplit_spec hpp hC hs_star hs_star_C hv
  have hu₁_C : u₁ ∈ C := by
    have hcl : u₁ ∈ closure s_star := by
      rw [hs_star.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
    exact closure_minimal hs_star_C (isClosed_cuff_univ hpp.is_surface hC) hcl
  rcases hx with ⟨u, hu_bd, rfl⟩ | ⟨s, hs, ⟨j, hsF⟩, rfl⟩
  · -- x = .vertex u
    have hu_cuff_ex : ∃ C' ∈ cuffs S, u ∈ C' := by
      have h := hu_bd.2
      rwa [← sUnion_cuffs (S := S), mem_sUnion] at h
    rcases hu_cuff_ex with ⟨C', hC', huC'⟩
    have hC'_eq : C' = C := by
      by_contra hne
      exact Set.disjoint_left.mp
        (hpp.p1_diff_cuff_disjoint C hC C' hC' (Ne.symm hne) (.vertex u₁) (.vertex u) hu₁_C huC')
        hv.1 hvx
    subst hC'_eq
    have hu_not_sstar : u ∉ s_star := fun h =>
      (subset_bd_diff_of_mem_drawingSpaces hs_star.1 h).2 hu_bd.1
    have hu_union : u ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv ∪
        pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv := by
      rw [hF_union]; exact ⟨huC', hu_not_sstar⟩
    have hu_ne_ustar : u ≠ pseudoSplitUStar hpp hC hs_star hs_star_C hv :=
      fun h => hv_not_ustar (h ▸ hvx)
    refine ⟨huC', ?_⟩
    rcases hu_union with huF₁ | huF₂
    · refine Or.inl ⟨huF₁, fun huF₂ => hu_ne_ustar ?_⟩
      have : u ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv ∩
          pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv := ⟨huF₁, huF₂⟩
      rwa [hF_inter, mem_singleton_iff] at this
    · refine Or.inr ⟨huF₂, fun huF₁ => hu_ne_ustar ?_⟩
      have : u ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv ∩
          pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv := ⟨huF₁, huF₂⟩
      rwa [hF_inter, mem_singleton_iff] at this
  · -- x = .space s
    obtain ⟨C', hC', hsC', hs_ne_empty⟩ :=
      exists_cuff_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs
    have hC'_eq : C' = C := by
      by_contra hne
      exact Set.disjoint_left.mp
        (hpp.p1_diff_cuff_disjoint C hC C' hC' (Ne.symm hne) (.vertex u₁) (.space s) hu₁_C hsC')
        hv.1 hvx
    subst hC'_eq
    have hs_ne : s ≠ s_star := fun h => huncov j (h ▸ hsF)
    refine ⟨hsC', ?_⟩
    rcases h_space_dichot s hs hsC' hs_ne with ⟨hsF₁, _, hdisj₂⟩ | ⟨hsF₂, _, hdisj₁⟩
    · refine Or.inl ⟨hsF₁, fun hsF₂ => ?_⟩
      rcases hs_ne_empty with ⟨z, hzs⟩
      exact Set.disjoint_left.mp hdisj₂ hzs (hsF₂ hzs)
    · refine Or.inr ⟨hsF₂, fun hsF₁ => ?_⟩
      rcases hs_ne_empty with ⟨z, hzs⟩
      exact Set.disjoint_left.mp hdisj₁ hzs (hsF₁ hzs)

/-- The sets `δ₁` and `δ₂` in the vertex-splitting construction are disjoint and their union is
`incidentEdges G v`, so `pseudoSplitGraph` satisfies `IsVertexSplit`. -/
theorem isVertexSplit_pseudoSplit {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v v₁ v₂ : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet)
    (hv₁ : v₁ ∉ G.vertexSet) (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂) :
    IsVertexSplit G (pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂) v v₁ v₂
      (pseudoSplitDelta₁ hpp hC hs_star hs_star_C hv)
      (pseudoSplitDelta₂ hpp hC hs_star hs_star_C hv) := by
  obtain ⟨hvG, hv_not_Γ⟩ := v_mem_and_not_mem_drawing hpp hs_star hv
  obtain ⟨hu_star, _, _, _, _, _, _, _, _, _, _, _, _, hF_inter, _, _, _, _⟩ :=
    pseudoSplit_spec hpp hC hs_star hs_star_C hv
  apply isVertexSplit_vertexSplitHypergraph hvG hv₁ hv₂ hne
  · -- Disjoint δ₁ δ₂
    rw [disjoint_iff_inter_eq_empty]
    ext e
    simp only [mem_inter_iff, pseudoSplitDelta₁, pseudoSplitDelta₂, splitDelta, mem_ofPred_eq,
      mem_empty_iff_false, iff_false, not_and]
    rintro ⟨j₁, s₁, hs₁, hs₁F_star, hs₁F₁, hinc₁⟩ ⟨j₂, s₂, hs₂, hs₂F_star, hs₂F₂, hinc₂⟩
    have he₁ : e ∈ (μ (.space s₁)).edgeSet := (μ (.space s₁)).edge_mem_of_inc hinc₁
    have he₂ : e ∈ (μ (.space s₂)).edgeSet := (μ (.space s₂)).edge_mem_of_inc hinc₂
    have hs_eq : s₁ = s₂ := by
      by_contra hne_s
      exact Set.disjoint_left.mp
        (hpp.p1_edge_disjoint_spaces s₁ hs₁ s₂ hs₂ ⟨j₁, hs₁F_star⟩ ⟨j₂, hs₂F_star⟩ hne_s)
        he₁ he₂
    subst hs_eq
    rcases (isConnected_of_mem_drawingSpaces hs₁).nonempty with ⟨z, hzs⟩
    have hz_inter : z ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv ∩
        pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv := ⟨hs₁F₁ hzs, hs₂F₂ hzs⟩
    rw [hF_inter, mem_singleton_iff] at hz_inter
    subst hz_inter
    exact (subset_bd_diff_of_mem_drawingSpaces hs₁ hzs).2 hu_star.1
  · -- δ₁ ∪ δ₂ = incidentEdges G v
    ext e
    simp only [mem_union, pseudoSplitDelta₁, pseudoSplitDelta₂, splitDelta, mem_ofPred_eq,
      incidentEdges]
    constructor
    · rintro (⟨j, s, hs, hsF_star, _, hinc⟩ | ⟨j, s, hs, hsF_star, _, hinc⟩)
      · have hle := hpp.μ_space j s hs hsF_star
        exact ⟨hle.edgeSet_subset ((μ (.space s)).edge_mem_of_inc hinc), GM10.inc_of_le hle hinc⟩
      · have hle := hpp.μ_space j s hs hsF_star
        exact ⟨hle.edgeSet_subset ((μ (.space s)).edge_mem_of_inc hinc), GM10.inc_of_le hle hinc⟩
    · rintro ⟨heG, hincG⟩
      rw [hpp.p1_union_E] at heG
      rcases heG with heΓ | he_supp
      · have hincΓ : Γ_sub.Inc e v := (GM10.inc_iff_of_le hpp.drawing_subgraph heΓ).2 hincG
        exact (hv_not_Γ (Γ_sub.vertex_mem_of_inc hincΓ)).elim
      · rw [mem_iUnion] at he_supp
        rcases he_supp with ⟨j, hej⟩
        rcases (mem_supportGraph_edgeSet_iff hpp j).1 hej with ⟨s, hs, hsF_star, hes⟩
        have hinc_s : (μ (.space s)).Inc e v :=
          (GM10.inc_iff_of_le (hpp.μ_space j s hs hsF_star) hes).2 hincG
        have hvs : v ∈ (μ (.space s)).vertexSet := (μ (.space s)).vertex_mem_of_inc hinc_s
        have hx_valid : IsValidUnit Γ r F_star (.space s) := Or.inr ⟨s, hs, ⟨j, hsF_star⟩, rfl⟩
        obtain ⟨_, ⟨hsF₁, _⟩ | ⟨hsF₂, _⟩⟩ :=
          validUnit_dichotomy_of_v_mem hpp hC hs_star hs_star_C huncov hv hx_valid hvs
        · exact Or.inl ⟨j, s, hs, hsF_star, hsF₁, hinc_s⟩
        · exact Or.inr ⟨j, s, hs, hsF_star, hsF₂, hinc_s⟩

/-- Characterization of `pseudoSplitMu` on a valid unit `x`. -/
theorem pseudoSplitMu_of_validUnit {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet)
    (v₁ v₂ : α) {x : BoundaryUnit S} (hx : IsValidUnit Γ r F_star x) :
    (v ∉ (μ x).vertexSet ∧
      pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x = μ x) ∨
    (v ∈ (μ x).vertexSet ∧
      x.InSet (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv) ∧
      ¬ x.InSet (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv) ∧
      pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x = replaceVertex (μ x) v v₁) ∨
    (v ∈ (μ x).vertexSet ∧
      x.InSet (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv) ∧
      ¬ x.InSet (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv) ∧
      pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x = replaceVertex (μ x) v v₂) := by
  dsimp only [pseudoSplitMu, splitMu]
  rw [if_pos hx]
  by_cases hvx : v ∈ (μ x).vertexSet
  · rw [if_pos hvx]
    obtain ⟨_, ⟨hxF₁, hx_notF₂⟩ | ⟨hxF₂, hx_notF₁⟩⟩ :=
      validUnit_dichotomy_of_v_mem hpp hC hs_star hs_star_C huncov hv hx hvx
    · rw [if_pos hxF₁]
      exact Or.inr (Or.inl ⟨hvx, hxF₁, hx_notF₂, rfl⟩)
    · rw [if_neg hx_notF₁, if_pos hxF₂]
      exact Or.inr (Or.inr ⟨hvx, hxF₂, hx_notF₁, rfl⟩)
  · rw [if_neg hvx]
    exact Or.inl ⟨hvx, rfl⟩

/-- Every unit `pseudoSplitMu ... x` is a subhypergraph of `pseudoSplitGraph`. -/
theorem pseudoSplitMu_le_pseudoSplitGraph {G : Hypergraph α β} {Γ : Drawing S}
    {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v v₁ v₂ : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet)
    (hv₁ : v₁ ∉ G.vertexSet) (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂)
    (x : BoundaryUnit S) :
    pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x ≤
      pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂ := by
  have hsplit := isVertexSplit_pseudoSplit hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne
  by_cases hx : IsValidUnit Γ r F_star x
  · have hμx_le : μ x ≤ G := validUnit_le hpp hx
    rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx with
      ⟨hvx, h_eq⟩ | ⟨hvx, hxF₁, _, h_eq⟩ | ⟨hvx, hxF₂, _, h_eq⟩
    · rw [h_eq]
      exact le_split_of_not_mem hsplit hμx_le hvx
    · rw [h_eq]
      refine replaceVertex_le_split_left hsplit hμx_le ?_
      intro e he hinc
      rcases hx with ⟨u, hu_bd, rfl⟩ | ⟨s, hs, ⟨j, hsF⟩, rfl⟩
      · have hu_cov := hpp.bd_vertices_covered hu_bd
        rw [mem_iUnion] at hu_cov
        rcases hu_cov with ⟨j, hj⟩
        rw [(hpp.μ_vertex j u ⟨hu_bd.1, hj⟩).2.1] at he
        exact he.elim
      · exact ⟨j, s, hs, hsF, hxF₁, hinc⟩
    · rw [h_eq]
      refine replaceVertex_le_split_right hsplit hμx_le ?_
      intro e he hinc
      rcases hx with ⟨u, hu_bd, rfl⟩ | ⟨s, hs, ⟨j, hsF⟩, rfl⟩
      · have hu_cov := hpp.bd_vertices_covered hu_bd
        rw [mem_iUnion] at hu_cov
        rcases hu_cov with ⟨j, hj⟩
        rw [(hpp.μ_vertex j u ⟨hu_bd.1, hj⟩).2.1] at he
        exact he.elim
      · exact ⟨j, s, hs, hsF, hxF₂, hinc⟩
  · dsimp only [pseudoSplitMu, splitMu]
    rw [if_neg hx]
    exact emptyHypergraph_le _

/-- **Graph Minors XXI, (8.2)** (page 34 of the preprint):
"$\Sigma, F_1^*, \dots, F_r^*, \mu'$ is a pseudo-presentation of $G'$."

The print's $\Sigma$ is a misprint for $\Gamma$, and Lean uses $\Gamma$ (see the correction to
(8.2) in `corrections/GM21.md`). -/
theorem theorem_8_2_proof {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    {C s_star : Set S} {u₁ u₂ : S} {v v₁ v₂ : α}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet)
    (hv₁ : v₁ ∉ G.vertexSet) (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂) :
    IsPseudoPresentation
      (pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂)
      Γ Γ_sub ιV ιE r F_star
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂) q := by
  have : T2Space S := hpp.is_surface.2.1
  have hsplit := isVertexSplit_pseudoSplit hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne
  obtain ⟨hvG, hv_not_Γ⟩ := v_mem_and_not_mem_drawing hpp hs_star hv
  have hv₁_not_Γ : v₁ ∉ Γ_sub.vertexSet := fun h => hv₁ (hpp.drawing_subgraph.vertexSet_subset h)
  have hv₂_not_Γ : v₂ ∉ Γ_sub.vertexSet := fun h => hv₂ (hpp.drawing_subgraph.vertexSet_subset h)
  obtain ⟨hu_star, hv_not_ustar, _, _, hF₁C, hF₂C, hF₁_ends, hF₂_ends,
    hu₁_F₁, _, hu₂_F₂, _, _, _, _, _, _, h_order_prop⟩ :=
    pseudoSplit_spec hpp hC hs_star hs_star_C hv
  have hF_sub_bd : ∀ j : Fin r, F_star j ⊆ bd S :=
    fun j => subset_bd_of_isSupportOfDrawing (hpp.supports_isSupport j)
  have h_valid_vert : ∀ j : Fin r, ∀ u ∈ Γ.V ∩ F_star j, IsValidUnit Γ r F_star (.vertex u) :=
    fun j u hu => Or.inl ⟨u, ⟨hu.1, hF_sub_bd j hu.2⟩, rfl⟩
  have h_valid_space : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j →
      IsValidUnit Γ r F_star (.space s) :=
    fun j s hs hsF => Or.inr ⟨s, hs, ⟨j, hsF⟩, rfl⟩
  have h_edge_eq : ∀ x : BoundaryUnit S, IsValidUnit Γ r F_star x →
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x).edgeSet = (μ x).edgeSet := by
    intro x hx
    rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx with
      ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩ <;> rw [h_eq] <;> rfl
  have h_inter_Γ : ∀ x : BoundaryUnit S, IsValidUnit Γ r F_star x →
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x).vertexSet ∩ Γ_sub.vertexSet =
        (μ x).vertexSet ∩ Γ_sub.vertexSet := by
    intro x hx
    rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx with
      ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩
    · rw [h_eq]
    · rw [h_eq, replaceVertex_vertexSet]
      ext w
      simp only [mem_inter_iff, mem_union, mem_sdiff, mem_singleton_iff]
      refine ⟨?_, fun ⟨hwx, hwΓ⟩ => ⟨Or.inl ⟨hwx, fun h => hv_not_Γ (h ▸ hwΓ)⟩, hwΓ⟩⟩
      rintro ⟨⟨hwx, _⟩ | rfl, hwΓ⟩
      · exact ⟨hwx, hwΓ⟩
      · exact (hv₁_not_Γ hwΓ).elim
    · rw [h_eq, replaceVertex_vertexSet]
      ext w
      simp only [mem_inter_iff, mem_union, mem_sdiff, mem_singleton_iff]
      refine ⟨?_, fun ⟨hwx, hwΓ⟩ => ⟨Or.inl ⟨hwx, fun h => hv_not_Γ (h ▸ hwΓ)⟩, hwΓ⟩⟩
      rintro ⟨⟨hwx, _⟩ | rfl, hwΓ⟩
      · exact ⟨hwx, hwΓ⟩
      · exact (hv₂_not_Γ hwΓ).elim
  have hμ'_vertex : ∀ j : Fin r, ∀ u ∈ Γ.V ∩ F_star j,
      pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex u) ≤
        pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂ ∧
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex u)).edgeSet = ∅ ∧
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex u)).vertexSet.ncard = q j ∧
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex u)).vertexSet ∩ Γ_sub.vertexSet =
        {ιV u} := by
    intro j u hu
    have hx := h_valid_vert j u hu
    have hμu := hpp.μ_vertex j u hu
    refine ⟨pseudoSplitMu_le_pseudoSplitGraph hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne (.vertex u),
      by rw [h_edge_eq _ hx, hμu.2.1], ?_, by rw [h_inter_Γ _ hx, hμu.2.2.2]⟩
    rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx with
      ⟨_, h_eq⟩ | ⟨hvu, _, _, h_eq⟩ | ⟨hvu, _, _, h_eq⟩
    · rw [h_eq, hμu.2.2.1]
    · rw [h_eq, replaceVertex_vertexSet_ncard hvu (fun h => hv₁ (hμu.1.vertexSet_subset h)), hμu.2.2.1]
    · rw [h_eq, replaceVertex_vertexSet_ncard hvu (fun h => hv₂ (hμu.1.vertexSet_subset h)), hμu.2.2.1]
  have hμ'_space : ∀ j : Fin r, ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j →
      pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.space s) ≤
        pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂ :=
    fun _ s _ _ => pseudoSplitMu_le_pseudoSplitGraph hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne (.space s)
  refine
    { is_surface := hpp.is_surface
      is_connected_surface := hpp.is_connected_surface
      is_proper_drawing := hpp.is_proper_drawing
      cuff_vertices_ge_two := hpp.cuff_vertices_ge_two
      drawing_subgraph := le_split_of_not_mem hsplit hpp.drawing_subgraph hv_not_Γ
      drawing_iso := hpp.drawing_iso
      supports_isSupport := hpp.supports_isSupport
      supports_disjoint := hpp.supports_disjoint
      bd_vertices_covered := hpp.bd_vertices_covered
      q_pos := hpp.q_pos
      μ_vertex := hμ'_vertex
      μ_space := hμ'_space
      p1_union_V := ?_
      p1_union_E := ?_
      p1_edge_disjoint_drawing := ?_
      p1_edge_disjoint_spaces := ?_
      p1_diff_cuff_disjoint := ?_
      p2_space := ?_
      p3_order := ?_
      p4_inter_null := ?_ }
  · -- p1_union_V
    ext w
    simp only [mem_union, mem_iUnion]
    constructor
    · intro hwG'
      have hwG'_copy := hwG'
      rw [hsplit.vertexSet_eq] at hwG'
      rcases hwG' with ⟨hwG, hwv⟩ | hw_eq₁ | hw_eq₂
      · rw [hpp.p1_union_V] at hwG
        rcases hwG with hwΓ | hw_supp
        · exact Or.inl hwΓ
        · rw [mem_iUnion] at hw_supp
          rcases hw_supp with ⟨j, hwj⟩
          right
          refine ⟨j, hwG'_copy, ?_⟩
          rcases (mem_supportGraph_vertexSet_iff hpp j).1 hwj with ⟨s, hs, hsF, hws⟩ | ⟨u, hu, hwu⟩
          · left
            rw [mem_iUnion₂]
            refine ⟨s, ⟨hs, hsF⟩, ?_⟩
            rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂
              (h_valid_space j s hs hsF) with ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩
            · rwa [h_eq]
            · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hws, hwv⟩
            · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hws, hwv⟩
          · right
            rw [mem_iUnion₂]
            refine ⟨u, hu, ?_⟩
            rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂
              (h_valid_vert j u hu) with ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩
            · rwa [h_eq]
            · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hwu, hwv⟩
            · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hwu, hwv⟩
      · -- w = v₁: u₁ ∈ Γ.V ∩ F_star j₁ and u₁ ∈ F₁
        subst w
        have hu₁_cov := hpp.bd_vertices_covered hs_star.2.1
        rw [mem_iUnion] at hu₁_cov
        rcases hu₁_cov with ⟨j₁, hj₁⟩
        right
        refine ⟨j₁, hwG'_copy, Or.inr ?_⟩
        rw [mem_iUnion₂]
        refine ⟨u₁, ⟨hs_star.2.1.1, hj₁⟩, ?_⟩
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂
          (h_valid_vert j₁ u₁ ⟨hs_star.2.1.1, hj₁⟩) with
          ⟨hnot, _⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, hnot_F₁, _⟩
        · exact (hnot hv.1).elim
        · rw [h_eq, replaceVertex_vertexSet]; exact Or.inr rfl
        · exact (hnot_F₁ hu₁_F₁).elim
      · -- w = v₂: u₂ ∈ Γ.V ∩ F_star j₂ and u₂ ∈ F₂
        subst w
        have hu₂_cov := hpp.bd_vertices_covered hs_star.2.2.1
        rw [mem_iUnion] at hu₂_cov
        rcases hu₂_cov with ⟨j₂, hj₂⟩
        right
        refine ⟨j₂, hwG'_copy, Or.inr ?_⟩
        rw [mem_iUnion₂]
        refine ⟨u₂, ⟨hs_star.2.2.1.1, hj₂⟩, ?_⟩
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂
          (h_valid_vert j₂ u₂ ⟨hs_star.2.2.1.1, hj₂⟩) with
          ⟨hnot, _⟩ | ⟨_, _, hnot_F₂, _⟩ | ⟨_, _, _, h_eq⟩
        · exact (hnot hv.2).elim
        · exact (hnot_F₂ hu₂_F₂).elim
        · rw [h_eq, replaceVertex_vertexSet]; exact Or.inr rfl
    · rintro (hwΓ | ⟨j, hwj⟩)
      · exact (le_split_of_not_mem hsplit hpp.drawing_subgraph hv_not_Γ).vertexSet_subset hwΓ
      · exact hwj.1
  · -- p1_union_E
    ext e
    simp only [mem_union, mem_iUnion]
    constructor
    · intro heG'
      have heG : e ∈ G.edgeSet := hsplit.edgeSet_eq ▸ heG'
      rw [hpp.p1_union_E] at heG
      rcases heG with heΓ | he_supp
      · exact Or.inl heΓ
      · rw [mem_iUnion] at he_supp
        rcases he_supp with ⟨j, hej⟩
        rcases (mem_supportGraph_edgeSet_iff hpp j).1 hej with ⟨s, hs, hsF, hes⟩
        right
        refine ⟨j, heG', Or.inl ?_⟩
        rw [mem_iUnion₂]
        refine ⟨s, ⟨hs, hsF⟩, ?_⟩
        rwa [h_edge_eq (.space s) (h_valid_space j s hs hsF)]
    · rintro (heΓ | ⟨j, hej⟩)
      · rw [hsplit.edgeSet_eq]; exact hpp.drawing_subgraph.edgeSet_subset heΓ
      · exact hej.1
  · -- p1_edge_disjoint_drawing
    intro j s hs hsF
    rw [h_edge_eq (.space s) (h_valid_space j s hs hsF)]
    exact hpp.p1_edge_disjoint_drawing j s hs hsF
  · -- p1_edge_disjoint_spaces
    intro s₁ hs₁ s₂ hs₂ ⟨j₁, hs₁F⟩ ⟨j₂, hs₂F⟩ hne_s
    rw [h_edge_eq (.space s₁) (h_valid_space j₁ s₁ hs₁ hs₁F),
        h_edge_eq (.space s₂) (h_valid_space j₂ s₂ hs₂ hs₂F)]
    exact hpp.p1_edge_disjoint_spaces s₁ hs₁ s₂ hs₂ ⟨j₁, hs₁F⟩ ⟨j₂, hs₂F⟩ hne_s
  · -- p1_diff_cuff_disjoint
    intro C₁ hC₁ C₂ hC₂ hC_ne x₁ x₂ hx₁C₁ hx₂C₂
    by_cases hx₁ : IsValidUnit Γ r F_star x₁
    · by_cases hx₂ : IsValidUnit Γ r F_star x₂
      · rw [disjoint_iff_inter_eq_empty]
        ext w
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro hw₁ hw₂
        have hdisj_orig := hpp.p1_diff_cuff_disjoint C₁ hC₁ C₂ hC₂ hC_ne x₁ x₂ hx₁C₁ hx₂C₂
        have h_cuff_eq_C : ∀ {x : BoundaryUnit S} {C' : Set S},
            IsValidUnit Γ r F_star x → C' ∈ cuffs S → x.InSet C' → v ∈ (μ x).vertexSet → C' = C := by
          intro x C' hx hC' hxC' hvx
          obtain ⟨hxC, _⟩ := validUnit_dichotomy_of_v_mem hpp hC hs_star hs_star_C huncov hv hx hvx
          by_contra hne'
          rcases hx with ⟨u, _, rfl⟩ | ⟨s, hs, _, rfl⟩
          · exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne') hxC' hxC
          · rcases (isConnected_of_mem_drawingSpaces hs).nonempty with ⟨z, hzs⟩
            exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne') (hxC' hzs) (hxC hzs)
        have hw₁_orig : (w ∈ (μ x₁).vertexSet ∧ w ≠ v₁ ∧ w ≠ v₂) ∨
            ((w = v₁ ∨ w = v₂) ∧ v ∈ (μ x₁).vertexSet ∧ C₁ = C) := by
          rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx₁ with
            ⟨_, h_eq⟩ | ⟨hvx₁, _, _, h_eq⟩ | ⟨hvx₁, _, _, h_eq⟩
          · rw [h_eq] at hw₁
            have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
            exact Or.inl ⟨hw₁, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG)⟩
          · rw [h_eq, replaceVertex_vertexSet] at hw₁
            rcases hw₁ with ⟨hw₁, _⟩ | rfl
            · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
              exact Or.inl ⟨hw₁, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG)⟩
            · exact Or.inr ⟨Or.inl rfl, hvx₁, h_cuff_eq_C hx₁ hC₁ hx₁C₁ hvx₁⟩
          · rw [h_eq, replaceVertex_vertexSet] at hw₁
            rcases hw₁ with ⟨hw₁, _⟩ | rfl
            · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
              exact Or.inl ⟨hw₁, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG)⟩
            · exact Or.inr ⟨Or.inr rfl, hvx₁, h_cuff_eq_C hx₁ hC₁ hx₁C₁ hvx₁⟩
        have hw₂_orig : (w ∈ (μ x₂).vertexSet ∧ w ≠ v₁ ∧ w ≠ v₂) ∨
            ((w = v₁ ∨ w = v₂) ∧ v ∈ (μ x₂).vertexSet ∧ C₂ = C) := by
          rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx₂ with
            ⟨_, h_eq⟩ | ⟨hvx₂, _, _, h_eq⟩ | ⟨hvx₂, _, _, h_eq⟩
          · rw [h_eq] at hw₂
            have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₂).vertexSet_subset hw₂
            exact Or.inl ⟨hw₂, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG)⟩
          · rw [h_eq, replaceVertex_vertexSet] at hw₂
            rcases hw₂ with ⟨hw₂, _⟩ | rfl
            · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₂).vertexSet_subset hw₂
              exact Or.inl ⟨hw₂, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG)⟩
            · exact Or.inr ⟨Or.inl rfl, hvx₂, h_cuff_eq_C hx₂ hC₂ hx₂C₂ hvx₂⟩
          · rw [h_eq, replaceVertex_vertexSet] at hw₂
            rcases hw₂ with ⟨hw₂, _⟩ | rfl
            · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₂).vertexSet_subset hw₂
              exact Or.inl ⟨hw₂, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG)⟩
            · exact Or.inr ⟨Or.inr rfl, hvx₂, h_cuff_eq_C hx₂ hC₂ hx₂C₂ hvx₂⟩
        rcases hw₁_orig with ⟨hw₁_m, hw_ne₁, hw_ne₂⟩ | ⟨hw_eq, _, hC₁_eq⟩ <;>
          rcases hw₂_orig with ⟨hw₂_m, hw₂_ne₁, hw₂_ne₂⟩ | ⟨hw_eq', _, hC₂_eq⟩
        · exact Set.disjoint_left.mp hdisj_orig hw₁_m hw₂_m
        · rcases hw_eq' with rfl | rfl
          · exact hw_ne₁ rfl
          · exact hw_ne₂ rfl
        · rcases hw_eq with rfl | rfl
          · exact hw₂_ne₁ rfl
          · exact hw₂_ne₂ rfl
        · exact hC_ne (hC₁_eq.trans hC₂_eq.symm)
      · dsimp only [pseudoSplitMu, splitMu]
        rw [if_neg hx₂, emptyHypergraph_vertexSet]
        exact disjoint_empty _
    · dsimp only [pseudoSplitMu, splitMu]
      rw [if_neg hx₁, emptyHypergraph_vertexSet]
      exact empty_disjoint _
  · -- p2_space
    intro j s hs a b hsF hs_ends
    have hxs := h_valid_space j s hs hsF
    have hcl_sub_F : closure s ⊆ F_star j :=
      closure_minimal hsF (isClosed_of_isSupportOfDrawing hpp.is_surface (hpp.supports_isSupport j))
    have ha_F : a ∈ Γ.V ∩ F_star j := by
      refine ⟨hs_ends.2.1.1, hcl_sub_F ?_⟩
      rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
    have hb_F : b ∈ Γ.V ∩ F_star j := by
      refine ⟨hs_ends.2.2.1.1, hcl_sub_F ?_⟩
      rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inr rfl)
    have hxa := h_valid_vert j a ha_F
    have hxb := h_valid_vert j b hb_F
    obtain ⟨h_inter, ha_le, hb_le, hpaths⟩ := hpp.p2_space j s hs a b hsF hs_ends
    have hμs_le : μ (.space s) ≤ G := hpp.μ_space j s hs hsF
    have hv₁_not_s : v₁ ∉ (μ (.space s)).vertexSet := fun h => hv₁ (hμs_le.vertexSet_subset h)
    have hv₂_not_s : v₂ ∉ (μ (.space s)).vertexSet := fun h => hv₂ (hμs_le.vertexSet_subset h)
    have hv₁_not_a : v₁ ∉ (μ (.vertex a)).vertexSet := fun h => hv₁_not_s (ha_le.vertexSet_subset h)
    have hv₂_not_a : v₂ ∉ (μ (.vertex a)).vertexSet := fun h => hv₂_not_s (ha_le.vertexSet_subset h)
    have hv₁_not_b : v₁ ∉ (μ (.vertex b)).vertexSet := fun h => hv₁_not_s (hb_le.vertexSet_subset h)
    have hv₂_not_b : v₂ ∉ (μ (.vertex b)).vertexSet := fun h => hv₂_not_s (hb_le.vertexSet_subset h)
    refine ⟨by rw [h_inter_Γ _ hxs, h_inter], ?_⟩
    rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxs with
      ⟨hvs, hs_eq⟩ | ⟨hvs, hsF₁, _, hs_eq⟩ | ⟨hvs, hsF₂, _, hs_eq⟩
    · -- v ∉ (μ (.space s)).vertexSet
      have hva : v ∉ (μ (.vertex a)).vertexSet := fun h => hvs (ha_le.vertexSet_subset h)
      have hvb : v ∉ (μ (.vertex b)).vertexSet := fun h => hvs (hb_le.vertexSet_subset h)
      have ha_eq : pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex a) = μ (.vertex a) := by
        dsimp only [pseudoSplitMu, splitMu]; rw [if_pos hxa, if_neg hva]
      have hb_eq : pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex b) = μ (.vertex b) := by
        dsimp only [pseudoSplitMu, splitMu]; rw [if_pos hxb, if_neg hvb]
      rw [hs_eq, ha_eq, hb_eq]
      exact ⟨ha_le, hb_le, hpaths⟩
    · -- v ∈ (μ (.space s)).vertexSet and s ⊆ F₁
      have hcl_F₁ : closure s ⊆ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv :=
        closure_minimal hsF₁ (isClosed_of_supportHasEnds hpp.is_surface hF₁_ends)
      have ha_F₁ : a ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv := by
        apply hcl_F₁; rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
      have hb_F₁ : b ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv := by
        apply hcl_F₁; rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inr rfl)
      have ha_le' : pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex a) ≤
          pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.space s) := by
        rw [hs_eq]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
          ⟨hva, ha_eq⟩ | ⟨_, _, _, ha_eq⟩ | ⟨_, _, ha_notF₁, _⟩
        · rw [ha_eq]; exact le_replaceVertex_of_not_mem ha_le hva hv₁_not_a
        · rw [ha_eq]; exact replaceVertex_mono ha_le
        · exact (ha_notF₁ ha_F₁).elim
      have hb_le' : pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex b) ≤
          pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.space s) := by
        rw [hs_eq]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
          ⟨hvb, hb_eq⟩ | ⟨_, _, _, hb_eq⟩ | ⟨_, _, hb_notF₁, _⟩
        · rw [hb_eq]; exact le_replaceVertex_of_not_mem hb_le hvb hv₁_not_b
        · rw [hb_eq]; exact replaceVertex_mono hb_le
        · exact (hb_notF₁ hb_F₁).elim
      have ha_swap : (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex a)).vertexSet =
          (Equiv.swap v v₁) '' (μ (.vertex a)).vertexSet := by
        rw [image_swap_of_subset hv₁_not_s ha_le.vertexSet_subset]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
          ⟨hva, ha_eq⟩ | ⟨hva, _, _, ha_eq⟩ | ⟨_, _, ha_notF₁, _⟩
        · rw [if_neg hva, ha_eq]
        · rw [if_pos hva, ha_eq, replaceVertex_vertexSet]
        · exact (ha_notF₁ ha_F₁).elim
      have hb_swap : (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex b)).vertexSet =
          (Equiv.swap v v₁) '' (μ (.vertex b)).vertexSet := by
        rw [image_swap_of_subset hv₁_not_s hb_le.vertexSet_subset]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
          ⟨hvb, hb_eq⟩ | ⟨hvb, _, _, hb_eq⟩ | ⟨_, _, hb_notF₁, _⟩
        · rw [if_neg hvb, hb_eq]
        · rw [if_pos hvb, hb_eq, replaceVertex_vertexSet]
        · exact (hb_notF₁ hb_F₁).elim
      refine ⟨ha_le', hb_le', ?_⟩
      rw [hs_eq, ha_swap, hb_swap]
      exact hasDisjointPaths_of_iso (replaceVertexSkeletonIso hvs hv₁_not_s) hpaths
    · -- v ∈ (μ (.space s)).vertexSet and s ⊆ F₂
      have hcl_F₂ : closure s ⊆ pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv :=
        closure_minimal hsF₂ (isClosed_of_supportHasEnds hpp.is_surface hF₂_ends)
      have ha_F₂ : a ∈ pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv := by
        apply hcl_F₂; rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
      have hb_F₂ : b ∈ pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv := by
        apply hcl_F₂; rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inr rfl)
      have ha_le' : pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex a) ≤
          pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.space s) := by
        rw [hs_eq]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
          ⟨hva, ha_eq⟩ | ⟨_, _, ha_notF₂, _⟩ | ⟨_, _, _, ha_eq⟩
        · rw [ha_eq]; exact le_replaceVertex_of_not_mem ha_le hva hv₂_not_a
        · exact (ha_notF₂ ha_F₂).elim
        · rw [ha_eq]; exact replaceVertex_mono ha_le
      have hb_le' : pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex b) ≤
          pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.space s) := by
        rw [hs_eq]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
          ⟨hvb, hb_eq⟩ | ⟨_, _, hb_notF₂, _⟩ | ⟨_, _, _, hb_eq⟩
        · rw [hb_eq]; exact le_replaceVertex_of_not_mem hb_le hvb hv₂_not_b
        · exact (hb_notF₂ hb_F₂).elim
        · rw [hb_eq]; exact replaceVertex_mono hb_le
      have ha_swap : (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex a)).vertexSet =
          (Equiv.swap v v₂) '' (μ (.vertex a)).vertexSet := by
        rw [image_swap_of_subset hv₂_not_s ha_le.vertexSet_subset]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
          ⟨hva, ha_eq⟩ | ⟨_, _, ha_notF₂, _⟩ | ⟨hva, _, _, ha_eq⟩
        · rw [if_neg hva, ha_eq]
        · exact (ha_notF₂ ha_F₂).elim
        · rw [if_pos hva, ha_eq, replaceVertex_vertexSet]
      have hb_swap : (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex b)).vertexSet =
          (Equiv.swap v v₂) '' (μ (.vertex b)).vertexSet := by
        rw [image_swap_of_subset hv₂_not_s hb_le.vertexSet_subset]
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
          ⟨hvb, hb_eq⟩ | ⟨_, _, hb_notF₂, _⟩ | ⟨hvb, _, _, hb_eq⟩
        · rw [if_neg hvb, hb_eq]
        · exact (hb_notF₂ hb_F₂).elim
        · rw [if_pos hvb, hb_eq, replaceVertex_vertexSet]
      refine ⟨ha_le', hb_le', ?_⟩
      rw [hs_eq, ha_swap, hb_swap]
      exact hasDisjointPaths_of_iso (replaceVertexSkeletonIso hvs hv₂_not_s) hpaths
  · -- p3_order
    intro C' hC' x₁ x₂ a ha b hb hx₁C' hx₂C' hord
    have ha_bd : a ∈ Γ.V ∩ bd S := by
      refine ⟨ha.2, ?_⟩; rw [← sUnion_cuffs (S := S)]; exact ⟨C', hC', ha.1⟩
    have hb_bd : b ∈ Γ.V ∩ bd S := by
      refine ⟨hb.2, ?_⟩; rw [← sUnion_cuffs (S := S)]; exact ⟨C', hC', hb.1⟩
    have hxa : IsValidUnit Γ r F_star (.vertex a) := Or.inl ⟨a, ha_bd, rfl⟩
    have hxb : IsValidUnit Γ r F_star (.vertex b) := Or.inl ⟨b, hb_bd, rfl⟩
    have h_inter_le_G' :
        pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x₁ ∩
        pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ x₂ ≤
        pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂ :=
      GM10.inter_le
        (pseudoSplitMu_le_pseudoSplitGraph hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne x₁)
        (pseudoSplitMu_le_pseudoSplitGraph hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne x₂)
    have h_union_le_G' :
        pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex a) ∪
        pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂ (.vertex b) ≤
        pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂ :=
      GM10.union_le
        (pseudoSplitMu_le_pseudoSplitGraph hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne (.vertex a))
        (pseudoSplitMu_le_pseudoSplitGraph hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne (.vertex b))
    rw [GM10.le_iff_of_le h_inter_le_G' h_union_le_G']
    by_cases hx₁ : IsValidUnit Γ r F_star x₁
    · by_cases hx₂ : IsValidUnit Γ r F_star x₂
      · refine ⟨?_, ?_⟩
        · -- Vertex inclusion
          intro w ⟨hw₁, hw₂⟩
          have h_orig_le := hpp.p3_order C' hC' x₁ x₂ a ha b hb hx₁C' hx₂C' hord
          have h_w_cases :
              (w ≠ v ∧ w ≠ v₁ ∧ w ≠ v₂ ∧ w ∈ (μ x₁).vertexSet ∧ w ∈ (μ x₂).vertexSet) ∨
              (w = v₁ ∧ v ∈ (μ x₁).vertexSet ∧ v ∈ (μ x₂).vertexSet ∧
                x₁.InSet (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv) ∧
                x₂.InSet (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv)) ∨
              (w = v₂ ∧ v ∈ (μ x₁).vertexSet ∧ v ∈ (μ x₂).vertexSet ∧
                x₁.InSet (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv) ∧
                x₂.InSet (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv)) := by
            rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx₁ with
              ⟨hvx₁, h1_eq⟩ | ⟨hvx₁, hx₁F₁, _, h1_eq⟩ | ⟨hvx₁, hx₁F₂, _, h1_eq⟩ <;>
            rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hx₂ with
              ⟨hvx₂, h2_eq⟩ | ⟨hvx₂, hx₂F₁, _, h2_eq⟩ | ⟨hvx₂, hx₂F₂, _, h2_eq⟩
            · rw [h1_eq] at hw₁; rw [h2_eq] at hw₂
              have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
              exact Or.inl ⟨fun h => hvx₁ (h ▸ hw₁), fun h => hv₁ (h ▸ hwG),
                fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
            · rw [h1_eq] at hw₁; rw [h2_eq, replaceVertex_vertexSet] at hw₂
              have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
              rcases hw₂ with ⟨hw₂, _⟩ | rfl
              · exact Or.inl ⟨fun h => hvx₁ (h ▸ hw₁), fun h => hv₁ (h ▸ hwG),
                  fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
              · exact (hv₁ hwG).elim
            · rw [h1_eq] at hw₁; rw [h2_eq, replaceVertex_vertexSet] at hw₂
              have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
              rcases hw₂ with ⟨hw₂, _⟩ | rfl
              · exact Or.inl ⟨fun h => hvx₁ (h ▸ hw₁), fun h => hv₁ (h ▸ hwG),
                  fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
              · exact (hv₂ hwG).elim
            · rw [h1_eq, replaceVertex_vertexSet] at hw₁; rw [h2_eq] at hw₂
              have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₂).vertexSet_subset hw₂
              rcases hw₁ with ⟨hw₁, _⟩ | rfl
              · exact Or.inl ⟨fun h => hvx₂ (h ▸ hw₂), fun h => hv₁ (h ▸ hwG),
                  fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
              · exact (hv₁ hwG).elim
            · rw [h1_eq, replaceVertex_vertexSet] at hw₁; rw [h2_eq, replaceVertex_vertexSet] at hw₂
              rcases hw₁ with ⟨hw₁, hwv⟩ | rfl
              · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
                rcases hw₂ with ⟨hw₂, _⟩ | rfl
                · exact Or.inl ⟨hwv, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
                · exact (hv₁ hwG).elim
              · exact Or.inr (Or.inl ⟨rfl, hvx₁, hvx₂, hx₁F₁, hx₂F₁⟩)
            · rw [h1_eq, replaceVertex_vertexSet] at hw₁; rw [h2_eq, replaceVertex_vertexSet] at hw₂
              rcases hw₁ with ⟨hw₁, hwv⟩ | rfl
              · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
                rcases hw₂ with ⟨hw₂, _⟩ | rfl
                · exact Or.inl ⟨hwv, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
                · exact (hv₂ hwG).elim
              · rcases hw₂ with ⟨hw₂, _⟩ | h_eq_v
                · exact (hv₁ ((validUnit_le hpp hx₂).vertexSet_subset hw₂)).elim
                · exact (hne h_eq_v).elim
            · rw [h1_eq, replaceVertex_vertexSet] at hw₁; rw [h2_eq] at hw₂
              have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₂).vertexSet_subset hw₂
              rcases hw₁ with ⟨hw₁, _⟩ | rfl
              · exact Or.inl ⟨fun h => hvx₂ (h ▸ hw₂), fun h => hv₁ (h ▸ hwG),
                  fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
              · exact (hv₂ hwG).elim
            · rw [h1_eq, replaceVertex_vertexSet] at hw₁; rw [h2_eq, replaceVertex_vertexSet] at hw₂
              rcases hw₁ with ⟨hw₁, hwv⟩ | rfl
              · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
                rcases hw₂ with ⟨hw₂, _⟩ | rfl
                · exact Or.inl ⟨hwv, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
                · exact (hv₁ hwG).elim
              · rcases hw₂ with ⟨hw₂, _⟩ | h_eq_v
                · exact (hv₂ ((validUnit_le hpp hx₂).vertexSet_subset hw₂)).elim
                · exact (hne.symm h_eq_v).elim
            · rw [h1_eq, replaceVertex_vertexSet] at hw₁; rw [h2_eq, replaceVertex_vertexSet] at hw₂
              rcases hw₁ with ⟨hw₁, hwv⟩ | rfl
              · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hx₁).vertexSet_subset hw₁
                rcases hw₂ with ⟨hw₂, _⟩ | rfl
                · exact Or.inl ⟨hwv, fun h => hv₁ (h ▸ hwG), fun h => hv₂ (h ▸ hwG), hw₁, hw₂⟩
                · exact (hv₂ hwG).elim
              · exact Or.inr (Or.inr ⟨rfl, hvx₁, hvx₂, hx₁F₂, hx₂F₂⟩)
          rcases h_w_cases with ⟨hwv, _, _, hw₁_orig, hw₂_orig⟩ |
            ⟨hw_eq₁, hvx₁, hvx₂, hx₁F₁, hx₂F₁⟩ | ⟨hw_eq₂, hvx₁, hvx₂, hx₁F₂, hx₂F₂⟩
          · -- Case 1: w ≠ v, v₁, v₂
            have hw_ab := h_orig_le.vertexSet_subset ⟨hw₁_orig, hw₂_orig⟩
            rcases hw_ab with hwa | hwb
            · left
              rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
                ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩
              · rwa [h_eq]
              · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hwa, hwv⟩
              · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hwa, hwv⟩
            · right
              rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
                ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩
              · rwa [h_eq]
              · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hwb, hwv⟩
              · rw [h_eq, replaceVertex_vertexSet]; exact Or.inl ⟨hwb, hwv⟩
          · -- Case 2: w = v₁, x₁, x₂ in F₁
            subst w
            have hC'_eq : C' = C := by
              obtain ⟨hx₁C, _⟩ :=
                validUnit_dichotomy_of_v_mem hpp hC hs_star hs_star_C huncov hv hx₁ hvx₁
              by_contra hne_C
              rcases hx₁ with ⟨u, _, rfl⟩ | ⟨s, hs, _, rfl⟩
              · exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne_C) hx₁C' hx₁C
              · rcases (isConnected_of_mem_drawingSpaces hs).nonempty with ⟨z, hzs⟩
                exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne_C) (hx₁C' hzs) (hx₁C hzs)
            subst C'
            have hx₁_unit_F₁ :
                (∃ u ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv, x₁ = .vertex u) ∨
                (∃ s ∈ drawingSpaces Γ,
                  s ⊆ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv ∧ x₁ = .space s) := by
              rcases hx₁ with ⟨u, _, rfl⟩ | ⟨s, hs, _, rfl⟩
              · exact Or.inl ⟨u, hx₁F₁, rfl⟩
              · exact Or.inr ⟨s, hs, hx₁F₁, rfl⟩
            have hx₂_unit_F₁ :
                (∃ u ∈ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv, x₂ = .vertex u) ∨
                (∃ s ∈ drawingSpaces Γ,
                  s ⊆ pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv ∧ x₂ = .space s) := by
              rcases hx₂ with ⟨u, _, rfl⟩ | ⟨s, hs, _, rfl⟩
              · exact Or.inl ⟨u, hx₂F₁, rfl⟩
              · exact Or.inr ⟨s, hs, hx₂F₁, rfl⟩
            rcases h_order_prop (pseudoSplitSupport₁ hpp hC hs_star hs_star_C hv) (Or.inl rfl)
              x₁ x₂ a b ha hb hx₁_unit_F₁ hx₂_unit_F₁ hord with
              ⟨haF₁, hord_a⟩ | ⟨hbF₁, hord_b⟩
            · have hle_a := hpp.p3_order C hC x₁ x₂ a ha
                (pseudoSplitUStar hpp hC hs_star hs_star_C hv) ⟨hu_star.2, hu_star.1⟩
                hx₁C' hx₂C' hord_a
              have hva : v ∈ (μ (.vertex a)).vertexSet :=
                (hle_a.vertexSet_subset ⟨hvx₁, hvx₂⟩).resolve_right hv_not_ustar
              left
              rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
                ⟨hnot, _⟩ | ⟨_, _, _, ha_eq⟩ | ⟨_, _, ha_notF₁, _⟩
              · exact (hnot hva).elim
              · rw [ha_eq, replaceVertex_vertexSet]; exact Or.inr rfl
              · exact (ha_notF₁ haF₁).elim
            · have hle_b := hpp.p3_order C hC x₁ x₂
                (pseudoSplitUStar hpp hC hs_star hs_star_C hv) ⟨hu_star.2, hu_star.1⟩ b hb
                hx₁C' hx₂C' hord_b
              have hvb : v ∈ (μ (.vertex b)).vertexSet :=
                (hle_b.vertexSet_subset ⟨hvx₁, hvx₂⟩).resolve_left hv_not_ustar
              right
              rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
                ⟨hnot, _⟩ | ⟨_, _, _, hb_eq⟩ | ⟨_, _, hb_notF₁, _⟩
              · exact (hnot hvb).elim
              · rw [hb_eq, replaceVertex_vertexSet]; exact Or.inr rfl
              · exact (hb_notF₁ hbF₁).elim
          · -- Case 3: w = v₂, x₁, x₂ in F₂
            subst w
            have hC'_eq : C' = C := by
              obtain ⟨hx₁C, _⟩ :=
                validUnit_dichotomy_of_v_mem hpp hC hs_star hs_star_C huncov hv hx₁ hvx₁
              by_contra hne_C
              rcases hx₁ with ⟨u, _, rfl⟩ | ⟨s, hs, _, rfl⟩
              · exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne_C) hx₁C' hx₁C
              · rcases (isConnected_of_mem_drawingSpaces hs).nonempty with ⟨z, hzs⟩
                exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne_C) (hx₁C' hzs) (hx₁C hzs)
            subst C'
            have hx₁_unit_F₂ :
                (∃ u ∈ pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv, x₁ = .vertex u) ∨
                (∃ s ∈ drawingSpaces Γ,
                  s ⊆ pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv ∧ x₁ = .space s) := by
              rcases hx₁ with ⟨u, _, rfl⟩ | ⟨s, hs, _, rfl⟩
              · exact Or.inl ⟨u, hx₁F₂, rfl⟩
              · exact Or.inr ⟨s, hs, hx₁F₂, rfl⟩
            have hx₂_unit_F₂ :
                (∃ u ∈ pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv, x₂ = .vertex u) ∨
                (∃ s ∈ drawingSpaces Γ,
                  s ⊆ pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv ∧ x₂ = .space s) := by
              rcases hx₂ with ⟨u, _, rfl⟩ | ⟨s, hs, _, rfl⟩
              · exact Or.inl ⟨u, hx₂F₂, rfl⟩
              · exact Or.inr ⟨s, hs, hx₂F₂, rfl⟩
            rcases h_order_prop (pseudoSplitSupport₂ hpp hC hs_star hs_star_C hv) (Or.inr rfl)
              x₁ x₂ a b ha hb hx₁_unit_F₂ hx₂_unit_F₂ hord with
              ⟨haF₂, hord_a⟩ | ⟨hbF₂, hord_b⟩
            · have hle_a := hpp.p3_order C hC x₁ x₂ a ha
                (pseudoSplitUStar hpp hC hs_star hs_star_C hv) ⟨hu_star.2, hu_star.1⟩
                hx₁C' hx₂C' hord_a
              have hva : v ∈ (μ (.vertex a)).vertexSet :=
                (hle_a.vertexSet_subset ⟨hvx₁, hvx₂⟩).resolve_right hv_not_ustar
              left
              rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
                ⟨hnot, _⟩ | ⟨_, _, ha_notF₂, _⟩ | ⟨_, _, _, ha_eq⟩
              · exact (hnot hva).elim
              · exact (ha_notF₂ haF₂).elim
              · rw [ha_eq, replaceVertex_vertexSet]; exact Or.inr rfl
            · have hle_b := hpp.p3_order C hC x₁ x₂
                (pseudoSplitUStar hpp hC hs_star hs_star_C hv) ⟨hu_star.2, hu_star.1⟩ b hb
                hx₁C' hx₂C' hord_b
              have hvb : v ∈ (μ (.vertex b)).vertexSet :=
                (hle_b.vertexSet_subset ⟨hvx₁, hvx₂⟩).resolve_left hv_not_ustar
              right
              rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
                ⟨hnot, _⟩ | ⟨_, _, hb_notF₂, _⟩ | ⟨_, _, _, hb_eq⟩
              · exact (hnot hvb).elim
              · exact (hb_notF₂ hbF₂).elim
              · rw [hb_eq, replaceVertex_vertexSet]; exact Or.inr rfl
        · -- Edge inclusion
          intro e ⟨he₁, he₂⟩
          rw [h_edge_eq x₁ hx₁] at he₁
          rw [h_edge_eq x₂ hx₂] at he₂
          have he_ab := (hpp.p3_order C' hC' x₁ x₂ a ha b hb hx₁C' hx₂C' hord).edgeSet_subset ⟨he₁, he₂⟩
          rcases he_ab with hea | heb
          · exact Or.inl (by rwa [h_edge_eq (.vertex a) hxa])
          · exact Or.inr (by rwa [h_edge_eq (.vertex b) hxb])
      · refine ⟨?_, ?_⟩
        · rintro w ⟨_, hw₂⟩
          dsimp only [pseudoSplitMu, splitMu] at hw₂
          rw [if_neg hx₂] at hw₂
          exact hw₂.elim
        · rintro e ⟨_, he₂⟩
          dsimp only [pseudoSplitMu, splitMu] at he₂
          rw [if_neg hx₂] at he₂
          exact he₂.elim
    · refine ⟨?_, ?_⟩
      · rintro w ⟨hw₁, _⟩
        dsimp only [pseudoSplitMu, splitMu] at hw₁
        rw [if_neg hx₁] at hw₁
        exact hw₁.elim
      · rintro e ⟨he₁, _⟩
        dsimp only [pseudoSplitMu, splitMu] at he₁
        rw [if_neg hx₁] at he₁
        exact he₁.elim
  · -- p4_inter_null
    intro C' hC'
    ext w
    simp only [mem_iInter, mem_empty_iff_false, iff_false]
    intro hw_all
    by_cases hw_new : w = v₁ ∨ w = v₂
    · have hne_V : (Γ.V ∩ C').Nonempty := by
        have h2 := hpp.cuff_vertices_ge_two C' hC'
        exact nonempty_of_ncard_ne_zero (by omega)
      rcases hne_V with ⟨u₀, hu₀⟩
      have hu₀_bd : u₀ ∈ Γ.V ∩ bd S := by
        refine ⟨hu₀.1, ?_⟩; rw [← sUnion_cuffs (S := S)]; exact ⟨C', hC', hu₀.2⟩
      have hxu₀ : IsValidUnit Γ r F_star (.vertex u₀) := Or.inl ⟨u₀, hu₀_bd, rfl⟩
      have hwu₀ := hw_all u₀ hu₀
      have hv_u₀ : v ∈ (μ (.vertex u₀)).vertexSet := by
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxu₀ with
          ⟨_, h_eq⟩ | ⟨hvu₀, _, _, _⟩ | ⟨hvu₀, _, _, _⟩
        · rw [h_eq] at hwu₀
          have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxu₀).vertexSet_subset hwu₀
          rcases hw_new with rfl | rfl
          · exact (hv₁ hwG).elim
          · exact (hv₂ hwG).elim
        · exact hvu₀
        · exact hvu₀
      obtain ⟨hu₀C, _⟩ := validUnit_dichotomy_of_v_mem hpp hC hs_star hs_star_C huncov hv hxu₀ hv_u₀
      have hC'_eq : C' = C := by
        by_contra hne_C
        exact Set.disjoint_left.mp (cuffs_disjoint hC' hC hne_C) hu₀.2 hu₀C
      subst C'
      have hwu_star := hw_all (pseudoSplitUStar hpp hC hs_star hs_star_C hv) hu_star
      have hxu_star : IsValidUnit Γ r F_star (.vertex (pseudoSplitUStar hpp hC hs_star hs_star_C hv)) := by
        refine Or.inl ⟨_, ⟨hu_star.1, ?_⟩, rfl⟩
        rw [← sUnion_cuffs (S := S)]; exact ⟨C, hC, hu_star.2⟩
      have hu_star_eq :
          pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂
            (.vertex (pseudoSplitUStar hpp hC hs_star hs_star_C hv)) =
          μ (.vertex (pseudoSplitUStar hpp hC hs_star hs_star_C hv)) := by
        dsimp only [pseudoSplitMu, splitMu]
        rw [if_pos hxu_star, if_neg hv_not_ustar]
      rw [hu_star_eq] at hwu_star
      have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxu_star).vertexSet_subset hwu_star
      rcases hw_new with rfl | rfl
      · exact hv₁ hwG
      · exact hv₂ hwG
    · push Not at hw_new
      have hw_orig : w ∈ ⋂ u ∈ Γ.V ∩ C', (μ (.vertex u)).vertexSet := by
        rw [mem_iInter₂]
        intro u hu
        have hwu := hw_all u hu
        have hxu : IsValidUnit Γ r F_star (.vertex u) := by
          refine Or.inl ⟨u, ⟨hu.1, ?_⟩, rfl⟩
          rw [← sUnion_cuffs (S := S)]; exact ⟨C', hC', hu.2⟩
        rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxu with
          ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩
        · rwa [h_eq] at hwu
        · rw [h_eq, replaceVertex_vertexSet] at hwu
          exact (hwu.resolve_right hw_new.1).1
        · rw [h_eq, replaceVertex_vertexSet] at hwu
          exact (hwu.resolve_right hw_new.2).1
      rw [hpp.p4_inter_null C' hC'] at hw_orig
      exact hw_orig

end PseudoSplit

/-! ## Section 3: Surrounding a tangle after splitting and proof of (8.3) -/

section TangleAfterSplit

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- In any pseudo-presentation, the attachments of `μ (.space s)` in `G` (for `s ⊆ F_star j` with
ends `a, b`) are contained in `(μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet`, so the
separation `(μ (.space s), GM17.complSubhypergraph G (μ (.space s)))` has order `≤ 2 * q_vec j`. -/
theorem separationOrder_complSubhypergraph_space_le
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {μ : BoundaryUnit S → Hypergraph α β} {q_vec : Fin r → ℕ}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q_vec)
    (j : Fin r) {s : Set S} (hs : s ∈ drawingSpaces Γ) (hsF : s ⊆ F_star j) :
    separationOrder (μ (.space s)) (GM17.complSubhypergraph G (μ (.space s))) ≤ 2 * q_vec j := by
  have : T2Space S := hpp.is_surface.2.1
  obtain ⟨a, b, hs_ends⟩ :=
    exists_spaceHasEnds_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs
  obtain ⟨C, hC, hsC, _⟩ :=
    exists_cuff_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs
  have hcl_sub_F : closure s ⊆ F_star j :=
    closure_minimal hsF (isClosed_of_isSupportOfDrawing hpp.is_surface (hpp.supports_isSupport j))
  have hcl_sub_C : closure s ⊆ C :=
    closure_minimal hsC (isClosed_cuff_univ hpp.is_surface hC)
  have ha_mem_cl : a ∈ closure s := by
    rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inl rfl)
  have hb_mem_cl : b ∈ closure s := by
    rw [hs_ends.2.2.2.2.2]; exact Or.inr (Or.inr rfl)
  have ha_F : a ∈ Γ.V ∩ F_star j := ⟨hs_ends.2.1.1, hcl_sub_F ha_mem_cl⟩
  have hb_F : b ∈ Γ.V ∩ F_star j := ⟨hs_ends.2.2.1.1, hcl_sub_F hb_mem_cl⟩
  have ha_CV : a ∈ C ∩ Γ.V := ⟨hcl_sub_C ha_mem_cl, hs_ends.2.1.1⟩
  have hb_CV : b ∈ C ∩ Γ.V := ⟨hcl_sub_C hb_mem_cl, hs_ends.2.2.1.1⟩
  have hatt_sub : GM17.attachments G (μ (.space s)) ⊆
      (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet := by
    rintro w ⟨hws, e, ⟨heG, he_not_s⟩, hincG⟩
    rw [hpp.p1_union_E] at heG
    rcases heG with heΓ | he_supp
    · have hincΓ : Γ_sub.Inc e w := (GM10.inc_iff_of_le hpp.drawing_subgraph heΓ).2 hincG
      have hwΓ : w ∈ Γ_sub.vertexSet := Γ_sub.vertex_mem_of_inc hincΓ
      have hw_inter : w ∈ (μ (.space s)).vertexSet ∩ Γ_sub.vertexSet := ⟨hws, hwΓ⟩
      rw [(hpp.p2_space j s hs a b hsF hs_ends).1] at hw_inter
      rcases hw_inter with rfl | rfl
      · left
        have h := (hpp.μ_vertex j a ha_F).2.2.2
        have hmem : ιV a ∈ (μ (.vertex a)).vertexSet ∩ Γ_sub.vertexSet := by
          rw [h]; exact mem_singleton (ιV a)
        exact hmem.1
      · right
        have h := (hpp.μ_vertex j b hb_F).2.2.2
        have hmem : ιV b ∈ (μ (.vertex b)).vertexSet ∩ Γ_sub.vertexSet := by
          rw [h]; exact mem_singleton (ιV b)
        exact hmem.1
    · rw [mem_iUnion] at he_supp
      rcases he_supp with ⟨i, hei⟩
      rcases (mem_supportGraph_edgeSet_iff hpp i).1 hei with ⟨s', hs', hs'F, hes'⟩
      have hne_s : s ≠ s' := fun h => he_not_s (h ▸ hes')
      have hinc_s' : (μ (.space s')).Inc e w :=
        (GM10.inc_iff_of_le (hpp.μ_space i s' hs' hs'F) hes').2 hincG
      have hws' : w ∈ (μ (.space s')).vertexSet := (μ (.space s')).vertex_mem_of_inc hinc_s'
      obtain ⟨C', hC', hs'C', _⟩ :=
        exists_cuff_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs'
      have hC'_eq : C' = C := by
        by_contra hne_C
        exact Set.disjoint_left.mp
          (hpp.p1_diff_cuff_disjoint C hC C' hC' (Ne.symm hne_C) (.space s) (.space s') hsC hs'C')
          hws hws'
      subst C'
      rcases inCuffOrder_of_ne_space hpp.is_surface hpp.cuff_vertices_ge_two hC hs_ends hs'
        hsC hs'C' hne_s with hord | hord
      · exact (hpp.p3_order C hC (.space s) (.space s') a ha_CV b hb_CV hsC hs'C' hord).vertexSet_subset
          ⟨hws, hws'⟩
      · have h := (hpp.p3_order C hC (.space s) (.space s') b hb_CV a ha_CV hsC hs'C' hord).vertexSet_subset
          ⟨hws, hws'⟩
        exact Or.symm h
  rw [GM17.separationOrder_complSubhypergraph]
  have hfin : ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet).Finite :=
    (μ (.vertex a)).vertexSet_finite.union (μ (.vertex b)).vertexSet_finite
  calc (GM17.attachments G (μ (.space s))).ncard
      ≤ ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet).ncard :=
        ncard_le_ncard hatt_sub hfin
    _ ≤ (μ (.vertex a)).vertexSet.ncard + (μ (.vertex b)).vertexSet.ncard := ncard_union_le _ _
    _ = q_vec j + q_vec j := by rw [(hpp.μ_vertex j a ha_F).2.2.1, (hpp.μ_vertex j b hb_F).2.2.1]
    _ = 2 * q_vec j := by omega

/-- **Graph Minors XXI, (8.3)** (page 36 of the preprint):
"With notation as in (8.2), suppose that $\Gamma, F_1^*, \dots, F_r^*, \mu$ is a
pseudo-presentation of depth $\le q$, and surrounds a tangle $\mathcal{T}$ in $G$ of order
$\theta \ge 2q + 3$. Then $\Gamma, F_1^*, \dots, F_r^*, \mu'$ surrounds a tangle in $G'$ of order
$\theta - 1$." -/
theorem theorem_8_3_proof {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
    {G : Hypergraph α β} (hG : G.IsGraph)
    {Γ : Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β} {q_vec : Fin r → ℕ}
    {C s_star : Set S} {u₁ u₂ : S} {v v₁ v₂ : α} {q θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q_vec)
    (hq : ∀ j : Fin r, q_vec j ≤ q)
    (hθ : 2 * q + 3 ≤ θ)
    (h𝒯 : IsTangle G θ 𝒯)
    (hsurr : PseudoPresentationSurroundsTangle Γ r F_star μ 𝒯)
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet)
    (hv₁ : v₁ ∉ G.vertexSet) (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂) :
    ∃ 𝒯' : Set (Hypergraph α β × Hypergraph α β),
      IsTangle (pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂) (θ - 1) 𝒯' ∧
      PseudoPresentationSurroundsTangle Γ r F_star
        (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂) 𝒯' := by
  have hsplit := isVertexSplit_pseudoSplit hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne
  have hpp' := theorem_8_2_proof hpp hC hs_star hs_star_C huncov hv hv₁ hv₂ hne
  let G' := pseudoSplitGraph hpp hC hs_star hs_star_C hv v₁ v₂
  let μ' := pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂
  have hv_sub : ({v} : Set α) ⊆ G.vertexSet := singleton_subset_iff.mpr hsplit.v_mem
  have hv_card : ({v} : Set α).ncard < θ := by
    rw [ncard_singleton]; omega
  let 𝒯_del := deleteVerticesTangle G {v} 𝒯 θ
  have h𝒯_del : IsTangle (G.deleteVertices {v}) (θ - 1) 𝒯_del := by
    simpa [ncard_singleton] using theorem_3_2_proof hG h𝒯 hv_sub hv_card
  have hdel_le : G.deleteVertices {v} ≤ G' := deleteVertex_le_of_isVertexSplit hsplit
  let 𝒯' := GM12.inducedBySubgraph G' (G.deleteVertices {v}) (θ - 1) 𝒯_del
  have h𝒯' : IsTangle G' (θ - 1) 𝒯' := theorem_3_4_proof hdel_le h𝒯_del
  refine ⟨𝒯', h𝒯', ?_⟩
  intro s hs ⟨j, hsF⟩
  -- Step 1: Let A = μ(s) and B = complSubhypergraph G A; then (A, B) ∈ 𝒯
  let A := μ (.space s)
  let B := GM17.complSubhypergraph G A
  have hA_le : A ≤ G := hpp.μ_space j s hs hsF
  have hsepAB : G.IsSeparation A B := GM17.isSeparation_complSubhypergraph hA_le
  have hordAB_le : separationOrder A B ≤ 2 * q :=
    (separationOrder_complSubhypergraph_space_le hpp j hs hsF).trans (by have := hq j; omega)
  have hAB_in_𝒯 : (A, B) ∈ 𝒯 :=
    GM17.theorem_4_1_i h𝒯 (hsurr s hs ⟨j, hsF⟩) hsepAB (by omega)
  -- Step 2: Add {v} to A and B to form (A₁, B₁) ∈ 𝒯, hence (A₁ \ {v}, B₁ \ {v}) ∈ 𝒯_del
  let A₁ := addVerticesSubhypergraph G A {v} hA_le hv_sub
  let B₁ := addVerticesSubhypergraph G B {v} hsepAB.right_le hv_sub
  have hA₁_le : A₁ ≤ G := ⟨union_subset hA_le.vertexSet_subset hv_sub, hA_le.edgeSet_subset, hA_le.ends_eq⟩
  have hB₁_le : B₁ ≤ G := ⟨union_subset hsepAB.right_le.vertexSet_subset hv_sub,
    hsepAB.right_le.edgeSet_subset, hsepAB.right_le.ends_eq⟩
  have hsepA₁B₁ : G.IsSeparation A₁ B₁ := by
    rw [GM10.isSeparation_iff_of_le hA₁_le hB₁_le]
    refine ⟨?_, hsepAB.edgeSet_union, hsepAB.edgeSet_inter_eq⟩
    change (A.vertexSet ∪ {v}) ∪ (B.vertexSet ∪ {v}) = G.vertexSet
    rw [union_union_union_comm, hsepAB.vertexSet_union, Set.union_self, union_eq_left.mpr hv_sub]
  have hordA₁B₁ : separationOrder A₁ B₁ < θ := by
    have h_inter : (A₁ ∩ B₁).vertexSet = (A ∩ B).vertexSet ∪ {v} := by
      ext w
      change (w ∈ A.vertexSet ∨ w ∈ ({v} : Set α)) ∧ (w ∈ B.vertexSet ∨ w ∈ ({v} : Set α)) ↔
        (w ∈ A.vertexSet ∧ w ∈ B.vertexSet) ∨ w ∈ ({v} : Set α)
      tauto
    have hle : separationOrder A₁ B₁ ≤ separationOrder A B + 1 := by
      unfold separationOrder
      rw [h_inter, ← ncard_singleton v]
      exact ncard_union_le _ _
    omega
  have hA₁B₁_in_𝒯 : (A₁, B₁) ∈ 𝒯 :=
    GM10.theorem_2_9_proof h𝒯 hAB_in_𝒯 hsepA₁B₁ hordA₁B₁ (Or.inl subset_union_left)
  have hdel_mono : ∀ {H : Hypergraph α β}, H ≤ G → H.deleteVertices {v} ≤ G.deleteVertices {v} := by
    intro H hH
    refine ⟨sdiff_subset_sdiff hH.vertexSet_subset Subset.rfl,
      fun e he => ⟨hH.edgeSet_subset he.1,
        fun w hw hincG => he.2 w hw ((GM10.inc_iff_of_le hH he.1).2 hincG)⟩,
      fun e he => ?_⟩
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq, deleteVertices]
    rw [GM10.inc_iff_of_le hH he.1]
    exact ⟨fun ⟨hinc, _⟩ => ⟨hinc, he.2⟩,
      fun ⟨hinc, _⟩ => ⟨hinc, fun w hw hH' => he.2 w hw ((GM10.inc_iff_of_le hH he.1).2 hH')⟩⟩
  have hsep_del₁ : (G.deleteVertices {v}).IsSeparation
      (A₁.deleteVertices {v}) (B₁.deleteVertices {v}) := by
    rw [GM10.isSeparation_iff_of_le (hdel_mono hA₁_le) (hdel_mono hB₁_le)]
    refine ⟨?_, ?_, ?_⟩
    · change (A₁.vertexSet \ {v}) ∪ (B₁.vertexSet \ {v}) = G.vertexSet \ {v}
      rw [← union_sdiff_distrib, hsepA₁B₁.vertexSet_union]
    · ext e
      simp only [mem_union, deleteVertices, mem_ofPred_eq]
      refine ⟨fun h => h.elim (fun h1 => (hdel_mono hA₁_le).edgeSet_subset h1)
        (fun h2 => (hdel_mono hB₁_le).edgeSet_subset h2), ?_⟩
      rintro ⟨heG, hno⟩
      rcases (hsepA₁B₁.edgeSet_union.symm ▸ heG) with heA | heB
      · exact Or.inl ⟨heA, fun w hw hinc => hno w hw (GM10.inc_of_le hA₁_le hinc)⟩
      · exact Or.inr ⟨heB, fun w hw hinc => hno w hw (GM10.inc_of_le hB₁_le hinc)⟩
    · ext e
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
      rintro ⟨⟨heA, _⟩, ⟨heB, _⟩⟩
      exact hsepA₁B₁.notMem_edgeSet_right heA heB
  have hord_del₁ : separationOrder (A₁.deleteVertices {v}) (B₁.deleteVertices {v}) < θ - 1 := by
    have hsub : ((A₁.deleteVertices {v}) ∩ (B₁.deleteVertices {v})).vertexSet ⊆ (A ∩ B).vertexSet := by
      rintro w ⟨⟨hwA | hw_eq, hwv⟩, ⟨hwB | hw_eq, _⟩⟩
      · exact ⟨hwA, hwB⟩
      · exact (hwv hw_eq).elim
      · exact (hwv hw_eq).elim
      · exact (hwv hw_eq).elim
    have hle : separationOrder (A₁.deleteVertices {v}) (B₁.deleteVertices {v}) ≤ separationOrder A B :=
      ncard_le_ncard hsub (A ∩ B).vertexSet_finite
    omega
  have hA₁B₁_del_in : (A₁.deleteVertices {v}, B₁.deleteVertices {v}) ∈ 𝒯_del :=
    ⟨hsep_del₁, by simpa [ncard_singleton] using hord_del₁, ⟨(A₁, B₁), hA₁B₁_in_𝒯,
      singleton_subset_iff.mpr ⟨Or.inr rfl, Or.inr rfl⟩, rfl, rfl⟩⟩
  -- Step 3: Let A₂ = μ'(s) and B₂ = complSubhypergraph G' A₂; show (A₂, B₂) ∈ 𝒯'
  let A₂ := μ' (.space s)
  let B₂ := GM17.complSubhypergraph G' A₂
  have hA₂_le : A₂ ≤ G' := hpp'.μ_space j s hs hsF
  have hsepA₂B₂ : G'.IsSeparation A₂ B₂ := GM17.isSeparation_complSubhypergraph hA₂_le
  have hordA₂B₂_le : separationOrder A₂ B₂ ≤ 2 * q :=
    (separationOrder_complSubhypergraph_space_le hpp' j hs hsF).trans (by have := hq j; omega)
  have hsep_del₂ : (G.deleteVertices {v}).IsSeparation
      (A₂ ∩ G.deleteVertices {v}) (B₂ ∩ G.deleteVertices {v}) := by
    simpa [GM10.inter_comm (G.deleteVertices {v}) A₂, GM10.inter_comm (G.deleteVertices {v}) B₂]
      using hsepA₂B₂.inter_left hdel_le
  have hord_del₂ : separationOrder (A₂ ∩ G.deleteVertices {v}) (B₂ ∩ G.deleteVertices {v}) < θ - 1 := by
    have hsub : ((A₂ ∩ G.deleteVertices {v}) ∩ (B₂ ∩ G.deleteVertices {v})).vertexSet ⊆
        (A₂ ∩ B₂).vertexSet := fun w hw => ⟨hw.1.1, hw.2.1⟩
    have hle : separationOrder (A₂ ∩ G.deleteVertices {v}) (B₂ ∩ G.deleteVertices {v}) ≤
        separationOrder A₂ B₂ := ncard_le_ncard hsub (A₂ ∩ B₂).vertexSet_finite
    omega
  have hV_sub : (A₂ ∩ G.deleteVertices {v}).vertexSet ⊆ (A₁.deleteVertices {v}).vertexSet := by
    rintro w ⟨hwA₂, hwG, hwv⟩
    have hw_ne₁ : w ≠ v₁ := fun h => hv₁ (h ▸ hwG)
    have hw_ne₂ : w ≠ v₂ := fun h => hv₂ (h ▸ hwG)
    have hwA : w ∈ A.vertexSet := by
      dsimp only [A₂, μ', A] at hwA₂ ⊢
      have hxs : IsValidUnit Γ r F_star (.space s) := Or.inr ⟨s, hs, ⟨j, hsF⟩, rfl⟩
      rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxs with
        ⟨_, h_eq⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, _, h_eq⟩
      · rwa [h_eq] at hwA₂
      · rw [h_eq, replaceVertex_vertexSet] at hwA₂
        exact (hwA₂.resolve_right hw_ne₁).1
      · rw [h_eq, replaceVertex_vertexSet] at hwA₂
        exact (hwA₂.resolve_right hw_ne₂).1
    exact ⟨Or.inl hwA, hwv⟩
  have hA₂B₂_del_in : (A₂ ∩ G.deleteVertices {v}, B₂ ∩ G.deleteVertices {v}) ∈ 𝒯_del :=
    GM10.theorem_2_9_proof h𝒯_del hA₁B₁_del_in hsep_del₂ hord_del₂ (Or.inr (Or.inl hV_sub))
  have hord_A₂B₂_lt : separationOrder A₂ B₂ < θ - 1 := by omega
  exact ⟨B₂, hsepA₂B₂, hord_A₂B₂_lt, hA₂B₂_del_in⟩

end TangleAfterSplit

/-! ## Section 4: Iterated vertex splitting and proof of (8.4) -/

section IteratedSplit

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-- Increasing `p` preserves `HasVitalPLinkage`. -/
theorem HasVitalPLinkage.mono {G : Hypergraph α β} {p p' : ℕ}
    (h : HasVitalPLinkage G p) (hle : p ≤ p') : HasVitalPLinkage G p' := by
  rcases h with ⟨L, hvit, hlink, hcard⟩
  exact ⟨L, hvit, hlink, hcard.trans hle⟩

/-- The set of spaces `s ∈ drawingSpaces Γ` not contained in any `F_star j` (`j : Fin r`). -/
def uncoveredSpaces (Γ : Drawing S) (r : ℕ) (F_star : Fin r → Set S) : Set (Set S) :=
  {s ∈ drawingSpaces Γ | ∀ j : Fin r, ¬ s ⊆ F_star j}

theorem uncoveredSpaces_finite (hS : IsSurface S) {Γ : Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) (r : ℕ) (F_star : Fin r → Set S) :
    (uncoveredSpaces Γ r F_star).Finite :=
  (drawingSpaces_finite hS hge2).subset (fun _ h => h.1)

/-- In a pseudo-presentation, every uncovered space `s` has its left endpoint `vNode ... i`
(in the canonical parameterization of its cuff `C`) equal to the right endpoint of a unique
support `F_star j`, so `(uncoveredSpaces Γ r F_star).ncard ≤ r`. -/
theorem uncoveredSpaces_ncard_le {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {μ : BoundaryUnit S → Hypergraph α β}
    {q : Fin r → ℕ} (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q) :
    (uncoveredSpaces Γ r F_star).ncard ≤ r := by
  have : T2Space S := hpp.is_surface.2.1
  -- Relation R s j: there exist C ∈ cuffs S and i such that s = vSpaceArc ... i and vNode ... i ∈ F_star j
  let R (s : Set S) (j : Fin r) : Prop :=
    ∃ (C : Set S) (hC : C ∈ cuffs S) (i : Fin (Γ.V ∩ C).ncard),
      s = vSpaceArc Γ.V Γ.finite_V (cuffHomeo hpp.is_surface hC) (hpp.cuff_vertices_ge_two C hC) i ∧
      vNode Γ.V Γ.finite_V (cuffHomeo hpp.is_surface hC) i ∈ F_star j
  have hR_ex : ∀ s ∈ uncoveredSpaces Γ r F_star, ∃ j : Fin r, R s j := by
    intro s ⟨hs, _⟩
    obtain ⟨C, hC, hsC, _⟩ :=
      exists_cuff_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs
    obtain ⟨i, rfl⟩ :=
      exists_index_of_mem_drawingSpaces_subset_cuff hpp.is_surface hpp.cuff_vertices_ge_two
        hs hC hsC (cuffHomeo hpp.is_surface hC)
    have hn_mem := vNode_mem Γ.V Γ.finite_V (cuffHomeo hpp.is_surface hC) i
    have hn_bd : vNode Γ.V Γ.finite_V (cuffHomeo hpp.is_surface hC) i ∈ Γ.V ∩ bd S := by
      refine ⟨hn_mem.1, ?_⟩
      rw [← sUnion_cuffs (S := S)]
      exact ⟨C, hC, hn_mem.2⟩
    have hn_cov := hpp.bd_vertices_covered hn_bd
    rw [mem_iUnion] at hn_cov
    rcases hn_cov with ⟨j, hj⟩
    exact ⟨j, C, hC, i, rfl, hj⟩
  have hR_uniq : ∀ s₁ ∈ uncoveredSpaces Γ r F_star, ∀ s₂ ∈ uncoveredSpaces Γ r F_star,
      ∀ j : Fin r, R s₁ j → R s₂ j → s₁ = s₂ := by
    intro s₁ ⟨_, huncov₁⟩ s₂ ⟨_, huncov₂⟩ j
      ⟨C₁, hC₁, i₁, hs₁_eq, hn₁_F⟩ ⟨C₂, hC₂, i₂, hs₂_eq, hn₂_F⟩
    obtain ⟨C, hC, hFC, _⟩ := exists_cuff_of_isSupportOfDrawing (hpp.supports_isSupport j)
    have hC₁_eq : C₁ = C := by
      by_contra hne
      exact Set.disjoint_left.mp (cuffs_disjoint hC₁ hC hne)
        (vNode_mem Γ.V Γ.finite_V (cuffHomeo hpp.is_surface hC₁) i₁).2 (hFC hn₁_F)
    have hC₂_eq : C₂ = C := by
      by_contra hne
      exact Set.disjoint_left.mp (cuffs_disjoint hC₂ hC hne)
        (vNode_mem Γ.V Γ.finite_V (cuffHomeo hpp.is_surface hC₂) i₂).2 (hFC hn₂_F)
    subst C₁; subst C₂
    let f := cuffHomeo hpp.is_surface hC
    have hk := hpp.cuff_vertices_ge_two C hC
    rcases hpp.supports_isSupport j with ⟨endA, endB, hF_ends⟩
    have hends_mem := ends_mem_of_supportHasEnds hF_ends
    obtain ⟨t₀, _, t₁, ⟨ht₀_le_t₁, ht₁_lt⟩, h_ab_eq, hF_eq, _⟩ :=
      support_eq_cuffPoint_Icc hpp.is_surface hC f hF_ends hFC
    have ht₀_mem : cuffPoint f t₀ ∈ Γ.V ∩ C := by
      refine ⟨?_, cuffPoint_mem f t₀⟩
      rcases h_ab_eq with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
      · exact hends_mem.2.2.1.1
      · exact hends_mem.2.2.2.1.1
    have ht₁_mem : cuffPoint f t₁ ∈ Γ.V ∩ C := by
      refine ⟨?_, cuffPoint_mem f t₁⟩
      rcases h_ab_eq with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]
      · exact hends_mem.2.2.2.1.1
      · exact hends_mem.2.2.1.1
    have h_node_eq_t₁ : ∀ (i : Fin (Γ.V ∩ C).ncard),
        vNode Γ.V Γ.finite_V f i ∈ F_star j →
        ¬ vSpaceArc Γ.V Γ.finite_V f hk i ⊆ F_star j →
        vNode Γ.V Γ.finite_V f i = cuffPoint f t₁ := by
      intro i hn_F hnot_sub
      obtain ⟨a', b', ha', hab', hb', ha'_eq, _, hs_eq, _⟩ :=
        vSpaceArc_eq_Ioo_from_vertex_angle hpp.is_surface hC f hk ht₀_mem i
      have ha'_in_F : cuffPoint f a' ∈ F_star j := by rw [ha'_eq]; exact hn_F
      rw [hF_eq] at ha'_in_F
      rcases ha'_in_F with ⟨t, ⟨ht1, ht2⟩, ht_eq⟩
      have ht_eq_a' : t = a' :=
        cuffPoint_injOn_Ico f t₀ ⟨ht1, ht2.trans_lt ht₁_lt⟩ ⟨ha', hab'.trans_le hb'⟩ ht_eq
      subst ht_eq_a'
      have ht₁_lt_b' : t₁ < b' := by
        by_contra hle
        push Not at hle
        apply hnot_sub
        rw [hs_eq, hF_eq]
        exact image_mono (fun x hx => ⟨ht1.trans hx.1.le, hx.2.le.trans hle⟩)
      rcases eq_or_lt_of_le ht2 with rfl | hlt
      · exact ha'_eq.symm
      · exfalso
        have ht₁_in_arc : cuffPoint f t₁ ∈ vSpaceArc Γ.V Γ.finite_V f hk i := by
          rw [hs_eq]; exact ⟨t₁, ⟨hlt, ht₁_lt_b'⟩, rfl⟩
        exact (vSpaceArc_subset_diff Γ.V Γ.finite_V f hk i ht₁_in_arc).2 ht₁_mem.1
    have h1 := h_node_eq_t₁ i₁ hn₁_F (hs₁_eq ▸ huncov₁ j)
    have h2 := h_node_eq_t₁ i₂ hn₂_F (hs₂_eq ▸ huncov₂ j)
    have hi_eq : i₁ = i₂ := injective_vNode Γ.V Γ.finite_V f (h1.trans h2.symm)
    rw [hs₁_eq, hs₂_eq, hi_eq]
  rcases Nat.eq_zero_or_pos r with rfl | hr_pos
  · have hemp : uncoveredSpaces Γ 0 F_star = ∅ := by
      ext s
      simp only [mem_empty_iff_false, iff_false]
      intro hs
      rcases hR_ex s hs with ⟨j, _⟩
      exact Fin.elim0 j
    rw [hemp, ncard_empty]
  · let φ (s : Set S) : Fin r :=
      if hs : s ∈ uncoveredSpaces Γ r F_star then (hR_ex s hs).choose else ⟨0, hr_pos⟩
    have hφ_inj : InjOn φ (uncoveredSpaces Γ r F_star) := by
      intro s₁ hs₁ s₂ hs₂ h_eq
      dsimp only [φ] at h_eq
      rw [dif_pos hs₁, dif_pos hs₂] at h_eq
      have hR₁ : R s₁ (hR_ex s₁ hs₁).choose := (hR_ex s₁ hs₁).choose_spec
      have hR₂ : R s₂ (hR_ex s₁ hs₁).choose := h_eq ▸ (hR_ex s₂ hs₂).choose_spec
      exact hR_uniq s₁ hs₁ s₂ hs₂ _ hR₁ hR₂
    let U_fin := (uncoveredSpaces_finite hpp.is_surface hpp.cuff_vertices_ge_two r F_star).toFinset
    have h_card : U_fin.card ≤ (Finset.univ : Finset (Fin r)).card :=
      Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _)
        (fun s₁ hs₁ s₂ hs₂ h_eq =>
          hφ_inj ((Finite.mem_toFinset _).mp hs₁) ((Finite.mem_toFinset _).mp hs₂) h_eq)
    rw [ncard_eq_toFinset_card _
      (uncoveredSpaces_finite hpp.is_surface hpp.cuff_vertices_ge_two r F_star)]
    simpa [Finset.card_univ, Fintype.card_fin] using h_card

/-- For a space `s`, `sharedVertices μ s` is the set of vertices shared by `μ (.vertex u)` for all
endpoints `u ∈ closure s \ s`. When `SpaceHasEnds Γ s u₁ u₂`, this equals
`(μ (.vertex u₁)).vertexSet ∩ (μ (.vertex u₂)).vertexSet`. -/
def sharedVertices (μ : BoundaryUnit S → Hypergraph α β) (s : Set S) : Set α :=
  ⋂ u ∈ closure s \ s, (μ (.vertex u)).vertexSet

theorem sharedVertices_eq_of_spaceHasEnds {Γ : Drawing S} {μ : BoundaryUnit S → Hypergraph α β}
    {s : Set S} {u₁ u₂ : S} (hs : SpaceHasEnds Γ s u₁ u₂) :
    sharedVertices μ s = (μ (.vertex u₁)).vertexSet ∩ (μ (.vertex u₂)).vertexSet := by
  unfold sharedVertices
  rw [closure_diff_eq_of_spaceHasEnds hs, biInter_insert, biInter_singleton]

theorem sharedVertices_finite {Γ : Drawing S} {μ : BoundaryUnit S → Hypergraph α β}
    {s : Set S} {u₁ u₂ : S} (hs : SpaceHasEnds Γ s u₁ u₂) :
    (sharedVertices μ s).Finite := by
  rw [sharedVertices_eq_of_spaceHasEnds hs]
  exact (μ (.vertex u₁)).vertexSet_finite.inter_of_left _

/-- The total number of shared boundary-unit vertices across all uncovered spaces of `(Γ, F_star)`. -/
noncomputable def uncoveredSharedSum (hS : IsSurface S) {Γ : Drawing S}
    (hge2 : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) (r : ℕ) (F_star : Fin r → Set S)
    (μ : BoundaryUnit S → Hypergraph α β) : ℕ :=
  ∑ s ∈ (uncoveredSpaces_finite hS hge2 r F_star).toFinset, (sharedVertices μ s).ncard

/-- In a pseudo-presentation of depth `≤ q`, `uncoveredSharedSum ≤ q * r`. -/
theorem uncoveredSharedSum_le {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {μ : BoundaryUnit S → Hypergraph α β}
    {q_vec : Fin r → ℕ} {q : ℕ}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q_vec)
    (hq : ∀ j : Fin r, q_vec j ≤ q) :
    uncoveredSharedSum hpp.is_surface hpp.cuff_vertices_ge_two r F_star μ ≤ q * r := by
  unfold uncoveredSharedSum
  let U_fin := (uncoveredSpaces_finite hpp.is_surface hpp.cuff_vertices_ge_two r F_star).toFinset
  have h_term_le : ∀ s ∈ U_fin, (sharedVertices μ s).ncard ≤ q := by
    intro s hs_fin
    have hs : s ∈ drawingSpaces Γ := ((Finite.mem_toFinset _).mp hs_fin).1
    obtain ⟨u₁, u₂, hs_ends⟩ :=
      exists_spaceHasEnds_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs
    have hu₁_cov := hpp.bd_vertices_covered hs_ends.2.1
    rw [mem_iUnion] at hu₁_cov
    rcases hu₁_cov with ⟨j, hj⟩
    rw [sharedVertices_eq_of_spaceHasEnds hs_ends]
    calc ((μ (.vertex u₁)).vertexSet ∩ (μ (.vertex u₂)).vertexSet).ncard
        ≤ (μ (.vertex u₁)).vertexSet.ncard :=
          ncard_le_ncard inter_subset_left (μ (.vertex u₁)).vertexSet_finite
      _ = q_vec j := (hpp.μ_vertex j u₁ ⟨hs_ends.2.1.1, hj⟩).2.2.1
      _ ≤ q := hq j
  have h_card_le : U_fin.card ≤ r := by
    have h_eq : U_fin.card = (uncoveredSpaces Γ r F_star).ncard := by
      rw [ncard_eq_toFinset_card (uncoveredSpaces Γ r F_star)
        (uncoveredSpaces_finite hpp.is_surface hpp.cuff_vertices_ge_two r F_star)]
    rw [h_eq]
    exact uncoveredSpaces_ncard_le hpp
  calc ∑ s ∈ U_fin, (sharedVertices μ s).ncard
      ≤ ∑ _s ∈ U_fin, q := Finset.sum_le_sum h_term_le
    _ = U_fin.card * q := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ r * q := Nat.mul_le_mul_right q h_card_le
    _ = q * r := Nat.mul_comm r q

/-- Under a vertex split (`pseudoSplitMu`), `(sharedVertices μ' s).ncard ≤ (sharedVertices μ s).ncard`
for every space `s ∈ drawingSpaces Γ`, and `(sharedVertices μ' s_star).ncard < (sharedVertices μ s_star).ncard`
for the split space `s_star`, so `uncoveredSharedSum` strictly decreases. -/
theorem uncoveredSharedSum_lt_of_pseudoSplit {G : Hypergraph α β} {Γ : Drawing S}
    {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r F_star μ q)
    {C s_star : Set S} {u₁ u₂ : S} {v v₁ v₂ : α}
    (hC : C ∈ cuffs S) (hs_star : SpaceHasEnds Γ s_star u₁ u₂) (hs_star_C : s_star ⊆ C)
    (huncov : ∀ j : Fin r, ¬ s_star ⊆ F_star j)
    (hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet)
    (hv₁ : v₁ ∉ G.vertexSet) (hv₂ : v₂ ∉ G.vertexSet) (hne : v₁ ≠ v₂) :
    uncoveredSharedSum hpp.is_surface hpp.cuff_vertices_ge_two r F_star
      (pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂) <
    uncoveredSharedSum hpp.is_surface hpp.cuff_vertices_ge_two r F_star μ := by
  let μ' := pseudoSplitMu hpp hC hs_star hs_star_C hv v₁ v₂
  let U_fin := (uncoveredSpaces_finite hpp.is_surface hpp.cuff_vertices_ge_two r F_star).toFinset
  obtain ⟨_, _, _, _, _, _, _, _, hu₁_F₁, _, hu₂_F₂, _, _, _, _, _, _, _⟩ :=
    pseudoSplit_spec hpp hC hs_star hs_star_C hv
  apply Finset.sum_lt_sum
  · -- Non-increasing on all s ∈ U_fin
    intro s hs_fin
    have hs : s ∈ drawingSpaces Γ := ((Finite.mem_toFinset _).mp hs_fin).1
    obtain ⟨a, b, hs_ends⟩ :=
      exists_spaceHasEnds_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs
    rw [sharedVertices_eq_of_spaceHasEnds hs_ends, sharedVertices_eq_of_spaceHasEnds hs_ends]
    have hxa : IsValidUnit Γ r F_star (.vertex a) := Or.inl ⟨a, hs_ends.2.1, rfl⟩
    have hxb : IsValidUnit Γ r F_star (.vertex b) := Or.inl ⟨b, hs_ends.2.2.1, rfl⟩
    have h_fin_ab : ((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet).Finite :=
      (μ (.vertex a)).vertexSet_finite.inter_of_left _
    rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxa with
      ⟨hva, ha_eq⟩ | ⟨hva, _, _, ha_eq⟩ | ⟨hva, _, _, ha_eq⟩ <;>
    rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxb with
      ⟨hvb, hb_eq⟩ | ⟨hvb, _, _, hb_eq⟩ | ⟨hvb, _, _, hb_eq⟩
    · rw [ha_eq, hb_eq]
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq] at hwa
        rw [hb_eq, replaceVertex_vertexSet] at hwb
        have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxa).vertexSet_subset hwa
        exact ⟨hwa, (hwb.resolve_right (fun h => hv₁ (h ▸ hwG))).1⟩
      exact ncard_le_ncard hsub h_fin_ab
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq] at hwa
        rw [hb_eq, replaceVertex_vertexSet] at hwb
        have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxa).vertexSet_subset hwa
        exact ⟨hwa, (hwb.resolve_right (fun h => hv₂ (h ▸ hwG))).1⟩
      exact ncard_le_ncard hsub h_fin_ab
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq, replaceVertex_vertexSet] at hwa
        rw [hb_eq] at hwb
        have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxb).vertexSet_subset hwb
        exact ⟨(hwa.resolve_right (fun h => hv₁ (h ▸ hwG))).1, hwb⟩
      exact ncard_le_ncard hsub h_fin_ab
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}) ∪ {v₁} := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq, replaceVertex_vertexSet] at hwa
        rw [hb_eq, replaceVertex_vertexSet] at hwb
        rcases hwa with ⟨hwa, hwv⟩ | rfl
        · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxa).vertexSet_subset hwa
          exact Or.inl ⟨⟨hwa, (hwb.resolve_right (fun h => hv₁ (h ▸ hwG))).1⟩, hwv⟩
        · exact Or.inr rfl
      have hfin' : ((((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}) ∪ {v₁}).Finite :=
        h_fin_ab.sdiff.union (finite_singleton v₁)
      calc ((μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet).ncard
          ≤ ((((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}) ∪ {v₁}).ncard :=
            ncard_le_ncard hsub hfin'
        _ ≤ (((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}).ncard + ({v₁} : Set α).ncard :=
            ncard_union_le _ _
        _ = (((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}).ncard + 1 := by
            rw [ncard_singleton]
        _ = ((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet).ncard :=
            ncard_sdiff_singleton_add_one ⟨hva, hvb⟩ h_fin_ab
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq, replaceVertex_vertexSet] at hwa
        rw [hb_eq, replaceVertex_vertexSet] at hwb
        rcases hwa with ⟨hwa, _⟩ | rfl
        · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxa).vertexSet_subset hwa
          exact ⟨hwa, (hwb.resolve_right (fun h => hv₂ (h ▸ hwG))).1⟩
        · rcases hwb with ⟨hwb, _⟩ | h_eq_v
          · exact (hv₁ ((validUnit_le hpp hxb).vertexSet_subset hwb)).elim
          · exact (hne h_eq_v).elim
      exact ncard_le_ncard hsub h_fin_ab
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq, replaceVertex_vertexSet] at hwa
        rw [hb_eq] at hwb
        have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxb).vertexSet_subset hwb
        exact ⟨(hwa.resolve_right (fun h => hv₂ (h ▸ hwG))).1, hwb⟩
      exact ncard_le_ncard hsub h_fin_ab
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq, replaceVertex_vertexSet] at hwa
        rw [hb_eq, replaceVertex_vertexSet] at hwb
        rcases hwa with ⟨hwa, _⟩ | rfl
        · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxa).vertexSet_subset hwa
          exact ⟨hwa, (hwb.resolve_right (fun h => hv₁ (h ▸ hwG))).1⟩
        · rcases hwb with ⟨hwb, _⟩ | h_eq_v
          · exact (hv₂ ((validUnit_le hpp hxb).vertexSet_subset hwb)).elim
          · exact (hne.symm h_eq_v).elim
      exact ncard_le_ncard hsub h_fin_ab
    · have hsub : (μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet ⊆
          (((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}) ∪ {v₂} := by
        rintro w ⟨hwa, hwb⟩
        dsimp only [μ'] at hwa hwb
        rw [ha_eq, replaceVertex_vertexSet] at hwa
        rw [hb_eq, replaceVertex_vertexSet] at hwb
        rcases hwa with ⟨hwa, hwv⟩ | rfl
        · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxa).vertexSet_subset hwa
          exact Or.inl ⟨⟨hwa, (hwb.resolve_right (fun h => hv₂ (h ▸ hwG))).1⟩, hwv⟩
        · exact Or.inr rfl
      have hfin' : ((((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}) ∪ {v₂}).Finite :=
        h_fin_ab.sdiff.union (finite_singleton v₂)
      calc ((μ' (.vertex a)).vertexSet ∩ (μ' (.vertex b)).vertexSet).ncard
          ≤ ((((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}) ∪ {v₂}).ncard :=
            ncard_le_ncard hsub hfin'
        _ ≤ (((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}).ncard + ({v₂} : Set α).ncard :=
            ncard_union_le _ _
        _ = (((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet) \ {v}).ncard + 1 := by
            rw [ncard_singleton]
        _ = ((μ (.vertex a)).vertexSet ∩ (μ (.vertex b)).vertexSet).ncard :=
            ncard_sdiff_singleton_add_one ⟨hva, hvb⟩ h_fin_ab
  · -- Strictly decreasing at s_star
    have hs_star_mem : s_star ∈ U_fin :=
      (Finite.mem_toFinset _).mpr ⟨hs_star.1, huncov⟩
    refine ⟨s_star, hs_star_mem, ?_⟩
    rw [sharedVertices_eq_of_spaceHasEnds hs_star, sharedVertices_eq_of_spaceHasEnds hs_star]
    have hxu₁ : IsValidUnit Γ r F_star (.vertex u₁) := Or.inl ⟨u₁, hs_star.2.1, rfl⟩
    have hxu₂ : IsValidUnit Γ r F_star (.vertex u₂) := Or.inl ⟨u₂, hs_star.2.2.1, rfl⟩
    have hu₁_eq : μ' (.vertex u₁) = replaceVertex (μ (.vertex u₁)) v v₁ := by
      rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxu₁ with
        ⟨hnot, _⟩ | ⟨_, _, _, h_eq⟩ | ⟨_, _, hnot_F₁, _⟩
      · exact (hnot hv.1).elim
      · exact h_eq
      · exact (hnot_F₁ hu₁_F₁).elim
    have hu₂_eq : μ' (.vertex u₂) = replaceVertex (μ (.vertex u₂)) v v₂ := by
      rcases pseudoSplitMu_of_validUnit hpp hC hs_star hs_star_C huncov hv v₁ v₂ hxu₂ with
        ⟨hnot, _⟩ | ⟨_, _, hnot_F₂, _⟩ | ⟨_, _, _, h_eq⟩
      · exact (hnot hv.2).elim
      · exact (hnot_F₂ hu₂_F₂).elim
      · exact h_eq
    have hsub : (μ' (.vertex u₁)).vertexSet ∩ (μ' (.vertex u₂)).vertexSet ⊆
        ((μ (.vertex u₁)).vertexSet ∩ (μ (.vertex u₂)).vertexSet) \ {v} := by
      rintro w ⟨hw₁, hw₂⟩
      rw [hu₁_eq, replaceVertex_vertexSet] at hw₁
      rw [hu₂_eq, replaceVertex_vertexSet] at hw₂
      rcases hw₁ with ⟨hw₁, hwv⟩ | rfl
      · have hwG : w ∈ G.vertexSet := (validUnit_le hpp hxu₁).vertexSet_subset hw₁
        exact ⟨⟨hw₁, (hw₂.resolve_right (fun h => hv₂ (h ▸ hwG))).1⟩, hwv⟩
      · rcases hw₂ with ⟨hw₂, _⟩ | h_eq_v
        · exact (hv₁ ((validUnit_le hpp hxu₂).vertexSet_subset hw₂)).elim
        · exact (hne h_eq_v).elim
    have h_fin_u : ((μ (.vertex u₁)).vertexSet ∩ (μ (.vertex u₂)).vertexSet).Finite :=
      (μ (.vertex u₁)).vertexSet_finite.inter_of_left _
    have hle := ncard_le_ncard hsub h_fin_u.sdiff
    have hv_inter : v ∈ (μ (.vertex u₁)).vertexSet ∩ (μ (.vertex u₂)).vertexSet := hv
    have h_add := ncard_sdiff_singleton_add_one hv_inter h_fin_u
    dsimp only [μ'] at hle
    omega

/-- **Graph Minors XXI, (8.4)** (page 36 of the preprint), for an infinite type `α` of
vertices. The paper's induction splits a vertex `v ∈ V(μ(u₁) ∩ μ(u₂))` by (8.2) and (8.3), and
each split needs two new vertices `v₁, v₂ ∉ V(G)`. Here they are taken from `α`, which is why `α`
must be infinite. `theorem_8_4_proof` in `GraphMinor.GM21.Section8Free` removes this hypothesis
by moving the graph into `α ⊕ ULift ℕ`. -/
theorem theorem_8_4_of_infinite
    (S : Type) [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsSurface S) (p r q : ℕ) (hq : 1 ≤ q) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ {α : Type u} {β : Type v} [Infinite α] (G : Hypergraph α β), G.IsGraph →
        ∀ (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) (ιE : Set S → β)
          (r' : ℕ) (F_star : Fin r' → Set S)
          (μ : BoundaryUnit S → Hypergraph α β)
          (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β)),
          r' ≤ r →
          PseudoPresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star μ q →
          θ ≤ θ_G →
          IsTangle G θ_G 𝒯 →
          PseudoPresentationSurroundsTangle Γ r' F_star μ 𝒯 →
          ¬ HasVitalPLinkage G p := by
  obtain ⟨θ', hθ'_pos, hθ'_spec⟩ := theorem_7_3_proof S hS (p + 2 * q * r) r q hq
  let θ := max θ' (2 * q + 3) + q * r
  have hθ_pos : 1 ≤ θ := by
    have : θ' ≤ max θ' (2 * q + 3) := le_max_left _ _
    omega
  refine ⟨θ, hθ_pos, ?_⟩
  intro α β _
  -- Strong induction on the uncovered shared vertex count k
  have h_ind : ∀ k : ℕ, k ≤ q * r →
      ∀ (G : Hypergraph α β), G.IsGraph →
        ∀ (Γ : Drawing S) (Γ_sub : Hypergraph α β) (ιV : S → α) (ιE : Set S → β)
          (r' : ℕ) (F_star : Fin r' → Set S)
          (μ : BoundaryUnit S → Hypergraph α β) (q_vec : Fin r' → ℕ)
          (θ_G : ℕ) (𝒯 : Set (Hypergraph α β × Hypergraph α β))
          (hpp : IsPseudoPresentation G Γ Γ_sub ιV ιE r' F_star μ q_vec),
          r' ≤ r →
          (∀ j : Fin r', q_vec j ≤ q) →
          (r' = 0 → bd S = ∅) →
          uncoveredSharedSum hpp.is_surface hpp.cuff_vertices_ge_two r' F_star μ = k →
          max θ' (2 * q + 3) + k ≤ θ_G →
          IsTangle G θ_G 𝒯 →
          PseudoPresentationSurroundsTangle Γ r' F_star μ 𝒯 →
          ¬ HasVitalPLinkage G (p + 2 * (q * r - k)) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk_le G hG Γ Γ_sub ιV ιE r' F_star μ q_vec θ_G 𝒯 hpp hr' hq_vec hr'0 hk_eq hθ_G h𝒯 hsurr hvital
      by_cases hdisj : ∀ s ∈ drawingSpaces Γ, ∀ u₁ u₂ : S,
          SpaceHasEnds Γ s u₁ u₂ → (∀ j : Fin r', ¬ s ⊆ F_star j) →
          Disjoint (μ (.vertex u₁)).vertexSet (μ (.vertex u₂)).vertexSet
      · -- Disjointed case: apply (8.1) and (7.3)
        have hpp_disj : IsDisjointedPseudoPresentation G Γ Γ_sub ιV ιE r' F_star μ q_vec :=
          ⟨hpp, hdisj⟩
        have hp : IsPresentation G Γ Γ_sub ιV ιE r' F_star
            (fun j => supportGraph G Γ μ (F_star j)) μ q_vec :=
          theorem_8_1_proof hpp_disj
        have hp_depth : PresentationHasDepthLe G Γ Γ_sub ιV ιE r' F_star
            (fun j => supportGraph G Γ μ (F_star j)) μ q :=
          ⟨q_vec, hp, hq_vec, hr'0⟩
        have hθ'_le_θG : θ' ≤ θ_G := by
          have : θ' ≤ max θ' (2 * q + 3) := le_max_left _ _
          omega
        have hvital_full : HasVitalPLinkage G (p + 2 * q * r) := by
          refine hvital.mono ?_
          calc p + 2 * (q * r - k)
              ≤ p + 2 * (q * r) := by omega
            _ = p + 2 * q * r := by ring
        exact hθ'_spec G Γ Γ_sub ιV ιE r' F_star
          (fun j => supportGraph G Γ μ (F_star j)) μ θ_G 𝒯 hG hr' hp_depth hθ'_le_θG h𝒯 hsurr hvital_full
      · -- Not disjointed: pick an uncovered space s_star with ends u₁, u₂ and shared vertex v
        push Not at hdisj
        rcases hdisj with ⟨s_star, hs_star_mem, u₁, u₂, hs_star_ends, huncov, hnot_disj⟩
        rw [Set.not_disjoint_iff] at hnot_disj
        rcases hnot_disj with ⟨v, hv₁_m, hv₂_m⟩
        have hv : v ∈ (μ (.vertex u₁) ∩ μ (.vertex u₂)).vertexSet := ⟨hv₁_m, hv₂_m⟩
        obtain ⟨C, hC, hs_star_C, _⟩ :=
          exists_cuff_of_mem_drawingSpaces hpp.is_surface hpp.cuff_vertices_ge_two hs_star_mem
        -- Pick two fresh vertices v₁, v₂ ∉ G.vertexSet with v₁ ≠ v₂
        obtain ⟨v₁, hv₁⟩ := G.vertexSet_finite.exists_notMem
        obtain ⟨v₂, hv₂_ins⟩ := (G.vertexSet_finite.insert v₁).exists_notMem
        rw [mem_insert_iff, not_or] at hv₂_ins
        have hne : v₁ ≠ v₂ := Ne.symm hv₂_ins.1
        have hv₂ : v₂ ∉ G.vertexSet := hv₂_ins.2
        have hsplit := isVertexSplit_pseudoSplit hpp hC hs_star_ends hs_star_C huncov hv hv₁ hv₂ hne
        have hG' : (pseudoSplitGraph hpp hC hs_star_ends hs_star_C hv v₁ v₂).IsGraph :=
          hsplit.isGraph hG
        have hpp' := theorem_8_2_proof hpp hC hs_star_ends hs_star_C huncov hv hv₁ hv₂ hne
        have hθ_ge_2q3 : 2 * q + 3 ≤ θ_G := by
          have : 2 * q + 3 ≤ max θ' (2 * q + 3) := le_max_right _ _
          omega
        obtain ⟨𝒯', h𝒯', hsurr'⟩ :=
          theorem_8_3_proof hG hpp hq_vec hθ_ge_2q3 h𝒯 hsurr hC hs_star_ends hs_star_C huncov hv hv₁ hv₂ hne
        have hk'_lt :
            uncoveredSharedSum hpp'.is_surface hpp'.cuff_vertices_ge_two r' F_star
              (pseudoSplitMu hpp hC hs_star_ends hs_star_C hv v₁ v₂) < k := by
          rw [← hk_eq]
          exact uncoveredSharedSum_lt_of_pseudoSplit hpp hC hs_star_ends hs_star_C huncov hv hv₁ hv₂ hne
        set k' := uncoveredSharedSum hpp'.is_surface hpp'.cuff_vertices_ge_two r' F_star
          (pseudoSplitMu hpp hC hs_star_ends hs_star_C hv v₁ v₂)
        have hvital_split : HasVitalPLinkage
            (pseudoSplitGraph hpp hC hs_star_ends hs_star_C hv v₁ v₂)
            (p + 2 * (q * r - k) + 2) :=
          theorem_2_4_proof ⟨_, _, _, _, _, hsplit⟩ hvital
        have hvital_k' : HasVitalPLinkage
            (pseudoSplitGraph hpp hC hs_star_ends hs_star_C hv v₁ v₂)
            (p + 2 * (q * r - k')) :=
          hvital_split.mono (by omega)
        exact ih k' hk'_lt (by omega)
          (pseudoSplitGraph hpp hC hs_star_ends hs_star_C hv v₁ v₂) hG'
          Γ Γ_sub ιV ιE r' F_star
          (pseudoSplitMu hpp hC hs_star_ends hs_star_C hv v₁ v₂) q_vec
          (θ_G - 1) 𝒯' hpp' hr' hq_vec hr'0 rfl (by omega) h𝒯' hsurr' hvital_k'
  intro G hG Γ Γ_sub ιV ιE r' F_star μ θ_G 𝒯 hr' ⟨q_vec, hpp, hq_vec, hr'0⟩ hθ_le h𝒯 hsurr hvital
  set k := uncoveredSharedSum hpp.is_surface hpp.cuff_vertices_ge_two r' F_star μ
  have hk_le_r' : k ≤ q * r' := uncoveredSharedSum_le hpp hq_vec
  have hk_le : k ≤ q * r := hk_le_r'.trans (Nat.mul_le_mul_left q hr')
  have hvital_k : HasVitalPLinkage G (p + 2 * (q * r - k)) :=
    hvital.mono (by omega)
  exact h_ind k hk_le G hG Γ Γ_sub ιV ιE r' F_star μ q_vec θ_G 𝒯 hpp
    hr' hq_vec hr'0 rfl (by omega) h𝒯 hsurr hvital_k

end IteratedSplit

end GM21
end GraphMinor
