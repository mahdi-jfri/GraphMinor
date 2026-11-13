module

public import GraphMinor.GM21.SeparationGluing

/-!
# Vertex Splitting and Vital Linkages: Graph Minors XXI, (2.4)

Proves that if `G'` is obtained from `G` by splitting a vertex `v` (`ObtainedBySplittingVertex G G'`)
and `L` is a vital `p`-linkage in `G`, then `splitSpanningSubgraph G' L` is a vital `(p + 2)`-linkage
in `G'`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Hypergraph GraphMinor.GM10 GraphMinor.GM17

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. `splitSpanningSubgraph` and basic properties of `IsVertexSplit` -/

/-- For a subgraph `L ≤ G` with `V(L) = V(G)` and a graph `G'` obtained from `G` by splitting a
vertex, `splitSpanningSubgraph G' L` is the subgraph `L'` of `G'` with `V(L') = V(G')` and
`E(L') = E(L)` constructed in the proof of Graph Minors XXI, (2.4) (page 3 of the preprint). -/
def splitSpanningSubgraph (G' L : Hypergraph α β) : Hypergraph α β where
  vertexSet := G'.vertexSet
  edgeSet := G'.edgeSet ∩ L.edgeSet
  Inc e u := e ∈ G'.edgeSet ∩ L.edgeSet ∧ G'.Inc e u
  vertex_mem_of_inc := fun _ _ h => G'.vertex_mem_of_inc h.2
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := G'.vertexSet_finite
  edgeSet_finite := G'.edgeSet_finite.subset inter_subset_left

/-- `splitSpanningSubgraph G' L` is a subhypergraph of `G'` with the same vertex set as `G'`. -/
lemma splitSpanningSubgraph_le (G' L : Hypergraph α β) : splitSpanningSubgraph G' L ≤ G' where
  vertexSet_subset := Subset.rfl
  edgeSet_subset := inter_subset_left
  ends_eq e he := by
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq, splitSpanningSubgraph]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

/-- Basic vertex and incidence facts for `IsVertexSplit G G' v v₁ v₂ δ₁ δ₂`. -/
lemma isVertexSplit_basic_props {G G' : Hypergraph α β} {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) :
    v ≠ v₁ ∧ v ≠ v₂ ∧
    v₁ ∈ G'.vertexSet ∧ v₂ ∈ G'.vertexSet ∧ v ∉ G'.vertexSet ∧
    (∀ u : α, u ≠ v → u ≠ v₁ → u ≠ v₂ → (u ∈ G'.vertexSet ↔ u ∈ G.vertexSet)) ∧
    (∀ e : β, ∀ u : α, u ≠ v → u ≠ v₁ → u ≠ v₂ → (G'.Inc e u ↔ G.Inc e u)) ∧
    (∀ e : β, G'.Inc e v₁ ↔ e ∈ δ₁) ∧
    (∀ e : β, G'.Inc e v₂ ↔ e ∈ δ₂) ∧
    (∀ e : β, ¬ (G'.Inc e v₁ ∧ G'.Inc e v₂)) ∧
    (∀ e : β, (G'.Inc e v₁ ∨ G'.Inc e v₂) ↔ G.Inc e v) := by
  have hvv₁ : v ≠ v₁ := fun h => hs.v₁_not_mem (h ▸ hs.v_mem)
  have hvv₂ : v ≠ v₂ := fun h => hs.v₂_not_mem (h ▸ hs.v_mem)
  have hv₁G' : v₁ ∈ G'.vertexSet := by
    rw [hs.vertexSet_eq]; exact Or.inr (Or.inl rfl)
  have hv₂G' : v₂ ∈ G'.vertexSet := by
    rw [hs.vertexSet_eq]; exact Or.inr (Or.inr rfl)
  have hv_notG' : v ∉ G'.vertexSet := by
    rw [hs.vertexSet_eq]
    rintro (⟨_, hvv⟩ | rfl | rfl)
    · exact hvv rfl
    · exact hvv₁ rfl
    · exact hvv₂ rfl
  have hV_other : ∀ u : α, u ≠ v → u ≠ v₁ → u ≠ v₂ → (u ∈ G'.vertexSet ↔ u ∈ G.vertexSet) := by
    intro u huv huv₁ huv₂
    rw [hs.vertexSet_eq]
    simp only [mem_union, mem_sdiff, mem_singleton_iff, mem_insert_iff]
    tauto
  have hδ₁_sub : δ₁ ⊆ G.edgeSet := by
    intro e he
    have : e ∈ incidentEdges G v := by rw [← hs.δ_union]; exact Or.inl he
    exact this.1
  have hδ₂_sub : δ₂ ⊆ G.edgeSet := by
    intro e he
    have : e ∈ incidentEdges G v := by rw [← hs.δ_union]; exact Or.inr he
    exact this.1
  have hinc_other : ∀ e : β, ∀ u : α, u ≠ v → u ≠ v₁ → u ≠ v₂ → (G'.Inc e u ↔ G.Inc e u) := by
    intro e u huv huv₁ huv₂
    constructor
    · intro hinc'
      have heG' : e ∈ G'.edgeSet := G'.edge_mem_of_inc hinc'
      have huG' : u ∈ G'.vertexSet := G'.vertex_mem_of_inc hinc'
      rw [hs.inc_iff e heG' u huG'] at hinc'
      rcases hinc' with ⟨_, _, hinc⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hinc
      · exact (huv₁ rfl).elim
      · exact (huv₂ rfl).elim
    · intro hinc
      have heG' : e ∈ G'.edgeSet := by rw [hs.edgeSet_eq]; exact G.edge_mem_of_inc hinc
      have huG' : u ∈ G'.vertexSet := (hV_other u huv huv₁ huv₂).mpr (G.vertex_mem_of_inc hinc)
      rw [hs.inc_iff e heG' u huG']
      exact Or.inl ⟨huv₁, huv₂, hinc⟩
  have hinc_v₁ : ∀ e : β, G'.Inc e v₁ ↔ e ∈ δ₁ := by
    intro e
    constructor
    · intro hinc'
      have heG' : e ∈ G'.edgeSet := G'.edge_mem_of_inc hinc'
      rw [hs.inc_iff e heG' v₁ hv₁G'] at hinc'
      rcases hinc' with ⟨hne, _, _⟩ | ⟨_, he⟩ | ⟨heq, _⟩
      · exact (hne rfl).elim
      · exact he
      · exact (hs.v₁_ne_v₂ heq).elim
    · intro heδ₁
      have heG' : e ∈ G'.edgeSet := by rw [hs.edgeSet_eq]; exact hδ₁_sub heδ₁
      rw [hs.inc_iff e heG' v₁ hv₁G']
      exact Or.inr (Or.inl ⟨rfl, heδ₁⟩)
  have hinc_v₂ : ∀ e : β, G'.Inc e v₂ ↔ e ∈ δ₂ := by
    intro e
    constructor
    · intro hinc'
      have heG' : e ∈ G'.edgeSet := G'.edge_mem_of_inc hinc'
      rw [hs.inc_iff e heG' v₂ hv₂G'] at hinc'
      rcases hinc' with ⟨_, hne, _⟩ | ⟨heq, _⟩ | ⟨_, he⟩
      · exact (hne rfl).elim
      · exact (hs.v₁_ne_v₂ heq.symm).elim
      · exact he
    · intro heδ₂
      have heG' : e ∈ G'.edgeSet := by rw [hs.edgeSet_eq]; exact hδ₂_sub heδ₂
      rw [hs.inc_iff e heG' v₂ hv₂G']
      exact Or.inr (Or.inr ⟨rfl, heδ₂⟩)
  have hnot_both : ∀ e : β, ¬ (G'.Inc e v₁ ∧ G'.Inc e v₂) := by
    intro e ⟨h1, h2⟩
    exact Set.disjoint_left.mp hs.δ_disjoint ((hinc_v₁ e).mp h1) ((hinc_v₂ e).mp h2)
  have hor_iff : ∀ e : β, (G'.Inc e v₁ ∨ G'.Inc e v₂) ↔ G.Inc e v := by
    intro e
    rw [hinc_v₁, hinc_v₂, ← mem_union, hs.δ_union]
    simp only [incidentEdges, mem_ofPred_eq]
    exact ⟨fun h => h.2, fun h => ⟨G.edge_mem_of_inc h, h⟩⟩
  exact ⟨hvv₁, hvv₂, hv₁G', hv₂G', hv_notG', hV_other, hinc_other, hinc_v₁, hinc_v₂,
    hnot_both, hor_iff⟩

/-- For any subhypergraphs `H ≤ G` and `H' ≤ G'` with `H.edgeSet = H'.edgeSet`,
- `incidentEdges H u = incidentEdges H' u` for all `u ∉ {v, v₁, v₂}`,
- `incidentEdges H v = incidentEdges H' v₁ ∪ incidentEdges H' v₂` (disjoint union),
- `(incidentEdges H v).ncard = (incidentEdges H' v₁).ncard + (incidentEdges H' v₂).ncard`. -/
lemma isVertexSplit_incidentEdges_props {G G' H H' : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂)
    (hHG : H ≤ G) (hH'G' : H' ≤ G') (hE : H.edgeSet = H'.edgeSet) :
    (∀ u : α, u ≠ v → u ≠ v₁ → u ≠ v₂ → incidentEdges H u = incidentEdges H' u) ∧
    incidentEdges H v = incidentEdges H' v₁ ∪ incidentEdges H' v₂ ∧
    Disjoint (incidentEdges H' v₁) (incidentEdges H' v₂) ∧
    (incidentEdges H v).ncard =
      (incidentEdges H' v₁).ncard + (incidentEdges H' v₂).ncard := by
  obtain ⟨hvv₁, hvv₂, _, _, _, _, hinc_other, _, _, hnot_both, hor_iff⟩ :=
    isVertexSplit_basic_props hs
  have hother : ∀ u : α, u ≠ v → u ≠ v₁ → u ≠ v₂ → incidentEdges H u = incidentEdges H' u := by
    intro u huv huv₁ huv₂
    ext e
    simp only [incidentEdges, mem_ofPred_eq]
    constructor
    · rintro ⟨heH, hincH⟩
      have heH' : e ∈ H'.edgeSet := hE ▸ heH
      have hincG : G.Inc e u := inc_of_le hHG hincH
      have hincG' : G'.Inc e u := (hinc_other e u huv huv₁ huv₂).mpr hincG
      exact ⟨heH', (inc_iff_of_le hH'G' heH').2 hincG'⟩
    · rintro ⟨heH', hincH'⟩
      have heH : e ∈ H.edgeSet := hE.symm ▸ heH'
      have hincG' : G'.Inc e u := inc_of_le hH'G' hincH'
      have hincG : G.Inc e u := (hinc_other e u huv huv₁ huv₂).mp hincG'
      exact ⟨heH, (inc_iff_of_le hHG heH).2 hincG⟩
  have hv_union : incidentEdges H v = incidentEdges H' v₁ ∪ incidentEdges H' v₂ := by
    ext e
    simp only [incidentEdges, mem_ofPred_eq, mem_union]
    constructor
    · rintro ⟨heH, hincH⟩
      have heH' : e ∈ H'.edgeSet := hE ▸ heH
      have hincG : G.Inc e v := inc_of_le hHG hincH
      rcases (hor_iff e).mpr hincG with h1 | h2
      · exact Or.inl ⟨heH', (inc_iff_of_le hH'G' heH').2 h1⟩
      · exact Or.inr ⟨heH', (inc_iff_of_le hH'G' heH').2 h2⟩
    · rintro (⟨heH', hinc1⟩ | ⟨heH', hinc2⟩)
      · have heH : e ∈ H.edgeSet := hE.symm ▸ heH'
        have hincG : G.Inc e v := (hor_iff e).mp (Or.inl (inc_of_le hH'G' hinc1))
        exact ⟨heH, (inc_iff_of_le hHG heH).2 hincG⟩
      · have heH : e ∈ H.edgeSet := hE.symm ▸ heH'
        have hincG : G.Inc e v := (hor_iff e).mp (Or.inr (inc_of_le hH'G' hinc2))
        exact ⟨heH, (inc_iff_of_le hHG heH).2 hincG⟩
  have hdisj : Disjoint (incidentEdges H' v₁) (incidentEdges H' v₂) :=
    Set.disjoint_left.mpr fun e h1 h2 =>
      hnot_both e ⟨inc_of_le hH'G' h1.2, inc_of_le hH'G' h2.2⟩
  have hcard : (incidentEdges H v).ncard =
      (incidentEdges H' v₁).ncard + (incidentEdges H' v₂).ncard := by
    rw [hv_union]
    exact ncard_union_eq hdisj
      (H'.edgeSet_finite.subset fun _ h => h.1)
      (H'.edgeSet_finite.subset fun _ h => h.1)
  exact ⟨hother, hv_union, hdisj, hcard⟩

/-- Under `IsVertexSplit G G' v v₁ v₂ δ₁ δ₂`, every edge `e` has the same number of ends in `G'`
as in `G`. -/
lemma isVertexSplit_ends_ncard_eq {G G' : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (e : β) :
    (G'.ends e).ncard = (G.ends e).ncard := by
  obtain ⟨hvv₁, hvv₂, _, _, hv_notG', _, hinc_other, _, _, hnot_both, hor_iff⟩ :=
    isVertexSplit_basic_props hs
  by_cases hinc_v : G.Inc e v
  · rcases (hor_iff e).mpr hinc_v with h1 | h2
    · have hnot2 : ¬ G'.Inc e v₂ := fun h2 => hnot_both e ⟨h1, h2⟩
      have hends_eq : G'.ends e = insert v₁ (G.ends e \ {v}) := by
        ext u
        simp only [Hypergraph.ends, mem_ofPred_eq, mem_insert_iff, mem_sdiff, mem_singleton_iff]
        by_cases huv₁ : u = v₁
        · subst huv₁; exact ⟨fun _ => Or.inl rfl, fun _ => h1⟩
        · by_cases huv₂ : u = v₂
          · subst huv₂
            exact ⟨fun h => (hnot2 h).elim,
              fun h => (hs.v₂_not_mem (G.vertex_mem_of_inc (h.resolve_left huv₁).1)).elim⟩
          · by_cases huv : u = v
            · subst u
              exact ⟨fun h => (hv_notG' (G'.vertex_mem_of_inc h)).elim,
                fun h => ((h.resolve_left huv₁).2 rfl).elim⟩
            · rw [hinc_other e u huv huv₁ huv₂]
              exact ⟨fun h => Or.inr ⟨h, huv⟩, fun h => (h.resolve_left huv₁).1⟩
      have hv₁_not : v₁ ∉ G.ends e \ {v} :=
        fun h => hs.v₁_not_mem (G.vertex_mem_of_inc h.1)
      have hfin : (G.ends e \ {v}).Finite :=
        G.vertexSet_finite.subset (Subset.trans sdiff_subset fun _ h => G.vertex_mem_of_inc h)
      have hG_eq : G.ends e = insert v (G.ends e \ {v}) :=
        (insert_sdiff_self_of_mem hinc_v).symm
      rw [hends_eq, ncard_insert_of_notMem hv₁_not hfin]
      conv_rhs => rw [hG_eq, ncard_insert_of_notMem (fun h => h.2 rfl) hfin]
    · have hnot1 : ¬ G'.Inc e v₁ := fun h1 => hnot_both e ⟨h1, h2⟩
      have hends_eq : G'.ends e = insert v₂ (G.ends e \ {v}) := by
        ext u
        simp only [Hypergraph.ends, mem_ofPred_eq, mem_insert_iff, mem_sdiff, mem_singleton_iff]
        by_cases huv₂ : u = v₂
        · subst u; exact ⟨fun _ => Or.inl rfl, fun _ => h2⟩
        · by_cases huv₁ : u = v₁
          · subst u
            exact ⟨fun h => (hnot1 h).elim,
              fun h => (hs.v₁_not_mem (G.vertex_mem_of_inc (h.resolve_left huv₂).1)).elim⟩
          · by_cases huv : u = v
            · subst u
              exact ⟨fun h => (hv_notG' (G'.vertex_mem_of_inc h)).elim,
                fun h => ((h.resolve_left huv₂).2 rfl).elim⟩
            · rw [hinc_other e u huv huv₁ huv₂]
              exact ⟨fun h => Or.inr ⟨h, huv⟩, fun h => (h.resolve_left huv₂).1⟩
      have hv₂_not : v₂ ∉ G.ends e \ {v} :=
        fun h => hs.v₂_not_mem (G.vertex_mem_of_inc h.1)
      have hfin : (G.ends e \ {v}).Finite :=
        G.vertexSet_finite.subset (Subset.trans sdiff_subset fun _ h => G.vertex_mem_of_inc h)
      have hG_eq : G.ends e = insert v (G.ends e \ {v}) :=
        (insert_sdiff_self_of_mem hinc_v).symm
      rw [hends_eq, ncard_insert_of_notMem hv₂_not hfin]
      conv_rhs => rw [hG_eq, ncard_insert_of_notMem (fun h => h.2 rfl) hfin]
  · have hnot1 : ¬ G'.Inc e v₁ := fun h1 => hinc_v ((hor_iff e).mp (Or.inl h1))
    have hnot2 : ¬ G'.Inc e v₂ := fun h2 => hinc_v ((hor_iff e).mp (Or.inr h2))
    have hends_eq : G'.ends e = G.ends e := by
      ext u
      simp only [Hypergraph.ends, mem_ofPred_eq]
      by_cases huv₁ : u = v₁
      · subst huv₁
        exact ⟨fun h => (hnot1 h).elim, fun h => (hs.v₁_not_mem (G.vertex_mem_of_inc h)).elim⟩
      · by_cases huv₂ : u = v₂
        · subst huv₂
          exact ⟨fun h => (hnot2 h).elim, fun h => (hs.v₂_not_mem (G.vertex_mem_of_inc h)).elim⟩
        · by_cases huv : u = v
          · subst huv
            exact ⟨fun h => (hv_notG' (G'.vertex_mem_of_inc h)).elim, fun h => (hinc_v h).elim⟩
          · exact hinc_other e u huv huv₁ huv₂
    rw [hends_eq]

/-! ## 2. `splitSpanningSubgraph G' L` is a `(p + 2)`-linkage in `G'` -/

/-- If `L` is a linkage in `G` and `G'` is obtained from `G` by splitting `v`, then
`splitSpanningSubgraph G' L` is a linkage in `G'`. -/
lemma isLinkage_splitSpanningSubgraph {G G' L : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hL : IsLinkage G L) :
    IsLinkage G' (splitSpanningSubgraph G' L) := by
  let L' := splitSpanningSubgraph G' L
  have hL'G' : L' ≤ G' := splitSpanningSubgraph_le G' L
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.edgeSet_subset]
  obtain ⟨hinc_other, _, _, hcard_v⟩ :=
    isVertexSplit_incidentEdges_props hs hL.1 hL'G' hE_L'
  have hloop : ∀ e ∈ L'.edgeSet, (L'.ends e).ncard = 2 := by
    intro e he
    rw [← hL'G'.ends_eq e he, isVertexSplit_ends_ncard_eq hs e,
      hL.1.ends_eq e (hE_L' ▸ he)]
    exact hL.ends_ncard_eq_two (hE_L' ▸ he)
  have hdeg2 : ∀ x ∈ L'.vertexSet, (incidentEdges L' x).ncard ≤ 2 := by
    intro x hx
    by_cases hxv₁ : x = v₁
    · subst hxv₁
      have := hL.ncard_incidentEdges_le_two v
      omega
    · by_cases hxv₂ : x = v₂
      · subst hxv₂
        have := hL.ncard_incidentEdges_le_two v
        omega
      · have hxv : x ≠ v := fun h => (isVertexSplit_basic_props hs).2.2.2.2.1 (h ▸ hx)
        rw [← hinc_other x hxv hxv₁ hxv₂]
        exact hL.ncard_incidentEdges_le_two x
  have hdeg1 : ∀ H' : Hypergraph α β, H' ≤ L' → H'.edgeSet.Nonempty →
      ∃ x ∈ H'.vertexSet, (incidentEdges H' x).ncard = 1 := by
    intro H' hH'L' hH'_ne
    let H : Hypergraph α β :=
      { vertexSet := L.vertexSet
        edgeSet := H'.edgeSet
        Inc := fun e u => e ∈ H'.edgeSet ∧ L.Inc e u
        vertex_mem_of_inc := fun _ _ h => L.vertex_mem_of_inc h.2
        edge_mem_of_inc := fun _ _ h => h.1
        vertexSet_finite := L.vertexSet_finite
        edgeSet_finite := H'.edgeSet_finite }
    have hHL : H ≤ L :=
      { vertexSet_subset := Subset.rfl
        edgeSet_subset := hE_L' ▸ hH'L'.edgeSet_subset
        ends_eq := fun e he => by
          ext u
          simp only [Hypergraph.ends, mem_ofPred_eq, H]
          exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
    obtain ⟨hH_other, _, _, hH_card_v⟩ :=
      isVertexSplit_incidentEdges_props hs (le_trans hHL hL.1) (le_trans hH'L' hL'G') rfl
    obtain ⟨x, _, hx1⟩ := hL.exists_deg_one_of_le hHL hH'_ne
    by_cases hxv : x = v
    · subst hxv
      rw [hH_card_v] at hx1
      have hor : (incidentEdges H' v₁).ncard = 1 ∨ (incidentEdges H' v₂).ncard = 1 := by omega
      rcases hor with h1 | h2
      · obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp h1
        have : e₀ ∈ incidentEdges H' v₁ := by rw [he₀]; exact rfl
        exact ⟨v₁, H'.vertex_mem_of_inc this.2, h1⟩
      · obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp h2
        have : e₀ ∈ incidentEdges H' v₂ := by rw [he₀]; exact rfl
        exact ⟨v₂, H'.vertex_mem_of_inc this.2, h2⟩
    · have hxv₁ : x ≠ v₁ := by
        intro h; subst x
        obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hx1
        have : e₀ ∈ incidentEdges H v₁ := by rw [he₀]; exact rfl
        exact hs.v₁_not_mem (hL.1.vertexSet_subset (L.vertex_mem_of_inc this.2.2))
      have hxv₂ : x ≠ v₂ := by
        intro h; subst x
        obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hx1
        have : e₀ ∈ incidentEdges H v₂ := by rw [he₀]; exact rfl
        exact hs.v₂_not_mem (hL.1.vertexSet_subset (L.vertex_mem_of_inc this.2.2))
      rw [hH_other x hxv hxv₁ hxv₂] at hx1
      obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hx1
      have : e₀ ∈ incidentEdges H' x := by rw [he₀]; exact rfl
      exact ⟨x, H'.vertex_mem_of_inc this.2, hx1⟩
  exact isLinkage_of_deg_le_two_of_exists_deg_one hL'G' hloop hdeg2 hdeg1

/-- Terminal bound for `(2.4)`: if `L` is a vital `p`-linkage in `G`, then
`(terminals (splitSpanningSubgraph G' L)).ncard ≤ p + 2`. -/
lemma terminals_splitSpanningSubgraph_ncard_le {G G' L : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β} {p : ℕ}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hL : IsVitalPLinkage G L p) :
    (terminals (splitSpanningSubgraph G' L)).ncard ≤ p + 2 := by
  let L' := splitSpanningSubgraph G' L
  have hL'_link : IsLinkage G' L' := isLinkage_splitSpanningSubgraph hs hL.1.1
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.1.1.edgeSet_subset]
  obtain ⟨hinc_other, _, _, _⟩ :=
    isVertexSplit_incidentEdges_props hs hL.1.1.1 (splitSpanningSubgraph_le G' L) hE_L'
  obtain ⟨_, _, _, _, hv_notG', hV_other, _, _, _, _, _⟩ := isVertexSplit_basic_props hs
  have hsub : terminals L' ⊆ insert v₁ (insert v₂ (terminals L)) := by
    intro x hx
    by_cases hxv₁ : x = v₁
    · exact Or.inl hxv₁
    · by_cases hxv₂ : x = v₂
      · exact Or.inr (Or.inl hxv₂)
      · right; right
        have hxv : x ≠ v := fun h => hv_notG' (h ▸ hx.1)
        have hxG : x ∈ G.vertexSet := (hV_other x hxv hxv₁ hxv₂).mp hx.1
        have hxL : x ∈ L.vertexSet := by rwa [hL.1.2.1]
        have hnot2 : (incidentEdges L x).ncard ≠ 2 := by
          rw [hinc_other x hxv hxv₁ hxv₂]
          exact fun h2 => (hL'_link.notMem_terminals_iff hx.1).mpr h2 hx
        by_contra hx_not_term
        exact hnot2 ((hL.1.1.notMem_terminals_iff hxL).mp hx_not_term)
  have hfin : (insert v₁ (insert v₂ (terminals L))).Finite :=
    ((L.vertexSet_finite.subset fun _ h => h.1).insert v₂).insert v₁
  calc
    (terminals L').ncard ≤ (insert v₁ (insert v₂ (terminals L))).ncard :=
      ncard_le_ncard hsub hfin
    _ ≤ (insert v₂ (terminals L)).ncard + 1 := ncard_insert_le v₁ _
    _ ≤ ((terminals L).ncard + 1) + 1 := Nat.add_le_add_right (ncard_insert_le v₂ _) 1
    _ ≤ p + 2 := by have := hL.2.2; omega

/-! ## 3. Unsplitting a linkage `M'` with the same pattern as `L'` -/

/-- If `x ∉ H.vertexSet`, then `incidentEdges H x = ∅`. -/
lemma incidentEdges_eq_empty_of_notMem {H : Hypergraph α β} {x : α} (hx : x ∉ H.vertexSet) :
    incidentEdges H x = ∅ := by
  ext e
  simp only [incidentEdges, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
  exact fun _ hinc => hx (H.vertex_mem_of_inc hinc)

/-- For a linkage `L`, `x ∈ terminals L` if and only if
`x ∈ L.vertexSet ∧ (incidentEdges L x).ncard ≤ 1`. -/
lemma IsLinkage.mem_terminals_iff {G L : Hypergraph α β} (hL : IsLinkage G L) {x : α} :
    x ∈ terminals L ↔ x ∈ L.vertexSet ∧ (incidentEdges L x).ncard ≤ 1 := by
  simp only [terminals, IsTerminal, mem_ofPred_eq,
    hL.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl x]

/-- Degree characterization of `patternSubgraph LB S` when `S ⊆ linkagePattern LB` consists of
pairs. -/
lemma patternSubgraph_deg_props {B LB : Hypergraph α β} {S : Set (Set α)}
    (hLB : IsLinkage B LB) (hS_sub : S ⊆ linkagePattern LB)
    (hS_two : ∀ P ∈ S, P.ncard = 2) :
    patternSubgraph LB S ≤ LB ∧
    (∀ z : α, (incidentEdges (patternSubgraph LB S) z).ncard = 1 ↔ z ∈ ⋃₀ S) ∧
    (∀ z : α, z ∉ ⋃₀ S →
      (incidentEdges (patternSubgraph LB S) z).ncard = 0 ∨
      (incidentEdges (patternSubgraph LB S) z).ncard = 2) := by
  have hle : patternSubgraph LB S ≤ LB := patternSubgraph_le LB S
  obtain ⟨hPB_term, hPB_not_term, _⟩ :=
    patternSubgraph_incidentEdges_props hLB hS_sub hS_two
  have hdeg1_iff : ∀ z : α, (incidentEdges (patternSubgraph LB S) z).ncard = 1 ↔ z ∈ ⋃₀ S := by
    intro z
    constructor
    · intro h1
      have hz_term : z ∈ terminals LB := by
        by_contra hnot
        exact hPB_not_term z hnot h1
      by_contra hnot_S
      have h0 : (incidentEdges (patternSubgraph LB S) z).ncard = 0 :=
        (hPB_term z hz_term).2 (by simpa [mem_sUnion] using hnot_S)
      omega
    · rintro ⟨P, hPS, hzP⟩
      have hz_term : z ∈ terminals LB := by
        rw [hLB.terminals_eq_sUnion_linkagePattern]
        exact ⟨P, hS_sub hPS, hzP⟩
      exact (hPB_term z hz_term).1 ⟨P, hPS, hzP⟩
  refine ⟨hle, hdeg1_iff, ?_⟩
  intro z hz_not_S
  have hne1 : (incidentEdges (patternSubgraph LB S) z).ncard ≠ 1 :=
    mt (hdeg1_iff z).mp hz_not_S
  have hle2 : (incidentEdges (patternSubgraph LB S) z).ncard ≤ 2 :=
    le_trans (ncard_le_ncard (incidentEdges_subset_of_le hle z)
      (LB.edgeSet_finite.subset fun _ h => h.1)) (hLB.ncard_incidentEdges_le_two z)
  omega

/-- If `(incidentEdges L' v₁).ncard = 1` and `(incidentEdges L' v₂).ncard = 1`, then `v₁` and `v₂`
belong to distinct components of `L'` (`¬ L'.skeleton.Reachable v₁ v₂`). -/
lemma not_reachable_split_vertices_of_deg_one {G G' L : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hL : IsLinkage G L)
    (hv₁1 : (incidentEdges (splitSpanningSubgraph G' L) v₁).ncard = 1)
    (hv₂1 : (incidentEdges (splitSpanningSubgraph G' L) v₂).ncard = 1) :
    ¬ (splitSpanningSubgraph G' L).skeleton.Reachable v₁ v₂ := by
  let L' := splitSpanningSubgraph G' L
  change (incidentEdges L' v₁).ncard = 1 at hv₁1
  change (incidentEdges L' v₂).ncard = 1 at hv₂1
  have hL'_link : IsLinkage G' L' := isLinkage_splitSpanningSubgraph hs hL
  obtain ⟨_, _, hv₁G', hv₂G', _, _, _, _, _, _, _⟩ := isVertexSplit_basic_props hs
  intro hr
  have hv₁_term : v₁ ∈ terminals L' := hL'_link.mem_terminals_iff.mpr ⟨hv₁G', by omega⟩
  have hv₂_term : v₂ ∈ terminals L' := hL'_link.mem_terminals_iff.mpr ⟨hv₂G', by omega⟩
  let C' := reachableComponent L' v₁
  have hC'_comp : IsComponentOf L' C' := isComponentOf_reachableComponent hL'_link.2.1 hv₁G'
  have hC'_path : IsPathGraph C' := hL'_link.2.2 C' hC'_comp
  have hv₁C' : v₁ ∈ C'.vertexSet := self_mem_reachableComponent hv₁G'
  have hv₂C' : v₂ ∈ C'.vertexSet := ⟨hv₂G', hr⟩
  have hC'_ne : C'.edgeSet.Nonempty := by
    obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hv₁1
    have he₀_mem : e₀ ∈ incidentEdges L' v₁ := by rw [he₀]; exact rfl
    exact ⟨e₀, he₀_mem.1, v₁, he₀_mem.2, SimpleGraph.Reachable.refl v₁⟩
  obtain ⟨a, _, b, _, hab, htermC', ha1, hb1, hother⟩ :=
    isPathGraph_of_edgeSet_nonempty hC'_path hC'_ne
  have hv₁_ab : v₁ ∈ ({a, b} : Set α) := by
    rw [← htermC', ← hL'_link.terminals_inter_component_eq hC'_comp]
    exact ⟨hv₁_term, hv₁C'⟩
  have hv₂_ab : v₂ ∈ ({a, b} : Set α) := by
    rw [← htermC', ← hL'_link.terminals_inter_component_eq hC'_comp]
    exact ⟨hv₂_term, hv₂C'⟩
  have hab_eq : ({a, b} : Set α) = {v₁, v₂} := by
    rcases hv₁_ab with rfl | rfl <;> rcases hv₂_ab with rfl | rfl
    · exact (hs.v₁_ne_v₂ rfl).elim
    · rfl
    · exact pair_comm v₂ v₁
    · exact (hs.v₁_ne_v₂ rfl).elim
  let Q : Hypergraph α β :=
    { vertexSet := L.vertexSet
      edgeSet := C'.edgeSet
      Inc := fun e u => e ∈ C'.edgeSet ∧ L.Inc e u
      vertex_mem_of_inc := fun _ _ h => L.vertex_mem_of_inc h.2
      edge_mem_of_inc := fun _ _ h => h.1
      vertexSet_finite := L.vertexSet_finite
      edgeSet_finite := C'.edgeSet_finite }
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.edgeSet_subset]
  have hQL : Q ≤ L :=
    { vertexSet_subset := Subset.rfl
      edgeSet_subset := hE_L' ▸ hC'_comp.1.edgeSet_subset
      ends_eq := fun e he => by
        ext u
        simp only [Hypergraph.ends, mem_ofPred_eq, Q]
        exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩ }
  obtain ⟨hQ_other, _, _, hQ_card_v⟩ :=
    isVertexSplit_incidentEdges_props hs (le_trans hQL hL.1)
      (le_trans hC'_comp.1 (splitSpanningSubgraph_le G' L)) rfl
  obtain ⟨x, hxL, hx1⟩ := hL.exists_deg_one_of_le hQL hC'_ne
  by_cases hxv : x = v
  · subst x
    have hv₁_C'1 : (incidentEdges C' v₁).ncard = 1 := by
      rw [incidentEdges_component_eq hL'_link.2.1 hC'_comp hv₁C']
      exact hv₁1
    have hv₂_C'1 : (incidentEdges C' v₂).ncard = 1 := by
      rw [incidentEdges_component_eq hL'_link.2.1 hC'_comp hv₂C']
      exact hv₂1
    rw [hQ_card_v, hv₁_C'1, hv₂_C'1] at hx1
    omega
  · have hxv₁ : x ≠ v₁ := fun h => hs.v₁_not_mem (h ▸ hL.1.vertexSet_subset hxL)
    have hxv₂ : x ≠ v₂ := fun h => hs.v₂_not_mem (h ▸ hL.1.vertexSet_subset hxL)
    rw [hQ_other x hxv hxv₁ hxv₂] at hx1
    obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hx1
    have he₀_mem : e₀ ∈ incidentEdges C' x := by rw [he₀]; exact rfl
    have hxC' : x ∈ C'.vertexSet := C'.vertex_mem_of_inc he₀_mem.2
    have hx_not_ab : x ∉ ({a, b} : Set α) := by
      rw [hab_eq]
      simp only [mem_insert_iff, mem_singleton_iff, not_or]
      exact ⟨hxv₁, hxv₂⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx_not_ab
    have h2 := hother x hxC' hx_not_ab.1 hx_not_ab.2
    omega

/-- Given a linkage `M'` in `G'`, `unsplitSubgraph G L v M'` is the subhypergraph `M` of `G`
with `E(M) = E(G) ∩ E(M')` and
`V(M) = {u ∈ V(G) | (∃ e ∈ E(G) ∩ E(M'), G.Inc e u) ∨ (u ≠ v ∧ u ∈ V(M')) ∨ (u = v ∧ v ∈ terminals L)}`. -/
def unsplitSubgraph (G L : Hypergraph α β) (v : α) (M' : Hypergraph α β) : Hypergraph α β where
  vertexSet :=
    {u ∈ G.vertexSet | (∃ e ∈ G.edgeSet ∩ M'.edgeSet, G.Inc e u) ∨
      (u ≠ v ∧ u ∈ M'.vertexSet) ∨ (u = v ∧ v ∈ terminals L)}
  edgeSet := G.edgeSet ∩ M'.edgeSet
  Inc e u := e ∈ G.edgeSet ∩ M'.edgeSet ∧ G.Inc e u
  vertex_mem_of_inc := fun _ _ h => ⟨G.vertex_mem_of_inc h.2, Or.inl ⟨_, h.1, h.2⟩⟩
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := G.vertexSet_finite.subset fun _ h => h.1
  edgeSet_finite := G.edgeSet_finite.subset inter_subset_left

lemma unsplitSubgraph_le (G L : Hypergraph α β) (v : α) (M' : Hypergraph α β) :
    unsplitSubgraph G L v M' ≤ G where
  vertexSet_subset := fun _ h => h.1
  edgeSet_subset := inter_subset_left
  ends_eq e he := by
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq, unsplitSubgraph]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

/-- Spanning subgraph of `G` with edge set `G.edgeSet ∩ E`. -/
def spanningEdgeSubgraph (G : Hypergraph α β) (E : Set β) : Hypergraph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet ∩ E
  Inc e u := e ∈ G.edgeSet ∩ E ∧ G.Inc e u
  vertex_mem_of_inc := fun _ _ h => G.vertex_mem_of_inc h.2
  edge_mem_of_inc := fun _ _ h => h.1
  vertexSet_finite := G.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.subset inter_subset_left

lemma spanningEdgeSubgraph_le (G : Hypergraph α β) (E : Set β) :
    spanningEdgeSubgraph G E ≤ G where
  vertexSet_subset := Subset.rfl
  edgeSet_subset := inter_subset_left
  ends_eq e he := by
    ext u
    simp only [Hypergraph.ends, mem_ofPred_eq, spanningEdgeSubgraph]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

lemma spanningEdgeSubgraph_edgeSet_eq {G : Hypergraph α β} {E : Set β} (hE : E ⊆ G.edgeSet) :
    (spanningEdgeSubgraph G E).edgeSet = E :=
  inter_eq_self_of_subset_right hE

/-- Degree and terminal properties of `M := unsplitSubgraph G L v M'` when `M'` is a linkage in `G'`
with `linkagePattern M' = linkagePattern (splitSpanningSubgraph G' L)`. -/
lemma unsplitSubgraph_degree_and_terminals {G G' L M' : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂)
    (hL : IsLinkage G L) (hL_span : L.vertexSet = G.vertexSet)
    (hM' : IsLinkage G' M')
    (hpat' : linkagePattern M' = linkagePattern (splitSpanningSubgraph G' L)) :
    let M := unsplitSubgraph G L v M'
    M.edgeSet = M'.edgeSet ∧
    (∀ u, (incidentEdges M u).ncard ≤ 2) ∧
    terminals M = terminals L ∧
    (∀ u ∈ terminals L, (incidentEdges M u).ncard = (incidentEdges L u).ncard) ∧
    ((incidentEdges M v).ncard = (incidentEdges M' v₁).ncard + (incidentEdges M' v₂).ncard) ∧
    (∀ u, u ≠ v → u ≠ v₁ → u ≠ v₂ → incidentEdges M u = incidentEdges M' u) ∧
    IsLinkage G M := by
  intro M
  let L' := splitSpanningSubgraph G' L
  have hL'_link : IsLinkage G' L' := isLinkage_splitSpanningSubgraph hs hL
  have hMG : M ≤ G := unsplitSubgraph_le G L v M'
  have hE_M : M.edgeSet = M'.edgeSet := by
    change G.edgeSet ∩ M'.edgeSet = M'.edgeSet
    rw [← hs.edgeSet_eq]
    exact inter_eq_self_of_subset_right hM'.1.edgeSet_subset
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.edgeSet_subset]
  obtain ⟨hM_other, _, _, hM_card_v⟩ :=
    isVertexSplit_incidentEdges_props hs hMG hM'.1 hE_M
  obtain ⟨hL_other, _, _, hL_card_v⟩ :=
    isVertexSplit_incidentEdges_props hs hL.1 (splitSpanningSubgraph_le G' L) hE_L'
  change (incidentEdges L v).ncard =
    (incidentEdges L' v₁).ncard + (incidentEdges L' v₂).ncard at hL_card_v
  change ∀ u : α, u ≠ v → u ≠ v₁ → u ≠ v₂ →
    incidentEdges L u = incidentEdges L' u at hL_other
  obtain ⟨hvv₁, hvv₂, hv₁G', hv₂G', hv_notG', hV_other, _, _, _, _, _⟩ :=
    isVertexSplit_basic_props hs
  have hv₁_notG : v₁ ∉ G.vertexSet := hs.v₁_not_mem
  have hv₂_notG : v₂ ∉ G.vertexSet := hs.v₂_not_mem
  have hterm' : terminals M' = terminals L' := terminals_eq_of_linkagePattern_eq hM' hL'_link hpat'
  have hdeg_term' : ∀ x ∈ terminals L', (incidentEdges M' x).ncard = (incidentEdges L' x).ncard :=
    fun x hx => ncard_incidentEdges_eq_of_linkagePattern_eq hM' hL'_link hpat' (hterm'.symm ▸ hx)
  -- Analyze `(incidentEdges M' v₁).ncard` and `(incidentEdges M' v₂).ncard`
  have hv_analysis :
      (v ∈ terminals L →
        (incidentEdges M' v₁).ncard = (incidentEdges L' v₁).ncard ∧
        (incidentEdges M' v₂).ncard = (incidentEdges L' v₂).ncard ∧
        (incidentEdges M v).ncard = (incidentEdges L v).ncard) ∧
      (v ∉ terminals L →
        (incidentEdges M v).ncard = 2 ∨
        ((incidentEdges M v).ncard = 0 ∧ ¬ ∃ e ∈ G.edgeSet ∩ M'.edgeSet, G.Inc e v)) := by
    have hvL : v ∈ L.vertexSet := hL_span ▸ hs.v_mem
    have hLv_le2 : (incidentEdges L v).ncard ≤ 2 := hL.ncard_incidentEdges_le_two v
    constructor
    · intro hv_term
      have hLv_le1 : (incidentEdges L v).ncard ≤ 1 := (hL.mem_terminals_iff.mp hv_term).2
      have hv₁_le1 : (incidentEdges L' v₁).ncard ≤ 1 := by omega
      have hv₂_le1 : (incidentEdges L' v₂).ncard ≤ 1 := by omega
      have hv₁_term' : v₁ ∈ terminals L' := hL'_link.mem_terminals_iff.mpr ⟨hv₁G', hv₁_le1⟩
      have hv₂_term' : v₂ ∈ terminals L' := hL'_link.mem_terminals_iff.mpr ⟨hv₂G', hv₂_le1⟩
      have h1 := hdeg_term' v₁ hv₁_term'
      have h2 := hdeg_term' v₂ hv₂_term'
      refine ⟨h1, h2, ?_⟩
      rw [hM_card_v, hL_card_v, h1, h2]
    · intro hv_not_term
      have hLv_eq2 : (incidentEdges L v).ncard = 2 :=
        (hL.notMem_terminals_iff hvL).mp hv_not_term
      by_cases hv₁_le1 : (incidentEdges L' v₁).ncard ≤ 1
      · by_cases hv₂_le1 : (incidentEdges L' v₂).ncard ≤ 1
        · have h1 := hdeg_term' v₁ (hL'_link.mem_terminals_iff.mpr ⟨hv₁G', hv₁_le1⟩)
          have h2 := hdeg_term' v₂ (hL'_link.mem_terminals_iff.mpr ⟨hv₂G', hv₂_le1⟩)
          left
          rw [hM_card_v, h1, h2, ← hL_card_v, hLv_eq2]
        · have hv₂_eq2 : (incidentEdges L' v₂).ncard = 2 := by
            have := hL'_link.ncard_incidentEdges_le_two v₂; omega
          have hv₁_eq0 : (incidentEdges L' v₁).ncard = 0 := by omega
          have h1 : (incidentEdges M' v₁).ncard = 0 := by
            rw [hdeg_term' v₁ (hL'_link.mem_terminals_iff.mpr ⟨hv₁G', hv₁_le1⟩), hv₁_eq0]
          have hv₂_not_termM' : v₂ ∉ terminals M' := by
            rw [hterm', hL'_link.mem_terminals_iff]
            intro h; have := h.2; omega
          by_cases hv₂M' : v₂ ∈ M'.vertexSet
          · have h2 : (incidentEdges M' v₂).ncard = 2 :=
              (hM'.notMem_terminals_iff hv₂M').mp hv₂_not_termM'
            left; rw [hM_card_v, h1, h2]
          · have h2 : (incidentEdges M' v₂).ncard = 0 := by
              rw [incidentEdges_eq_empty_of_notMem hv₂M', ncard_empty]
            right
            have hMv0 : (incidentEdges M v).ncard = 0 := by rw [hM_card_v, h1, h2]
            refine ⟨hMv0, ?_⟩
            rintro ⟨e, he, hincG⟩
            have heM : e ∈ incidentEdges M v := ⟨he, he, hincG⟩
            have hne : (incidentEdges M v).Nonempty := ⟨e, heM⟩
            exact hne.ne_empty ((ncard_eq_zero (s := incidentEdges M v)
              (M.edgeSet_finite.subset fun _ h => h.1)).mp hMv0)
      · have hv₁_eq2 : (incidentEdges L' v₁).ncard = 2 := by
          have := hL'_link.ncard_incidentEdges_le_two v₁; omega
        have hv₂_eq0 : (incidentEdges L' v₂).ncard = 0 := by omega
        have h2 : (incidentEdges M' v₂).ncard = 0 := by
          rw [hdeg_term' v₂ (hL'_link.mem_terminals_iff.mpr ⟨hv₂G', by omega⟩), hv₂_eq0]
        have hv₁_not_termM' : v₁ ∉ terminals M' := by
          rw [hterm', hL'_link.mem_terminals_iff]
          intro h; have := h.2; omega
        by_cases hv₁M' : v₁ ∈ M'.vertexSet
        · have h1 : (incidentEdges M' v₁).ncard = 2 :=
            (hM'.notMem_terminals_iff hv₁M').mp hv₁_not_termM'
          left; rw [hM_card_v, h1, h2]
        · have h1 : (incidentEdges M' v₁).ncard = 0 := by
            rw [incidentEdges_eq_empty_of_notMem hv₁M', ncard_empty]
          right
          have hMv0 : (incidentEdges M v).ncard = 0 := by rw [hM_card_v, h1, h2]
          refine ⟨hMv0, ?_⟩
          rintro ⟨e, he, hincG⟩
          have heM : e ∈ incidentEdges M v := ⟨he, he, hincG⟩
          have hne : (incidentEdges M v).Nonempty := ⟨e, heM⟩
          exact hne.ne_empty ((ncard_eq_zero (s := incidentEdges M v)
            (M.edgeSet_finite.subset fun _ h => h.1)).mp hMv0)
  have hM_deg_le_two : ∀ u, (incidentEdges M u).ncard ≤ 2 := by
    intro u
    by_cases huv : u = v
    · subst u
      by_cases hv_term : v ∈ terminals L
      · rw [(hv_analysis.1 hv_term).2.2]
        exact hL.ncard_incidentEdges_le_two v
      · rcases hv_analysis.2 hv_term with h2 | ⟨h0, _⟩ <;> omega
    · by_cases huv₁ : u = v₁
      · subst u
        rw [incidentEdges_eq_empty_of_notMem (fun h => hv₁_notG (hMG.vertexSet_subset h)), ncard_empty]
        omega
      · by_cases huv₂ : u = v₂
        · subst u
          rw [incidentEdges_eq_empty_of_notMem (fun h => hv₂_notG (hMG.vertexSet_subset h)), ncard_empty]
          omega
        · rw [hM_other u huv huv₁ huv₂]
          exact hM'.ncard_incidentEdges_le_two u
  have hM_V_other : ∀ u, u ≠ v → u ≠ v₁ → u ≠ v₂ → (u ∈ M.vertexSet ↔ u ∈ M'.vertexSet) := by
    intro u huv huv₁ huv₂
    constructor
    · rintro ⟨_, ⟨e, he, hincG⟩ | ⟨_, huM'⟩ | ⟨rfl, _⟩⟩
      · have he_incM : e ∈ incidentEdges M u := ⟨he, he, hincG⟩
        rw [hM_other u huv huv₁ huv₂] at he_incM
        exact M'.vertex_mem_of_inc he_incM.2
      · exact huM'
      · exact (huv rfl).elim
    · intro huM'
      have huG' : u ∈ G'.vertexSet := hM'.1.vertexSet_subset huM'
      have huG : u ∈ G.vertexSet := (hV_other u huv huv₁ huv₂).mp huG'
      exact ⟨huG, Or.inr (Or.inl ⟨huv, huM'⟩)⟩
  have hM_loop : ∀ e ∈ M.edgeSet, (M.ends e).ncard = 2 := by
    intro e he
    rw [← hMG.ends_eq e he, ← isVertexSplit_ends_ncard_eq hs e,
      hM'.1.ends_eq e (hE_M ▸ he)]
    exact hM'.ends_ncard_eq_two (hE_M ▸ he)
  have hM_acyclic : ∀ H ≤ M, H.edgeSet.Nonempty → ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1 := by
    intro H hHM hH_ne
    by_contra! hno1
    have hH_02 : ∀ x, (incidentEdges H x).ncard = 0 ∨ (incidentEdges H x).ncard = 2 := by
      intro x
      by_cases hxH : x ∈ H.vertexSet
      · have hle : (incidentEdges H x).ncard ≤ 2 :=
          le_trans (ncard_le_ncard (incidentEdges_subset_of_le hHM x)
            (M.edgeSet_finite.subset fun _ h => h.1)) (hM_deg_le_two x)
        have hne1 := hno1 x hxH
        omega
      · left
        rw [incidentEdges_eq_empty_of_notMem hxH, ncard_empty]
    let H' := spanningEdgeSubgraph M' H.edgeSet
    have hH'M' : H' ≤ M' := spanningEdgeSubgraph_le M' H.edgeSet
    have hE_H : H.edgeSet = H'.edgeSet :=
      (spanningEdgeSubgraph_edgeSet_eq (hE_M ▸ hHM.edgeSet_subset)).symm
    obtain ⟨hH_other, _, _, hH_card_v⟩ :=
      isVertexSplit_incidentEdges_props hs (le_trans hHM hMG) (le_trans hH'M' hM'.1) hE_H
    have hH'_other_02 : ∀ x, x ≠ v₁ → x ≠ v₂ →
        (incidentEdges H' x).ncard = 0 ∨ (incidentEdges H' x).ncard = 2 := by
      intro x hxv₁ hxv₂
      by_cases hxv : x = v
      · subst x
        left
        have hv_notH' : v ∉ H'.vertexSet := fun h => hv_notG' (hM'.1.vertexSet_subset h)
        rw [incidentEdges_eq_empty_of_notMem hv_notH', ncard_empty]
      · rw [← hH_other x hxv hxv₁ hxv₂]
        exact hH_02 x
    obtain ⟨z, hzH', hz1⟩ := hM'.exists_deg_one_of_le hH'M' (hE_H ▸ hH_ne)
    have hzv₁₂ : z = v₁ ∨ z = v₂ := by
      by_contra! hne
      rcases hH'_other_02 z hne.1 hne.2 with h0 | h2 <;> omega
    have hv_sum : (incidentEdges H' v₁).ncard + (incidentEdges H' v₂).ncard = 0 ∨
        (incidentEdges H' v₁).ncard + (incidentEdges H' v₂).ncard = 2 := by
      rw [← hH_card_v]
      exact hH_02 v
    have hv₁_1 : (incidentEdges H' v₁).ncard = 1 := by
      rcases hzv₁₂ with rfl | rfl <;> rcases hv_sum with h0 | h2 <;> omega
    have hv₂_1 : (incidentEdges H' v₂).ncard = 1 := by
      rcases hzv₁₂ with rfl | rfl <;> rcases hv_sum with h0 | h2 <;> omega
    have hv₁_H' : v₁ ∈ H'.vertexSet := by
      obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hv₁_1
      have he₀_mem : e₀ ∈ incidentEdges H' v₁ := by rw [he₀]; exact rfl
      exact H'.vertex_mem_of_inc he₀_mem.2
    have hv₂_H' : v₂ ∈ H'.vertexSet := by
      obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hv₂_1
      have he₀_mem : e₀ ∈ incidentEdges H' v₂ := by rw [he₀]; exact rfl
      exact H'.vertex_mem_of_inc he₀_mem.2
    have hreachM' : M'.skeleton.Reachable v₁ v₂ :=
      same_component_of_deg_one_two_subgraph hM' hH'M' hv₁_H' hv₂_H' hs.v₁_ne_v₂ hv₁_1
        (fun x _ hx1 => by
          by_contra! hne
          rcases hH'_other_02 x hne.1 hne.2 with h0 | h2 <;> omega)
    have hv₁_le : (incidentEdges H' v₁).ncard ≤ (incidentEdges M' v₁).ncard :=
      ncard_le_ncard (incidentEdges_subset_of_le hH'M' v₁) (M'.edgeSet_finite.subset fun _ h => h.1)
    have hv₂_le : (incidentEdges H' v₂).ncard ≤ (incidentEdges M' v₂).ncard :=
      ncard_le_ncard (incidentEdges_subset_of_le hH'M' v₂) (M'.edgeSet_finite.subset fun _ h => h.1)
    have hv_M_le2 : (incidentEdges M' v₁).ncard + (incidentEdges M' v₂).ncard ≤ 2 := by
      rw [← hM_card_v]; exact hM_deg_le_two v
    have hv₁_M'1 : (incidentEdges M' v₁).ncard = 1 := by omega
    have hv₂_M'1 : (incidentEdges M' v₂).ncard = 1 := by omega
    have hv₁_termM' : v₁ ∈ terminals M' :=
      hM'.mem_terminals_iff.mpr ⟨hH'M'.vertexSet_subset hv₁_H', by omega⟩
    have hv₂_termM' : v₂ ∈ terminals M' :=
      hM'.mem_terminals_iff.mpr ⟨hH'M'.vertexSet_subset hv₂_H', by omega⟩
    have hpair_M' : ({v₁, v₂} : Set α) ∈ linkagePattern M' :=
      (hM'.pair_mem_linkagePattern_iff hv₁_termM' hv₂_termM' hs.v₁_ne_v₂).mpr hreachM'
    have hpair_L' : ({v₁, v₂} : Set α) ∈ linkagePattern L' := hpat' ▸ hpair_M'
    have hv₁_termL' : v₁ ∈ terminals L' := hterm' ▸ hv₁_termM'
    have hv₂_termL' : v₂ ∈ terminals L' := hterm' ▸ hv₂_termM'
    have hreachL' : L'.skeleton.Reachable v₁ v₂ :=
      (hL'_link.pair_mem_linkagePattern_iff hv₁_termL' hv₂_termL' hs.v₁_ne_v₂).mp hpair_L'
    have hv₁_L'1 : (incidentEdges L' v₁).ncard = 1 := by
      rw [← hdeg_term' v₁ hv₁_termL', hv₁_M'1]
    have hv₂_L'1 : (incidentEdges L' v₂).ncard = 1 := by
      rw [← hdeg_term' v₂ hv₂_termL', hv₂_M'1]
    exact not_reachable_split_vertices_of_deg_one hs hL hv₁_L'1 hv₂_L'1 hreachL'
  have hM_link : IsLinkage G M :=
    isLinkage_of_deg_le_two_of_exists_deg_one hMG hM_loop (fun u _ => hM_deg_le_two u) hM_acyclic
  have hterm_eq : terminals M = terminals L := by
    ext u
    rw [hM_link.mem_terminals_iff, hL.mem_terminals_iff]
    by_cases huv : u = v
    · subst u
      constructor
      · rintro ⟨hvM, hdegM⟩
        by_contra hv_not_termL
        have hv_not : v ∉ terminals L := by rwa [hL.mem_terminals_iff]
        rcases hv_analysis.2 hv_not with h2 | ⟨_, hno_e⟩
        · omega
        · rcases hvM with ⟨_, h_e | ⟨hvv, _⟩ | ⟨_, hvL⟩⟩
          · exact hno_e h_e
          · exact hvv rfl
          · exact hv_not hvL
      · intro hv_termL
        have hv_termL' : v ∈ terminals L := hL.mem_terminals_iff.mpr hv_termL
        refine ⟨⟨hs.v_mem, Or.inr (Or.inr ⟨rfl, hv_termL'⟩)⟩, ?_⟩
        rw [(hv_analysis.1 hv_termL').2.2]
        exact hv_termL.2
    · by_cases huv₁ : u = v₁
      · subst u
        exact ⟨fun h => (hv₁_notG (hMG.vertexSet_subset h.1)).elim,
          fun h => (hv₁_notG (hL.1.vertexSet_subset h.1)).elim⟩
      · by_cases huv₂ : u = v₂
        · subst u
          exact ⟨fun h => (hv₂_notG (hMG.vertexSet_subset h.1)).elim,
            fun h => (hv₂_notG (hL.1.vertexSet_subset h.1)).elim⟩
        · constructor
          · rintro ⟨huM, hdegM⟩
            have huM' : u ∈ M'.vertexSet := (hM_V_other u huv huv₁ huv₂).mp huM
            rw [hM_other u huv huv₁ huv₂] at hdegM
            have hu_termM' : u ∈ terminals M' := hM'.mem_terminals_iff.mpr ⟨huM', hdegM⟩
            have hu_termL' : u ∈ terminals L' := hterm' ▸ hu_termM'
            have hu_L'_props := hL'_link.mem_terminals_iff.mp hu_termL'
            have huG : u ∈ G.vertexSet := (hV_other u huv huv₁ huv₂).mp hu_L'_props.1
            refine ⟨hL_span.symm ▸ huG, ?_⟩
            rw [hL_other u huv huv₁ huv₂]
            exact hu_L'_props.2
          · rintro ⟨huL, hdegL⟩
            have huG : u ∈ G.vertexSet := hL.1.vertexSet_subset huL
            have huG' : u ∈ G'.vertexSet := (hV_other u huv huv₁ huv₂).mpr huG
            rw [hL_other u huv huv₁ huv₂] at hdegL
            have hu_termL' : u ∈ terminals L' := hL'_link.mem_terminals_iff.mpr ⟨huG', hdegL⟩
            have hu_termM' : u ∈ terminals M' := hterm'.symm ▸ hu_termL'
            have hu_M'_props := hM'.mem_terminals_iff.mp hu_termM'
            refine ⟨(hM_V_other u huv huv₁ huv₂).mpr hu_M'_props.1, ?_⟩
            rw [hM_other u huv huv₁ huv₂]
            exact hu_M'_props.2
  have hdeg_term_eq : ∀ u ∈ terminals L, (incidentEdges M u).ncard = (incidentEdges L u).ncard := by
    intro u huL
    by_cases huv : u = v
    · subst u
      exact (hv_analysis.1 huL).2.2
    · have huv₁ : u ≠ v₁ := fun h => hv₁_notG (hL.1.vertexSet_subset (h ▸ huL.1))
      have huv₂ : u ≠ v₂ := fun h => hv₂_notG (hL.1.vertexSet_subset (h ▸ huL.1))
      rw [hM_other u huv huv₁ huv₂, hL_other u huv huv₁ huv₂]
      have huG' : u ∈ G'.vertexSet := (hV_other u huv huv₁ huv₂).mpr (hL.1.vertexSet_subset huL.1)
      have hu_degL : (incidentEdges L u).ncard ≤ 1 := (hL.mem_terminals_iff.mp huL).2
      have hu_termL' : u ∈ terminals L' :=
        hL'_link.mem_terminals_iff.mpr ⟨huG', by rw [← hL_other u huv huv₁ huv₂]; exact hu_degL⟩
      exact hdeg_term' u hu_termL'
  exact ⟨hE_M, hM_deg_le_two, hterm_eq, hdeg_term_eq, hM_card_v, hM_other, hM_link⟩

/-- For `M := unsplitSubgraph G L v M'`, if `M'` is a linkage in `G'` with the same pattern as
`L' := splitSpanningSubgraph G' L`, then `linkagePattern M = linkagePattern L`. -/
lemma unsplitSubgraph_linkagePattern_eq {G G' L M' : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂)
    (hL : IsLinkage G L) (hL_span : L.vertexSet = G.vertexSet)
    (hM' : IsLinkage G' M')
    (hpat' : linkagePattern M' = linkagePattern (splitSpanningSubgraph G' L)) :
    linkagePattern (unsplitSubgraph G L v M') = linkagePattern L := by
  let M := unsplitSubgraph G L v M'
  let L' := splitSpanningSubgraph G' L
  have hL'_link : IsLinkage G' L' := isLinkage_splitSpanningSubgraph hs hL
  have hMG : M ≤ G := unsplitSubgraph_le G L v M'
  obtain ⟨hE_M, _, hterm_eq, hdeg_term_eq, hM_card_v, hM_other, hM_link⟩ :=
    unsplitSubgraph_degree_and_terminals hs hL hL_span hM' hpat'
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.edgeSet_subset]
  obtain ⟨hL_other, _, _, hL_card_v⟩ :=
    isVertexSplit_incidentEdges_props hs hL.1 (splitSpanningSubgraph_le G' L) hE_L'
  change (incidentEdges L v).ncard =
    (incidentEdges L' v₁).ncard + (incidentEdges L' v₂).ncard at hL_card_v
  obtain ⟨_, _, hv₁G', hv₂G', hv_notG', _, _, _, _, _, _⟩ :=
    isVertexSplit_basic_props hs
  have hv₁_notG : v₁ ∉ G.vertexSet := hs.v₁_not_mem
  have hv₂_notG : v₂ ∉ G.vertexSet := hs.v₂_not_mem
  have hterm' : terminals M' = terminals L' := terminals_eq_of_linkagePattern_eq hM' hL'_link hpat'
  have hdeg_term' : ∀ x ∈ terminals L', (incidentEdges M' x).ncard = (incidentEdges L' x).ncard :=
    fun x hx => ncard_incidentEdges_eq_of_linkagePattern_eq hM' hL'_link hpat' (hterm'.symm ▸ hx)
  apply linkagePattern_eq_of_subset hM_link hL hterm_eq.symm.subset
  intro P hP
  rcases hM_link.mem_linkagePattern_structure hP with
    ⟨u, huM, rfl, hu0⟩ | ⟨u, huM, w, hwM, huw, rfl, hu1, hw1⟩
  · have huL : u ∈ terminals L := hterm_eq ▸ huM
    rw [hdeg_term_eq u huL] at hu0
    exact (hL.ncard_incidentEdges_eq_zero_iff huL.1).mp hu0
  · have hreach : M.skeleton.Reachable u w :=
      (hM_link.pair_mem_linkagePattern_iff huM hwM huw).mp hP
    have huL : u ∈ terminals L := hterm_eq ▸ huM
    have hwL : w ∈ terminals L := hterm_eq ▸ hwM
    rw [hL.pair_mem_linkagePattern_iff huL hwL huw]
    let C := reachableComponent M u
    have hC_comp : IsComponentOf M C := isComponentOf_reachableComponent hM_link.2.1 huM.1
    have hC_path : IsPathGraph C := hM_link.2.2 C hC_comp
    have huC : u ∈ C.vertexSet := self_mem_reachableComponent huM.1
    have hwC : w ∈ C.vertexSet := ⟨hwM.1, hreach⟩
    have hC_ne : C.edgeSet.Nonempty := by
      obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hu1
      have he₀_mem : e₀ ∈ incidentEdges M u := by rw [he₀]; exact rfl
      exact ⟨e₀, he₀_mem.1, u, he₀_mem.2, SimpleGraph.Reachable.refl u⟩
    obtain ⟨a, _, b, _, _, htermC_ab, ha1, hb1, hC_other_ab⟩ :=
      isPathGraph_of_edgeSet_nonempty hC_path hC_ne
    have htermC_eq : terminals C = {u, w} := by
      have hu_termC : u ∈ terminals C := by
        rw [← hM_link.terminals_inter_component_eq hC_comp]
        exact ⟨huM, huC⟩
      have hw_termC : w ∈ terminals C := by
        rw [← hM_link.terminals_inter_component_eq hC_comp]
        exact ⟨hwM, hwC⟩
      rw [htermC_ab] at hu_termC hw_termC ⊢
      rcases hu_termC with rfl | rfl <;> rcases hw_termC with rfl | rfl
      · exact (huw rfl).elim
      · rfl
      · exact pair_comm w u
      · exact (huw rfl).elim
    have hC_deg_props :
        (incidentEdges C u).ncard = 1 ∧
        (incidentEdges C w).ncard = 1 ∧
        ∀ z, z ≠ u → z ≠ w → (incidentEdges C z).ncard = 0 ∨ (incidentEdges C z).ncard = 2 := by
      refine ⟨?_, ?_, ?_⟩
      · rw [incidentEdges_component_eq hM_link.2.1 hC_comp huC]; exact hu1
      · rw [incidentEdges_component_eq hM_link.2.1 hC_comp hwC]; exact hw1
      · intro z hzu hzw
        by_cases hzC : z ∈ C.vertexSet
        · right
          have hz_not_ab : z ∉ ({a, b} : Set α) := by
            rw [← htermC_ab, htermC_eq]
            simp only [mem_insert_iff, mem_singleton_iff, not_or]
            exact ⟨hzu, hzw⟩
          simp only [mem_insert_iff, mem_singleton_iff, not_or] at hz_not_ab
          exact hC_other_ab z hzC hz_not_ab.1 hz_not_ab.2
        · left
          rw [incidentEdges_eq_empty_of_notMem hzC, ncard_empty]
    let C' := spanningEdgeSubgraph M' C.edgeSet
    have hC'M' : C' ≤ M' := spanningEdgeSubgraph_le M' C.edgeSet
    have hE_C : C.edgeSet = C'.edgeSet :=
      (spanningEdgeSubgraph_edgeSet_eq (hE_M ▸ hC_comp.1.edgeSet_subset)).symm
    obtain ⟨hC_other, _, _, hC_card_v⟩ :=
      isVertexSplit_incidentEdges_props hs (le_trans hC_comp.1 hMG) (le_trans hC'M' hM'.1) hE_C
    change (incidentEdges M v).ncard =
      (incidentEdges M' v₁).ncard + (incidentEdges M' v₂).ncard at hM_card_v
    change (incidentEdges C v).ncard =
      (incidentEdges C' v₁).ncard + (incidentEdges C' v₂).ncard at hC_card_v
    -- Claim 1: every degree-1 vertex of `C'` has degree 1 in `M'` (hence is in `terminals M'`)
    have hC'_deg1_imp_M' : ∀ z, (incidentEdges C' z).ncard = 1 →
        (incidentEdges M' z).ncard = 1 ∧ z ∈ terminals M' := by
      intro z hz1
      have hzM' : z ∈ M'.vertexSet := by
        obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hz1
        have he₀_mem : e₀ ∈ incidentEdges C' z := by rw [he₀]; exact rfl
        exact C'.vertex_mem_of_inc he₀_mem.2
      suffices hM'z1 : (incidentEdges M' z).ncard = 1 from
        ⟨hM'z1, hM'.mem_terminals_iff.mpr ⟨hzM', by omega⟩⟩
      by_cases hzv : z = v
      · subst z
        have hv_notC' : v ∉ C'.vertexSet := fun h => hv_notG' (hM'.1.vertexSet_subset h)
        rw [incidentEdges_eq_empty_of_notMem hv_notC', ncard_empty] at hz1
        omega
      · by_cases hzv₁ : z = v₁
        · subst z
          have hv₁_le : (incidentEdges C' v₁).ncard ≤ (incidentEdges M' v₁).ncard :=
            ncard_le_ncard (incidentEdges_subset_of_le hC'M' v₁) (M'.edgeSet_finite.subset fun _ h => h.1)
          have hv₂_le : (incidentEdges C' v₂).ncard ≤ (incidentEdges M' v₂).ncard :=
            ncard_le_ncard (incidentEdges_subset_of_le hC'M' v₂) (M'.edgeSet_finite.subset fun _ h => h.1)
          have hCM_le : (incidentEdges C v).ncard ≤ (incidentEdges M v).ncard :=
            ncard_le_ncard (incidentEdges_subset_of_le hC_comp.1 v) (M.edgeSet_finite.subset fun _ h => h.1)
          have hMv_le2 : (incidentEdges M v).ncard ≤ 2 := hM_link.ncard_incidentEdges_le_two v
          by_cases hv_uw : v = u ∨ v = w
          · have hCv1 : (incidentEdges C v).ncard = 1 := by
              rcases hv_uw with hvu | hvw
              · rw [hvu]; exact hC_deg_props.1
              · rw [hvw]; exact hC_deg_props.2.1
            have hMv1 : (incidentEdges M v).ncard = 1 := by
              rcases hv_uw with hvu | hvw
              · rw [hvu]; exact hu1
              · rw [hvw]; exact hw1
            omega
          · rw [not_or] at hv_uw
            rcases hC_deg_props.2.2 v hv_uw.1 hv_uw.2 with hCv0 | hCv2 <;> omega
        · by_cases hzv₂ : z = v₂
          · subst z
            have hv₁_le : (incidentEdges C' v₁).ncard ≤ (incidentEdges M' v₁).ncard :=
              ncard_le_ncard (incidentEdges_subset_of_le hC'M' v₁) (M'.edgeSet_finite.subset fun _ h => h.1)
            have hv₂_le : (incidentEdges C' v₂).ncard ≤ (incidentEdges M' v₂).ncard :=
              ncard_le_ncard (incidentEdges_subset_of_le hC'M' v₂) (M'.edgeSet_finite.subset fun _ h => h.1)
            have hCM_le : (incidentEdges C v).ncard ≤ (incidentEdges M v).ncard :=
              ncard_le_ncard (incidentEdges_subset_of_le hC_comp.1 v) (M.edgeSet_finite.subset fun _ h => h.1)
            have hMv_le2 : (incidentEdges M v).ncard ≤ 2 := hM_link.ncard_incidentEdges_le_two v
            by_cases hv_uw : v = u ∨ v = w
            · have hCv1 : (incidentEdges C v).ncard = 1 := by
                rcases hv_uw with hvu | hvw
                · rw [hvu]; exact hC_deg_props.1
                · rw [hvw]; exact hC_deg_props.2.1
              have hMv1 : (incidentEdges M v).ncard = 1 := by
                rcases hv_uw with hvu | hvw
                · rw [hvu]; exact hu1
                · rw [hvw]; exact hw1
              omega
            · rw [not_or] at hv_uw
              rcases hC_deg_props.2.2 v hv_uw.1 hv_uw.2 with hCv0 | hCv2 <;> omega
          · have hCz1 : (incidentEdges C z).ncard = 1 := by
              rw [hC_other z hzv hzv₁ hzv₂]; exact hz1
            have hz_uw : z = u ∨ z = w := by
              by_contra! hne
              rcases hC_deg_props.2.2 z hne.1 hne.2 with h0 | h2 <;> omega
            rw [← hM_other z hzv hzv₁ hzv₂]
            rcases hz_uw with rfl | rfl
            · exact hu1
            · exact hw1
    -- Define `S` as the set of pairs in `linkagePattern M'` meeting a degree-1 vertex of `C'`
    let S : Set (Set α) :=
      {Q ∈ linkagePattern M' | Q.ncard = 2 ∧ ∃ x ∈ Q, (incidentEdges C' x).ncard = 1}
    have hS_sub : S ⊆ linkagePattern L' := by
      intro Q hQ; rw [← hpat']; exact hQ.1
    have hS_card : ∀ Q ∈ S, Q.ncard = 2 := fun _ hQ => hQ.2.1
    -- Claim 3: if `Q ∈ S`, then BOTH members of `Q` have degree 1 in `C'`
    have hS_all_deg1 : ∀ Q ∈ S, ∀ y ∈ Q, (incidentEdges C' y).ncard = 1 := by
      rintro Q ⟨hQ_pat, hQ2, x, hxQ, hx1⟩ y hyQ
      rcases hM'.mem_linkagePattern_structure hQ_pat with
        ⟨z, _, rfl, _⟩ | ⟨z₁, hz₁M', z₂, hz₂M', hz₁₂, rfl, _⟩
      · rw [ncard_singleton] at hQ2; omega
      · have hreachM' : M'.skeleton.Reachable z₁ z₂ :=
          (hM'.pair_mem_linkagePattern_iff hz₁M' hz₂M' hz₁₂).mp hQ_pat
        let K' := reachableComponent M' z₁
        have hK'_comp : IsComponentOf M' K' := isComponentOf_reachableComponent hM'.2.1 hz₁M'.1
        have hz₁K' : z₁ ∈ K'.vertexSet := self_mem_reachableComponent hz₁M'.1
        have hz₂K' : z₂ ∈ K'.vertexSet := ⟨hz₂M'.1, hreachM'⟩
        let J := C' ∩ K'
        have hJM' : J ≤ M' := le_trans (inter_le_left hC'M' hK'_comp.1) hC'M'
        have hJ_link : IsLinkage G' J := isLinkage_of_le hM' hJM' (le_trans hJM' hM'.1)
        have hJ_inc : ∀ t ∈ K'.vertexSet, incidentEdges J t = incidentEdges C' t := by
          intro t htK'
          ext e
          simp only [incidentEdges, mem_ofPred_eq, J, inter_edgeSet, inter_inc]
          refine ⟨fun h => ⟨h.1.1, h.2.1⟩, fun ⟨heC', hincC'⟩ => ?_⟩
          have heM' : e ∈ M'.edgeSet := hC'M'.edgeSet_subset heC'
          have hincM' : M'.Inc e t := inc_of_le hC'M' hincC'
          have heK' : e ∈ K'.edgeSet := ⟨heM', t, hincM', htK'.2⟩
          have hincK' : K'.Inc e t := (inc_iff_of_le hK'_comp.1 heK').mpr hincM'
          exact ⟨⟨heC', heK'⟩, hincC', hincK'⟩
        have hxK' : x ∈ K'.vertexSet := by
          rcases hxQ with rfl | rfl
          · exact hz₁K'
          · exact hz₂K'
        have hxJ1 : (incidentEdges J x).ncard = 1 := by
          rw [hJ_inc x hxK']; exact hx1
        have hJ_ne : J.edgeSet.Nonempty := by
          obtain ⟨e₀, he₀⟩ := ncard_eq_one.mp hxJ1
          have he₀_mem : e₀ ∈ incidentEdges J x := by rw [he₀]; exact rfl
          exact ⟨e₀, he₀_mem.1⟩
        obtain ⟨x₁, hx₁J, x₂, hx₂J, hx₁₂, hx₁1, hx₂1⟩ :=
          exists_two_deg_one_of_edgeSet_nonempty
            (fun _ he => hJ_link.ends_ncard_eq_two he)
            (fun _ hle hne => hJ_link.exists_deg_one_of_le hle hne)
            J le_rfl hJ_ne
        have hx₁K' : x₁ ∈ K'.vertexSet := hx₁J.2
        have hx₂K' : x₂ ∈ K'.vertexSet := hx₂J.2
        rw [hJ_inc x₁ hx₁K'] at hx₁1
        rw [hJ_inc x₂ hx₂K'] at hx₂1
        have hx₁_termM' : x₁ ∈ terminals M' := (hC'_deg1_imp_M' x₁ hx₁1).2
        have hx₂_termM' : x₂ ∈ terminals M' := (hC'_deg1_imp_M' x₂ hx₂1).2
        have htermK'_eq : terminals M' ∩ K'.vertexSet = {z₁, z₂} := by
          have h1 : z₁ ∈ terminals K' := by
            rw [← hM'.terminals_inter_component_eq hK'_comp]
            exact ⟨hz₁M', hz₁K'⟩
          have h2 : z₂ ∈ terminals K' := by
            rw [← hM'.terminals_inter_component_eq hK'_comp]
            exact ⟨hz₂M', hz₂K'⟩
          rw [hM'.terminals_inter_component_eq hK'_comp]
          have hK'_path : IsPathGraph K' := hM'.2.2 K' hK'_comp
          have hK'_ne : K'.edgeSet.Nonempty := by
            obtain ⟨e₀, he₀⟩ := hJ_ne
            exact ⟨e₀, he₀.2⟩
          obtain ⟨a', _, b', _, _, htermK'_ab, _, _, _⟩ :=
            isPathGraph_of_edgeSet_nonempty hK'_path hK'_ne
          rw [htermK'_ab] at h1 h2 ⊢
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
          · exact (hz₁₂ rfl).elim
          · rfl
          · exact pair_comm z₂ z₁
          · exact (hz₁₂ rfl).elim
        have hx₁_z : x₁ ∈ ({z₁, z₂} : Set α) := htermK'_eq ▸ ⟨hx₁_termM', hx₁K'⟩
        have hx₂_z : x₂ ∈ ({z₁, z₂} : Set α) := htermK'_eq ▸ ⟨hx₂_termM', hx₂K'⟩
        have hy_x : y = x₁ ∨ y = x₂ := by
          rcases hx₁_z with rfl | rfl <;> rcases hx₂_z with rfl | rfl
          · exact (hx₁₂ rfl).elim
          · rcases hyQ with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr rfl
          · rcases hyQ with rfl | rfl
            · exact Or.inr rfl
            · exact Or.inl rfl
          · exact (hx₁₂ rfl).elim
        rcases hy_x with rfl | rfl
        · exact hx₁1
        · exact hx₂1
    -- Claim 4: `z ∈ ⋃₀ S ↔ (incidentEdges C' z).ncard = 1`
    have h_mem_sUnion_S : ∀ z, z ∈ ⋃₀ S ↔ (incidentEdges C' z).ncard = 1 := by
      intro z
      constructor
      · rintro ⟨Q, hQS, hzQ⟩
        exact hS_all_deg1 Q hQS z hzQ
      · intro hz1
        obtain ⟨hzM'1, hz_termM'⟩ := hC'_deg1_imp_M' z hz1
        rw [hM'.terminals_eq_sUnion_linkagePattern] at hz_termM'
        obtain ⟨Q, hQ_pat, hzQ⟩ := hz_termM'
        rcases hM'.mem_linkagePattern_structure hQ_pat with
          ⟨a, _, rfl, ha0⟩ | ⟨a, _, b, _, hab, rfl, _⟩
        · simp only [mem_singleton_iff] at hzQ
          subst z; omega
        · refine ⟨{a, b}, ⟨hQ_pat, ncard_pair hab, z, hzQ, hz1⟩, hzQ⟩
    -- Construct `H'_L := patternSubgraph L' S` and `H_L := spanningEdgeSubgraph L H'_L.edgeSet`
    let H'_L := patternSubgraph L' S
    obtain ⟨hH'_LL', hH'_L_deg1, hH'_L_deg02⟩ :=
      patternSubgraph_deg_props hL'_link hS_sub hS_card
    let H_L := spanningEdgeSubgraph L H'_L.edgeSet
    have hH_LL : H_L ≤ L := spanningEdgeSubgraph_le L H'_L.edgeSet
    have hE_HL : H_L.edgeSet = H'_L.edgeSet :=
      spanningEdgeSubgraph_edgeSet_eq (hE_L'.symm ▸ hH'_LL'.edgeSet_subset)
    obtain ⟨hHL_other, _, _, hHL_card_v⟩ :=
      isVertexSplit_incidentEdges_props hs (le_trans hH_LL hL.1)
        (le_trans hH'_LL' (splitSpanningSubgraph_le G' L)) hE_HL
    -- Helper: if `(incidentEdges L' x).ncard = 0`, then `(incidentEdges H'_L x).ncard = 0`
    have hH'_L_zero_of_L'_zero : ∀ x, (incidentEdges L' x).ncard = 0 →
        (incidentEdges H'_L x).ncard = 0 := by
      intro x hx0
      have hle : (incidentEdges H'_L x).ncard ≤ (incidentEdges L' x).ncard :=
        ncard_le_ncard (incidentEdges_subset_of_le hH'_LL' x) (L'.edgeSet_finite.subset fun _ h => h.1)
      omega
    -- Check degrees in `H_L` at `u`, `w`, and all `z ≠ u, w`
    have hHL_deg : ∀ z,
        ((z = u ∨ z = w) → (incidentEdges H_L z).ncard = 1) ∧
        (z ≠ u → z ≠ w → (incidentEdges H_L z).ncard = 0 ∨ (incidentEdges H_L z).ncard = 2) := by
      intro z
      by_cases hzv : z = v
      · subst z
        have hv₁_iff : (incidentEdges H'_L v₁).ncard = 1 ↔ (incidentEdges C' v₁).ncard = 1 :=
          (hH'_L_deg1 v₁).trans (h_mem_sUnion_S v₁)
        have hv₂_iff : (incidentEdges H'_L v₂).ncard = 1 ↔ (incidentEdges C' v₂).ncard = 1 :=
          (hH'_L_deg1 v₂).trans (h_mem_sUnion_S v₂)
        constructor
        · intro hv_uw
          have hCv1 : (incidentEdges C v).ncard = 1 := by
            rcases hv_uw with hvu | hvw
            · rw [hvu]; exact hC_deg_props.1
            · rw [hvw]; exact hC_deg_props.2.1
          have hLv1 : (incidentEdges L v).ncard = 1 := by
            rcases hv_uw with hvu | hvw
            · rw [hvu, ← hdeg_term_eq u huL]; exact hu1
            · rw [hvw, ← hdeg_term_eq w hwL]; exact hw1
          have hC'_sum : (incidentEdges C' v₁).ncard + (incidentEdges C' v₂).ncard = 1 := by
            rw [← hC_card_v]; exact hCv1
          have hL'_sum : (incidentEdges L' v₁).ncard + (incidentEdges L' v₂).ncard = 1 := by
            rw [← hL_card_v]; exact hLv1
          by_cases hv₁1 : (incidentEdges C' v₁).ncard = 1
          · have hv₂0 : (incidentEdges C' v₂).ncard = 0 := by omega
            have hv₁_M'1 : (incidentEdges M' v₁).ncard = 1 := (hC'_deg1_imp_M' v₁ hv₁1).1
            have hv₁_L'1 : (incidentEdges L' v₁).ncard = 1 := by
              rw [← hdeg_term' v₁ (hL'_link.mem_terminals_iff.mpr ⟨hv₁G', by omega⟩)]
              exact hv₁_M'1
            have hv₂_L'0 : (incidentEdges L' v₂).ncard = 0 := by omega
            rw [hHL_card_v, hv₁_iff.mpr hv₁1, hH'_L_zero_of_L'_zero v₂ hv₂_L'0]
          · have hv₂1 : (incidentEdges C' v₂).ncard = 1 := by omega
            have hv₂_M'1 : (incidentEdges M' v₂).ncard = 1 := (hC'_deg1_imp_M' v₂ hv₂1).1
            have hv₂_L'1 : (incidentEdges L' v₂).ncard = 1 := by
              rw [← hdeg_term' v₂ (hL'_link.mem_terminals_iff.mpr ⟨hv₂G', by omega⟩)]
              exact hv₂_M'1
            have hv₁_L'0 : (incidentEdges L' v₁).ncard = 0 := by omega
            rw [hHL_card_v, hH'_L_zero_of_L'_zero v₁ hv₁_L'0, hv₂_iff.mpr hv₂1]
        · intro hvu hvw
          have hCv02 : (incidentEdges C' v₁).ncard + (incidentEdges C' v₂).ncard = 0 ∨
              (incidentEdges C' v₁).ncard + (incidentEdges C' v₂).ncard = 2 := by
            rw [← hC_card_v]
            exact hC_deg_props.2.2 v hvu hvw
          have hHL_le2 : (incidentEdges H_L v).ncard ≤ 2 :=
            le_trans (ncard_le_ncard (incidentEdges_subset_of_le hH_LL v)
              (L.edgeSet_finite.subset fun _ h => h.1)) (hL.ncard_incidentEdges_le_two v)
          by_cases hv₁1 : (incidentEdges C' v₁).ncard = 1
          · have hv₂1 : (incidentEdges C' v₂).ncard = 1 := by
              rcases hCv02 with h0 | h2 <;> omega
            right
            rw [hHL_card_v, hv₁_iff.mpr hv₁1, hv₂_iff.mpr hv₂1]
          · have hv₂_not1 : (incidentEdges C' v₂).ncard ≠ 1 := by
              have hle1 : (incidentEdges C' v₁).ncard ≤ 2 :=
                le_trans (ncard_le_ncard (incidentEdges_subset_of_le hC'M' v₁)
                  (M'.edgeSet_finite.subset fun _ h => h.1)) (hM'.ncard_incidentEdges_le_two v₁)
              rcases hCv02 with h0 | h2 <;> omega
            have h1_02 := hH'_L_deg02 v₁ (mt (h_mem_sUnion_S v₁).mp hv₁1)
            have h2_02 := hH'_L_deg02 v₂ (mt (h_mem_sUnion_S v₂).mp hv₂_not1)
            rw [hHL_card_v] at hHL_le2 ⊢
            rcases h1_02 with h1_0 | h1_2 <;> rcases h2_02 with h2_0 | h2_2 <;> omega
      · by_cases hzv₁ : z = v₁
        · subst z
          have hv₁u : v₁ ≠ u := fun h => hv₁_notG (hL.1.vertexSet_subset (h ▸ huL.1))
          have hv₁w : v₁ ≠ w := fun h => hv₁_notG (hL.1.vertexSet_subset (h ▸ hwL.1))
          refine ⟨fun h => (h.elim hv₁u hv₁w).elim, fun _ _ => Or.inl ?_⟩
          have hv₁_notHL : v₁ ∉ H_L.vertexSet :=
            fun h => hv₁_notG (hL.1.vertexSet_subset (hH_LL.vertexSet_subset h))
          rw [incidentEdges_eq_empty_of_notMem hv₁_notHL, ncard_empty]
        · by_cases hzv₂ : z = v₂
          · subst z
            have hv₂u : v₂ ≠ u := fun h => hv₂_notG (hL.1.vertexSet_subset (h ▸ huL.1))
            have hv₂w : v₂ ≠ w := fun h => hv₂_notG (hL.1.vertexSet_subset (h ▸ hwL.1))
            refine ⟨fun h => (h.elim hv₂u hv₂w).elim, fun _ _ => Or.inl ?_⟩
            have hv₂_notHL : v₂ ∉ H_L.vertexSet :=
              fun h => hv₂_notG (hL.1.vertexSet_subset (hH_LL.vertexSet_subset h))
            rw [incidentEdges_eq_empty_of_notMem hv₂_notHL, ncard_empty]
          · rw [hHL_other z hzv hzv₁ hzv₂]
            have hz_iff : (incidentEdges H'_L z).ncard = 1 ↔ (incidentEdges C z).ncard = 1 := by
              rw [hH'_L_deg1 z, h_mem_sUnion_S z, hC_other z hzv hzv₁ hzv₂]
            constructor
            · intro hz_uw
              rw [hz_iff]
              rcases hz_uw with rfl | rfl
              · exact hC_deg_props.1
              · exact hC_deg_props.2.1
            · intro hzu hzw
              apply hH'_L_deg02 z
              rw [h_mem_sUnion_S z, ← hC_other z hzv hzv₁ hzv₂]
              rcases hC_deg_props.2.2 z hzu hzw with h0 | h2 <;> omega
    exact same_component_of_deg_one_two_subgraph hL hH_LL huL.1 hwL.1 huw
      ((hHL_deg u).1 (Or.inl rfl))
      (fun z _ hz1 => by
        by_contra! hne
        rcases (hHL_deg z).2 hne.1 hne.2 with h0 | h2 <;> omega)

/-- Complete proof of Graph Minors XXI, `(2.4)` (page 3 of the preprint):
if `G'` is obtained from `G` by splitting a vertex (`IsVertexSplit G G' v v₁ v₂ δ₁ δ₂`)
and `L` is a vital `p`-linkage in `G`, then `splitSpanningSubgraph G' L` is a vital `(p + 2)`-linkage
in `G'`. -/
theorem isVitalPLinkage_splitSpanningSubgraph {G G' L : Hypergraph α β}
    {v v₁ v₂ : α} {δ₁ δ₂ : Set β} {p : ℕ}
    (hs : IsVertexSplit G G' v v₁ v₂ δ₁ δ₂) (hL : IsVitalPLinkage G L p) :
    IsVitalPLinkage G' (splitSpanningSubgraph G' L) (p + 2) := by
  let L' := splitSpanningSubgraph G' L
  have hL'_link : IsLinkage G' L' := isLinkage_splitSpanningSubgraph hs hL.1.1
  refine ⟨⟨hL'_link, rfl, ?_⟩, ⟨hL'_link, terminals_splitSpanningSubgraph_ncard_le hs hL⟩⟩
  intro M' hM' hpat'
  let M := unsplitSubgraph G L v M'
  obtain ⟨hE_M, _, _, _, _, _, hM_link⟩ :=
    unsplitSubgraph_degree_and_terminals hs hL.1.1 hL.1.2.1 hM' hpat'
  have hM_pat : linkagePattern M = linkagePattern L :=
    unsplitSubgraph_linkagePattern_eq hs hL.1.1 hL.1.2.1 hM' hpat'
  have hML : M = L := hL.1.2.2 M hM_link hM_pat
  have hE_L' : L.edgeSet = L'.edgeSet := by
    simp only [L', splitSpanningSubgraph, hs.edgeSet_eq,
      inter_eq_self_of_subset_right hL.1.1.1.edgeSet_subset]
  have hE_eq : M'.edgeSet = L'.edgeSet := by
    change M.edgeSet = M'.edgeSet at hE_M
    rw [← hE_M, hML, hE_L']
  have hterm' : terminals M' = terminals L' :=
    terminals_eq_of_linkagePattern_eq hM' hL'_link hpat'
  have hV_eq : M'.vertexSet = L'.vertexSet := by
    apply Subset.antisymm hM'.1.vertexSet_subset
    intro x hxL'
    by_cases hx_term : x ∈ terminals L'
    · exact (hterm' ▸ hx_term).1
    · have hx2 : (incidentEdges L' x).ncard = 2 :=
        (hL'_link.notMem_terminals_iff hxL').mp hx_term
      have hne : (incidentEdges L' x).Nonempty :=
        nonempty_of_ncard_ne_zero (by omega)
      obtain ⟨e, heL', hincL'⟩ := hne
      have heM' : e ∈ M'.edgeSet := hE_eq.symm ▸ heL'
      have hincG' : G'.Inc e x :=
        inc_of_le (splitSpanningSubgraph_le G' L) hincL'
      have hincM' : M'.Inc e x :=
        (inc_iff_of_le hM'.1 heM').mpr hincG'
      exact M'.vertex_mem_of_inc hincM'
  exact le_antisymm
    ((le_iff_of_le hM'.1 (splitSpanningSubgraph_le G' L)).mpr ⟨hV_eq.subset, hE_eq.subset⟩)
    ((le_iff_of_le (splitSpanningSubgraph_le G' L) hM'.1).mpr ⟨hV_eq.symm.subset, hE_eq.symm.subset⟩)

end GM21
end GraphMinor
