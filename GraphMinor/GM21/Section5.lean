module

public import GraphMinor.GM21.Parallel
public import GraphMinor.GM21.Section2
public import GraphMinor.GM21.Section5One
public import GraphMinor.GM21.Section5Tie

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-!
# Graph Minors XXI, Section 5: Linkages in surfaces (`(5.2)`)

Formalizes `(5.2)` (`theorem_5_2`, pages 17–21 of the preprint) of
N. Robertson and P. D. Seymour, *Graph Minors. XXI. Graphs with unique linkages*,
J. Combin. Theory Ser. B 99 (2009), 583–616, joining:

- Step 1 (`GraphMinor.GM21.Section5Puncture`): puncturing `Σ₀` at no more than `p` terminals to
  reduce `(5.2)` to statement `(*)` (`exists_punctured_surface_at_terminals`, `reduce_5_2_to_star`).
- Step 2 (`GraphMinor.GM21.Section5Lift`): multi-step vertex splitting, loop deletion, lifting a
  loopless drawing across a cut along a normal line or `O`-arc, and Claims `(4)`–`(9)` and `(11)`
  (`claim_5_2_4`, `claim_5_2_5`, `claim_5_2_6`, `claim_5_2_7`, `claim_5_2_8`, `claim_5_2_9`,
  `claim_5_2_11`, `claim_5_2_11_card`).
- Step 3 (`GraphMinor.GM21.Section5Tie`): extracting the normal `O`-arcs `F₁, F₂` and normal line
  `F₀` of Claim `(10)(i)`–`(iii)` and proving Claim `(10)` (`claim_5_2_10`).
- Step 4 (`GraphMinor.GM21.Section5Enlarge`): enlarging `Σ` across a boundary vertex that is not a
  terminal in Claim `(12)` (`claim_5_2_12`).
- This file:
  - Drawing-level minimal-counterexample reduction for Claim `(4)` (`claim_5_2_4_drawing`).
  - Final contradiction (`claim_5_2_final_contradiction`).
  - Statement `(*)` of the proof of `(5.2)` (`claim_5_2_star`).
  - Main theorem `(5.2)` (`theorem_5_2`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11
  GraphMinor.GM12 GraphMinor.GM17 GraphMinor.GM19

universe u v w

/-! ## 1. Subdrawings from Subhypergraphs and Claim (4) for Minimal Counterexamples -/

/-- Every subhypergraph `H ≤ Γ.toHypergraph` of a drawing `Γ : Drawing S` is the hypergraph of the
subdrawing `Γ.span H.vertexSet H.edgeSet`, with the same vertex set and edge set, and preserving
`IsProper`. -/
theorem subdrawing_of_subhypergraph {S : Type*} [TopologicalSpace S] [T1Space S]
    (Γ : Surface.Drawing S) {H : Hypergraph S (Set S)} (hH : H ≤ Γ.toHypergraph) :
    let D := Γ.span H.vertexSet H.edgeSet
    D.V = H.vertexSet ∧
    D.E = H.edgeSet ∧
    D.toHypergraph = H ∧
    D.U ⊆ Γ.U ∧
    (Γ.IsProper → D.IsProper) := by
  let D := Γ.span H.vertexSet H.edgeSet
  have hE : D.E = H.edgeSet :=
    (Γ.span_E H.vertexSet H.edgeSet).trans (inter_eq_left.mpr hH.edgeSet_subset)
  have hV : D.V = H.vertexSet := by
    apply Subset.antisymm
    · rintro x (hx | hx)
      · exact hx.1
      · obtain ⟨e, ⟨heH, heΓ⟩, hxcl, hxV⟩ := mem_iUnion₂.mp hx
        have hinc : Γ.toHypergraph.Inc e x := ⟨heΓ, hxV, hxcl⟩
        exact H.vertex_mem_of_inc ((GM10.inc_iff_of_le hH heH).2 hinc)
    · intro x hx
      exact Or.inl ⟨hx, hH.vertexSet_subset hx⟩
  have hD_le : D.toHypergraph ≤ Γ.toHypergraph :=
    { vertexSet_subset := hV.subset.trans hH.vertexSet_subset
      edgeSet_subset := hE.subset.trans hH.edgeSet_subset
      ends_eq := fun e he => by
        ext v
        change (e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e) ↔ (e ∈ D.E ∧ v ∈ D.V ∧ v ∈ closure e)
        rw [hE, hV]
        have heH : e ∈ H.edgeSet := hE ▸ he
        have heΓ : e ∈ Γ.E := hH.edgeSet_subset heH
        refine ⟨fun ⟨_, hvΓ, hvcl⟩ => ⟨heH, ?_, hvcl⟩,
          fun ⟨_, hvH, hvcl⟩ => ⟨heΓ, hH.vertexSet_subset hvH, hvcl⟩⟩
        exact H.vertex_mem_of_inc ((GM10.inc_iff_of_le hH heH).2 ⟨heΓ, hvΓ, hvcl⟩) }
  have hH_eq : D.toHypergraph = H :=
    GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hD_le hH hV hE
  have hU_sub : D.U ⊆ Γ.U :=
    union_subset ((Γ.spanV_subset H.vertexSet H.edgeSet).trans Γ.V_subset_U)
      (iUnion₂_subset fun e he => Γ.closure_subset_U he.2)
  refine ⟨hV, hE, hH_eq, hU_sub, fun hΓ x ⟨hx_bd, hx_U⟩ => ?_⟩
  have hxV : x ∈ Γ.V := hΓ ⟨hx_bd, hU_sub hx_U⟩
  rcases hx_U with hx_spanV | hx_cl
  · exact hx_spanV
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx_cl
    exact Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe, hxV⟩)

/-- If `Γ.U` is not preconnected and `𝒯` is a tangle in `Γ.toHypergraph`, then there is a separation
`(Γ₁, Γ₂) ∈ 𝒯` of order `0` with `Γ₂.vertexSet.ncard + Γ₂.edgeSet.ncard < Γ.V.ncard + Γ.E.ncard`. -/
theorem exists_order_zero_separation_of_not_isPreconnected_U
    {S : Type*} [TopologicalSpace S] [T1Space S]
    {Γ : Surface.Drawing S} {θ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hnot : ¬ IsPreconnected Γ.U) :
    ∃ Γ₁ Γ₂ : Hypergraph S (Set S),
      (Γ₁, Γ₂) ∈ 𝒯 ∧
      separationOrder Γ₁ Γ₂ = 0 ∧
      Γ₂.vertexSet.ncard + Γ₂.edgeSet.ncard < Γ.V.ncard + Γ.E.ncard := by
  simp only [IsPreconnected, not_forall] at hnot
  rcases hnot with ⟨U₁, U₂, hU₁, hU₂, hcov, hne₁, hne₂, hdisj⟩
  have h_edge_side : ∀ e ∈ Γ.E, closure e ⊆ U₁ ∨ closure e ⊆ U₂ := by
    intro e he
    have hcl_sub : closure e ⊆ Γ.U := Γ.closure_subset_U he
    have hcl_pre : IsPreconnected (closure e) :=
      he.2.2.1.isConnected.isPreconnected.closure
    by_contra! hboth
    rcases hboth with ⟨hnot₁, hnot₂⟩
    have hne_e₁ : (closure e ∩ U₁).Nonempty := by
      rcases not_subset.mp hnot₂ with ⟨x, hxe, hx₂⟩
      exact ⟨x, hxe, (hcov (hcl_sub hxe)).resolve_right hx₂⟩
    have hne_e₂ : (closure e ∩ U₂).Nonempty := by
      rcases not_subset.mp hnot₁ with ⟨x, hxe, hx₁⟩
      exact ⟨x, hxe, (hcov (hcl_sub hxe)).resolve_left hx₁⟩
    obtain ⟨z, hze, hz₁₂⟩ := hcl_pre U₁ U₂ hU₁ hU₂ (hcl_sub.trans hcov) hne_e₁ hne_e₂
    exact hdisj ⟨z, hcl_sub hze, hz₁₂⟩
  have h_edge_not_both : ∀ e ∈ Γ.E, ¬ (closure e ⊆ U₁ ∧ closure e ⊆ U₂) := by
    intro e he ⟨h₁, h₂⟩
    obtain ⟨z, hz⟩ := he.1
    have hcl_sub : closure e ⊆ Γ.U := Γ.closure_subset_U he
    exact hdisj ⟨z, hcl_sub (subset_closure hz), h₁ (subset_closure hz), h₂ (subset_closure hz)⟩
  let V₁ : Set S := Γ.V ∩ U₁
  let E₁ : Set (Set S) := {e ∈ Γ.E | closure e ⊆ U₁}
  let V₂ : Set S := Γ.V ∩ U₂
  let E₂ : Set (Set S) := {e ∈ Γ.E | closure e ⊆ U₂}
  let D₁ := Γ.span V₁ E₁
  let D₂ := Γ.span V₂ E₂
  have hD₁_E : D₁.E = E₁ :=
    (Γ.span_E V₁ E₁).trans (inter_eq_left.mpr fun _ h => h.1)
  have hD₂_E : D₂.E = E₂ :=
    (Γ.span_E V₂ E₂).trans (inter_eq_left.mpr fun _ h => h.1)
  have hD₁_V : D₁.V = V₁ := by
    apply Subset.antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, ⟨⟨heΓ, heU₁⟩, _⟩, hxcl, hxV⟩ := mem_iUnion₂.mp hx
        exact ⟨hxV, heU₁ hxcl⟩
    · intro x hx
      exact Or.inl ⟨hx, hx.1⟩
  have hD₂_V : D₂.V = V₂ := by
    apply Subset.antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, ⟨⟨heΓ, heU₂⟩, _⟩, hxcl, hxV⟩ := mem_iUnion₂.mp hx
        exact ⟨hxV, heU₂ hxcl⟩
    · intro x hx
      exact Or.inl ⟨hx, hx.1⟩
  let H₁ := D₁.toHypergraph
  let H₂ := D₂.toHypergraph
  have hH₁_le : H₁ ≤ Γ.toHypergraph :=
    { vertexSet_subset := hD₁_V.subset.trans inter_subset_left
      edgeSet_subset := hD₁_E.subset.trans fun _ h => h.1
      ends_eq := fun e he => by
        ext v
        change (e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e) ↔ (e ∈ D₁.E ∧ v ∈ D₁.V ∧ v ∈ closure e)
        rw [hD₁_E, hD₁_V]
        have he₁ : e ∈ E₁ := hD₁_E ▸ he
        refine ⟨fun ⟨_, hvΓ, hvcl⟩ => ⟨he₁, ⟨hvΓ, he₁.2 hvcl⟩, hvcl⟩,
          fun ⟨_, ⟨hvΓ, _⟩, hvcl⟩ => ⟨he₁.1, hvΓ, hvcl⟩⟩ }
  have hH₂_le : H₂ ≤ Γ.toHypergraph :=
    { vertexSet_subset := hD₂_V.subset.trans inter_subset_left
      edgeSet_subset := hD₂_E.subset.trans fun _ h => h.1
      ends_eq := fun e he => by
        ext v
        change (e ∈ Γ.E ∧ v ∈ Γ.V ∧ v ∈ closure e) ↔ (e ∈ D₂.E ∧ v ∈ D₂.V ∧ v ∈ closure e)
        rw [hD₂_E, hD₂_V]
        have he₂ : e ∈ E₂ := hD₂_E ▸ he
        refine ⟨fun ⟨_, hvΓ, hvcl⟩ => ⟨he₂, ⟨hvΓ, he₂.2 hvcl⟩, hvcl⟩,
          fun ⟨_, ⟨hvΓ, _⟩, hvcl⟩ => ⟨he₂.1, hvΓ, hvcl⟩⟩ }
  have hV_union : V₁ ∪ V₂ = Γ.V := by
    ext v
    simp only [V₁, V₂, mem_union, mem_inter_iff]
    exact ⟨by rintro (⟨hv, _⟩ | ⟨hv, _⟩) <;> exact hv,
      fun hv => (hcov (Γ.V_subset_U hv)).elim (fun h₁ => Or.inl ⟨hv, h₁⟩) (fun h₂ => Or.inr ⟨hv, h₂⟩)⟩
  have hV_disj : Disjoint V₁ V₂ := by
    refine disjoint_left.mpr fun v ⟨hvΓ, hv₁⟩ ⟨_, hv₂⟩ => ?_
    exact hdisj ⟨v, Γ.V_subset_U hvΓ, hv₁, hv₂⟩
  have hE_union : E₁ ∪ E₂ = Γ.E := by
    ext e
    simp only [E₁, E₂, mem_union, mem_ofPred_eq]
    exact ⟨by rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he,
      fun he => (h_edge_side e he).elim (fun h₁ => Or.inl ⟨he, h₁⟩) (fun h₂ => Or.inr ⟨he, h₂⟩)⟩
  have hE_disj : Disjoint E₁ E₂ := by
    refine disjoint_left.mpr fun e ⟨heΓ, h₁⟩ ⟨_, h₂⟩ => ?_
    exact h_edge_not_both e heΓ ⟨h₁, h₂⟩
  have hsep : Γ.toHypergraph.IsSeparation H₁ H₂ := by
    rw [GM10.isSeparation_iff_of_le hH₁_le hH₂_le]
    refine ⟨?_, ?_, ?_⟩
    · change D₁.V ∪ D₂.V = Γ.V
      rw [hD₁_V, hD₂_V, hV_union]
    · change D₁.E ∪ D₂.E = Γ.E
      rw [hD₁_E, hD₂_E, hE_union]
    · change D₁.E ∩ D₂.E = ∅
      rw [hD₁_E, hD₂_E]
      exact hE_disj.inter_eq
  have hord0 : separationOrder H₁ H₂ = 0 := by
    unfold separationOrder
    change (D₁.V ∩ D₂.V).ncard = 0
    rw [hD₁_V, hD₂_V, hV_disj.inter_eq, ncard_empty]
  have hex_arc : ∀ {x : S}, x ∈ Γ.U \ Γ.V → ∃ e ∈ Γ.E, x ∈ e := fun hx =>
    ⟨pathComponentIn (Γ.U \ Γ.V) _,
      ⟨⟨_, mem_pathComponentIn_self hx⟩, pathComponentIn_subset,
        isPathConnected_pathComponentIn hx, fun D hD hc hsub =>
          subset_antisymm (hc.subset_pathComponentIn (hsub (mem_pathComponentIn_self hx)) hD) hsub⟩,
      mem_pathComponentIn_self hx⟩
  have h_pos₁ : 0 < V₁.ncard + E₁.ncard := by
    rcases hne₁ with ⟨x, hxU, hx₁⟩
    by_cases hxV : x ∈ Γ.V
    · have hne_V₁ : V₁.Nonempty := ⟨x, hxV, hx₁⟩
      have hpos : 0 < V₁.ncard := (ncard_pos (Γ.finite_V.subset inter_subset_left)).mpr hne_V₁
      omega
    · obtain ⟨e, heΓ, hxe⟩ := hex_arc ⟨hxU, hxV⟩
      have he_E₁ : e ∈ E₁ := by
        refine ⟨heΓ, (h_edge_side e heΓ).resolve_right fun h₂ => ?_⟩
        exact hdisj ⟨x, hxU, hx₁, h₂ (subset_closure hxe)⟩
      have hne_E₁ : E₁.Nonempty := ⟨e, he_E₁⟩
      have hpos : 0 < E₁.ncard := (ncard_pos (Γ.finite_edges.subset fun _ h => h.1)).mpr hne_E₁
      omega
  have h_pos₂ : 0 < V₂.ncard + E₂.ncard := by
    rcases hne₂ with ⟨x, hxU, hx₂⟩
    by_cases hxV : x ∈ Γ.V
    · have hne_V₂ : V₂.Nonempty := ⟨x, hxV, hx₂⟩
      have hpos : 0 < V₂.ncard := (ncard_pos (Γ.finite_V.subset inter_subset_left)).mpr hne_V₂
      omega
    · obtain ⟨e, heΓ, hxe⟩ := hex_arc ⟨hxU, hxV⟩
      have he_E₂ : e ∈ E₂ := by
        refine ⟨heΓ, (h_edge_side e heΓ).resolve_left fun h₁ => ?_⟩
        exact hdisj ⟨x, hxU, h₁ (subset_closure hxe), hx₂⟩
      have hne_E₂ : E₂.Nonempty := ⟨e, he_E₂⟩
      have hpos : 0 < E₂.ncard := (ncard_pos (Γ.finite_edges.subset fun _ h => h.1)).mpr hne_E₂
      omega
  have hV_sum : Γ.V.ncard = V₁.ncard + V₂.ncard := by
    rw [← hV_union]
    exact ncard_union_eq hV_disj (Γ.finite_V.subset inter_subset_left)
      (Γ.finite_V.subset inter_subset_left)
  have hE_sum : Γ.E.ncard = E₁.ncard + E₂.ncard := by
    rw [← hE_union]
    exact ncard_union_eq hE_disj (Γ.finite_edges.subset fun _ h => h.1)
      (Γ.finite_edges.subset fun _ h => h.1)
  have hord_lt : separationOrder H₁ H₂ < θ := by
    rw [hord0]
    exact h𝒯.one_le
  rcases h𝒯.axiom1 hsep hord_lt with hm | hm
  · refine ⟨H₁, H₂, hm, hord0, ?_⟩
    change D₂.V.ncard + D₂.E.ncard < Γ.V.ncard + Γ.E.ncard
    rw [hD₂_V, hD₂_E]
    omega
  · refine ⟨H₂, H₁, hm, ?_, ?_⟩
    · rw [GM10.separationOrder_comm, hord0]
    · change D₁.V.ncard + D₁.E.ncard < Γ.V.ncard + Γ.E.ncard
      rw [hD₁_V, hD₁_E]
      omega

/-- **Graph Minors XXI, (5.2), Claim (4) for a minimal counterexample drawing** (page 18 of the
preprint): If `(Γ, 𝒯, L)` is a counterexample to `(*)` in `S` minimizing `Γ.V.ncard + Γ.E.ncard`,
then `Γ` is connected (`IsPreconnected Γ.U`) and loopless
(`∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard`). -/
theorem claim_5_2_4_drawing {S : Type*} [TopologicalSpace S] [T1Space S]
    {Γ : Surface.Drawing S} {L : Hypergraph S (Set S)} {p θ : ℕ}
    {𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hΓ : Γ.IsProper)
    (hΓ_bd : (Γ.V ∩ bd S).ncard ≤ p)
    (h𝒯 : IsTangle Γ.toHypergraph θ 𝒯)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (hmin : ∀ (Γ' : Surface.Drawing S)
      (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (L' : Hypergraph S (Set S)),
      Γ'.IsProper →
      (Γ'.V ∩ bd S).ncard ≤ p →
      IsTangle Γ'.toHypergraph θ 𝒯' →
      IsVitalLinkage Γ'.toHypergraph L' →
      terminals L' ⊆ bd S →
      Γ.V.ncard + Γ.E.ncard ≤ Γ'.V.ncard + Γ'.E.ncard) :
    IsPreconnected Γ.U ∧ (∀ e ∈ Γ.E, 2 ≤ (Γ.toHypergraph.ends e).ncard) := by
  have h4 := claim_5_2_4 h𝒯 hL
  refine ⟨?_, ?_⟩
  · by_contra hnot_conn
    obtain ⟨Γ₁, Γ₂, hmem, hord0, hlt_size⟩ :=
      exists_order_zero_separation_of_not_isPreconnected_U h𝒯 hnot_conn
    obtain ⟨h𝒯₂, hL₂, hterm₂, hV₂_sub⟩ := h4.1 Γ₁ Γ₂ hmem hord0
    have hΓ₂_le : Γ₂ ≤ Γ.toHypergraph := (h𝒯.isSeparation hmem).right_le
    obtain ⟨hD₂_V, hD₂_E, hD₂_H, _, hD₂_prop⟩ := subdrawing_of_subhypergraph Γ hΓ₂_le
    let D₂ := Γ.span Γ₂.vertexSet Γ₂.edgeSet
    have hD₂_bd : (D₂.V ∩ bd S).ncard ≤ p := by
      rw [hD₂_V]
      have hsub : Γ₂.vertexSet ∩ bd S ⊆ Γ.V ∩ bd S := inter_subset_inter_left _ hV₂_sub
      exact (ncard_le_ncard hsub (Γ.finite_V.subset inter_subset_left)).trans hΓ_bd
    have hle := hmin D₂ (restrictOrderZeroTangle Γ₂ 𝒯) (L ∩ Γ₂) (hD₂_prop hΓ) hD₂_bd
      (hD₂_H.symm ▸ h𝒯₂) (hD₂_H.symm ▸ hL₂) (hterm₂.trans hL_bd)
    rw [hD₂_V, hD₂_E] at hle
    omega
  · intro e he
    by_contra! hsize
    have hsize1 : (Γ.toHypergraph.ends e).ncard ≤ 1 := by omega
    obtain ⟨h𝒯_del, hL_del, hV_del, hE_lt⟩ := h4.2 e he hsize1
    have hdel_le : Γ.toHypergraph.deleteEdges {e} ≤ Γ.toHypergraph :=
      GM10.deleteEdges_le Γ.toHypergraph {e}
    obtain ⟨hD_V, hD_E, hD_H, _, hD_prop⟩ := subdrawing_of_subhypergraph Γ hdel_le
    let D := Γ.span (Γ.toHypergraph.deleteEdges {e}).vertexSet
      (Γ.toHypergraph.deleteEdges {e}).edgeSet
    have hD_bd : (D.V ∩ bd S).ncard ≤ p := by
      rw [hD_V, hV_del]
      exact hΓ_bd
    have hle := hmin D (deleteLoopTangle Γ.toHypergraph e 𝒯 θ) L (hD_prop hΓ) hD_bd
      (hD_H.symm ▸ h𝒯_del) (hD_H.symm ▸ hL_del) hL_bd
    rw [hD_V, hD_E, hV_del] at hle
    change Γ.V.ncard + Γ.E.ncard ≤ Γ.V.ncard + (Γ.toHypergraph.deleteEdges {e}).edgeSet.ncard at hle
    change (Γ.toHypergraph.deleteEdges {e}).edgeSet.ncard < Γ.E.ncard at hE_lt
    omega

/-! ## 2. Final Contradiction and Statement `(*)` of `(5.2)` -/

/-- Final contradiction in the proof of **Graph Minors XXI, (5.2)** (page 21 of the preprint):
"But (8), (10), (11) and (12) contradict (5.1). Thus our assumption that $\theta$ does not satisfy
(*) was false, and the proof is complete." -/
theorem claim_5_2_final_contradiction {S Shat : Type}
    [TopologicalSpace S] [TopologicalSpace Shat] [T2Space Shat]
    (hS : IsSurface S) (cap : GM19.IsCappedSurface S Shat)
    {Γ : Surface.Drawing S}
    {θ₄ : ℕ}
    {T₁ : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat))}
    {d₁ : Set Shat → Set Shat → ℕ}
    {L : Hypergraph S (Set S)}
    (h51 : ∀ (Γ : Surface.Drawing S), Γ.IsProper →
      ∀ (θ₀ : ℕ), θ₄ ≤ θ₀ →
      ∀ (T : Set (Hypergraph Shat (Set Shat) × Hypergraph Shat (Set Shat)))
        (d : Set Shat → Set Shat → ℕ),
      GM14.HasTangleMetric (capDrawing hS cap Γ) θ₀ T d →
      (∀ (F : Set S) (D : Set Shat) (C : Set S),
        (PaintingOrDrawing.drawing Γ).IsNormal F → IsOArc F →
        (F ∩ Γ.V).ncard < (C ∩ Γ.V).ncard → C ∈ cuffs S →
        IsClosedDisc D → subBd D = cap.emb '' F →
        ((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
          (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈ T →
        ¬ cap.emb '' C ⊆ D) →
      (∀ (C₁ C₂ : Set S) (r₁ r₂ : Set Shat),
        C₁ ≠ C₂ → IsCuffRegion hS cap Γ C₁ r₁ → IsCuffRegion hS cap Γ C₂ r₂ →
        θ₄ ≤ d r₁ r₂) →
      ∀ (L : Hypergraph S (Set S)), IsVitalLinkage Γ.toHypergraph L →
        terminals L ≠ Γ.V ∩ bd S)
    (hΓ : Γ.IsProper)
    (h8 : GM14.HasTangleMetric (capDrawing hS cap Γ) θ₄ T₁ d₁)
    (h10 : ∀ (C₁ C₂ : Set S) (r₁ r₂ : Set Shat),
      C₁ ≠ C₂ → IsCuffRegion hS cap Γ C₁ r₁ → IsCuffRegion hS cap Γ C₂ r₂ →
      θ₄ ≤ d₁ r₁ r₂)
    (h11 : ∀ (F : Set S) (D : Set Shat) (C : Set S),
      (PaintingOrDrawing.drawing Γ).IsNormal F → IsOArc F →
      C ∈ cuffs S →
      IsClosedDisc D → subBd D = cap.emb '' F →
      ((PaintingOrDrawing.drawing (capDrawing hS cap Γ)).inter D,
        (PaintingOrDrawing.drawing (capDrawing hS cap Γ)).interOutside D) ∈ T₁ →
      cap.emb '' C ⊆ D →
      (C ∩ Γ.V).ncard ≤ (F ∩ Γ.V).ncard)
    (hL : IsVitalLinkage Γ.toHypergraph L)
    (hL_bd : terminals L ⊆ bd S)
    (h12 : Γ.V ∩ bd S ⊆ terminals L) :
    False := by
  have hterm_eq : terminals L = Γ.V ∩ bd S :=
    Subset.antisymm
      (fun v hv => ⟨hL.1.1.vertexSet_subset hv.1, hL_bd hv⟩)
      h12
  refine h51 Γ hΓ θ₄ le_rfl T₁ d₁ h8 ?_ h10 L hL hterm_eq
  intro F D C hnF hF hlt hC hD hbd hm hCD
  have hle := h11 F D C hnF hF hC hD hbd hm hCD
  omega

/-! ## 2b. Explicit bounds for `(5.2)` -/

/-- One boundary-vertex shift `p ↦ p + 3 * θ₄(k, c, p)` in the proof of Graph Minors XXI, (5.2). -/
def shift52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k c p : ℕ) : ℕ :=
  p + 3 * theorem_5_1_bound V k c p

/-- Maximum boundary-vertex count reached after at most `c` cuff-reduction steps in `(5.2)`. -/
def pTop52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k c p : ℕ) : ℕ :=
  Nat.iterate (shift52 V k c) c p

/-- Additive slack for statement `(*)` of Graph Minors XXI, (5.2). -/
def addStar52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k c p : ℕ) : ℕ :=
  2 * (c + 1) * (pTop52 V k c p + 1) * theorem_5_1_bound V k c (pTop52 V k c p)

/-- Explicit bound for statement `(*)` of Graph Minors XXI, (5.2) given a monotone bound `G_prev`
for all strictly simpler closed surfaces. -/
def starBound52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (G_prev : ℕ → ℕ) (k c p : ℕ) : ℕ :=
  addStar52 V k c p + G_prev (shift52 V k c (pTop52 V k c p))

/-- One closed-surface complexity step for Graph Minors XXI, (5.2), tracking `(p, acc)`. -/
def closedStep52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k_cap : ℕ) (st : ℕ × ℕ) : ℕ × ℕ :=
  (shift52 V k_cap st.1 (pTop52 V k_cap st.1 st.1), st.2 + addStar52 V k_cap st.1 st.1)

/-- Iterated closed-surface bound for Graph Minors XXI, (5.2) at step `m` with complexity cap `k_cap`. -/
def theorem_5_2_iter (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k_cap m p : ℕ) : ℕ :=
  (Nat.iterate (closedStep52 V k_cap) (m + 1) (p, 1)).2

/-- Explicit tangle-order bound for **Graph Minors XXI, (5.2)** over closed connected surfaces with
`4 * a + 2 * b + c ≤ k`, parameterized by an upper bound `V` on `GM07.vModel`. -/
def theorem_5_2_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k p : ℕ) : ℕ :=
  theorem_5_2_iter V k k p

private lemma shift52_mono {V : ℕ → ℕ → ℕ → ℕ → ℕ} {k₁ k₂ c₁ c₂ p₁ p₂ : ℕ}
    (hk : k₁ ≤ k₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) :
    shift52 V k₁ c₁ p₁ ≤ shift52 V k₂ c₂ p₂ := by
  dsimp only [shift52]
  have := theorem_5_1_bound_mono (V := V) hk hc hp
  omega

private lemma le_shift52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k c p : ℕ) :
    p ≤ shift52 V k c p := by
  dsimp only [shift52]; omega

private lemma shift52_strict_step {V : ℕ → ℕ → ℕ → ℕ → ℕ} {k c p₁ p₂ : ℕ}
    (hp : p₁ + 1 ≤ p₂) :
    shift52 V k c p₁ + 1 ≤ shift52 V k c p₂ := by
  dsimp only [shift52]
  have := theorem_5_1_bound_mono (V := V) (k₁ := k) (k₂ := k) (c₁ := c) (c₂ := c) le_rfl le_rfl (by omega : p₁ ≤ p₂)
  omega

private lemma iterate_shift52_mono {V : ℕ → ℕ → ℕ → ℕ → ℕ} {k₁ k₂ c₁ c₂ : ℕ}
    (hk : k₁ ≤ k₂) (hc : c₁ ≤ c₂) :
    ∀ (m : ℕ) {p₁ p₂ : ℕ}, p₁ ≤ p₂ →
      Nat.iterate (shift52 V k₁ c₁) m p₁ ≤ Nat.iterate (shift52 V k₂ c₂) m p₂ := by
  intro m
  induction m with
  | zero => intro _ _ hp; exact hp
  | succ m ih =>
    intro p₁ p₂ hp
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact shift52_mono hk hc (ih hp)

private lemma iterate_shift52_le_add {V : ℕ → ℕ → ℕ → ℕ → ℕ} (k c : ℕ) :
    ∀ (m n p : ℕ), m ≤ n →
      Nat.iterate (shift52 V k c) m p ≤ Nat.iterate (shift52 V k c) n p := by
  intro m n p hmn
  induction hmn with
  | refl => exact le_rfl
  | @step t _ ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_shift52 V k c _)

private lemma le_pTop52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k c p : ℕ) :
    p ≤ pTop52 V k c p :=
  iterate_shift52_le_add k c 0 c p (Nat.zero_le c)

private lemma pTop52_mono {V : ℕ → ℕ → ℕ → ℕ → ℕ} {k₁ k₂ c₁ c₂ p₁ p₂ : ℕ}
    (hk : k₁ ≤ k₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) :
    pTop52 V k₁ c₁ p₁ ≤ pTop52 V k₂ c₂ p₂ :=
  (iterate_shift52_mono hk hc c₁ hp).trans (iterate_shift52_le_add k₂ c₂ c₁ c₂ p₂ hc)

private lemma pTop52_strict_step {V : ℕ → ℕ → ℕ → ℕ → ℕ} (k c : ℕ) {p₁ p₂ : ℕ}
    (hp : p₁ + 1 ≤ p₂) :
    pTop52 V k c p₁ + 1 ≤ pTop52 V k c p₂ := by
  dsimp only [pTop52]
  have h : ∀ m {x y}, x + 1 ≤ y →
      Nat.iterate (shift52 V k c) m x + 1 ≤ Nat.iterate (shift52 V k c) m y := by
    intro m
    induction m with
    | zero => intro _ _ hxy; exact hxy
    | succ m ih =>
      intro x y hxy
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact shift52_strict_step (ih hxy)
  exact h c hp

private lemma pTop52_shift_le_succ (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k c p : ℕ) :
    pTop52 V k c (shift52 V k (c + 1) p) ≤ pTop52 V k (c + 1) p := by
  dsimp only [pTop52]
  rw [Function.iterate_succ_apply]
  exact iterate_shift52_mono le_rfl (Nat.le_succ c) c le_rfl

private lemma addStar52_mono {V : ℕ → ℕ → ℕ → ℕ → ℕ} {k₁ k₂ c₁ c₂ p₁ p₂ : ℕ}
    (hk : k₁ ≤ k₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) :
    addStar52 V k₁ c₁ p₁ ≤ addStar52 V k₂ c₂ p₂ := by
  dsimp only [addStar52]
  have hP := pTop52_mono (V := V) hk hc hp
  exact Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega))
    (theorem_5_1_bound_mono hk hc hP)

private lemma starBound52_mono {V : ℕ → ℕ → ℕ → ℕ → ℕ} {G_prev : ℕ → ℕ}
    (hG : Monotone G_prev) {k₁ k₂ c₁ c₂ p₁ p₂ : ℕ}
    (hk : k₁ ≤ k₂) (hc : c₁ ≤ c₂) (hp : p₁ ≤ p₂) :
    starBound52 V G_prev k₁ c₁ p₁ ≤ starBound52 V G_prev k₂ c₂ p₂ := by
  dsimp only [starBound52]
  exact Nat.add_le_add (addStar52_mono hk hc hp)
    (hG (shift52_mono hk hc (pTop52_mono hk hc hp)))

private lemma two_mul_h51_le_addStar52 (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k c p : ℕ) :
    2 * theorem_5_1_bound V k c p ≤ addStar52 V k c p := by
  dsimp only [addStar52]
  have h1 : 2 * 1 * 1 ≤ 2 * (c + 1) * (pTop52 V k c p + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left 2 (by omega)) (by omega)
  have h2 : theorem_5_1_bound V k c p ≤ theorem_5_1_bound V k c (pTop52 V k c p) :=
    theorem_5_1_bound_mono le_rfl le_rfl (le_pTop52 V k c p)
  have := Nat.mul_le_mul h1 h2
  simpa only [mul_one] using this

private lemma one_le_starBound52 {V : ℕ → ℕ → ℕ → ℕ → ℕ} {G_prev : ℕ → ℕ}
    (hG_pos : ∀ p', 1 ≤ G_prev p') (k c p : ℕ) :
    1 ≤ starBound52 V G_prev k c p := by
  dsimp only [starBound52]
  have := hG_pos (shift52 V k c (pTop52 V k c p))
  omega

private lemma starBound52_ge_branch1 {V : ℕ → ℕ → ℕ → ℕ → ℕ} {G_prev : ℕ → ℕ}
    (hG : Monotone G_prev) (k c p : ℕ) :
    2 * theorem_5_1_bound V k c p + G_prev (p + 3 * theorem_5_1_bound V k c p) ≤
      starBound52 V G_prev k c p := by
  dsimp only [starBound52]
  refine Nat.add_le_add (two_mul_h51_le_addStar52 V k c p) ?_
  exact hG (shift52_mono le_rfl le_rfl (le_pTop52 V k c p))

private lemma starBound52_ge_branch2 {V : ℕ → ℕ → ℕ → ℕ → ℕ} {G_prev : ℕ → ℕ}
    (hG : Monotone G_prev) (hG_pos : ∀ p', 1 ≤ G_prev p') (k c p : ℕ) :
    2 * theorem_5_1_bound V k c p +
        (if c = 0 then 1 else starBound52 V G_prev k (c - 1) (p + 3 * theorem_5_1_bound V k c p)) ≤
      starBound52 V G_prev k c p := by
  rcases c with _ | c'
  · simp only [↓reduceIte, starBound52]
    exact Nat.add_le_add (two_mul_h51_le_addStar52 V k 0 p) (hG_pos _)
  · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, starBound52]
    change 2 * theorem_5_1_bound V k (c' + 1) p +
        (addStar52 V k c' (shift52 V k (c' + 1) p) +
          G_prev (shift52 V k c' (pTop52 V k c' (shift52 V k (c' + 1) p)))) ≤
      addStar52 V k (c' + 1) p + G_prev (shift52 V k (c' + 1) (pTop52 V k (c' + 1) p))
    have hP : pTop52 V k c' (shift52 V k (c' + 1) p) ≤ pTop52 V k (c' + 1) p :=
      pTop52_shift_le_succ V k c' p
    have hG_le : G_prev (shift52 V k c' (pTop52 V k c' (shift52 V k (c' + 1) p))) ≤
        G_prev (shift52 V k (c' + 1) (pTop52 V k (c' + 1) p)) :=
      hG (shift52_mono le_rfl (Nat.le_succ c') hP)
    have hadd_le : 2 * theorem_5_1_bound V k (c' + 1) p + addStar52 V k c' (shift52 V k (c' + 1) p) ≤
        addStar52 V k (c' + 1) p := by
      dsimp only [addStar52]
      set P := pTop52 V k (c' + 1) p
      set H := theorem_5_1_bound V k (c' + 1) P
      have h1 : 2 * theorem_5_1_bound V k (c' + 1) p ≤ 2 * 1 * (P + 1) * H := by
        have ha : 2 * 1 * 1 ≤ 2 * 1 * (P + 1) := by omega
        have hb : theorem_5_1_bound V k (c' + 1) p ≤ H :=
          theorem_5_1_bound_mono le_rfl le_rfl (le_pTop52 V k (c' + 1) p)
        simpa only [mul_one] using Nat.mul_le_mul ha hb
      have h2 : 2 * (c' + 1) * (pTop52 V k c' (shift52 V k (c' + 1) p) + 1) *
            theorem_5_1_bound V k c' (pTop52 V k c' (shift52 V k (c' + 1) p)) ≤
          2 * (c' + 1) * (P + 1) * H :=
        Nat.mul_le_mul
          (Nat.mul_le_mul_left _ (by omega))
          (theorem_5_1_bound_mono le_rfl (Nat.le_succ c') hP)
      have hsum : 2 * 1 * (P + 1) * H + 2 * (c' + 1) * (P + 1) * H =
          2 * (c' + 1 + 1) * (P + 1) * H := by ring
      omega
    omega

private lemma starBound52_ge_branch3 {V : ℕ → ℕ → ℕ → ℕ → ℕ} {G_prev : ℕ → ℕ}
    (hG : Monotone G_prev) (hG_pos : ∀ p', 1 ≤ G_prev p') (k c p : ℕ) :
    2 * theorem_5_1_bound V k c p +
        (if p = 0 then 1 else starBound52 V G_prev k c (p - 1)) ≤
      starBound52 V G_prev k c p := by
  rcases p with _ | p'
  · simp only [↓reduceIte, starBound52]
    exact Nat.add_le_add (two_mul_h51_le_addStar52 V k c 0) (hG_pos _)
  · simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, starBound52]
    have hP : pTop52 V k c p' + 1 ≤ pTop52 V k c (p' + 1) :=
      pTop52_strict_step k c le_rfl
    have hG_le : G_prev (shift52 V k c (pTop52 V k c p')) ≤
        G_prev (shift52 V k c (pTop52 V k c (p' + 1))) :=
      hG (shift52_mono le_rfl le_rfl (by omega))
    have hadd_le : 2 * theorem_5_1_bound V k c (p' + 1) + addStar52 V k c p' ≤
        addStar52 V k c (p' + 1) := by
      dsimp only [addStar52]
      set P' := pTop52 V k c p'
      set P := pTop52 V k c (p' + 1)
      set H := theorem_5_1_bound V k c P
      have h1 : 2 * theorem_5_1_bound V k c (p' + 1) ≤ 2 * (c + 1) * 1 * H := by
        have ha : 2 * 1 * 1 ≤ 2 * (c + 1) * 1 := by omega
        have hb : theorem_5_1_bound V k c (p' + 1) ≤ H :=
          theorem_5_1_bound_mono le_rfl le_rfl (le_pTop52 V k c (p' + 1))
        simpa only [mul_one] using Nat.mul_le_mul ha hb
      have h2 : 2 * (c + 1) * (P' + 1) * theorem_5_1_bound V k c P' ≤ 2 * (c + 1) * (P' + 1) * H :=
        Nat.mul_le_mul_left _ (theorem_5_1_bound_mono le_rfl le_rfl (by omega))
      have h3 : 2 * (c + 1) * (P' + 2) * H ≤ 2 * (c + 1) * (P + 1) * H :=
        Nat.mul_le_mul_right H (Nat.mul_le_mul_left _ (by omega))
      have hsum : 2 * (c + 1) * 1 * H + 2 * (c + 1) * (P' + 1) * H = 2 * (c + 1) * (P' + 2) * H := by
        ring
      omega
    omega

private lemma iterate_closedStep52_snd_add (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k_cap : ℕ) :
    ∀ (n p a b : ℕ),
      (Nat.iterate (closedStep52 V k_cap) n (p, a + b)).2 =
        a + (Nat.iterate (closedStep52 V k_cap) n (p, b)).2 := by
  intro n
  induction n with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro p a b
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    dsimp only [closedStep52]
    rw [Nat.add_assoc, ih]

private lemma theorem_5_2_iter_zero (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k_cap p : ℕ) :
    theorem_5_2_iter V k_cap 0 p = starBound52 V (fun _ => 1) k_cap p p := by
  change 1 + addStar52 V k_cap p p = addStar52 V k_cap p p + 1
  omega

private lemma theorem_5_2_iter_succ (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k_cap m p : ℕ) :
    theorem_5_2_iter V k_cap (m + 1) p =
      starBound52 V (theorem_5_2_iter V k_cap m) k_cap p p := by
  dsimp only [theorem_5_2_iter, starBound52]
  rw [Function.iterate_succ_apply]
  dsimp only [closedStep52]
  rw [Nat.add_comm 1 (addStar52 V k_cap p p), iterate_closedStep52_snd_add]

private lemma one_le_theorem_5_2_iter (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k_cap : ℕ) :
    ∀ m p, 1 ≤ theorem_5_2_iter V k_cap m p := by
  intro m
  induction m with
  | zero => intro p; rw [theorem_5_2_iter_zero]; exact one_le_starBound52 (fun _ => le_rfl) _ _ _
  | succ m ih => intro p; rw [theorem_5_2_iter_succ]; exact one_le_starBound52 ih _ _ _

private lemma theorem_5_2_iter_mono_p (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k_cap : ℕ) :
    ∀ m, Monotone (theorem_5_2_iter V k_cap m) := by
  intro m
  induction m with
  | zero =>
    intro p₁ p₂ hp
    rw [theorem_5_2_iter_zero, theorem_5_2_iter_zero]
    exact starBound52_mono (fun _ _ _ => le_rfl) le_rfl hp hp
  | succ m ih =>
    intro p₁ p₂ hp
    rw [theorem_5_2_iter_succ, theorem_5_2_iter_succ]
    exact starBound52_mono ih le_rfl hp hp

lemma one_le_theorem_5_2_bound (V : ℕ → ℕ → ℕ → ℕ → ℕ) (k p : ℕ) :
    1 ≤ theorem_5_2_bound V k p :=
  one_le_theorem_5_2_iter V k k p

/-- Explicit version of **Graph Minors XXI, (5.2), Statement `(*)`** (page 17 of the preprint) with
bound `starBound52 V G_prev k c p`. -/
theorem claim_5_2_star_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀]
    (hS₀ : IsSurface S₀) (hbd₀ : bd S₀ = ∅)
    {k : ℕ} (hk : ∃ a₀ b₀, 4 * a₀ + 2 * b₀ ≤ k ∧ Nonempty (S₀ ≃ₜ SurfaceModel a₀ b₀ 0))
    (G_prev : ℕ → ℕ) (hG_mono : Monotone G_prev) (hG_pos : ∀ p', 1 ≤ G_prev p')
    (h_simpler : ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
      IsSurface S' → bd S' = ∅ → IsSimplerThan S' S₀ →
      ∀ (p' : ℕ) (Γ : Surface.Drawing S') (θ_G : ℕ)
        (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
        G_prev p' ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p') :
    ∀ (c : ℕ) (S : Type) [TopologicalSpace S] [ConnectedSpace S],
      IsSurface S → Nonempty (IsCappedSurface S S₀) → (cuffs S).ncard = c →
      ∀ (p : ℕ) (Γ : Surface.Drawing S) (θ_G : ℕ)
        (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (L : Hypergraph S (Set S)),
        Γ.IsProper →
        (Γ.V ∩ bd S).ncard ≤ p →
        starBound52 V G_prev k c p ≤ θ_G →
        IsTangle Γ.toHypergraph θ_G 𝒯 →
        IsVitalLinkage Γ.toHypergraph L →
        terminals L ⊆ bd S →
        False := by
  classical
  haveI : T2Space S₀ := hS₀.2.1
  rcases hk with ⟨a₀, b₀, hab₀, ⟨e₀⟩⟩
  have h_ind_c : ∀ (c : ℕ),
      ∀ (S Shat : Type) [TopologicalSpace S] [TopologicalSpace Shat] [ConnectedSpace S],
        IsSurface S → IsCappedSurface S Shat → Nonempty (Shat ≃ₜ S₀) → (cuffs S).ncard = c →
        ∀ (p : ℕ) (Γ : Surface.Drawing S) (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (L : Hypergraph S (Set S)),
          Γ.IsProper →
          (Γ.V ∩ bd S).ncard ≤ p →
          starBound52 V G_prev k c p ≤ θ_G →
          IsTangle Γ.toHypergraph θ_G 𝒯 →
          IsVitalLinkage Γ.toHypergraph L →
          terminals L ⊆ bd S →
          False := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih_c =>
      intro S Shat tS tShat cS hS cap hhat₀ hc p
      induction p using Nat.strong_induction_on with
      | h p ih_p =>
        letI := tS
        letI := tShat
        letI := cS
        haveI : T2Space S := hS.2.1
        haveI : T2Space Shat := cap.isSurface.2.1
        rcases hhat₀ with ⟨e_hat₀⟩
        -- Choose `θ₄ > p` explicitly from (5.1).
        set θ₄ := theorem_5_1_bound V k c p
        have hp_lt_θ₄ : p < θ₄ := lt_theorem_5_1_bound V k c p
        have h51 := theorem_5_1_explicit V hV hS cap
          ⟨a₀, b₀, hab₀, ⟨e_hat₀.trans e₀⟩⟩ hc.le p
        have hθ₄_pos : 1 ≤ θ₄ := by omega
        -- Inductive hypothesis (1) at `p' = p + 3 * θ₄`.
        set θ₁ := G_prev (p + 3 * θ₄)
        have hθ₁_pos : 1 ≤ θ₁ := hG_pos (p + 3 * θ₄)
        have h_ind1 : ∀ (Shat' : Type) [TopologicalSpace Shat'],
            IsSurface Shat' → bd Shat' = ∅ → [ConnectedSpace Shat'] →
            IsSimplerThan Shat' Shat →
            ∀ (S' : Type) [TopologicalSpace S'],
              IsSurface S' → [ConnectedSpace S'] →
              GM19.IsCappedSurface S' Shat' →
              ∀ (Γ' : Surface.Drawing S')
                (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
                IsTangle Γ'.toHypergraph θ₁ T' →
                ¬ HasVitalPLinkage Γ'.toHypergraph (p + 3 * θ₄) := by
          intro Shat' tShat' hShat' hbd_Shat' cShat' hsimp' S' tS' hS' cS' cap' Γ' T' hT' hL'
          letI := tShat'
          letI := cShat'
          letI := tS'
          letI := cS'
          haveI : CompactSpace S' := hS'.1
          haveI : T2Space Shat' := hShat'.2.1
          have hsimp₀ : IsSimplerThan Shat' S₀ := by
            rcases hsimp' with ⟨a, b, c', a', b', c'', h₁, ⟨h₂⟩, h₃⟩
            exact ⟨a, b, c', a', b', c'', h₁, ⟨e_hat₀.symm.trans h₂⟩, h₃⟩
          have hT'_hat : IsTangle (capDrawing hS' cap' Γ').toHypergraph θ₁
              (mapTangleInjOn cap'.emb T') :=
            isTangle_mapDrawingInjOn Γ' cap'.emb
              cap'.isEmbedding.continuous.continuousOn cap'.isEmbedding.injective.injOn hT'
          have h_toH : (capDrawing hS' cap' Γ').toHypergraph =
              mapHypergraph cap'.emb (image cap'.emb) Γ'.toHypergraph :=
            toHypergraph_mapDrawingInjOn Γ' cap'.emb
              cap'.isEmbedding.continuous.continuousOn cap'.isEmbedding.injective.injOn
          have hinj_V : InjOn cap'.emb Γ'.V := cap'.isEmbedding.injective.injOn
          have hinj_E : InjOn (image cap'.emb) Γ'.E :=
            (Set.image_injective.mpr cap'.isEmbedding.injective).injOn
          rcases hL' with ⟨L', hL'_vital, _, hL'_card⟩
          have hL'_p : IsVitalPLinkage Γ'.toHypergraph L' (p + 3 * θ₄) :=
            ⟨hL'_vital, hL'_vital.1, hL'_card⟩
          have hL'_hat : HasVitalPLinkage (capDrawing hS' cap' Γ').toHypergraph (p + 3 * θ₄) := by
            rw [h_toH]
            exact ⟨mapHypergraph cap'.emb (image cap'.emb) L',
              (isVitalPLinkage_mapHypergraph hL'_vital.1.1 hinj_V hinj_E).mpr hL'_p⟩
          exact h_simpler Shat' hShat' hbd_Shat' hsimp₀ (p + 3 * θ₄) (capDrawing hS' cap' Γ') θ₁
            (mapTangleInjOn cap'.emb T') le_rfl hT'_hat hL'_hat
        -- Inductive hypothesis (2) at `p' = p + 3 * θ₄` for fewer cuffs.
        set θ₂ : ℕ := if c = 0 then 1 else starBound52 V G_prev k (c - 1) (p + 3 * θ₄)
        have hθ₂_pos : 1 ≤ θ₂ := by
          dsimp only [θ₂]
          split_ifs
          · exact le_rfl
          · exact one_le_starBound52 hG_pos _ _ _
        have h_ind2 : ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
            IsSurface S' → [ConnectedSpace S'] →
            GM19.IsCappedSurface S' Shat' →
            Nonempty (Shat' ≃ₜ Shat) →
            (cuffs S').ncard < (cuffs S).ncard →
            ∀ (Γ' : Surface.Drawing S'),
              Γ'.IsProper →
              (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
              ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
                (L' : Hypergraph S' (Set S')),
                IsTangle Γ'.toHypergraph θ₂ T' →
                IsVitalLinkage Γ'.toHypergraph L' →
                ¬ (terminals L' ⊆ bd S') := by
          intro S' Shat' _ _ hS' _ cap' ⟨e_hat'⟩ hlt Γ' hprop' hbd' T' L' hT' hL' hterm'
          have hc_ne : c ≠ 0 := by omega
          have hle_θ₂ : starBound52 V G_prev k (cuffs S').ncard (p + 3 * θ₄) ≤ θ₂ := by
            simp only [θ₂, hc_ne, ↓reduceIte]
            exact starBound52_mono hG_mono le_rfl (by omega) le_rfl
          exact ih_c (cuffs S').ncard (by omega) S' Shat' hS' cap' ⟨e_hat'.trans e_hat₀⟩ rfl
            (p + 3 * θ₄) Γ' θ₂ T' L' hprop' hbd' hle_θ₂ hT' hL' hterm'
        -- Inductive hypothesis (3) at `< p`.
        set θ₃ : ℕ := if p = 0 then 1 else starBound52 V G_prev k c (p - 1)
        have hθ₃_pos : 1 ≤ θ₃ := by
          dsimp only [θ₃]
          split_ifs
          · exact le_rfl
          · exact one_le_starBound52 hG_pos _ _ _
        have h_ind3 : ∀ (S' : Type) [TopologicalSpace S'],
            IsSurface S' → [ConnectedSpace S'] →
            Nonempty (S' ≃ₜ S) →
            ∀ (Γ' : Surface.Drawing S'),
              Γ'.IsProper →
              (Γ'.V ∩ bd S').ncard < p →
              ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
                (L' : Hypergraph S' (Set S')),
                IsTangle Γ'.toHypergraph θ₃ T' →
                IsVitalLinkage Γ'.toHypergraph L' →
                ¬ (terminals L' ⊆ bd S') := by
          intro S' _ hS' _ ⟨e_S⟩ Γ' hprop' hlt T' L' hT' hL' hterm'
          have hp_ne : p ≠ 0 := by omega
          have hθ₃_eq : θ₃ = starBound52 V G_prev k c (p - 1) := by simp [θ₃, hp_ne]
          have hle_p1 : (Γ'.V ∩ bd S').ncard ≤ p - 1 := by omega
          exact no_vitalLinkage_bd_of_homeomorph hS e_S
            (fun Γ'' θ_G'' 𝒯'' L'' hprop'' hbd'' hle'' h𝒯'' hL'' hterm'' =>
              ih_p (p - 1) (by omega) Γ'' θ_G'' 𝒯'' L'' hprop'' hbd'' (hθ₃_eq ▸ hle'') h𝒯'' hL'' hterm'')
            Γ' θ₃ T' L' hprop' hle_p1 le_rfl hT' hL' hterm'
        -- Check `θ = starBound52 V G_prev k c p` dominates all three branches.
        set θ : ℕ := starBound52 V G_prev k c p
        have hθ_pos : 1 ≤ θ := one_le_starBound52 hG_pos k c p
        have hθ_θ₁ : 2 * θ₄ + θ₁ ≤ θ := starBound52_ge_branch1 hG_mono k c p
        have hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ := starBound52_ge_branch2 hG_mono hG_pos k c p
        have hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ := starBound52_ge_branch3 hG_mono hG_pos k c p
        have hθ₃_le_θ : θ₃ ≤ θ := by omega
        intro Γ₀ θ_G 𝒯₀ L₀ hΓ₀_prop hΓ₀_bd hθ_G h𝒯₀ hL₀ hL₀_bd
        -- Pass to a minimal counterexample `(Γ, 𝒯, L)` minimizing `Γ.V.ncard + Γ.E.ncard`.
        have hex_n : ∃ n : ℕ, ∃ (Γ : Surface.Drawing S)
            (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (L : Hypergraph S (Set S)),
            Γ.IsProper ∧
            (Γ.V ∩ bd S).ncard ≤ p ∧
            IsTangle Γ.toHypergraph θ 𝒯 ∧
            IsVitalLinkage Γ.toHypergraph L ∧
            terminals L ⊆ bd S ∧
            Γ.V.ncard + Γ.E.ncard = n :=
          ⟨Γ₀.V.ncard + Γ₀.E.ncard, Γ₀, truncation 𝒯₀ θ, L₀,
            hΓ₀_prop, hΓ₀_bd, h𝒯₀.truncation hθ_pos hθ_G, hL₀, hL₀_bd, rfl⟩
        obtain ⟨Γ, 𝒯, L, hΓ_prop, hΓ_bd, h𝒯, hL, hL_bd, hn_eq⟩ := Nat.find_spec hex_n
        have hmin : ∀ (Γ' : Surface.Drawing S)
            (𝒯' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (L' : Hypergraph S (Set S)),
            Γ'.IsProper →
            (Γ'.V ∩ bd S).ncard ≤ p →
            IsTangle Γ'.toHypergraph θ 𝒯' →
            IsVitalLinkage Γ'.toHypergraph L' →
            terminals L' ⊆ bd S →
            Γ.V.ncard + Γ.E.ncard ≤ Γ'.V.ncard + Γ'.E.ncard := by
          intro Γ' 𝒯' L' hprop' hbd' h𝒯' hL' hterm'
          rw [hn_eq]
          exact Nat.find_min' hex_n ⟨Γ', 𝒯', L', hprop', hbd', h𝒯', hL', hterm', rfl⟩
        -- Claim (4): `Γ` is connected and loopless.
        obtain ⟨hΓ_conn, hΓ_loopless⟩ :=
          claim_5_2_4_drawing hΓ_prop hΓ_bd h𝒯 hL hL_bd hmin
        have hL_p : IsVitalPLinkage Γ.toHypergraph L p := by
          refine ⟨hL, hL.1, ?_⟩
          have hsub : terminals L ⊆ Γ.V ∩ bd S :=
            fun v hv => ⟨hL.1.1.vertexSet_subset hv.1, hL_bd hv⟩
          exact (ncard_le_ncard hsub (Γ.finite_V.subset inter_subset_left)).trans hΓ_bd
        -- Claim (8): `T₁` has a tangle metric `d₁` in `capDrawing hS cap Γ`.
        obtain ⟨d₁, h8⟩ :=
          claim_5_2_8 hS cap hΓ_conn hΓ_loopless h𝒯 hL_p hθ₄_pos hθ_θ₁ hθ₁_pos h_ind1
        -- Claim (10): `d₁ r₁ r₂ ≥ θ₄` for distinct cuffs `C₁ ≠ C₂`.
        have h10 :=
          claim_5_2_10 hS cap hΓ_prop hΓ_loopless hΓ_bd h𝒯 hL hL_bd
            hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos hθ₄_pos h_ind2 h_ind3 h8
        -- Claim (11): `|C ∩ V(Γ)| ≤ |F ∩ V(Γ)|` when `ins(F)` includes a unique cuff `C`.
        have h11 :=
          claim_5_2_11 hS cap hΓ_bd h𝒯 hL hL_bd hθ_θ₂ hθ₂_pos hθ_θ₃ hθ₃_pos
            (fun S' _ hS' cS' cap' hlt Γ' T' L' hprop' hbd' hT' hL' => by
              letI := cS'
              exact h_ind2 S' Shat hS' cap' ⟨Homeomorph.refl Shat⟩ hlt Γ' hprop' hbd' T' L' hT' hL')
            (fun S' _ hS' cS' hhomeo Γ' T' L' hprop' hbd' hT' hL' => by
              letI := cS'
              exact h_ind3 S' hS' hhomeo Γ' hprop' hbd' T' L' hT' hL')
        -- Claim (12): `Γ.V ∩ bd S ⊆ terminals L`.
        have h12 : Γ.V ∩ bd S ⊆ terminals L :=
          claim_5_2_12 hS cap hΓ_prop hΓ_bd hθ₃_pos hθ₃_le_θ h𝒯 hL hL_bd
            (fun Γ' hprop' hbd' T' L' hT' hL' =>
              h_ind3 S hS ⟨Homeomorph.refl S⟩ Γ' hprop' hbd' T' L' hT' hL')
        -- Moreover, `(Γ.V ∩ bd S).ncard = p` by inductive hypothesis (3) applied to `Γ` itself.
        have hΓ_bd_eq : (Γ.V ∩ bd S).ncard = p := by
          rcases lt_or_eq_of_le hΓ_bd with hlt | heq
          · exfalso
            exact h_ind3 S hS ⟨Homeomorph.refl S⟩ Γ hΓ_prop hlt
              (truncation 𝒯 θ₃) L (h𝒯.truncation hθ₃_pos hθ₃_le_θ) hL hL_bd
          · exact heq
        -- Final contradiction with (5.1).
        have hterm_eq : terminals L = Γ.V ∩ bd S :=
          Subset.antisymm
            (fun v hv => ⟨hL.1.1.vertexSet_subset hv.1, hL_bd hv⟩)
            h12
        refine h51 Γ hΓ_prop hΓ_bd_eq θ₄ le_rfl
          (mapTangle cap.emb (image cap.emb) (truncation 𝒯 θ₄)) d₁ h8 ?_ h10 L hL hterm_eq
        intro F D C hnF hF hlt hC hD hbd hm hCD
        have hle := h11 F D C hnF hF hC hD hbd hm hCD
        omega
  intro c S _ _ hS ⟨cap⟩ hc
  exact h_ind_c c S S₀ hS cap ⟨Homeomorph.refl S₀⟩ hc

/-! ## 3. Main Theorem: Graph Minors XXI, (5.2) -/

/-- Complexity-indexed outer induction for **Graph Minors XXI, (5.2)** with explicit bound
`theorem_5_2_iter V k_cap k p`. -/
private theorem prove_5_2_by_complexity_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    (k_cap : ℕ) :
    ∀ (k : ℕ), k ≤ k_cap →
      ∀ (S₀ : Type) [TopologicalSpace S₀] [ConnectedSpace S₀],
        IsSurface S₀ → bd S₀ = ∅ →
        (∃ a₀ b₀ c₀, 4 * a₀ + 2 * b₀ + c₀ ≤ k ∧ Nonempty (S₀ ≃ₜ SurfaceModel a₀ b₀ c₀)) →
        ∀ (p : ℕ) (Γ : Surface.Drawing S₀) (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S₀ (Set S₀) × Hypergraph S₀ (Set S₀))),
          theorem_5_2_iter V k_cap k p ≤ θ_G →
          IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p := by
  intro k
  induction k with
  | zero =>
    intro hk_le S₀ _ _ hS₀ hbd₀ ⟨a₀, b₀, c₀, hk, ⟨e₀⟩⟩ p Γ θ_G 𝒯 hθ_G h𝒯 hL
    haveI : T2Space S₀ := hS₀.2.1
    have hcl₀ : IsClosedSurface S₀ := isClosedSurface_of_bd_eq_empty hS₀ hbd₀
    obtain ⟨a₁, b₁, ⟨e₁⟩⟩ := GM12.exists_closed_surface_model hcl₀
    obtain ⟨hc₀, heuler, _⟩ := (modelCriterion.2 a₁ b₁ 0 a₀ b₀ c₀).mp ⟨e₁.symm.trans e₀⟩
    have hab₁ : 4 * a₁ + 2 * b₁ ≤ k_cap := by omega
    have h_simpler : ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
        IsSurface S' → bd S' = ∅ → IsSimplerThan S' S₀ →
        ∀ (p' : ℕ) (Γ' : Surface.Drawing S') (θ_G' : ℕ)
          (𝒯' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          1 ≤ θ_G' → IsTangle Γ'.toHypergraph θ_G' 𝒯' → ¬ HasVitalPLinkage Γ'.toHypergraph p' := by
      intro S' _ _ _ _ ⟨a, b, c, a', b', c', _, ⟨e'⟩, _, _, hlt⟩
      obtain ⟨h_eq1, h_eq2, -⟩ := (modelCriterion.2 a₀ b₀ c₀ a' b' c').mp ⟨e₀.symm.trans e'⟩
      omega
    have hstar := claim_5_2_star_explicit V hV hS₀ hbd₀ ⟨a₁, b₁, hab₁, ⟨e₁⟩⟩
      (fun _ => 1) (fun _ _ _ => le_rfl) (fun _ => le_rfl) h_simpler
    obtain ⟨L_vit, hL_vit⟩ := hL
    obtain ⟨S, _, _, hS, hcap, hcuffs_le, Γ_W, 𝒯_W, L_W, hprop_W, hbd_W, h𝒯_W, hL_W, hterm_W⟩ :=
      exists_punctured_surface_at_terminals hS₀ hbd₀ Γ h𝒯 hL_vit
    have hle_star : starBound52 V (fun _ => 1) k_cap (cuffs S).ncard p ≤ θ_G := by
      have h1 : starBound52 V (fun _ => 1) k_cap (cuffs S).ncard p ≤
          starBound52 V (fun _ => 1) k_cap p p :=
        starBound52_mono (fun _ _ _ => le_rfl) le_rfl hcuffs_le le_rfl
      rw [← theorem_5_2_iter_zero] at h1
      exact h1.trans hθ_G
    exact hstar (cuffs S).ncard S hS hcap rfl p Γ_W θ_G 𝒯_W L_W hprop_W hbd_W hle_star h𝒯_W hL_W hterm_W
  | succ k ih =>
    intro hk_le S₀ _ _ hS₀ hbd₀ ⟨a₀, b₀, c₀, hk, ⟨e₀⟩⟩ p Γ θ_G 𝒯 hθ_G h𝒯 hL
    haveI : T2Space S₀ := hS₀.2.1
    have hcl₀ : IsClosedSurface S₀ := isClosedSurface_of_bd_eq_empty hS₀ hbd₀
    obtain ⟨a₁, b₁, ⟨e₁⟩⟩ := GM12.exists_closed_surface_model hcl₀
    obtain ⟨hc₀, heuler, _⟩ := (modelCriterion.2 a₁ b₁ 0 a₀ b₀ c₀).mp ⟨e₁.symm.trans e₀⟩
    have hab₁ : 4 * a₁ + 2 * b₁ ≤ k_cap := by omega
    have h_simpler : ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
        IsSurface S' → bd S' = ∅ → IsSimplerThan S' S₀ →
        ∀ (p' : ℕ) (Γ' : Surface.Drawing S') (θ_G' : ℕ)
          (𝒯' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          theorem_5_2_iter V k_cap k p' ≤ θ_G' →
          IsTangle Γ'.toHypergraph θ_G' 𝒯' → ¬ HasVitalPLinkage Γ'.toHypergraph p' := by
      intro S' _ _ hS' hbd' ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, _, _, hlt⟩ p' Γ' θ_G' 𝒯' hθ' h𝒯'
      obtain ⟨h_eq1, h_eq2, -⟩ := (modelCriterion.2 a₀ b₀ c₀ a' b' c').mp ⟨e₀.symm.trans e'⟩
      have h_le_k : 4 * a + 2 * b + c ≤ k := by omega
      exact ih (by omega) S' hS' hbd' ⟨a, b, c, h_le_k, ⟨e⟩⟩ p' Γ' θ_G' 𝒯' hθ' h𝒯'
    have hstar := claim_5_2_star_explicit V hV hS₀ hbd₀ ⟨a₁, b₁, hab₁, ⟨e₁⟩⟩
      (theorem_5_2_iter V k_cap k) (theorem_5_2_iter_mono_p V k_cap k)
      (one_le_theorem_5_2_iter V k_cap k) h_simpler
    obtain ⟨L_vit, hL_vit⟩ := hL
    obtain ⟨S, _, _, hS, hcap, hcuffs_le, Γ_W, 𝒯_W, L_W, hprop_W, hbd_W, h𝒯_W, hL_W, hterm_W⟩ :=
      exists_punctured_surface_at_terminals hS₀ hbd₀ Γ h𝒯 hL_vit
    have hle_star : starBound52 V (theorem_5_2_iter V k_cap k) k_cap (cuffs S).ncard p ≤ θ_G := by
      have h1 : starBound52 V (theorem_5_2_iter V k_cap k) k_cap (cuffs S).ncard p ≤
          starBound52 V (theorem_5_2_iter V k_cap k) k_cap p p :=
        starBound52_mono (theorem_5_2_iter_mono_p V k_cap k) le_rfl hcuffs_le le_rfl
      rw [← theorem_5_2_iter_succ] at h1
      exact h1.trans hθ_G
    exact hstar (cuffs S).ncard S hS hcap rfl p Γ_W θ_G 𝒯_W L_W hprop_W hbd_W hle_star h𝒯_W hL_W hterm_W

/-- Explicit version of **Graph Minors XXI, (5.2)** (page 17 of the preprint) with bound
`theorem_5_2_bound V k p`. -/
theorem theorem_5_2_explicit
    (V : ℕ → ℕ → ℕ → ℕ → ℕ) (hV : ∀ a b c k, GM07.vModel a b c k ≤ V a b c k)
    {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀]
    (hS₀ : IsSurface S₀) (hbd₀ : bd S₀ = ∅)
    {k : ℕ} (hk : ∃ a₀ b₀ c₀, 4 * a₀ + 2 * b₀ + c₀ ≤ k ∧ Nonempty (S₀ ≃ₜ SurfaceModel a₀ b₀ c₀))
    (p : ℕ) :
    ∀ (Γ : Surface.Drawing S₀) (θ_G : ℕ)
      (𝒯 : Set (Hypergraph S₀ (Set S₀) × Hypergraph S₀ (Set S₀))),
      theorem_5_2_bound V k p ≤ θ_G →
      IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p :=
  prove_5_2_by_complexity_explicit V hV k k le_rfl S₀ hS₀ hbd₀ hk p

/-- **Graph Minors XXI, (5.2)** (page 17 of the preprint):
"For every surface $\Sigma$ with $bd(\Sigma) = \emptyset$ and every integer $p \ge 0$ there exists
$\theta \ge 1$ such that every drawing in $\Sigma$ with a tangle of order $\ge \theta$ has no vital
$p$-linkage." -/
theorem theorem_5_2_proof
    {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀]
    (hS₀ : IsSurface S₀) (hbd₀ : bd S₀ = ∅) (p : ℕ) :
    ∃ θ : ℕ, 1 ≤ θ ∧
      ∀ (Γ : Surface.Drawing S₀) (θ_G : ℕ)
        (𝒯 : Set (Hypergraph S₀ (Set S₀) × Hypergraph S₀ (Set S₀))),
        θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p := by
  obtain ⟨a₀, b₀, c₀, ⟨e₀⟩⟩ := classification S₀ hS₀ inferInstance
  exact ⟨theorem_5_2_bound GM07.vModel (4 * a₀ + 2 * b₀ + c₀) p,
    one_le_theorem_5_2_bound _ _ _,
    theorem_5_2_explicit GM07.vModel (fun _ _ _ _ => le_rfl) hS₀ hbd₀ ⟨a₀, b₀, c₀, le_rfl, ⟨e₀⟩⟩ p⟩

/-- Proof of `GM21Theorem52Statement` (`Parallel.lean`) from `theorem_5_2_proof`. -/
theorem theorem_5_2_parallel : GM21Theorem52Statement :=
  fun _ _ _ hS hbd p => theorem_5_2_proof hS hbd p

end GM21
end GraphMinor
