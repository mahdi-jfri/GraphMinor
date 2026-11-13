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

/-- **Graph Minors XXI, (5.2), Statement `(*)`** (page 17 of the preprint):
"(*) *For every surface* $\Sigma$ *with* $\hat{\Sigma}$ *homeomorphic to* $\Sigma_0$ *and every
integer* $p \ge 0$, *there exists* $\theta \ge 1$ *such that every drawing* $\Gamma$ *in* $\Sigma$
*with* $|V(\Gamma) \cap bd(\Sigma)| \le p$ *and with a tangle of order* $\ge \theta$ *has no vital
linkage with all its terminals in* $bd(\Sigma)$." -/
theorem claim_5_2_star
    {S₀ : Type} [TopologicalSpace S₀] [ConnectedSpace S₀]
    (hS₀ : IsSurface S₀) (hbd₀ : bd S₀ = ∅)
    (h_simpler : ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
      IsSurface S' → bd S' = ∅ → IsSimplerThan S' S₀ →
      ∀ (p' : ℕ), ∃ θ : ℕ, 1 ≤ θ ∧
        ∀ (Γ : Surface.Drawing S') (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
          θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p') :
    ∀ (S : Type) [TopologicalSpace S] [ConnectedSpace S],
      IsSurface S → Nonempty (IsCappedSurface S S₀) →
      ∀ (p : ℕ), ∃ θ : ℕ, 1 ≤ θ ∧
        ∀ (Γ : Surface.Drawing S) (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
          (L : Hypergraph S (Set S)),
          Γ.IsProper →
          (Γ.V ∩ bd S).ncard ≤ p →
          θ ≤ θ_G →
          IsTangle Γ.toHypergraph θ_G 𝒯 →
          IsVitalLinkage Γ.toHypergraph L →
          terminals L ⊆ bd S →
          False := by
  classical
  haveI : T2Space S₀ := hS₀.2.1
  -- We prove `(*)` by strong induction on `c = (cuffs S).ncard`, and then on `p`, for any
  -- connected surface `S` with capping `cap : IsCappedSurface S Shat` and `Nonempty (Shat ≃ₜ S₀)`.
  have h_ind_c : ∀ (c : ℕ),
      ∀ (S Shat : Type) [TopologicalSpace S] [TopologicalSpace Shat] [ConnectedSpace S],
        IsSurface S → IsCappedSurface S Shat → Nonempty (Shat ≃ₜ S₀) → (cuffs S).ncard = c →
        ∀ (p : ℕ), ∃ θ : ℕ, 1 ≤ θ ∧
          ∀ (Γ : Surface.Drawing S) (θ_G : ℕ)
            (𝒯 : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
            (L : Hypergraph S (Set S)),
            Γ.IsProper →
            (Γ.V ∩ bd S).ncard ≤ p →
            θ ≤ θ_G →
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
        -- Choose `θ₄ > p` from (5.1).
        obtain ⟨θ₄, hp_lt_θ₄, h51⟩ := theorem_5_1_proof hS cap p
        have hθ₄_pos : 1 ≤ θ₄ := by omega
        -- Inductive hypothesis (1) at `p' = p + 3 * θ₄`.
        obtain ⟨θ₁, hθ₁_pos, hθ₁_prop⟩ :=
          exists_theta1_of_simpler hS₀ h_simpler (p + 3 * θ₄)
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
            rcases hsimp' with ⟨a, b, c, a', b', c', h₁, ⟨h₂⟩, h₃⟩
            exact ⟨a, b, c, a', b', c', h₁, ⟨e_hat₀.symm.trans h₂⟩, h₃⟩
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
          exact hθ₁_prop Shat' hShat' hbd_Shat' hsimp₀ (capDrawing hS' cap' Γ') θ₁
            (mapTangleInjOn cap'.emb T') le_rfl hT'_hat hL'_hat
        -- Inductive hypothesis (2) at `p' = p + 3 * θ₄`.
        have hex_θ₂_t : ∀ t : Fin c, ∃ θ_t : ℕ, 1 ≤ θ_t ∧
            ∀ (S' Shat' : Type) [TopologicalSpace S'] [TopologicalSpace Shat'],
              IsSurface S' → [ConnectedSpace S'] →
              GM19.IsCappedSurface S' Shat' →
              Nonempty (Shat' ≃ₜ Shat) →
              (cuffs S').ncard = t.1 →
              ∀ (Γ' : Surface.Drawing S'),
                Γ'.IsProper →
                (Γ'.V ∩ bd S').ncard ≤ p + 3 * θ₄ →
                ∀ (T' : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S')))
                  (L' : Hypergraph S' (Set S')),
                  IsTangle Γ'.toHypergraph θ_t T' →
                  IsVitalLinkage Γ'.toHypergraph L' →
                  ¬ (terminals L' ⊆ bd S') := by
          intro t
          by_cases h_ex : ∃ (S_t Shat_t : Type) (_ : TopologicalSpace S_t)
              (_ : TopologicalSpace Shat_t) (_ : ConnectedSpace S_t),
              IsSurface S_t ∧ Nonempty (IsCappedSurface S_t Shat_t) ∧
              Nonempty (Shat_t ≃ₜ Shat) ∧ (cuffs S_t).ncard = t.1
          · rcases h_ex with ⟨S_t, Shat_t, tS_t, tShat_t, cS_t, hsurf_t, ⟨cap_t⟩, ⟨e_hat_t⟩, hcuffs_t⟩
            letI := tS_t
            letI := tShat_t
            letI := cS_t
            obtain ⟨θ_t, hθ_t_pos, hθ_t⟩ :=
              ih_c t.1 t.2 S_t Shat_t hsurf_t cap_t ⟨e_hat_t.trans e_hat₀⟩ hcuffs_t (p + 3 * θ₄)
            refine ⟨θ_t, hθ_t_pos, ?_⟩
            intro S' Shat' _ _ hS' _ cap' ⟨e_hat'⟩ hcuffs' Γ' hprop' hbd' T' L' hT' hL' hterm'
            obtain ⟨e_S'⟩ :=
              homeo_of_capped_homeo_and_cuffs_ncard_eq hsurf_t hS' cap_t cap'
                ⟨e_hat'.trans e_hat_t.symm⟩ (hcuffs'.trans hcuffs_t.symm)
            exact no_vitalLinkage_bd_of_homeomorph hsurf_t e_S' hθ_t
              Γ' θ_t T' L' hprop' hbd' le_rfl hT' hL' hterm'
          · refine ⟨1, le_rfl, ?_⟩
            intro S' Shat' tS' tShat' hS' cS' cap' hhat' hcuffs'
            exact (h_ex ⟨S', Shat', tS', tShat', cS', hS', ⟨cap'⟩, hhat', hcuffs'⟩).elim
        choose θ₂_fn hθ₂_fn_pos hθ₂_fn_prop using hex_θ₂_t
        let θ₂ : ℕ := 1 + ∑ t : Fin c, θ₂_fn t
        have hθ₂_pos : 1 ≤ θ₂ := by dsimp only [θ₂]; omega
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
          intro S' Shat' _ _ hS' _ cap' hhat' hlt Γ' hprop' hbd' T' L' hT' hL' hterm'
          let t : Fin c := ⟨(cuffs S').ncard, hc ▸ hlt⟩
          have hle_sum : θ₂_fn t ≤ θ₂ := by
            have hmem : t ∈ (Finset.univ : Finset (Fin c)) := Finset.mem_univ t
            have hle := Finset.single_le_sum (fun i _ => Nat.zero_le (θ₂_fn i)) hmem
            dsimp only [θ₂]
            omega
          have hT'_t : IsTangle Γ'.toHypergraph (θ₂_fn t) (truncation T' (θ₂_fn t)) :=
            hT'.truncation (hθ₂_fn_pos t) hle_sum
          exact hθ₂_fn_prop t S' Shat' hS' cap' hhat' rfl Γ' hprop' hbd'
            (truncation T' (θ₂_fn t)) L' hT'_t hL' hterm'
        -- Inductive hypothesis (3) at `< p`.
        have hex_θ₃ : ∃ θ₃ : ℕ, 1 ≤ θ₃ ∧
            ∀ (S' : Type) [TopologicalSpace S'],
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
          rcases Nat.eq_zero_or_pos p with rfl | hp_pos
          · refine ⟨1, le_rfl, ?_⟩
            intro S' _ _ _ _ Γ' _ hlt
            omega
          · obtain ⟨θ₃, hθ₃_pos, hθ₃_prop⟩ := ih_p (p - 1) (by omega)
            refine ⟨θ₃, hθ₃_pos, ?_⟩
            intro S' _ hS' _ ⟨e_S⟩ Γ' hprop' hlt T' L' hT' hL' hterm'
            have hle_p1 : (Γ'.V ∩ bd S').ncard ≤ p - 1 := by omega
            exact no_vitalLinkage_bd_of_homeomorph hS e_S hθ₃_prop
              Γ' θ₃ T' L' hprop' hle_p1 le_rfl hT' hL' hterm'
        obtain ⟨θ₃, hθ₃_pos, h_ind3⟩ := hex_θ₃
        -- Set `θ = 2 * θ₄ + max θ₁ (max θ₂ θ₃)`.
        let θ : ℕ := 2 * θ₄ + max θ₁ (max θ₂ θ₃)
        have hθ_pos : 1 ≤ θ := by
          dsimp only [θ]; omega
        have hθ_θ₁ : 2 * θ₄ + θ₁ ≤ θ := by
          have : θ₁ ≤ max θ₁ (max θ₂ θ₃) := le_max_left _ _
          dsimp only [θ]; omega
        have hθ_θ₂ : 2 * θ₄ + θ₂ ≤ θ := by
          have : θ₂ ≤ max θ₁ (max θ₂ θ₃) := (le_max_left θ₂ θ₃).trans (le_max_right _ _)
          dsimp only [θ]; omega
        have hθ_θ₃ : 2 * θ₄ + θ₃ ≤ θ := by
          have : θ₃ ≤ max θ₁ (max θ₂ θ₃) := (le_max_right θ₂ θ₃).trans (le_max_right _ _)
          dsimp only [θ]; omega
        have hθ₃_le_θ : θ₃ ≤ θ := by omega
        refine ⟨θ, hθ_pos, ?_⟩
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
        let n_min := Nat.find hex_n
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
  intro S _ _ hS ⟨cap⟩ p
  exact h_ind_c (cuffs S).ncard S S₀ hS cap ⟨Homeomorph.refl S₀⟩ rfl p

/-! ## 3. Main Theorem: Graph Minors XXI, (5.2) -/

/-- Complexity-indexed outer induction for **Graph Minors XXI, (5.2)** over closed connected
surfaces `S₀` with `4 * a₀ + 2 * b₀ + c₀ ≤ k`. -/
private theorem prove_5_2_by_complexity (k : ℕ) :
    ∀ (S₀ : Type) [TopologicalSpace S₀] [ConnectedSpace S₀],
      IsSurface S₀ → bd S₀ = ∅ →
      (∃ a₀ b₀ c₀, 4 * a₀ + 2 * b₀ + c₀ ≤ k ∧ Nonempty (S₀ ≃ₜ SurfaceModel a₀ b₀ c₀)) →
      ∀ (p : ℕ), ∃ θ : ℕ, 1 ≤ θ ∧
        ∀ (Γ : Surface.Drawing S₀) (θ_G : ℕ)
          (𝒯 : Set (Hypergraph S₀ (Set S₀) × Hypergraph S₀ (Set S₀))),
          θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro S₀ _ _ hS₀ hbd₀ ⟨a₀, b₀, c₀, hk, ⟨e₀⟩⟩ p
    have h_simpler : ∀ (S' : Type) [TopologicalSpace S'] [ConnectedSpace S'],
        IsSurface S' → bd S' = ∅ → IsSimplerThan S' S₀ →
        ∀ (p' : ℕ), ∃ θ : ℕ, 1 ≤ θ ∧
          ∀ (Γ : Surface.Drawing S') (θ_G : ℕ)
            (𝒯 : Set (Hypergraph S' (Set S') × Hypergraph S' (Set S'))),
            θ ≤ θ_G → IsTangle Γ.toHypergraph θ_G 𝒯 → ¬ HasVitalPLinkage Γ.toHypergraph p' := by
      intro S' _ _ hS' hbd' ⟨a, b, c, a', b', c', ⟨e⟩, ⟨e'⟩, _, _, hlt⟩ p'
      obtain ⟨h_eq1, h_eq2, -⟩ := (modelCriterion.2 a₀ b₀ c₀ a' b' c').mp ⟨e₀.symm.trans e'⟩
      have h_lt_k : 4 * a + 2 * b + c < k := by omega
      exact ih (4 * a + 2 * b + c) h_lt_k S' hS' hbd' ⟨a, b, c, le_rfl, ⟨e⟩⟩ p'
    exact reduce_5_2_to_star hS₀ hbd₀ (claim_5_2_star hS₀ hbd₀ h_simpler) p

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
  exact prove_5_2_by_complexity (4 * a₀ + 2 * b₀ + c₀) S₀ hS₀ hbd₀
    ⟨a₀, b₀, c₀, le_rfl, ⟨e₀⟩⟩ p

/-- Proof of `GM21Theorem52Statement` (`Parallel.lean`) from `theorem_5_2_proof`. -/
theorem theorem_5_2_parallel : GM21Theorem52Statement :=
  fun _ _ _ hS hbd p => theorem_5_2_proof hS hbd p

end GM21
end GraphMinor
