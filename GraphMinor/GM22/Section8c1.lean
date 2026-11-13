module

public import GraphMinor.GM22.Section8a
public import GraphMinor.GM22.Section8b
import GraphMinor.GM12.Section79

/-!
# Graph Minors XXII, Section 8 (Part c1: Claims 7–11 of Theorem 8.3)

This file proves Claims (7)–(11) of the proof of Theorem (8.3) from:
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
Journal of Combinatorial Theory, Series B 102 (2012), 530–563 (pages 561–562).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Separation `(J, K₀)` and Tangle Distance Helpers for Claims (7)–(11) -/

/-- Under the hypotheses of (8.3), there exists a subgraph `K₀ ≤ R_G.G.toGraph` such that
`IsGraphSeparation R_G.G.toGraph J K₀` and `V(J) ∩ V(K₀) = (ιV '' C₀.V) ∪ W`. -/
theorem exists_separation_J_K₀_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star) :
    ∃ K₀ : Graph α β,
      IsGraphSeparation R_G.G.toGraph J K₀ ∧
      V(J) ∩ V(K₀) = (ιV '' C₀.V) ∪ W := by
  let G := R_G.G.toGraph
  let X₀ := (ιV '' C₀.V) ∪ W
  let G' := G.deleteVerts X₀
  have hVJ_eq : V(J) = W ∪ (ιV '' Γ.V) ∪
      ⋃ C ∈ {C ∈ graphComponents G' | (V(C) ∩ (ιV '' Γ.V)).Nonempty}, V(C) := by
    have h := congrArg Graph.vertexSet h83.hyp_v.2
    rwa [vertexSet_induce] at h
  have hX₀_sub_VJ : X₀ ⊆ V(J) := by
    rw [hVJ_eq]
    rintro x (hxC₀ | hxW)
    · exact Or.inl (Or.inr (image_mono h83.hyp_ii.1.1 hxC₀))
    · exact Or.inl (Or.inl hxW)
  have hVJ_sub_VG : V(J) ⊆ V(G) := h83.hyp_v.1.vertexSet_mono
  have hX₀_sub_VG : X₀ ⊆ V(G) := hX₀_sub_VJ.trans hVJ_sub_VG
  -- Any link in `G'` with one endpoint in `V(J)` has the other endpoint in `V(J)`.
  have hstep_G' : ∀ {e x y}, G'.IsLink e x y → y ∈ V(J) → x ∈ V(J) := by
    intro e x y hlk hyJ
    have hyG' : y ∈ V(G') := hlk.right_mem
    have hy_del : y ∈ V(G) \ X₀ := by
      rw [← vertexSet_deleteVerts]
      exact hyG'
    have hy_not_W : y ∉ W := fun hW => hy_del.2 (Or.inr hW)
    let C := compOf G' y
    have hC_comp : C ∈ graphComponents G' := isGraphComponent_compOf hyG'
    have hyC : y ∈ V(C) := self_mem_reachSet hyG'
    have hxC : x ∈ V(C) := (hC_comp.mem_iff_of_isLink hlk).mpr hyC
    have hy_cases : y ∈ (ιV '' Γ.V) ∨
        ∃ C' ∈ graphComponents G', (V(C') ∩ (ιV '' Γ.V)).Nonempty ∧ y ∈ V(C') := by
      have hyJ' := hVJ_eq ▸ hyJ
      rcases hyJ' with (hyW | hyΓ) | hyU
      · exact False.elim (hy_not_W hyW)
      · exact Or.inl hyΓ
      · obtain ⟨C', ⟨hC'_comp, hC'_ne⟩, hyC'⟩ := mem_iUnion₂.mp hyU
        exact Or.inr ⟨C', hC'_comp, hC'_ne, hyC'⟩
    have hC_ne : (V(C) ∩ (ιV '' Γ.V)).Nonempty := by
      rcases hy_cases with hyΓ | ⟨C', hC'_comp, hC'_ne, hyC'⟩
      · exact ⟨y, hyC, hyΓ⟩
      · have hCC' : C = C' := hC_comp.eq_of_mem_mem hC'_comp hyC hyC'
        exact hCC' ▸ hC'_ne
    rw [hVJ_eq]
    exact Or.inr (mem_iUnion₂.mpr ⟨C, ⟨hC_comp, hC_ne⟩, hxC⟩)
  -- Every edge `e ∈ E(G) \ E(J)` has both endpoints in `X₀ ∪ (V(G) \ V(J))`.
  have hlink_not_EJ : ∀ {e x y}, G.IsLink e x y → e ∉ E(J) →
      x ∈ X₀ ∪ (V(G) \ V(J)) := by
    intro e x y hlk he_not
    by_cases hxJ : x ∈ V(J)
    · left
      by_contra hx_not_X₀
      have hy_not_VJ : y ∉ V(J) := by
        intro hyJ
        have hlk_J : J.IsLink e x y := by
          rw [h83.hyp_v.2]
          have hxJ' := hVJ_eq ▸ hxJ
          have hyJ' := hVJ_eq ▸ hyJ
          rw [induce_isLink]
          exact ⟨hlk, hxJ', hyJ'⟩
        exact he_not hlk_J.edge_mem
      have hy_not_X₀ : y ∉ X₀ := fun hyX₀ => hy_not_VJ (hX₀_sub_VJ hyX₀)
      have hlk_G' : G'.IsLink e y x := by
        rw [deleteVerts_isLink]
        exact ⟨hlk.symm, hy_not_X₀, hx_not_X₀⟩
      exact hy_not_VJ (hstep_G' hlk_G' hxJ)
    · exact Or.inr ⟨hlk.left_mem, hxJ⟩
  let K₀ : Graph α β :=
    { vertexSet := X₀ ∪ (V(G) \ V(J))
      edgeSet := E(G) \ E(J)
      IsLink := fun e x y => G.IsLink e x y ∧ e ∉ E(J)
      isLink_symm := fun _ _ => ⟨fun _ _ ⟨hlk, hne⟩ => ⟨hlk.symm, hne⟩⟩
      eq_or_eq_of_isLink_of_isLink := fun _ _ _ _ _ ⟨h₁, _⟩ ⟨h₂, _⟩ => h₁.left_eq_or_eq h₂
      edge_mem_iff_exists_isLink := fun e => by
        constructor
        · rintro ⟨heG, heJ⟩
          obtain ⟨x, y, hlk⟩ := G.exists_isLink_of_mem_edgeSet heG
          exact ⟨x, y, hlk, heJ⟩
        · rintro ⟨x, y, hlk, heJ⟩
          exact ⟨hlk.edge_mem, heJ⟩
      left_mem_of_isLink := fun _ _ _ ⟨hlk, heJ⟩ => hlink_not_EJ hlk heJ }
  have hK₀_le : K₀ ≤ G :=
    ⟨union_subset hX₀_sub_VG sdiff_subset, fun _ _ _ ⟨hlk, _⟩ => hlk⟩
  refine ⟨K₀, ⟨h83.hyp_v.1, hK₀_le, ?_, ?_, disjoint_sdiff_right⟩, ?_⟩
  · ext x
    change x ∈ V(J) ∨ x ∈ X₀ ∪ (V(G) \ V(J)) ↔ x ∈ V(G)
    simp only [mem_union, mem_sdiff]
    exact ⟨fun h => h.elim (fun hx => hVJ_sub_VG hx)
      (fun h2 => h2.elim (fun hx => hX₀_sub_VG hx) And.left),
      fun hxG => by by_cases hxJ : x ∈ V(J); exact Or.inl hxJ; exact Or.inr (Or.inr ⟨hxG, hxJ⟩)⟩
  · change E(J) ∪ (E(G) \ E(J)) = E(G)
    exact union_sdiff_cancel h83.hyp_v.1.edgeSet_mono
  · ext x
    change x ∈ V(J) ∧ (x ∈ X₀ ∨ x ∈ V(G) ∧ x ∉ V(J)) ↔ x ∈ X₀
    constructor
    · rintro ⟨hxJ, hxX₀ | ⟨_, hx_not⟩⟩
      · exact hxX₀
      · exact False.elim (hx_not hxJ)
    · intro hxX₀
      exact ⟨hX₀_sub_VJ hxX₀, Or.inl hxX₀⟩

/-- Under `h83`, `Γ.E.Nonempty` (since `C₀` is a circuit of `Γ`). -/
theorem Γ_E_nonempty_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star) :
    Γ.E.Nonempty := by
  obtain ⟨u, W_C, _, hlen, _, hEC⟩ := h83.hyp_ii.2.1
  rcases W_C with _ | ⟨hlk, _⟩
  · simp [GraphWalk.length, GraphWalk.edges] at hlen
  · exact ⟨_, h83.hyp_ii.1.2 hlk.edge_mem⟩

/-- Under `h83`, for any `v ∈ Γ.V` and `r ∈ Γ.R` with `v ∈ subBd r`, we have `d {v} r ≤ 1` and
`d r {v} ≤ 1`. -/
theorem dist_vertex_region_le_one_8_3
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {v : S} (hv : v ∈ Γ.V) {r : Set S} (hr : r ∈ Γ.R) (hvr : v ∈ subBd r) :
    d {v} r ≤ 1 ∧ d r {v} ≤ 1 := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hrA : r ∈ Γ.A := Or.inr hr
  have hv_cl : v ∈ closure r := by
    rw [GM11.subBd_eq_frontier] at hvr
    exact hvr.1
  obtain ⟨_, K, ins, hK, _, hdeq⟩ := h83.hyp_iv.2.1
  have h1 : d {v} r ≤ 1 := by
    rw [hdeq {v} hvA r hrA]
    exact GM11.tangleMetric_le_one hS hK (Γ_E_nonempty_8_3 h83) hv hr hv_cl
  exact ⟨h1, (HasTangleMetric.comm h83.hyp_iv.2.1 hrA hvA).trans_le h1⟩

/-- Under `h83`, if `Δ₀` is a closed disc with `(univ \ Δ₀).Nonempty` and `univ \ Δ₀ ⊆ r₀`, then
for any `X ⊆ S`, `subsetTangleDist Γ ord d X (univ \ Δ₀) = subsetTangleDist Γ ord d X r₀`, and for
`u ∈ Γ.V`, `subsetTangleDist Γ ord d {u} (univ \ Δ₀) = d {u} r₀`. -/
theorem subsetTangleDist_compl_Δ₀_eq_r₀
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hcompl_r₀ : Set.univ \ Δ₀ ⊆ r₀) :
    (∀ X : Set S, subsetTangleDist Γ ord d X (Set.univ \ Δ₀) = subsetTangleDist Γ ord d X r₀) ∧
    (∀ u ∈ Γ.V, subsetTangleDist Γ ord d {u} (Set.univ \ Δ₀) = d {u} r₀) := by
  obtain ⟨Δ_c, hΔc_disc, _, _, hΔc_int⟩ :=
    exists_complementary_closedDisc_in_sphere h83.hyp_i.1 hΔ₀
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hbd_c : subBd Δ_c = discBd Δ_c :=
    GM14.IsClosedDisc.subBd_eq_discBd hS hΔc_disc
  obtain ⟨_, g_c, hc_chart⟩ := hΔc_disc.exists_isChart
  have hp₀_int : g_c 0 ∈ Δ_c \ discBd Δ_c := by
    refine ⟨hc_chart.gm (Metric.mem_closedBall_self zero_le_one), ?_⟩
    rw [← hc_chart.g_sphere]
    rintro ⟨w, hw, heq⟩
    have h0w : w = 0 := hc_chart.injOn (sphere_subset_closedBall hw)
      (Metric.mem_closedBall_self zero_le_one) heq
    rw [h0w] at hw
    simp at hw
  have hp₀_compl : g_c 0 ∈ Set.univ \ Δ₀ := by
    rw [← hΔc_int, hbd_c]
    exact hp₀_int
  have hp₀_r₀ : g_c 0 ∈ r₀ := hcompl_r₀ hp₀_compl
  have hr₀_A : r₀ ∈ Γ.A := Or.inr h83.hyp_ii.2.2.1
  have hatom_iff : ∀ b ∈ Γ.A, (b ∩ (Set.univ \ Δ₀)).Nonempty ↔ (b ∩ r₀).Nonempty := by
    intro b hb
    constructor
    · exact fun hne => hne.mono (inter_subset_inter_right b hcompl_r₀)
    · intro hne
      have hb_eq : b = r₀ := GM12.atom_eq_of_inter_nonempty hb hr₀_A hne
      subst hb_eq
      exact ⟨g_c 0, hp₀_r₀, hp₀_compl⟩
  have hX_eq : ∀ X : Set S,
      subsetTangleDist Γ ord d X (Set.univ \ Δ₀) = subsetTangleDist Γ ord d X r₀ := by
    intro X
    unfold subsetTangleDist
    have hex_iff : (∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ (Set.univ \ Δ₀)).Nonempty) ↔
        (∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ r₀).Nonempty) := by
      constructor <;> rintro ⟨a, ha, b, hb, haX, hbY⟩
      · exact ⟨a, ha, b, hb, haX, (hatom_iff b hb).mp hbY⟩
      · exact ⟨a, ha, b, hb, haX, (hatom_iff b hb).mpr hbY⟩
    have hset_eq : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
        (a ∩ X).Nonempty ∧ (b ∩ (Set.univ \ Δ₀)).Nonempty ∧ d a b = k} =
        {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
          (a ∩ X).Nonempty ∧ (b ∩ r₀).Nonempty ∧ d a b = k} := by
      ext k
      simp only [mem_ofPred_eq]
      constructor <;> rintro ⟨a, ha, b, hb, haX, hbY, hdk⟩
      · exact ⟨a, ha, b, hb, haX, (hatom_iff b hb).mp hbY, hdk⟩
      · exact ⟨a, ha, b, hb, haX, (hatom_iff b hb).mpr hbY, hdk⟩
    by_cases h1 : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ r₀).Nonempty
    · have h2 := hex_iff.mpr h1
      simp only [h1, h2, ↓reduceIte, hset_eq]
    · have h2 : ¬ ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ (Set.univ \ Δ₀)).Nonempty :=
        fun h => h1 (hex_iff.mp h)
      simp only [h1, h2, ↓reduceIte]
  refine ⟨hX_eq, ?_⟩
  intro u hu
  rw [hX_eq {u}]
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  refine le_antisymm
    (subsetTangleDist_le_of_mem huA hr₀_A ⟨u, rfl, rfl⟩ ⟨g_c 0, hp₀_r₀, hp₀_r₀⟩) ?_
  refine le_subsetTangleDist_of_forall (HasTangleMetric.le_ord h83.hyp_iv.2.1 huA hr₀_A)
    fun a ha b hb hau hbr₀ => ?_
  have ha_eq : a = {u} := GM12.atom_eq_of_inter_nonempty ha huA hau
  have hb_eq : b = r₀ := GM12.atom_eq_of_inter_nonempty hb hr₀_A hbr₀
  rw [ha_eq, hb_eq]

/-- Under `h83` and the conclusions of Claims (5) and (6), for every `A ∈ 𝒜`:
(1) for any atoms `y, z ∈ Γ.A` meeting `D A`, `d y z ≤ 3`;
(2) for any atom `z ∈ Γ.A` meeting `D A`, `d {vA A} z ≤ 3` and `d z {vA A} ≤ 3`;
(3) `subsetTangleDist Γ ord d {vA A} (D A) ≤ 1`. -/
theorem dist_vA_atom_meets_DA_le_three
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {D : Graph α β → Set S}
    (hD_disc : ∀ A ∈ 𝒜, IsClosedDisc (D A))
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hD_bdV : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)})
    (hD_interV : ∀ A ∈ 𝒜, (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)})
    (hins : ∀ A ∈ 𝒜, IsTangleIns Γ T (subBd (D A)) (D A))
    (hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D A).Nonempty)
    {A : Graph α β} (hA : A ∈ 𝒜) :
    (∀ y ∈ Γ.A, ∀ z ∈ Γ.A, (y ∩ D A).Nonempty → (z ∩ D A).Nonempty → d y z ≤ 3) ∧
    (∀ z ∈ Γ.A, (z ∩ D A).Nonempty → d {vA A} z ≤ 3 ∧ d z {vA A} ≤ 3) ∧
    subsetTangleDist Γ ord d {vA A} (D A) ≤ 1 := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  let F : Set S := subBd (D A)
  have hF_eq_discBd : F = discBd (D A) :=
    GM14.IsClosedDisc.subBd_eq_discBd hS (hD_disc A hA)
  have hF_oarc : IsOArc F := hF_eq_discBd ▸ (hD_disc A hA).isOArc_discBd
  have hFV_sub_pre : F ∩ Γ.V ⊆ ιV ⁻¹' Set.range (πA A) := by
    rw [hD_bdV A hA]
    exact fun _ hv => hv.2
  have hFV_card_le : (F ∩ Γ.V).ncard ≤ 3 := by
    have hsub_img : ιV '' (F ∩ Γ.V) ⊆ Set.range (πA A) := by
      rintro _ ⟨v, hv, rfl⟩
      exact hFV_sub_pre hv
    have h1 : (F ∩ Γ.V).ncard = (ιV '' (F ∩ Γ.V)).ncard :=
      (Set.ncard_image_of_injective (F ∩ Γ.V) ιV.injective).symm
    have h2 : (ιV '' (F ∩ Γ.V)).ncard ≤ (Set.range (πA A)).ncard :=
      Set.ncard_le_ncard hsub_img (Set.finite_range (πA A))
    have h3 : (Set.range (πA A)).ncard ≤ πLen A :=
      (Set.image_univ.symm ▸ Set.ncard_image_le finite_univ).trans (by simp)
    have h4 : πLen A ≤ 3 := (h83.hyp_vii A hA).1
    omega
  have hFV_lt_ord : (F ∩ Γ.V).ncard < ord := by omega
  obtain ⟨_, hbd_ins, hmem_T⟩ := hins A hA
  have hdist_FV : ∀ y ∈ Γ.A, ∀ z ∈ Γ.A, (y ∩ D A).Nonempty → (z ∩ D A).Nonempty →
      d y z ≤ (F ∩ Γ.V).ncard :=
    fun y hy z hz hyD hzD =>
      GM12.dist_le_of_oarc_disc hS h83.hyp_iv.2.1 hF_oarc (hD_norm A hA) hFV_lt_ord
        (hD_disc A hA) hbd_ins hmem_T hy hz hyD hzD
  have hdist_3 : ∀ y ∈ Γ.A, ∀ z ∈ Γ.A, (y ∩ D A).Nonempty → (z ∩ D A).Nonempty → d y z ≤ 3 :=
    fun y hy z hz hyD hzD => (hdist_FV y hy z hz hyD hzD).trans hFV_card_le
  obtain ⟨hvA_V, u, hu_ZA, P, hP_path, hP_inter_ΓV⟩ := h83.hyp_xi A hA
  have hvA_atom : ({vA A} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨vA A, hvA_V, rfl⟩)
  obtain ⟨r, hr, hvA_bd_r, hr_DA⟩ := hc6 A hA
  have hr_atom : r ∈ Γ.A := Or.inr hr
  obtain ⟨hd_vr, hd_rv⟩ := dist_vertex_region_le_one_8_3 h83 hvA_V hr hvA_bd_r
  have hsub_dist_1 : subsetTangleDist Γ ord d {vA A} (D A) ≤ 1 := by
    have hle : subsetTangleDist Γ ord d {vA A} (D A) ≤ d {vA A} r :=
      subsetTangleDist_le_of_mem hvA_atom hr_atom ⟨vA A, rfl, rfl⟩ hr_DA
    exact hle.trans hd_vr
  refine ⟨hdist_3, ?_, hsub_dist_1⟩
  intro z hz hzD
  by_cases hvA_in_A : ιV (vA A) ∈ V(A)
  · have hvA_interV : vA A ∈ (Γ.interSet (D A)).V := by
      rw [hD_bdV A hA] at *
      rw [hD_interV A hA]
      exact ⟨hvA_V, hvA_in_A⟩
    have hvA_DA : vA A ∈ D A := by
      obtain ⟨hV_eq, _⟩ := interSet_V_and_U (hD_disc A hA).isClosed (hD_norm A hA)
      exact (hV_eq ▸ hvA_interV).2
    have h1 : d {vA A} z ≤ 3 := hdist_3 {vA A} hvA_atom z hz ⟨vA A, rfl, hvA_DA⟩ hzD
    exact ⟨h1, (HasTangleMetric.comm h83.hyp_iv.2.1 hz hvA_atom).trans_le h1⟩
  · -- When `ιV (vA A) ∉ V(A)`, `u ∈ (Z ∩ V(A)) \ (ιV '' Γ.V)` so `(F ∩ Γ.V).ncard ≤ 2`.
    have hπ_eq_Z : Set.range (πA A) = Z ∩ V(A) := (h83.hyp_vii A hA).2.2
    have hu_range : u ∈ Set.range (πA A) := hπ_eq_Z.symm ▸ hu_ZA
    have hv_ne_u : ιV (vA A) ≠ u := fun h => hvA_in_A (h ▸ hu_ZA.2)
    obtain ⟨_, W₀, _, hVP, _⟩ := hP_path
    have hu_VP : u ∈ V(P) := by rw [hVP]; exact W₀.end_mem_support
    have hu_not_ΓV : u ∉ ιV '' Γ.V := by
      intro huΓ
      have hu_in : u ∈ V(P) ∩ (ιV '' Γ.V) := ⟨hu_VP, huΓ⟩
      rw [hP_inter_ΓV, mem_singleton_iff] at hu_in
      exact hv_ne_u.symm hu_in
    have hFV_card_le_2 : (F ∩ Γ.V).ncard ≤ 2 := by
      have hsub_diff : ιV '' (F ∩ Γ.V) ⊆ Set.range (πA A) \ {u} := by
        rintro _ ⟨w, hw, rfl⟩
        have hw' : w ∈ {v ∈ Γ.V | ιV v ∈ Set.range (πA A)} := hD_bdV A hA ▸ hw
        exact ⟨hw'.2, fun heq => hu_not_ΓV (heq ▸ ⟨w, hw'.1, rfl⟩)⟩
      have h1 : (F ∩ Γ.V).ncard = (ιV '' (F ∩ Γ.V)).ncard :=
        (Set.ncard_image_of_injective (F ∩ Γ.V) ιV.injective).symm
      have h2 : (ιV '' (F ∩ Γ.V)).ncard ≤ (Set.range (πA A) \ {u}).ncard :=
        Set.ncard_le_ncard hsub_diff ((Set.finite_range (πA A)).sdiff)
      have h3 : (Set.range (πA A) \ {u}).ncard + 1 = (Set.range (πA A)).ncard :=
        Set.ncard_sdiff_singleton_add_one hu_range (Set.finite_range (πA A))
      have h4 : (Set.range (πA A)).ncard ≤ πLen A :=
        (Set.image_univ.symm ▸ Set.ncard_image_le finite_univ).trans (by simp)
      have h5 : πLen A ≤ 3 := (h83.hyp_vii A hA).1
      omega
    have hd_rz : d r z ≤ 2 := (hdist_FV r hr_atom z hz hr_DA hzD).trans hFV_card_le_2
    have htri : d {vA A} z ≤ d {vA A} r + d r z :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hvA_atom hr_atom hz
    have h1 : d {vA A} z ≤ 3 := by omega
    exact ⟨h1, (HasTangleMetric.comm h83.hyp_iv.2.1 hz hvA_atom).trans_le h1⟩

/-- If `u ∈ Γ.V` satisfies `subsetTangleDist Γ ord d {u} C₀.V < 5` (and `5 ≤ ord`), then
`d {u} r₀ ≤ 5` and `subsetTangleDist Γ ord d {u} (univ \ Δ₀) ≤ 5`. -/
theorem dist_compl_Δ₀_le_five_of_dist_C₀_lt_five
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 5 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hcompl_r₀ : Set.univ \ Δ₀ ⊆ r₀)
    {u : S} (hu : u ∈ Γ.V) (hlt : subsetTangleDist Γ ord d {u} C₀.V < 5) :
    d {u} r₀ ≤ 5 ∧ subsetTangleDist Γ ord d {u} (Set.univ \ Δ₀) ≤ 5 := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hr₀A : r₀ ∈ Γ.A := Or.inr h83.hyp_ii.2.2.1
  have hle_4 : subsetTangleDist Γ ord d {u} C₀.V ≤ 4 := by omega
  obtain ⟨z, hz, hzC₀, hd_uz⟩ :=
    exists_atom_of_subsetTangleDist_singleton_le hu hle_4 (by omega)
  obtain ⟨w, hwz, hwC₀⟩ := hzC₀
  have hwV : w ∈ Γ.V := h83.hyp_ii.1.1 hwC₀
  have hwA : ({w} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨w, hwV, rfl⟩)
  have hz_eq : z = {w} := GM12.atom_eq_of_inter_nonempty hz hwA ⟨w, hwz, rfl⟩
  subst hz_eq
  have hw_bd_r₀ : w ∈ subBd r₀ := by
    rw [h83.hyp_ii.2.2.2]
    exact C₀.V_subset_U hwC₀
  have hd_wr₀ : d {w} r₀ ≤ 1 :=
    (dist_vertex_region_le_one_8_3 h83 hwV h83.hyp_ii.2.2.1 hw_bd_r₀).1
  have htri : d {u} r₀ ≤ d {u} {w} + d {w} r₀ :=
    HasTangleMetric.triangle hS h83.hyp_iv.2.1 huA hwA hr₀A
  have hd_ur₀ : d {u} r₀ ≤ 5 := by omega
  rw [(subsetTangleDist_compl_Δ₀_eq_r₀ h83 hΔ₀ hcompl_r₀).2 u hu]
  exact ⟨hd_ur₀, hd_ur₀⟩

/-! ## 2. Proofs of Claims (7)–(11) of Theorem 8.3 -/

/-- **Claim (7) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 561):
"(7) $A \cap K_0 = N_W$ for all $A \in \mathcal{A}'$." -/
theorem lemma_8_3_claim_7
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 4 ≤ ord)
    {D : Graph α β → Set S}
    (hD_disc : ∀ A ∈ 𝒜, IsClosedDisc (D A))
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hD_bdV : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)})
    (hD_interV : ∀ A ∈ 𝒜, (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)})
    (hins : ∀ A ∈ 𝒜, IsTangleIns Γ T (subBd (D A)) (D A))
    (hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D A).Nonempty)
    {K₀ : Graph α β}
    (hsep_K₀ : IsGraphSeparation R_G.G.toGraph J K₀)
    (hinter_K₀ : V(J) ∩ V(K₀) = (ιV '' C₀.V) ∪ W) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    ∀ A ∈ 𝒜', A ⊓ K₀ = Graph.noEdge W β := by
  intro 𝒜' A ⟨hA, hdist_5⟩
  have hA_le_J : A ≤ J := h83.hyp_vi.2.2.1.2.1 A hA
  have hA_le_G : A ≤ R_G.G.toGraph := hA_le_J.trans hsep_K₀.1
  have hW_sub_A : W ⊆ V(A) := h83.hyp_vi.2.2.2 A hA
  have hW_sub_K₀ : W ⊆ V(K₀) := by
    have : W ⊆ V(J) ∩ V(K₀) := hinter_K₀.symm ▸ subset_union_right
    exact this.trans inter_subset_right
  have hE_emp : E(A ⊓ K₀) = ∅ := by
    rw [(Compatible.of_le_le hA_le_G hsep_K₀.2.1).edgeSet_inf,
      disjoint_iff_inter_eq_empty.mp (hsep_K₀.2.2.2.2.mono_left hA_le_J.edgeSet_mono)]
  have hV_eq : V(A ⊓ K₀) = W := by
    refine Subset.antisymm ?_ (subset_inter hW_sub_A hW_sub_K₀)
    intro x ⟨hxA, hxK₀⟩
    have hx_JK₀ : x ∈ V(J) ∩ V(K₀) := ⟨hA_le_J.vertexSet_mono hxA, hxK₀⟩
    rw [hinter_K₀] at hx_JK₀
    rcases hx_JK₀ with ⟨w, hwC₀, rfl⟩ | hxW
    · exfalso
      have hwV : w ∈ Γ.V := h83.hyp_ii.1.1 hwC₀
      have hw_interV : w ∈ (Γ.interSet (D A)).V := by
        rw [hD_interV A hA]
        exact ⟨hwV, hxA⟩
      have hw_DA : w ∈ D A := by
        obtain ⟨hV_eq, _⟩ := interSet_V_and_U (hD_disc A hA).isClosed (hD_norm A hA)
        exact (hV_eq ▸ hw_interV).2
      have hwA : ({w} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨w, hwV, rfl⟩)
      have hvA_V : vA A ∈ Γ.V := (h83.hyp_xi A hA).1
      have hvA_atom : ({vA A} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨vA A, hvA_V, rfl⟩)
      have hd_vw : d {vA A} {w} ≤ 3 :=
        ((dist_vA_atom_meets_DA_le_three h83 hord hD_disc hD_norm hD_bdV hD_interV hins hc6 hA).2.1
          {w} hwA ⟨w, rfl, hw_DA⟩).1
      have hdist_le : subsetTangleDist Γ ord d {vA A} C₀.V ≤ 3 := by
        have hle : subsetTangleDist Γ ord d {vA A} C₀.V ≤ d {vA A} {w} :=
          subsetTangleDist_le_of_mem hvA_atom hwA ⟨vA A, rfl, rfl⟩ ⟨w, rfl, hwC₀⟩
        exact hle.trans hd_vw
      omega
    · exact hxW
  refine Graph.ext hV_eq fun e x y => ?_
  simp only [Graph.noEdge_isLink, iff_false]
  intro hlk
  have he : e ∈ E(A ⊓ K₀) := hlk.edge_mem
  rw [hE_emp] at he
  exact he

/-- **Claim (8) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 561):
"(8) $(N, K)$ is a separation of $G$ and $W \subseteq V(K)$, and if $v \in V(K \cap N) \setminus W$
then $v \in \Sigma$ and $d(v, \Sigma \setminus \Delta_0) \le 7$."

Note: When $A \notin \mathcal{A}'$, $d(v(A), V(C_0)) \le 4$; since each vertex of $V(C_0)$ lies on
$\operatorname{bd}(r_0)$ at tangle distance $\le 1$ from $r_0$ (the unique atom meeting
$\Sigma \setminus \Delta_0$), we have $d(v(A), \Sigma \setminus \Delta_0) \le 4 + 1 = 5$ and hence
$d(v, \Sigma \setminus \Delta_0) \le 3 + 5 = 8$ (the paper writes $4$ and $7$). -/
theorem lemma_8_3_claim_8
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 5 ≤ ord)
    {Δ₀ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hcompl_r₀ : Set.univ \ Δ₀ ⊆ r₀)
    {D : Graph α β → Set S}
    (hD_disc : ∀ A ∈ 𝒜, IsClosedDisc (D A))
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hD_bdV : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)})
    (hD_interV : ∀ A ∈ 𝒜, (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)})
    (hins : ∀ A ∈ 𝒜, IsTangleIns Γ T (subBd (D A)) (D A))
    (hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D A).Nonempty)
    {K₀ : Graph α β}
    (hsep_K₀ : IsGraphSeparation R_G.G.toGraph J K₀)
    (hinter_K₀ : V(J) ∩ V(K₀) = (ιV '' C₀.V) ∪ W) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    let N := graphUnion (graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β))
      (subgraphSUnion R_G.G.toGraph 𝒜')
    let K := graphUnion K₀
      (subgraphSUnion R_G.G.toGraph ((fun A => A.deleteEdges E((Γ.toEmbeddedGraph ιV ιE) ⊓ A)) '' (𝒜 \ 𝒜')))
    IsGraphSeparation R_G.G.toGraph N K ∧
    W ⊆ V(N) ∩ V(K) ∧
    (∀ v ∈ (V(K) ∩ V(N)) \ W, v ∈ (ιV '' Γ.V) ∪ Z) ∧
    (∀ w ∈ Γ.V, ιV w ∈ (V(K) ∩ V(N)) \ W →
      subsetTangleDist Γ ord d {w} (Set.univ \ Δ₀) ≤ 8) := by
  intro 𝒜' N K
  let G := R_G.G.toGraph
  let Γ_emb := Γ.toEmbeddedGraph ιV ιE
  have hJ_le_G : J ≤ G := hsep_K₀.1
  have hK₀_le_G : K₀ ≤ G := hsep_K₀.2.1
  have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
  have hA_le_J : ∀ A ∈ 𝒜, A ≤ J := hZdiv.2.1
  have hA_le_G : ∀ A ∈ 𝒜, A ≤ G := fun A hA => (hA_le_J A hA).trans hJ_le_G
  have hΓ_le_J : Γ_emb ≤ J := (Γ_le_J_8_3 h83).2
  have hΓ_le_G : Γ_emb ≤ G := hΓ_le_J.trans hJ_le_G
  have hNW_le_J : Graph.noEdge W β ≤ J := by
    refine ⟨?_, fun _ _ _ hl => by simp at hl⟩
    rw [h83.hyp_v.2, vertexSet_induce]
    exact fun x hx => Or.inl (Or.inl hx)
  have hNW_le_G : Graph.noEdge W β ≤ G := hNW_le_J.trans hJ_le_G
  have h𝒜'_le_J : subgraphSUnion G 𝒜' ≤ J :=
    subgraphSUnion_le_of_forall_le (fun A hA => hA_le_G A hA.1) hJ_le_G (fun A hA => hA_le_J A hA.1)
  have hN_le_J : N ≤ J :=
    graphUnion_le (graphUnion_le hΓ_le_J hNW_le_J) h𝒜'_le_J
  have hN_le_G : N ≤ G := hN_le_J.trans hJ_le_G
  let remPiece (A : Graph α β) : Graph α β := A.deleteEdges E(Γ_emb ⊓ A)
  have hrem_le_J : ∀ B ∈ remPiece '' (𝒜 \ 𝒜'), B ≤ J := by
    rintro _ ⟨A, hA, rfl⟩
    exact Graph.deleteEdges_le.trans (hA_le_J A hA.1)
  have hrem_le_G : ∀ B ∈ remPiece '' (𝒜 \ 𝒜'), B ≤ G :=
    fun B hB => (hrem_le_J B hB).trans hJ_le_G
  have hrem_sUnion_le_J : subgraphSUnion G (remPiece '' (𝒜 \ 𝒜')) ≤ J :=
    subgraphSUnion_le_of_forall_le hrem_le_G hJ_le_G hrem_le_J
  have hK_le_G : K ≤ G :=
    graphUnion_le hK₀_le_G (subgraphSUnion_le hrem_le_G)
  -- Vertex and edge sets of `N` and `K`.
  have hVN : V(N) = (ιV '' Γ.V) ∪ W ∪ ⋃ A ∈ 𝒜', V(A) := by
    change V(graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜')) = _
    rw [vertexSet_graphUnion, vertexSet_graphUnion, Graph.vertexSet_noEdge, vertexSet_subgraphSUnion]
    rfl
  have hEN : E(N) = (ιE '' Γ.E) ∪ ⋃ A ∈ 𝒜', E(A) := by
    change E(graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜')) = _
    rw [edgeSet_graphUnion, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
      edgeSet_subgraphSUnion (fun A (hA : A ∈ 𝒜') => hA_le_G A hA.1)]
    rfl
  have hVK : V(K) = V(K₀) ∪ ⋃ A ∈ 𝒜 \ 𝒜', V(A) := by
    change V(graphUnion K₀ (subgraphSUnion G (remPiece '' (𝒜 \ 𝒜')))) = _
    rw [vertexSet_graphUnion, vertexSet_subgraphSUnion]
    ext x
    simp only [mem_union, mem_iUnion, exists_prop, mem_image, remPiece]
    constructor
    · rintro (hx | ⟨_, ⟨A, hA, rfl⟩, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨A, hA, hx⟩
    · rintro (hx | ⟨A, hA, hx⟩)
      · exact Or.inl hx
      · exact Or.inr ⟨A.deleteEdges E(Γ_emb ⊓ A), ⟨A, hA, rfl⟩, hx⟩
  have hEK : E(K) = E(K₀) ∪ ⋃ A ∈ 𝒜 \ 𝒜', (E(A) \ E(Γ_emb ⊓ A)) := by
    change E(graphUnion K₀ (subgraphSUnion G (remPiece '' (𝒜 \ 𝒜')))) = _
    rw [edgeSet_graphUnion, edgeSet_subgraphSUnion hrem_le_G]
    ext e
    simp only [mem_union, mem_iUnion, exists_prop, mem_image, remPiece]
    constructor
    · rintro (he | ⟨_, ⟨A, hA, rfl⟩, he⟩)
      · exact Or.inl he
      · exact Or.inr ⟨A, hA, he⟩
    · rintro (he | ⟨A, hA, he⟩)
      · exact Or.inl he
      · exact Or.inr ⟨A.deleteEdges E(Γ_emb ⊓ A), ⟨A, hA, rfl⟩, he⟩
  -- Show `V(J) ⊆ V(N) ∪ V(K)` and `E(J) ⊆ E(N) ∪ E(K)`.
  have hVJ_eq_𝒜 : V(J) = ⋃ A ∈ 𝒜, V(A) := by
    have := congrArg Graph.vertexSet hZdiv.2.2.1.symm
    rwa [vertexSet_subgraphSUnion] at this
  have hEJ_eq_𝒜 : E(J) = ⋃ A ∈ 𝒜, E(A) := by
    have := congrArg Graph.edgeSet hZdiv.2.2.1.symm
    rwa [edgeSet_subgraphSUnion hA_le_J] at this
  have hVN_VK : V(N) ∪ V(K) = V(G) := by
    refine Subset.antisymm (union_subset hN_le_G.vertexSet_mono hK_le_G.vertexSet_mono) ?_
    rw [← hsep_K₀.2.2.1]
    rintro x (hxJ | hxK₀)
    · rw [hVJ_eq_𝒜] at hxJ
      obtain ⟨A, hA, hxA⟩ := mem_iUnion₂.mp hxJ
      by_cases hA' : A ∈ 𝒜'
      · exact Or.inl (by rw [hVN]; exact Or.inr (mem_iUnion₂.mpr ⟨A, hA', hxA⟩))
      · exact Or.inr (by rw [hVK]; exact Or.inr (mem_iUnion₂.mpr ⟨A, ⟨hA, hA'⟩, hxA⟩))
    · exact Or.inr (by rw [hVK]; exact Or.inl hxK₀)
  have hEN_EK : E(N) ∪ E(K) = E(G) := by
    refine Subset.antisymm (union_subset hN_le_G.edgeSet_mono hK_le_G.edgeSet_mono) ?_
    rw [← hsep_K₀.2.2.2.1]
    rintro e (heJ | heK₀)
    · rw [hEJ_eq_𝒜] at heJ
      obtain ⟨A, hA, heA⟩ := mem_iUnion₂.mp heJ
      by_cases hA' : A ∈ 𝒜'
      · exact Or.inl (by rw [hEN]; exact Or.inr (mem_iUnion₂.mpr ⟨A, hA', heA⟩))
      · by_cases heΓ : e ∈ E(Γ_emb)
        · exact Or.inl (by rw [hEN]; exact Or.inl heΓ)
        · right
          rw [hEK]
          refine Or.inr (mem_iUnion₂.mpr ⟨A, ⟨hA, hA'⟩, heA, ?_⟩)
          rw [(Compatible.of_le_le hΓ_le_G (hA_le_G A hA)).edgeSet_inf]
          exact fun h => heΓ h.1
    · exact Or.inr (by rw [hEK]; exact Or.inl heK₀)
  have hdisj_E : Disjoint E(N) E(K) := by
    rw [disjoint_left]
    intro e heN heK
    rw [hEK] at heK
    rcases heK with heK₀ | heRem
    · exact disjoint_left.mp hsep_K₀.2.2.2.2 (hN_le_J.edgeSet_mono heN) heK₀
    · obtain ⟨A, ⟨hA, hA_not'⟩, heA, he_not_ΓA⟩ := mem_iUnion₂.mp heRem
      rw [(Compatible.of_le_le hΓ_le_G (hA_le_G A hA)).edgeSet_inf] at he_not_ΓA
      rw [hEN] at heN
      rcases heN with heΓ | heA'
      · exact he_not_ΓA ⟨heΓ, heA⟩
      · obtain ⟨A', hA', heA'⟩ := mem_iUnion₂.mp heA'
        have hne : A ≠ A' := fun heq => hA_not' (heq ▸ hA')
        exact disjoint_left.mp (hZdiv.2.2.2 A hA A' hA'.1 hne).1 heA heA'
  have hsep_NK : IsGraphSeparation G N K :=
    ⟨hN_le_G, hK_le_G, hVN_VK, hEN_EK, hdisj_E⟩
  have hW_sub_NK : W ⊆ V(N) ∩ V(K) := by
    intro w hw
    have hw_K₀ : w ∈ V(K₀) := (hinter_K₀.symm ▸ Or.inr hw : w ∈ V(J) ∩ V(K₀)).2
    exact ⟨by rw [hVN]; exact Or.inl (Or.inr hw), by rw [hVK]; exact Or.inl hw_K₀⟩
  -- Analyse vertices `v ∈ (V(K) ∩ V(N)) \ W`.
  have hv_cases : ∀ v ∈ (V(K) ∩ V(N)) \ W,
      v ∈ ιV '' C₀.V ∨
        ∃ A ∈ 𝒜 \ 𝒜', (v ∈ V(A) ∩ (ιV '' Γ.V)) ∨ (v ∈ Z ∩ V(A)) := by
    rintro v ⟨⟨hvK, hvN⟩, hvW⟩
    rw [hVK] at hvK
    rcases hvK with hvK₀ | hvRem
    · left
      have hv_JK₀ : v ∈ V(J) ∩ V(K₀) := ⟨hN_le_J.vertexSet_mono hvN, hvK₀⟩
      rw [hinter_K₀] at hv_JK₀
      exact hv_JK₀.resolve_right hvW
    · right
      obtain ⟨A, hA, hvA_mem⟩ := mem_iUnion₂.mp hvRem
      refine ⟨A, hA, ?_⟩
      rw [hVN] at hvN
      rcases hvN with (hvΓ | hvW') | hvA'
      · exact Or.inl ⟨hvA_mem, hvΓ⟩
      · exact False.elim (hvW hvW')
      · obtain ⟨A', hA', hvA'⟩ := mem_iUnion₂.mp hvA'
        have hne : A ≠ A' := fun heq => hA.2 (heq ▸ hA')
        have hv_ZW : v ∈ Z ∪ W := (hZdiv.2.2.2 A hA.1 A' hA'.1 hne).2 ⟨hvA_mem, hvA'⟩
        exact Or.inr ⟨hv_ZW.resolve_right hvW, hvA_mem⟩
  refine ⟨hsep_NK, hW_sub_NK, ?_, ?_⟩
  · intro v hv
    rcases hv_cases v hv with hvC₀ | ⟨A, _, ⟨_, hvΓ⟩ | ⟨hvZ, _⟩⟩
    · exact Or.inl (image_mono h83.hyp_ii.1.1 hvC₀)
    · exact Or.inl hvΓ
    · exact Or.inr hvZ
  · intro w hwV hw_mem
    obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
    have hwA : ({w} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨w, hwV, rfl⟩)
    have hr₀A : r₀ ∈ Γ.A := Or.inr h83.hyp_ii.2.2.1
    rw [(subsetTangleDist_compl_Δ₀_eq_r₀ h83 hΔ₀ hcompl_r₀).2 w hwV]
    rcases hv_cases (ιV w) hw_mem with hwC₀ | ⟨A, ⟨hA, hA_not'⟩, h_in⟩
    · have hw_C₀V : w ∈ C₀.V := (ιV.injective.mem_set_image).mp hwC₀
      have hw_bd_r₀ : w ∈ subBd r₀ := by
        rw [h83.hyp_ii.2.2.2]
        exact C₀.V_subset_U hw_C₀V
      have hd1 := (dist_vertex_region_le_one_8_3 h83 hwV h83.hyp_ii.2.2.1 hw_bd_r₀).1
      omega
    · have hw_in_A : ιV w ∈ V(A) := h_in.elim And.left And.right
      have hw_interV : w ∈ (Γ.interSet (D A)).V := by
        rw [hD_interV A hA]
        exact ⟨hwV, hw_in_A⟩
      have hw_DA : w ∈ D A := by
        obtain ⟨hV_eq, _⟩ := interSet_V_and_U (hD_disc A hA).isClosed (hD_norm A hA)
        exact (hV_eq ▸ hw_interV).2
      have hd_wvA : d {w} {vA A} ≤ 3 :=
        ((dist_vA_atom_meets_DA_le_three h83 (by omega) hD_disc hD_norm hD_bdV hD_interV hins hc6 hA).2.1
          {w} hwA ⟨w, rfl, hw_DA⟩).2
      have hvA_V : vA A ∈ Γ.V := (h83.hyp_xi A hA).1
      have hvA_atom : ({vA A} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨vA A, hvA_V, rfl⟩)
      have hlt_5 : subsetTangleDist Γ ord d {vA A} C₀.V < 5 :=
        not_le.mp fun hge => hA_not' ⟨hA, hge⟩
      have hd_vA_r₀ : d {vA A} r₀ ≤ 5 :=
        (dist_compl_Δ₀_le_five_of_dist_C₀_lt_five h83 hord hΔ₀ hcompl_r₀ hvA_V hlt_5).1
      have htri : d {w} r₀ ≤ d {w} {vA A} + d {vA A} r₀ :=
        HasTangleMetric.triangle hS h83.hyp_iv.2.1 hwA hvA_atom hr₀A
      omega

/-- **Claim (9) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 561):
"(9) There is a closed disc $\Delta \subseteq \Sigma$ with $\text{bd}(\Delta) \subseteq U(\Gamma)$
and $v^* \notin \Delta$ and $\Sigma \setminus \Delta_0 \subseteq \Delta$, such that
$d(v^*, \Delta) \ge \theta'$ and $d(v^*, x) \le \theta' + 2$ for every $x \in A(\Gamma)$ with
$x \not\subseteq \Delta \setminus \text{bd}(\Delta)$." -/
theorem lemma_8_3_claim_9
    {q δ h θ θ' : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hθ'_ge : 3 ≤ θ') (hθ'_θ : θ' + 3 ≤ θ)
    {Δ₀ : Set S} (hcompl_r₀ : Set.univ \ Δ₀ ⊆ r₀) :
    ∃ Δ : Set S,
      IsClosedDisc Δ ∧
      subBd Δ ⊆ Γ.U ∧
      v_star ∉ Δ ∧
      Set.univ \ Δ₀ ⊆ Δ ∧
      θ' ≤ subsetTangleDist Γ ord d {v_star} Δ ∧
      (∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → d {v_star} x ≤ θ' + 2) := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hv_star : v_star ∈ Γ.V := h83.hyp_xiv.1.1
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hv_star, rfl⟩)
  have hθ'_ord : θ' + 3 ≤ ord := hθ'_θ.trans h83.hyp_iv.1
  obtain ⟨Δ', hΔ'_disc, hΔ'_bd, hΔ'_le, hΔ'_ge, hv_star_in⟩ :=
    gm22_theorem_5_1 Γ ord θ' T d {v_star} hS h83.hyp_iv.2.1 hv_star_A (by omega) hθ'_ord
  obtain ⟨Δ, hΔ_disc, hΔ_bd_eq, hΔ_eq, hΔ_int_eq⟩ :=
    exists_complementary_closedDisc_in_sphere h83.hyp_i.1 hΔ'_disc
  refine ⟨Δ, hΔ_disc, hΔ_bd_eq ▸ hΔ'_bd, ?_, ?_, ?_, ?_⟩
  · have hv_in : v_star ∈ Δ' \ subBd Δ' := hv_star_in rfl
    intro hv_Δ
    rcases hΔ_eq ▸ hv_Δ with ⟨_, hv_not_Δ'⟩ | hv_bd
    · exact hv_not_Δ' hv_in.1
    · exact hv_in.2 hv_bd
  · intro p hp_compl
    have hp_D : p ∈ D_disc := h83.hyp_xii.2.2 (hcompl_r₀ hp_compl)
    rw [hΔ_eq]
    by_cases hp_in : p ∈ Δ' \ subBd Δ'
    · obtain ⟨a, ha, hpa⟩ := GM11.exists_atom Γ p
      have hd_le : d {v_star} a ≤ θ' + 2 := hΔ'_le a ha ⟨p, hpa, hp_in.1⟩
      have hd_ge : θ ≤ d {v_star} a :=
        h83.hyp_xiv.2.trans
          (subsetTangleDist_le_of_mem hv_star_A ha ⟨v_star, rfl, rfl⟩ ⟨p, hpa, hp_D⟩)
      omega
    · by_cases hp_Δ' : p ∈ Δ'
      · exact Or.inr (by_contra fun h => hp_in ⟨hp_Δ', h⟩)
      · exact Or.inl ⟨mem_univ p, hp_Δ'⟩
  · refine le_subsetTangleDist_of_forall (by omega) fun a ha b hb hav hbΔ => ?_
    have ha_eq : a = {v_star} := GM12.atom_eq_of_inter_nonempty ha hv_star_A hav
    subst ha_eq
    refine hΔ'_ge b hb ?_
    intro hb_sub
    rcases hbΔ with ⟨p, hpb, hpΔ⟩
    have hp_in : p ∈ Δ' \ subBd Δ' := hb_sub hpb
    rcases hΔ_eq ▸ hpΔ with ⟨_, hp_not⟩ | hp_bd
    · exact hp_not hp_in.1
    · exact hp_in.2 hp_bd
  · intro x hx hx_not
    rw [hΔ_int_eq] at hx_not
    obtain ⟨p, hpx, hp_not_sdiff⟩ := not_subset.mp hx_not
    have hp_Δ' : p ∈ Δ' := by_contra fun h => hp_not_sdiff ⟨mem_univ p, h⟩
    exact hΔ'_le x hx ⟨p, hpx, hp_Δ'⟩

/-- **Claim (10) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 562):
"(10) $d(D, \Sigma \setminus \Delta) \ge \theta - \theta' - 2$, and in particular,
$D \subseteq \Delta$." -/
theorem lemma_8_3_claim_10
    {q δ h θ θ' : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hθ_gt : θ' + 3 ≤ θ)
    {Δ : Set S}
    (hc9 : ∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → d {v_star} x ≤ θ' + 2) :
    θ - θ' - 2 ≤ subsetTangleDist Γ ord d D_disc (Set.univ \ Δ) ∧ D_disc ⊆ Δ := by
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have hv_star : v_star ∈ Γ.V := h83.hyp_xiv.1.1
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hv_star, rfl⟩)
  have hθ_ord := h83.hyp_iv.1
  have hdist : θ - θ' - 2 ≤ subsetTangleDist Γ ord d D_disc (Set.univ \ Δ) := by
    refine le_subsetTangleDist_of_forall (by omega) fun a ha x hx haD hx_compl => ?_
    obtain ⟨p, hpx, _, hp_not_Δ⟩ := hx_compl
    have hx_not_int : ¬ (x ⊆ Δ \ subBd Δ) := fun h => hp_not_Δ (h hpx).1
    have hd_vx : d {v_star} x ≤ θ' + 2 := hc9 x hx hx_not_int
    have hd_va : θ ≤ d {v_star} a :=
      h83.hyp_xiv.2.trans (subsetTangleDist_le_of_mem hv_star_A ha ⟨v_star, rfl, rfl⟩ haD)
    have htri : d {v_star} a ≤ d {v_star} x + d x a :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hv_star_A hx ha
    have hcomm : d x a = d a x := HasTangleMetric.comm h83.hyp_iv.2.1 hx ha
    omega
  have hsub : D_disc ⊆ Δ :=
    subset_of_one_le_subsetTangleDist_compl h83.hyp_iv.2.1 (by omega)
  exact ⟨hdist, hsub⟩

/-- **Claim (11) of Theorem (8.3)** (Graph Minors XXII, Section 8, page 562):
"(11) $d(v, \Sigma \setminus \Delta) \ge \theta'$ for all $v \in V(\Gamma \cap K)$, and
$d(D(A), \Sigma \setminus \Delta) \ge \theta'$ for all $A \in \mathcal{A}'$ with
$A \cap K \ne N_W$." -/
theorem lemma_8_3_claim_11
    {q δ h θ θ' : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hord : 5 ≤ ord)
    (hθ_bound : 2 * θ' + 13 ≤ θ)
    {Δ₀ Δ : Set S} (hΔ₀ : IsClosedDisc Δ₀) (hcompl_r₀ : Set.univ \ Δ₀ ⊆ r₀)
    {D : Graph α β → Set S}
    (hD_disc : ∀ A ∈ 𝒜, IsClosedDisc (D A))
    (hD_norm : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.U ⊆ Γ.V)
    (hα_bdA : ∀ A ∈ 𝒜, ∀ v ∈ Set.range (πA A), ∃ p ∈ subBd (D A),
      ∀ A' ∈ 𝒜, v ∈ Set.range (πA A') → p ∈ subBd (D A'))
    (hD_bdV : ∀ A ∈ 𝒜, subBd (D A) ∩ Γ.V = {v ∈ Γ.V | ιV v ∈ Set.range (πA A)})
    (hD_interV : ∀ A ∈ 𝒜, (Γ.interSet (D A)).V = {v ∈ Γ.V | ιV v ∈ V(A)})
    (hins : ∀ A ∈ 𝒜, IsTangleIns Γ T (subBd (D A)) (D A))
    (hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D A).Nonempty)
    {K₀ : Graph α β}
    (hsep_K₀ : IsGraphSeparation R_G.G.toGraph J K₀)
    (hinter_K₀ : V(J) ∩ V(K₀) = (ιV '' C₀.V) ∪ W)
    (hc10 : θ - θ' - 2 ≤ subsetTangleDist Γ ord d D_disc (Set.univ \ Δ)) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    let K := graphUnion K₀
      (subgraphSUnion R_G.G.toGraph ((fun A => A.deleteEdges E((Γ.toEmbeddedGraph ιV ιE) ⊓ A)) '' (𝒜 \ 𝒜')))
    (∀ v ∈ Γ.V, ιV v ∈ V(K) → θ' ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ)) ∧
    (∀ A ∈ 𝒜', A ⊓ K ≠ Graph.noEdge W β →
      θ' ≤ subsetTangleDist Γ ord d (D A) (Set.univ \ Δ)) := by
  intro 𝒜' K
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  let G := R_G.G.toGraph
  let Γ_emb := Γ.toEmbeddedGraph ιV ιE
  let N := graphUnion (graphUnion Γ_emb (Graph.noEdge W β)) (subgraphSUnion G 𝒜')
  obtain ⟨_, _, _, hc8_dist⟩ :=
    lemma_8_3_claim_8 h83 hord hΔ₀ hcompl_r₀ hD_disc hD_norm hD_bdV hD_interV hins hc6 hsep_K₀ hinter_K₀
  have hcompl_sub_D : Set.univ \ Δ₀ ⊆ D_disc := hcompl_r₀.trans h83.hyp_xii.2.2
  have hθ_ord := h83.hyp_iv.1
  have hle_ord_atom : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, d a b ≤ ord :=
    fun a ha b hb => HasTangleMetric.le_ord h83.hyp_iv.2.1 ha hb
  obtain ⟨Δ_c, hΔc_disc, _, _, hΔc_int⟩ :=
    exists_complementary_closedDisc_in_sphere h83.hyp_i.1 hΔ₀
  have hbd_c : subBd Δ_c = discBd Δ_c := GM14.IsClosedDisc.subBd_eq_discBd hS hΔc_disc
  obtain ⟨_, g_c, hc_chart⟩ := hΔc_disc.exists_isChart
  have hp₀_compl : g_c 0 ∈ Set.univ \ Δ₀ := by
    rw [← hΔc_int, hbd_c]
    refine ⟨hc_chart.gm (Metric.mem_closedBall_self zero_le_one), ?_⟩
    rw [← hc_chart.g_sphere]
    rintro ⟨w, hw, heq⟩
    have h0w : w = 0 := hc_chart.injOn (sphere_subset_closedBall hw)
      (Metric.mem_closedBall_self zero_le_one) heq
    rw [h0w] at hw
    simp at hw
  have hp₀_r₀ : g_c 0 ∈ r₀ := hcompl_r₀ hp₀_compl
  have hp₀_D : g_c 0 ∈ D_disc := hcompl_sub_D hp₀_compl
  have hr₀A : r₀ ∈ Γ.A := Or.inr h83.hyp_ii.2.2.1
  refine ⟨?_, ?_⟩
  · -- Part 1: `v ∈ Γ.V` with `ιV v ∈ V(K)`.
    intro v hvV hvK
    have hv_N : ιV v ∈ V(N) := by
      simp only [N, vertexSet_graphUnion]
      exact Or.inl (Or.inl ⟨v, hvV, rfl⟩)
    have hv_not_W : ιV v ∉ W := by
      have hv_del : ιV v ∈ V(J.deleteVerts W) :=
        (Γ_le_J_8_3 h83).1.vertexSet_mono ⟨v, hvV, rfl⟩
      rw [Graph.vertexSet_deleteVerts] at hv_del
      exact hv_del.2
    have hd_v_compl : subsetTangleDist Γ ord d {v} (Set.univ \ Δ₀) ≤ 8 :=
      hc8_dist v hvV ⟨⟨hvK, hv_N⟩, hv_not_W⟩
    have hd_vr₀ : d {v} r₀ ≤ 8 := by
      rwa [← (subsetTangleDist_compl_Δ₀_eq_r₀ h83 hΔ₀ hcompl_r₀).2 v hvV]
    have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hvV, rfl⟩)
    refine le_subsetTangleDist_of_forall (by omega) fun a ha b hb hav hb_compl => ?_
    have ha_eq : a = {v} := GM12.atom_eq_of_inter_nonempty ha hvA hav
    subst ha_eq
    have hd_r₀b : θ - θ' - 2 ≤ d r₀ b :=
      hc10.trans (subsetTangleDist_le_of_mem hr₀A hb ⟨g_c 0, hp₀_r₀, hp₀_D⟩ hb_compl)
    have htri : d r₀ b ≤ d r₀ {v} + d {v} b :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hr₀A hvA hb
    have hcomm : d r₀ {v} = d {v} r₀ := HasTangleMetric.comm h83.hyp_iv.2.1 hr₀A hvA
    omega
  · -- Part 2: `A ∈ 𝒜'` with `A ⊓ K ≠ Graph.noEdge W β`.
    intro A hA' hne_NW
    have hA : A ∈ 𝒜 := hA'.1
    have hc7 : A ⊓ K₀ = Graph.noEdge W β :=
      lemma_8_3_claim_7 h83 (by omega) hD_disc hD_norm hD_bdV hD_interV hins hc6 hsep_K₀ hinter_K₀ A hA'
    have hZdiv : IsZDivision J (Z ∪ W) 𝒜 := h83.hyp_vi.2.2.1
    have hA_le_G : ∀ B ∈ 𝒜, B ≤ G := fun B hB => (hZdiv.2.1 B hB).trans hsep_K₀.1
    let remPiece (B : Graph α β) : Graph α β := B.deleteEdges E(Γ_emb ⊓ B)
    have hrem_le_G : ∀ B ∈ remPiece '' (𝒜 \ 𝒜'), B ≤ G := by
      rintro _ ⟨B, hB, rfl⟩
      exact Graph.deleteEdges_le.trans (hA_le_G B hB.1)
    have hK_le_G : K ≤ G := graphUnion_le hsep_K₀.2.1 (subgraphSUnion_le hrem_le_G)
    -- Show there is `A' ∈ 𝒜 \ 𝒜'` and `x ∈ (V(A) ∩ V(A')) \ W`.
    have hex_A' : ∃ A' ∈ 𝒜 \ 𝒜', ∃ x ∈ Z, x ∈ V(A) ∧ x ∈ V(A') := by
      by_contra! hno
      apply hne_NW
      have hW_sub_AK : W ⊆ V(A ⊓ K) := by
        have hW_A : W ⊆ V(A) := h83.hyp_vi.2.2.2 A hA
        have hW_K₀ : W ⊆ V(K₀) := by
          have : W ⊆ V(J) ∩ V(K₀) := hinter_K₀.symm ▸ subset_union_right
          exact this.trans inter_subset_right
        exact subset_inter hW_A (hW_K₀.trans (le_graphUnion_left K₀ _).vertexSet_mono)
      have hV_sub_W : V(A ⊓ K) ⊆ W := by
        rintro x ⟨hxA, hxK⟩
        simp only [K, vertexSet_graphUnion, vertexSet_subgraphSUnion] at hxK
        rcases hxK with hxK₀ | hxRem
        · have hx_AK₀ : x ∈ V(A ⊓ K₀) := ⟨hxA, hxK₀⟩
          rw [hc7] at hx_AK₀
          exact hx_AK₀
        · obtain ⟨_, ⟨A', hA'diff, rfl⟩, hxA'⟩ := mem_iUnion₂.mp hxRem
          have hne_AA' : A ≠ A' := fun heq => hA'diff.2 (heq ▸ hA')
          have hx_ZW : x ∈ Z ∪ W := (hZdiv.2.2.2 A hA A' hA'diff.1 hne_AA').2 ⟨hxA, hxA'⟩
          rcases hx_ZW with hxZ | hxW
          · exact False.elim (hno A' hA'diff x hxZ hxA hxA')
          · exact hxW
      have hE_emp : E(A ⊓ K) = ∅ := by
        rw [(Compatible.of_le_le (hA_le_G A hA) hK_le_G).edgeSet_inf]
        ext e
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        intro heA heK
        change e ∈ E(graphUnion K₀ (subgraphSUnion G (remPiece '' (𝒜 \ 𝒜')))) at heK
        rw [edgeSet_graphUnion, edgeSet_subgraphSUnion hrem_le_G] at heK
        rcases heK with heK₀ | heRem
        · exact disjoint_left.mp hsep_K₀.2.2.2.2 ((hZdiv.2.1 A hA).edgeSet_mono heA) heK₀
        · obtain ⟨_, ⟨A', hA'diff, rfl⟩, heA'_rem⟩ := mem_iUnion₂.mp heRem
          have hne_AA' : A ≠ A' := fun heq => hA'diff.2 (heq ▸ hA')
          exact disjoint_left.mp (hZdiv.2.2.2 A hA A' hA'diff.1 hne_AA').1 heA heA'_rem.1
      refine Graph.ext (Subset.antisymm hV_sub_W hW_sub_AK) fun e x y => ?_
      simp only [Graph.noEdge_isLink, iff_false]
      intro hlk
      have he : e ∈ E(A ⊓ K) := hlk.edge_mem
      rw [hE_emp] at he
      exact he
    obtain ⟨A', ⟨hA'_mem, hA'_not'⟩, x, hxZ, hxA, hxA'⟩ := hex_A'
    have hx_range_A : x ∈ Set.range (πA A) := (h83.hyp_vii A hA).2.2.symm ▸ ⟨hxZ, hxA⟩
    have hx_range_A' : x ∈ Set.range (πA A') := (h83.hyp_vii A' hA'_mem).2.2.symm ▸ ⟨hxZ, hxA'⟩
    obtain ⟨p_x, hp_bdA, hp_bd_all⟩ := hα_bdA A hA x hx_range_A
    have hp_DA : p_x ∈ D A :=
      GM14.Whitney.subBd_subset_of subset_rfl (hD_disc A hA).isClosed hp_bdA
    have hp_DA' : p_x ∈ D A' :=
      GM14.Whitney.subBd_subset_of subset_rfl (hD_disc A' hA'_mem).isClosed
        (hp_bd_all A' hA'_mem hx_range_A')
    obtain ⟨y_atom, hy_atom, hpy⟩ := GM11.exists_atom Γ p_x
    have hd_y_vA' : d y_atom {vA A'} ≤ 3 :=
      ((dist_vA_atom_meets_DA_le_three h83 (by omega) hD_disc hD_norm hD_bdV hD_interV hins hc6 hA'_mem).2.1
        y_atom hy_atom ⟨p_x, hpy, hp_DA'⟩).2
    have hvA'_V : vA A' ∈ Γ.V := (h83.hyp_xi A' hA'_mem).1
    have hvA'_atom : ({vA A'} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨vA A', hvA'_V, rfl⟩)
    have hlt_5 : subsetTangleDist Γ ord d {vA A'} C₀.V < 5 :=
      not_le.mp fun hge => hA'_not' ⟨hA'_mem, hge⟩
    have hd_vA'_r₀ : d {vA A'} r₀ ≤ 5 :=
      (dist_compl_Δ₀_le_five_of_dist_C₀_lt_five h83 hord hΔ₀ hcompl_r₀ hvA'_V hlt_5).1
    have hdist_A_3 :=
      (dist_vA_atom_meets_DA_le_three h83 (by omega) hD_disc hD_norm hD_bdV hD_interV hins hc6 hA).1
    refine le_subsetTangleDist_of_forall (by omega) fun z hz b hb hzDA hb_compl => ?_
    have hd_zy : d z y_atom ≤ 3 := hdist_A_3 z hz y_atom hy_atom hzDA ⟨p_x, hpy, hp_DA⟩
    have hd_r₀b : θ - θ' - 2 ≤ d r₀ b :=
      hc10.trans (subsetTangleDist_le_of_mem hr₀A hb ⟨g_c 0, hp₀_r₀, hp₀_D⟩ hb_compl)
    have htri₁ : d r₀ b ≤ d r₀ {vA A'} + d {vA A'} b :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hr₀A hvA'_atom hb
    have htri₂ : d {vA A'} b ≤ d {vA A'} y_atom + d y_atom b :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hvA'_atom hy_atom hb
    have htri₃ : d y_atom b ≤ d y_atom z + d z b :=
      HasTangleMetric.triangle hS h83.hyp_iv.2.1 hy_atom hz hb
    have hc1 : d r₀ {vA A'} = d {vA A'} r₀ := HasTangleMetric.comm h83.hyp_iv.2.1 hr₀A hvA'_atom
    have hc2 : d {vA A'} y_atom = d y_atom {vA A'} :=
      HasTangleMetric.comm h83.hyp_iv.2.1 hvA'_atom hy_atom
    have hc3 : d y_atom z = d z y_atom := HasTangleMetric.comm h83.hyp_iv.2.1 hy_atom hz
    omega

end GraphMinor.GM22
