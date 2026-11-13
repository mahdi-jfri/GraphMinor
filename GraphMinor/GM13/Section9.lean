module

public import GraphMinor.GM13.Section8
public import GraphMinor.GM13.Section9b

/-!
# Graph Minors XIII, Section 9: Finding a Flat Section of a Wall ((9.6)–(9.9))

This file completes the formalization of Section 9 ("Finding a Flat Section of a Wall") of
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 97–106):

- `theorem_9_7` and `theorem_9_6` ((9.6)–(9.7), page 103): Given a wall `H` of height `h'` in `G`,
  finding either a `K_p`-model in `G` or a set `X ⊆ V(G)` with `|X| < binom(p, 2)` and `s` mutually
  vertex-disjoint subwalls `H₁, …, H_s` of `H` of height `h`, each flat and dividing in
  `(G \ X) ∪ H` and disjoint from `X`.
- `theorem_9_9`, `theorem_9_8`, and `theorem_9_8_parallel` ((9.8)–(9.9), pages 103–106): Given a
  graph `G`, finding either a branch-decomposition of `G` of width `≤ ω`, a `K_p`-model in `G`, or
  a vertex set `X ⊆ V(G)` with `|X| < binom(p, 2)`, a flat wall `H` of height `h` in `G \ X`, a
  rural division `𝒜` of the society of `H` in `G \ X`, and a branch-decomposition of width `≤ ω`
  of each interior member of `𝒜`.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph
open GraphMinor
open GraphMinor.Surface
open GraphMinor.GM09
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

/-! ## Disjoint Subset Selection and Cross Monotonicity Helpers -/

/-- If `J : Finset ι` indexes pairwise disjoint sets `S i : Set α` and `X : Set α` is finite, then
at most `X.ncard` indices `i ∈ J` have `S i` intersecting `X`, so at least `J.card - X.ncard`
indices `i ∈ J` satisfy `Disjoint (S i) X`. -/
theorem card_filter_disjoint_ge {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (S : ι → Set α)
    (hdisj : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (S i) (S j))
    {X : Set α} (hX : X.Finite) :
    J.card - X.ncard ≤ (J.filter (fun i => Disjoint (S i) X)).card := by
  let J_miss := J.filter (fun i => Disjoint (S i) X)
  let J_hit := J.filter (fun i => ¬ Disjoint (S i) X)
  have hsum : J_miss.card + J_hit.card = J.card :=
    Finset.card_filter_add_card_filter_not (fun i => Disjoint (S i) X)
  have hhit_le : J_hit.card ≤ X.ncard := by
    have hex : ∀ i : J_hit, ∃ x ∈ S i.1, x ∈ X := by
      intro i
      exact Set.not_disjoint_iff.mp (Finset.mem_filter.mp i.2).2
    let x_of (i : J_hit) : hX.toFinset :=
      ⟨Classical.choose (hex i), hX.mem_toFinset.mpr (Classical.choose_spec (hex i)).2⟩
    have hx_inj : Function.Injective x_of := by
      intro i₁ i₂ heq
      by_contra hne
      have hne_val : i₁.1 ≠ i₂.1 := Subtype.coe_ne_coe.mpr hne
      have hi₁J : i₁.1 ∈ J := (Finset.mem_filter.mp i₁.2).1
      have hi₂J : i₂.1 ∈ J := (Finset.mem_filter.mp i₂.2).1
      have hx₁ : (x_of i₁).1 ∈ S i₁.1 := (Classical.choose_spec (hex i₁)).1
      have hx₂ : (x_of i₁).1 ∈ S i₂.1 := by
        rw [Subtype.ext_iff.mp heq]
        exact (Classical.choose_spec (hex i₂)).1
      exact Set.disjoint_left.mp (hdisj i₁.1 hi₁J i₂.1 hi₂J hne_val) hx₁ hx₂
    have hcard := Fintype.card_le_of_injective x_of hx_inj
    simp only [Fintype.card_coe] at hcard
    rw [Set.ncard_eq_toFinset_card X hX]
    exact hcard
  change J.card - X.ncard ≤ J_miss.card
  omega

/-- Monotonicity of `IsCrossOverWall` with respect to the ambient graph `G' ≤ G`. -/
theorem IsCrossOverWall.mono {G' G : Graph α β} {W : Wall α β} {P Q : Graph α β}
    (hle : G' ≤ G) (h : IsCrossOverWall G' W P Q) :
    IsCrossOverWall G W P Q :=
  ⟨h.1, h.2.1.mono hle, h.2.2.mono hle⟩

/-! ## (9.6) and Algorithm (9.7): Finding Flat Dividing Subwalls (page 103) -/

/-- **Graph Minors XIII, Algorithm (9.7)** (page 103):
"(9.7) Algorithm.
*Input:* A graph $G$, and a wall $H$ in $G$ of height $h'$.
*Output:* Either
(i) a model of $K_p$ in $G$, or
(ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and $s$ subwalls $H_1, \dots, H_s$ of $H$
of height $h$, mutually vertex-disjoint, and each flat and dividing in $(G \setminus X) \cup H$, and
each disjoint from $X$."

Given `(k₁, r₁)` from (9.3) (`theorem_9_3_proof p`) and `(k₂, r₂)` from (9.1) (`theorem_9_1_proof p`), for any
wall `H` in `G` of height
`h' = 2 * ((s + k₁ + k₂ + p.choose 2 + 1) * (h + max r₁ (max r₂ 1) + 4) + p ^ 2 + 2)`, we construct
a Fig. 1 plane drawing `H_drawn` of `H` (`H.exists_drawnWall_isFigure1`) and
`t = s + k₁ + k₂ + p.choose 2` proper subwalls `H_sub` of `H` of height `h` at pairwise distance
`≥ max r₁ (max r₂ 1)` (`DrawnWall.IsFigure1.exists_subwalls_far_apart`), apply (9.3)/(9.4), test
flatness of the dividing subwalls via (8.1), and either obtain a `K_p`-model by (9.5) and (9.1) or
select `s` flat dividing subwalls disjoint from `X`. -/
theorem theorem_9_7_proof
    {p s h : ℕ} (h2 : 2 ≤ h) (heven : Even h)
    {G : Graph α β} {H : Wall α β}
    (hHG : H.graph ≤ G)
    (hHh : H.height =
      let k₁ := Classical.choose.{1} (theorem_9_3_proof.{u, v} p)
      let r₁ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_3_proof.{u, v} p))
      let k₂ := Classical.choose.{1} (theorem_9_1_proof.{u, v} p)
      let r₂ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_1_proof.{u, v} p))
      2 * ((s + k₁ + k₂ + p.choose 2 + 1) *
        (h + max r₁ (max r₂ 1) + 4) + p ^ 2 + 2)) :
    HasGraphModel (GM16.completeGraph p) G ∨
      ∃ (X : Set α) (H_flat : Fin s → Wall α β),
        X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
        Pairwise (fun a b : Fin s => Disjoint V((H_flat a).graph) V((H_flat b).graph)) ∧
        ∀ a : Fin s,
          IsProperSubwallOf (H_flat a) H ∧
          (H_flat a).height = h ∧
          IsFlatWallIn (subgraphUnion G (G.induce (V(G) \ X)) H.graph) (H_flat a) ∧
          IsDividingSubwall (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H (H_flat a) ∧
          Disjoint V((H_flat a).graph) X := by
  let k₁ := Classical.choose.{1} (theorem_9_3_proof.{u, v} p)
  let r₁ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_3_proof.{u, v} p))
  let k₂ := Classical.choose.{1} (theorem_9_1_proof.{u, v} p)
  let r₂ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_1_proof.{u, v} p))
  let t := s + k₁ + k₂ + p.choose 2
  let r := max r₁ (max r₂ 1)
  -- Construct a Fig. 1 plane drawing `H_drawn` of `H` and `t` subwalls `H_sub` of height `h`
  obtain ⟨H_drawn, hH_eq, hfig⟩ := H.exists_drawnWall_isFigure1
  have hG_eq : H_drawn.graph = H.graph := congrArg Wall.graph hH_eq
  have hHG_drawn : H_drawn.graph ≤ G := by simpa [hG_eq] using hHG
  have hh'_bound : (t + 1) * (2 * h + 2 * r + 8) ≤ H_drawn.height := by
    have hH_height_eq : H_drawn.height = H.height := congrArg Wall.height hH_eq
    rw [hH_height_eq, hHh]
    change (s + k₁ + k₂ + p.choose 2 + 1) * (2 * h + 2 * max r₁ (max r₂ 1) + 8) ≤
      2 * ((s + k₁ + k₂ + p.choose 2 + 1) * (h + max r₁ (max r₂ 1) + 4) + p ^ 2 + 2)
    have hlin : (s + k₁ + k₂ + p.choose 2 + 1) *
        (2 * h + 2 * max r₁ (max r₂ 1) + 8) =
      2 * ((s + k₁ + k₂ + p.choose 2 + 1) *
        (h + max r₁ (max r₂ 1) + 4)) := by ring
    omega
  obtain ⟨H_sub, hsub_isSub, hsub_height, hdist⟩ :=
    hfig.exists_subwalls_far_apart t r h h2 heven hh'_bound
  have hsub_proper : ∀ i : Fin t, IsProperSubwallOf (H_sub i) H := by
    intro i
    have hsub_H : (H_sub i).IsSubwallOf H := hH_eq ▸ hsub_isSub i
    exact hsub_H.toIsProperSubwallOf
  have hdist_r₁ : ∀ i j : Fin t, i ≠ j →
      r₁ ≤ wallSubgraphDist H_drawn (H_sub i).graph (H_sub j).graph :=
    fun i j hij => (le_max_left r₁ _).trans (hdist i j hij)
  have hdist_r₂ : ∀ i j : Fin t, i ≠ j →
      r₂ ≤ wallSubgraphDist H_drawn (H_sub i).graph (H_sub j).graph :=
    fun i j hij => ((le_max_left r₂ 1).trans (le_max_right r₁ _)).trans (hdist i j hij)
  have hdisj_sub : ∀ i j : Fin t, i ≠ j → Disjoint V((H_sub i).graph) V((H_sub j).graph) := by
    intro i j hij
    refine disjoint_of_pos_wallSubgraphDist (W := H_drawn) ?_
    have hr_le := hdist i j hij
    have hr_pos : 1 ≤ r := (le_max_right r₂ 1).trans (le_max_right r₁ _)
    omega
  -- Step 1: Apply (9.3) / (9.4)
  rcases Classical.choose_spec.{1} (Classical.choose_spec.{1} (theorem_9_3_proof.{u, v} p))
      H_sub hfig hHG_drawn hsub_isSub hdist_r₁ with
    hModel | ⟨X, I, hX_sub, hX_fin, hX_card, hI_card, hI_div⟩
  · exact Or.inl hModel
  · let G' := subgraphUnion G (G.induce (V(G) \ X)) H.graph
    have hle_ind : G.induce (V(G) \ X) ≤ G := G.induce_le sdiff_subset
    have hG'_le : G' ≤ G := subgraphUnion_le hle_ind hHG
    have hHG' : H.graph ≤ G' := le_subgraphUnion_right hle_ind hHG
    have hHG'_drawn : H_drawn.graph ≤ G' := by rwa [hG_eq]
    have hI_div' : ∀ i ∈ I, IsDividingSubwall G' H (H_sub i) := by
      intro i hi
      simpa [G', hH_eq, hG_eq] using hI_div i hi
    -- Step 2: Partition `I` into subwalls with a cross in their compass in `G'` and flat subwalls
    let I_cross := I.filter (fun i =>
      ∃ P Q : Graph α β, IsCrossOverWall (wallCompass G' (H_sub i)) (H_sub i) P Q)
    let I_flat := I.filter (fun i =>
      ¬ ∃ P Q : Graph α β, IsCrossOverWall (wallCompass G' (H_sub i)) (H_sub i) P Q)
    have hI_part : I_cross.card + I_flat.card = I.card :=
      Finset.card_filter_add_card_filter_not _
    by_cases hcross_ge : k₂ ≤ I_cross.card
    · -- Step 3a: At least `k₂` subwalls have crosses in their compasses; apply (9.5) and (9.1)
      let embC : Fin k₂ ↪ I_cross :=
        (Fin.castLEEmb hcross_ge).trans I_cross.equivFin.symm.toEmbedding
      let emb : Fin k₂ ↪ Fin t := embC.trans (Function.Embedding.subtype _)
      have hemb_cross : ∀ a : Fin k₂,
          ∃ P Q : Graph α β,
            IsCrossOverWall (wallCompass G' (H_sub (emb a))) (H_sub (emb a)) P Q :=
        fun a => (Finset.mem_filter.mp (embC a).2).2
      have hemb_div : ∀ a : Fin k₂, IsDividingSubwall G' H (H_sub (emb a)) :=
        fun a => hI_div' (emb a) (Finset.mem_filter.mp (embC a).2).1
      let P : Fin k₂ → Graph α β := fun a => Classical.choose (hemb_cross a)
      let Q : Fin k₂ → Graph α β :=
        fun a => Classical.choose (Classical.choose_spec (hemb_cross a))
      have hPQ_spec : ∀ a : Fin k₂,
          IsCrossOverWall (wallCompass G' (H_sub (emb a))) (H_sub (emb a)) (P a) (Q a) :=
        fun a => Classical.choose_spec (Classical.choose_spec (hemb_cross a))
      have hsub_le_G' : ∀ a : Fin k₂, (H_sub (emb a)).graph ≤ G' :=
        fun a => (hsub_proper (emb a)).graph_le.trans hHG'
      have hK_le_G' : ∀ a : Fin k₂, wallCompass G' (H_sub (emb a)) ≤ G' :=
        fun a => wallCompass_le (hsub_le_G' a)
      have hPQ_G' : ∀ a : Fin k₂, IsCrossOverWall G' (H_sub (emb a)) (P a) (Q a) :=
        fun a => (hPQ_spec a).mono (hK_le_G' a)
      have hPQ_sub_K : ∀ a : Fin k₂,
          V(P a) ∪ V(Q a) ⊆ V(wallCompass G' (H_sub (emb a))) := by
        intro a
        exact union_subset (hPQ_spec a).2.1.le.vertexSet_mono (hPQ_spec a).2.2.le.vertexSet_mono
      have hinter_H : ∀ a : Fin k₂,
          (V(P a) ∪ V(Q a)) ∩ V(H_drawn.graph) ⊆ V((H_sub (emb a)).graph) := by
        intro a
        rw [hG_eq]
        exact (inter_subset_inter_left _ (hPQ_sub_K a)).trans
          (compass_inter_wall_vertexSet_subset hHG' (hsub_proper (emb a)) (hemb_div a))
      have hdisj_PQ : Pairwise (fun a b : Fin k₂ =>
          Disjoint (V(P a) ∪ V(Q a)) (V(P b) ∪ V(Q b))) := by
        intro a b hab
        have hdisj_K :
            Disjoint V(wallCompass G' (H_sub (emb a))) V(wallCompass G' (H_sub (emb b))) :=
          disjoint_compass_of_dividingSubwalls hHG'
            (hsub_proper (emb a)) (hsub_proper (emb b))
            (hemb_div a) (hemb_div b)
            (hdisj_sub (emb a) (emb b) (emb.injective.ne hab))
        exact hdisj_K.mono (hPQ_sub_K a) (hPQ_sub_K b)
      have hModel_G' : HasGraphModel (GM16.completeGraph p) G' :=
        Classical.choose_spec.{1} (Classical.choose_spec.{1} (theorem_9_1_proof.{u, v} p)) G' H_drawn
          (fun a => H_sub (emb a)) P Q
          hfig hHG'_drawn
          (fun a => hsub_isSub (emb a))
          (fun a b hab => hdist_r₂ (emb a) (emb b) (emb.injective.ne hab))
          hPQ_G' hinter_H hdisj_PQ
      exact Or.inl (hModel_G'.mono_right hG'_le)
    · -- Step 3b: Fewer than `k₂` subwalls have crosses; choose `s` flat dividing subwalls missing `X`
      have hflat_ge : s + p.choose 2 ≤ I_flat.card := by omega
      let I_good := I_flat.filter (fun i => Disjoint V((H_sub i).graph) X)
      have hgood_card : I_flat.card - X.ncard ≤ I_good.card :=
        card_filter_disjoint_ge I_flat (fun i => V((H_sub i).graph))
          (fun i _ j _ hij => hdisj_sub i j hij) hX_fin
      have hs_le_good : s ≤ I_good.card := by omega
      let embG : Fin s ↪ I_good :=
        (Fin.castLEEmb hs_le_good).trans I_good.equivFin.symm.toEmbedding
      let emb : Fin s ↪ Fin t := embG.trans (Function.Embedding.subtype _)
      refine Or.inr ⟨X, fun a => H_sub (emb a), hX_sub, hX_fin, hX_card, ?_, ?_⟩
      · intro a b hab
        exact hdisj_sub (emb a) (emb b) (emb.injective.ne hab)
      · intro a
        have ha_good := Finset.mem_filter.mp (embG a).2
        have ha_flat := Finset.mem_filter.mp ha_good.1
        have ha_I : emb a ∈ I := ha_flat.1
        have hsub_le_G' : (H_sub (emb a)).graph ≤ G' :=
          (hsub_proper (emb a)).graph_le.trans hHG'
        exact ⟨hsub_proper (emb a), hsub_height (emb a),
          ⟨hsub_le_G', ha_flat.2⟩,
          hI_div' (emb a) ha_I,
          ha_good.2⟩

/-- **Graph Minors XIII, (9.6)** (page 103):
"For any $p, s \ge 0$ and $h \ge 2$, even, there exists $h' \ge p^2 + 2$, even, and an algorithm as
in (9.7) with running time $O(v\varepsilon)$ for fixed $p, s, h$." -/
theorem theorem_9_6_proof
    (p s h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    ∃ h' : ℕ,
      p ^ 2 + 2 ≤ h' ∧ Even h' ∧
      ∀ {α : Type u} {β : Type v} {G : Graph α β} {H : Wall α β},
        H.graph ≤ G →
        H.height = h' →
        HasGraphModel (GM16.completeGraph p) G ∨
          ∃ (X : Set α) (H_flat : Fin s → Wall α β),
            X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
            Pairwise (fun a b : Fin s => Disjoint V((H_flat a).graph) V((H_flat b).graph)) ∧
            ∀ a : Fin s,
              IsProperSubwallOf (H_flat a) H ∧
              (H_flat a).height = h ∧
              IsFlatWallIn (subgraphUnion G (G.induce (V(G) \ X)) H.graph) (H_flat a) ∧
              IsDividingSubwall (subgraphUnion G (G.induce (V(G) \ X)) H.graph) H (H_flat a) ∧
              Disjoint V((H_flat a).graph) X := by
  let k₁ := Classical.choose.{1} (theorem_9_3_proof.{u, v} p)
  let r₁ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_3_proof.{u, v} p))
  let k₂ := Classical.choose.{1} (theorem_9_1_proof.{u, v} p)
  let r₂ := Classical.choose.{1} (Classical.choose_spec.{1} (theorem_9_1_proof.{u, v} p))
  let t := s + k₁ + k₂ + p.choose 2
  let r := max r₁ (max r₂ 1)
  let h' := 2 * ((t + 1) * (h + r + 4) + p ^ 2 + 2)
  have hh'_ge : p ^ 2 + 2 ≤ h' := by dsimp [h']; omega
  have hh'_even : Even h' := ⟨(t + 1) * (h + r + 4) + p ^ 2 + 2, by ring⟩
  refine ⟨h', hh'_ge, hh'_even, ?_⟩
  intro α β G H hHG hHh
  exact theorem_9_7_proof h2 heven hHG hHh

/-! ## Wall Society, Compass Invariance, and Graph Size Bounds for (9.8)–(9.9) -/

/-- The size parameter `ε(G) = |E(G)| + |V(G)| + 1` of a graph `G`
(Graph Minors XIII, Section 9, page 105: "we recall that by definition,
$\varepsilon(G) = |E(G)| + |V(G)| + 1$"). -/
noncomputable def graphSize (G : Graph α β) : ℕ :=
  E(G).ncard + V(G).ncard + 1

/-- Canonical society `(K, Ω)` of a wall `W` in a finite graph `G` (`W.graph ≤ G`), where
`K = wallCompass G W` and `Ω = wallCornerCyclicPerm W` (Graph Minors XIII, pages 103–104). -/
noncomputable def wallSociety {G : Graph α β} {W : Wall α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hW : W.graph ≤ G) : Society α β where
  G := wallCompass G W
  Ω := wallCornerCyclicPerm W
  finite_V := hVG.subset (wallCompass_le hW).vertexSet_mono
  finite_E := hEG.subset (wallCompass_le hW).edgeSet_mono
  bar_subset := by
    rintro _ ⟨k, rfl⟩
    exact wall_vertexSet_subset_wallCompass hW (W.corner_mem_vertexSet k)

/-- `wallSociety hVG hEG hW` satisfies `IsWallSociety G W`. -/
theorem isWallSociety_wallSociety {G : Graph α β} {W : Wall α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hW : W.graph ≤ G) :
    IsWallSociety G W (wallSociety hVG hEG hW) :=
  ⟨rfl, rfl⟩

/-- For `Ω = wallCornerCyclicPerm W`, if `L` is a nodup list of length `4` with all elements in
`Ω.bar`, then `{v | v ∈ L} = Ω.bar`. -/
theorem wallCornerCyclicPerm_setOf_mem_eq_bar (W : Wall α β) {L : List α}
    (hnd : L.Nodup) (hlen : L.length = 4) (hsub : ∀ v ∈ L, v ∈ (wallCornerCyclicPerm W).bar) :
    {v : α | v ∈ L} = (wallCornerCyclicPerm W).bar := by
  let B : Finset α := Finset.univ.image W.corner
  have hL_sub : L.toFinset ⊆ B := by
    intro v hv
    obtain ⟨k, rfl⟩ := hsub v (List.mem_toFinset.mp hv)
    exact Finset.mem_image_of_mem W.corner (Finset.mem_univ k)
  have hB_le : B.card ≤ 4 := by
    simpa [B] using Finset.card_image_le (f := W.corner) (s := Finset.univ)
  have hL_card : L.toFinset.card = 4 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  have heq : L.toFinset = B :=
    Finset.eq_of_subset_of_card_le hL_sub (by omega)
  ext v
  simp only [mem_ofPred_eq, wallCornerCyclicPerm, Wall.corners, mem_range]
  rw [← List.mem_toFinset, heq]
  simp [B]

/-- In any cyclic permutation `Ω`, `FirstHitIn Ω.bar x y` implies `Ω x = y` for `x ∈ Ω.bar`. -/
theorem CyclicPerm.apply_eq_of_firstHitIn_bar {Ω : CyclicPerm α} {x y : α}
    (hx : x ∈ Ω.bar) (h : Ω.FirstHitIn Ω.bar x y) :
    Ω x = y := by
  rcases h with ⟨k, hk1, hiter, _, hmin⟩
  have hk_lt2 : k < 2 := by
    by_contra hge2
    have h1_mem : (Ω.toFun^[1]) x ∈ Ω.bar := Ω.bijOn.mapsTo hx
    exact hmin 1 le_rfl (by omega) h1_mem
  have hk_eq : k = 1 := by omega
  subst hk_eq
  exact hiter

/-- If `[a, b, c, d]` is clockwise in `wallCornerCyclicPerm W`, then `{a, c}` and `{b, d}` are the
two opposite corner pairs `{W.corner 0, W.corner 2}` and `{W.corner 1, W.corner 3}`. -/
theorem wallCornerCyclicPerm_clockwise4_pairs (W : Wall α β) {a b c d : α}
    (hcw : (wallCornerCyclicPerm W).IsClockwiseSeq [a, b, c, d]) :
    ((a = W.corner 0 ∧ c = W.corner 2) ∨ (a = W.corner 2 ∧ c = W.corner 0)) ∧
      ((b = W.corner 1 ∧ d = W.corner 3) ∨ (b = W.corner 3 ∧ d = W.corner 1)) ∨
    ((a = W.corner 1 ∧ c = W.corner 3) ∨ (a = W.corner 3 ∧ c = W.corner 1)) ∧
      ((b = W.corner 0 ∧ d = W.corner 2) ∨ (b = W.corner 2 ∧ d = W.corner 0)) := by
  let Ω := wallCornerCyclicPerm W
  rcases hcw with ⟨hnd, hsub, hstep⟩
  have hset : {v : α | v ∈ ([a, b, c, d] : List α)} = Ω.bar :=
    wallCornerCyclicPerm_setOf_mem_eq_bar W hnd rfl hsub
  have ha_bar : a ∈ Ω.bar := hsub a (by simp)
  have hb_bar : b ∈ Ω.bar := hsub b (by simp)
  have hc_bar : c ∈ Ω.bar := hsub c (by simp)
  have h0 := hstep 0 (by simp)
  have h1 := hstep 1 (by simp)
  have h2 := hstep 2 (by simp)
  simp only [List.length_cons, List.length_nil] at h0 h1 h2
  rw [hset] at h0 h1 h2
  have hb_eq : Ω a = b := CyclicPerm.apply_eq_of_firstHitIn_bar ha_bar h0
  have hc_eq : Ω b = c := CyclicPerm.apply_eq_of_firstHitIn_bar hb_bar h1
  have hd_eq : Ω c = d := CyclicPerm.apply_eq_of_firstHitIn_bar hc_bar h2
  have h01 : W.corner 0 ≠ W.corner 1 := W.corner_injective.ne (by decide)
  have h02 : W.corner 0 ≠ W.corner 2 := W.corner_injective.ne (by decide)
  have h03 : W.corner 0 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  have h12 : W.corner 1 ≠ W.corner 2 := W.corner_injective.ne (by decide)
  have h13 : W.corner 1 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  have h23 : W.corner 2 ≠ W.corner 3 := W.corner_injective.ne (by decide)
  obtain ⟨i, rfl⟩ : a ∈ range W.corner := ha_bar
  subst hb_eq hc_eq hd_eq
  fin_cases i
  · left
    simp [Ω, wallCornerCyclicPerm, Ne.symm h01, Ne.symm h02, Ne.symm h12]
  · right
    simp [Ω, wallCornerCyclicPerm, Ne.symm h01, Ne.symm h02, Ne.symm h12,
      Ne.symm h03, Ne.symm h13, Ne.symm h23]
  · left
    simp [Ω, wallCornerCyclicPerm, Ne.symm h02, Ne.symm h12, Ne.symm h03, Ne.symm h13, Ne.symm h23]
  · right
    simp [Ω, wallCornerCyclicPerm, Ne.symm h01, Ne.symm h03, Ne.symm h13, Ne.symm h23]

/-- If the society `S` of a wall `W` in `G` has a cross (`HasCross S`), then there is a cross over
`W` in `wallCompass G W` (`∃ P Q, IsCrossOverWall (wallCompass G W) W P Q`). -/
theorem exists_isCrossOverWall_of_hasCross_wallSociety
    {G : Graph α β} {W : Wall α β} {S : Society α β}
    (hS : IsWallSociety G W S) (hcross : HasCross S) :
    ∃ P Q : Graph α β, IsCrossOverWall (wallCompass G W) W P Q := by
  rcases hS with ⟨hSG, hSΩ⟩
  rcases hcross with ⟨P₁, P₂, hdisj, s₁, t₁, s₂, t₂, hP₁, hP₂, hcr⟩
  have hP₁_path : IsGraphPathWithEnds (wallCompass G W) P₁ s₁ t₁ := hSG ▸ hP₁.1
  have hP₂_path : IsGraphPathWithEnds (wallCompass G W) P₂ s₂ t₂ := hSG ▸ hP₂.1
  have hcr' : (wallCornerCyclicPerm W).Crosses s₁ t₁ s₂ t₂ := hSΩ ▸ hcr
  have hpairs :
      ((s₁ = W.corner 0 ∧ t₁ = W.corner 2) ∨ (s₁ = W.corner 2 ∧ t₁ = W.corner 0)) ∧
        ((s₂ = W.corner 1 ∧ t₂ = W.corner 3) ∨ (s₂ = W.corner 3 ∧ t₂ = W.corner 1)) ∨
      ((s₁ = W.corner 1 ∧ t₁ = W.corner 3) ∨ (s₁ = W.corner 3 ∧ t₁ = W.corner 1)) ∧
        ((s₂ = W.corner 0 ∧ t₂ = W.corner 2) ∨ (s₂ = W.corner 2 ∧ t₂ = W.corner 0)) := by
    rcases hcr' with hcw | hcw
    · exact wallCornerCyclicPerm_clockwise4_pairs W hcw
    · rcases wallCornerCyclicPerm_clockwise4_pairs W hcw with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        refine ⟨?_, ?_⟩
        · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact Or.inr ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩]
        · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact Or.inr ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩]
      · left
        refine ⟨?_, ?_⟩
        · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact Or.inr ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩]
        · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [exact Or.inr ⟨rfl, rfl⟩; exact Or.inl ⟨rfl, rfl⟩]
  rcases hpairs with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨P₁, P₂, hdisj, ?_, ?_⟩
    · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP₁_path
      · exact hP₁_path.symm
    · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP₂_path
      · exact hP₂_path.symm
  · refine ⟨P₂, P₁, hdisj.symm, ?_, ?_⟩
    · rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP₂_path
      · exact hP₂_path.symm
    · rcases h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hP₁_path
      · exact hP₁_path.symm

/-- By Algorithm (8.6) (`theorem_8_6_proof`), if `W` is flat in `G`, then the society `S` of `W` in `G`
admits a rural division `𝒜` (`IsRuralDivision S 𝒜`). -/
theorem exists_isRuralDivision_of_isFlatWallIn
    {G : Graph α β} {W : Wall α β} {S : Society α β}
    (hflat : IsFlatWallIn G W) (hS : IsWallSociety G W S) :
    ∃ 𝒜 : Set (Graph α β), IsRuralDivision S 𝒜 := by
  rcases theorem_8_6_proof S with ⟨_, hcross⟩ | ⟨_, 𝒜, h𝒜⟩
  · exfalso
    exact hflat.2 (exists_isCrossOverWall_of_hasCross_wallSociety hS hcross)
  · exact ⟨𝒜, h𝒜⟩

/-- In Step (4) of the proof of **(9.8)** (page 104):
if `W` is a dividing proper subwall of `H_i` in `G' = (G_i \ X) ∪ H_i` and `Disjoint V(W.graph) X`,
then the compass `wallCompass G' W` contains no vertex in `X` (`Disjoint V(wallCompass G' W) X`). -/
theorem disjoint_wallCompass_deleted_of_dividing
    {G_i : Graph α β} {H_i W : Wall α β} {X : Set α}
    (hHi : H_i.graph ≤ G_i) (hsub : IsProperSubwallOf W H_i)
    (hdiv : IsDividingSubwall (subgraphUnion G_i (deleteVertices G_i X) H_i.graph) H_i W)
    (hdisj : Disjoint V(W.graph) X) :
    Disjoint V(wallCompass (subgraphUnion G_i (deleteVertices G_i X) H_i.graph) W) X := by
  let G' := subgraphUnion G_i (deleteVertices G_i X) H_i.graph
  have hdel_le : deleteVertices G_i X ≤ G_i := deleteVertices_le G_i X
  have hHi_G' : H_i.graph ≤ G' := le_subgraphUnion_right hdel_le hHi
  have hW_G' : W.graph ≤ G' := hsub.graph_le.trans hHi_G'
  have hK_le : wallCompass G' W ≤ G' := wallCompass_le hW_G'
  have hinter : V(wallCompass G' W) ∩ V(H_i.graph) ⊆ V(W.graph) :=
    compass_inter_wall_vertexSet_subset hHi_G' hsub hdiv
  rw [Set.disjoint_left]
  intro v hvK hvX
  have hvG' : v ∈ V(G') := hK_le.vertexSet_mono hvK
  change v ∈ V(deleteVertices G_i X) ∪ V(H_i.graph) at hvG'
  rw [vertexSet_deleteVertices] at hvG'
  rcases hvG' with ⟨_, hv_not_X⟩ | hvHi
  · exact hv_not_X hvX
  · have hvW : v ∈ V(W.graph) := hinter ⟨hvK, hvHi⟩
    exact Set.disjoint_left.mp hdisj hvW hvX

/-- If `W.graph ≤ G_i` and `Disjoint V(W.graph) X`, then `W.graph ≤ deleteVertices G_i X`. -/
theorem wall_le_deleteVertices_of_disjoint
    {G_i : Graph α β} {W : Wall α β} {X : Set α}
    (hW : W.graph ≤ G_i) (hdisj : Disjoint V(W.graph) X) :
    W.graph ≤ deleteVertices G_i X := by
  refine ⟨fun v hv => ⟨hW.vertexSet_mono hv, Set.disjoint_left.mp hdisj hv⟩, fun e x y hlink => ?_⟩
  rw [deleteVertices_isLink]
  exact ⟨hlink.mono hW,
    Set.disjoint_left.mp hdisj hlink.left_mem,
    Set.disjoint_left.mp hdisj hlink.right_mem⟩

/-- If `W` is a dividing proper subwall of `H_i` in `G' = (G_i \ X) ∪ H_i` and is disjoint from `X`,
then the compass of `W` in `G'` is identical to the compass of `W` in `G_i \ X`. -/
theorem wallCompass_union_eq_of_dividing
    {G_i : Graph α β} {H_i W : Wall α β} {X : Set α}
    (hHi : H_i.graph ≤ G_i) (hsub : IsProperSubwallOf W H_i)
    (hdiv : IsDividingSubwall (subgraphUnion G_i (deleteVertices G_i X) H_i.graph) H_i W)
    (hdisj : Disjoint V(W.graph) X) :
    wallCompass (subgraphUnion G_i (deleteVertices G_i X) H_i.graph) W =
      wallCompass (deleteVertices G_i X) W := by
  let G' := subgraphUnion G_i (deleteVertices G_i X) H_i.graph
  have hdel_le_Gi : deleteVertices G_i X ≤ G_i := deleteVertices_le G_i X
  have hG'_le_Gi : G' ≤ G_i := subgraphUnion_le hdel_le_Gi hHi
  have hdel_le_G' : deleteVertices G_i X ≤ G' := le_subgraphUnion_left hdel_le_Gi hHi
  have hHi_G' : H_i.graph ≤ G' := le_subgraphUnion_right hdel_le_Gi hHi
  have hW_Gi : W.graph ≤ G_i := hsub.graph_le.trans hHi
  have hW_del : W.graph ≤ deleteVertices G_i X := wall_le_deleteVertices_of_disjoint hW_Gi hdisj
  have hW_G' : W.graph ≤ G' := hsub.graph_le.trans hHi_G'
  have hdisj_K : Disjoint V(wallCompass G' W) X :=
    disjoint_wallCompass_deleted_of_dividing hHi hsub hdiv hdisj
  -- First show `wallCompassVerts G' W = wallCompassVerts (deleteVertices G_i X) W`
  have hverts_eq : wallCompassVerts G' W = wallCompassVerts (deleteVertices G_i X) W := by
    apply Subset.antisymm
    · rintro v (hvP | ⟨hv_delG', u, hu_in, ⟨w⟩⟩)
      · exact Or.inl hvP
      · refine Or.inr ⟨?_, u, hu_in, ?_⟩
        · have hvK : v ∈ V(wallCompass G' W) := Or.inr ⟨hv_delG', u, hu_in, ⟨w⟩⟩
          have hv_not_X : v ∉ X := Set.disjoint_left.mp hdisj_K hvK
          have hv_Gi : v ∈ V(G_i) := hG'_le_Gi.vertexSet_mono hv_delG'.1
          exact ⟨⟨hv_Gi, hv_not_X⟩, hv_delG'.2⟩
        · have hu_K : u ∈ V(wallCompass G' W) \ V(W.perimeter) :=
            ⟨insideVerts_subset_wallCompass hW_G' hu_in, hu_in.2⟩
          have hw_K : ∀ z ∈ w.support, z ∈ V(wallCompass G' W) \ V(W.perimeter) :=
            wallCompass_walk_support_mem hW_G' hu_K w
          have hdel_sub :
              deleteVertices (deleteVertices G_i X) V(W.perimeter) ≤
                deleteVertices G' V(W.perimeter) := by
            refine ⟨fun z hz => ⟨hdel_le_G'.vertexSet_mono hz.1, hz.2⟩, fun e x y hlink => ?_⟩
            rw [deleteVertices_isLink] at hlink ⊢
            exact ⟨hlink.1.mono hdel_le_G', hlink.2⟩
          have hw_verts : ∀ z ∈ w.support,
              z ∈ V(deleteVertices (deleteVertices G_i X) V(W.perimeter)) := by
            intro z hz
            have hzK := hw_K z hz
            have hz_not_X : z ∉ X := Set.disjoint_left.mp hdisj_K hzK.1
            have hz_Gi : z ∈ V(G_i) :=
              hG'_le_Gi.vertexSet_mono ((wallCompass_le hW_G').vertexSet_mono hzK.1)
            exact ⟨⟨hz_Gi, hz_not_X⟩, hzK.2⟩
          obtain ⟨w_down, _, _⟩ :=
            exists_walk_down_of_le hdel_sub w hw_verts (by
              intro e he
              have he_edge := walk_edges_subset_edgeSet w e he
              obtain ⟨x, y, hxy⟩ :=
                (deleteVertices G' V(W.perimeter)).exists_isLink_of_mem_edgeSet he_edge
              have hm := walk_isLink_mem_support w he hxy
              have hx := hw_verts x hm.1
              have hy := hw_verts y hm.2
              rw [deleteVertices_isLink] at hxy
              have hxy_Gi : G_i.IsLink e x y := hxy.1.mono hG'_le_Gi
              have hxy_delX : (deleteVertices G_i X).IsLink e x y :=
                (deleteVertices_isLink G_i X).mpr ⟨hxy_Gi, hx.1.2, hy.1.2⟩
              exact ((deleteVertices_isLink (deleteVertices G_i X) V(W.perimeter)).mpr
                ⟨hxy_delX, hx.2, hy.2⟩).edge_mem)
          exact ⟨w_down⟩
    · rintro v (hvP | ⟨hv_del, u, hu_in, ⟨w⟩⟩)
      · exact Or.inl hvP
      · have hdel_sub :
            deleteVertices (deleteVertices G_i X) V(W.perimeter) ≤
              deleteVertices G' V(W.perimeter) := by
          refine ⟨fun z hz => ⟨hdel_le_G'.vertexSet_mono hz.1, hz.2⟩, fun e x y hlink => ?_⟩
          rw [deleteVertices_isLink] at hlink ⊢
          exact ⟨hlink.1.mono hdel_le_G', hlink.2⟩
        obtain ⟨w_up, _, _⟩ := exists_walk_up_of_le hdel_sub w
        exact Or.inr ⟨⟨hdel_le_G'.vertexSet_mono hv_del.1, hv_del.2⟩, u, hu_in, ⟨w_up⟩⟩
  -- Both compasses are induced subgraphs on the same vertex set, which is disjoint from `X`
  have hK1_le : wallCompass G' W ≤ G_i := (wallCompass_le hW_G').trans hG'_le_Gi
  have hK2_le : wallCompass (deleteVertices G_i X) W ≤ G_i :=
    (wallCompass_le hW_del).trans hdel_le_Gi
  refine (Compatible.of_le_le hK1_le hK2_le).ext hverts_eq ?_
  ext e
  constructor
  · intro he
    obtain ⟨x, y, hxy⟩ := (wallCompass G' W).exists_isLink_of_mem_edgeSet he
    rw [wallCompass, induce_isLink] at hxy
    have hx_not_X : x ∉ X := Set.disjoint_left.mp hdisj_K hxy.2.1
    have hy_not_X : y ∉ X := Set.disjoint_left.mp hdisj_K hxy.2.2
    have hxy_del : (deleteVertices G_i X).IsLink e x y :=
      (deleteVertices_isLink G_i X).mpr ⟨hxy.1.mono hG'_le_Gi, hx_not_X, hy_not_X⟩
    rw [hverts_eq] at hxy
    have hxy_ind : ((deleteVertices G_i X).induce (wallCompassVerts (deleteVertices G_i X) W)).IsLink e x y := by
      rw [induce_isLink]
      exact ⟨hxy_del, hxy.2.1, hxy.2.2⟩
    exact hxy_ind.edge_mem
  · intro he
    obtain ⟨x, y, hxy⟩ := (wallCompass (deleteVertices G_i X) W).exists_isLink_of_mem_edgeSet he
    rw [wallCompass, induce_isLink, ← hverts_eq] at hxy
    have hxy_ind : (G'.induce (wallCompassVerts G' W)).IsLink e x y := by
      rw [induce_isLink]
      exact ⟨hxy.1.mono hdel_le_G', hxy.2.1, hxy.2.2⟩
    exact hxy_ind.edge_mem

/-- In Step (4)–(7) of the proof of **(9.8)** (pages 104–105):
if `G_i ≤ G`, no vertex of `V(G_i) \ Z_i` is incident with an edge of `G` outside `E(G_i)`,
`W.graph ≤ deleteVertices G_i X`, and `Disjoint V(wallCompass (deleteVertices G_i X) W) Z_i`,
then the compass of `W` in `G_i \ X` is equal to the compass of `W` in `G \ X`. -/
theorem wallCompass_eq_of_closed_outside_Z
    {G G_i : Graph α β} {W : Wall α β} {Z_i X : Set α}
    (hGi : G_i ≤ G)
    (hclosed : ∀ v ∈ V(G_i) \ Z_i, ∀ e ∈ E(G), G.Inc e v → e ∈ E(G_i))
    (hW : W.graph ≤ deleteVertices G_i X)
    (hdisj_Z : Disjoint V(wallCompass (deleteVertices G_i X) W) Z_i) :
    wallCompass (deleteVertices G_i X) W = wallCompass (deleteVertices G X) W := by
  have hdel_le : deleteVertices G_i X ≤ deleteVertices G X := by
    refine ⟨fun v hv => ⟨hGi.vertexSet_mono hv.1, hv.2⟩, fun e x y hlink => ?_⟩
    rw [deleteVertices_isLink] at hlink ⊢
    exact ⟨hlink.1.mono hGi, hlink.2⟩
  have hW_G : W.graph ≤ deleteVertices G X := hW.trans hdel_le
  have hK_le_Gi : wallCompass (deleteVertices G_i X) W ≤ G_i :=
    (wallCompass_le hW).trans (deleteVertices_le G_i X)
  -- Any walk in `deleteVertices (deleteVertices G X) V(W.perimeter)` starting at a vertex in
  -- `V(wallCompass (deleteVertices G_i X) W) \ V(W.perimeter)` stays inside `G_i \ X`
  have hwalk_stay : ∀ {u v : α},
      u ∈ V(wallCompass (deleteVertices G_i X) W) \ V(W.perimeter) →
      (w : GraphWalk (deleteVertices (deleteVertices G X) V(W.perimeter)) u v) →
      v ∈ V(wallCompass (deleteVertices G_i X) W) \ V(W.perimeter) ∧
      Nonempty (GraphWalk (deleteVertices (deleteVertices G_i X) V(W.perimeter)) u v) := by
    intro u v hu w
    induction w with
    | nil _ =>
      exact ⟨hu, ⟨GraphWalk.nil ⟨(wallCompass_le hW).vertexSet_mono hu.1, hu.2⟩⟩⟩
    | @cons u x v e hlink w_tail ih =>
      have hu_Gi : u ∈ V(G_i) \ Z_i :=
        ⟨hK_le_Gi.vertexSet_mono hu.1, Set.disjoint_left.mp hdisj_Z hu.1⟩
      have hlink_delG := hlink
      rw [deleteVertices_isLink, deleteVertices_isLink] at hlink_delG
      have hlink_G : G.IsLink e u x := hlink_delG.1.1
      have he_Gi : e ∈ E(G_i) := hclosed u hu_Gi e hlink_G.edge_mem ⟨x, hlink_G⟩
      have hlink_Gi : G_i.IsLink e u x := (hGi.isLink_iff he_Gi).mpr hlink_G
      have hlink_delGi : (deleteVertices (deleteVertices G_i X) V(W.perimeter)).IsLink e u x := by
        rw [deleteVertices_isLink, deleteVertices_isLink]
        exact ⟨⟨hlink_Gi, hlink_delG.1.2⟩, hlink_delG.2⟩
      have hx_K : x ∈ V(wallCompass (deleteVertices G_i X) W) \ V(W.perimeter) :=
        wallCompass_walk_mem hW hu (GraphWalk.cons hlink_delGi (GraphWalk.nil hlink_delGi.right_mem))
      obtain ⟨hv_K, ⟨w_tail'⟩⟩ := ih hx_K
      exact ⟨hv_K, ⟨GraphWalk.cons hlink_delGi w_tail'⟩⟩
  have hverts_eq :
      wallCompassVerts (deleteVertices G_i X) W = wallCompassVerts (deleteVertices G X) W := by
    apply Subset.antisymm
    · rintro v (hvP | ⟨hv_del, u, hu_in, ⟨w⟩⟩)
      · exact Or.inl hvP
      · have hdel_sub :
            deleteVertices (deleteVertices G_i X) V(W.perimeter) ≤
              deleteVertices (deleteVertices G X) V(W.perimeter) := by
          refine ⟨fun z hz => ⟨hdel_le.vertexSet_mono hz.1, hz.2⟩, fun e x y hlink => ?_⟩
          rw [deleteVertices_isLink] at hlink ⊢
          exact ⟨hlink.1.mono hdel_le, hlink.2⟩
        obtain ⟨w_up, _, _⟩ := exists_walk_up_of_le hdel_sub w
        exact Or.inr ⟨⟨hdel_le.vertexSet_mono hv_del.1, hv_del.2⟩, u, hu_in, ⟨w_up⟩⟩
    · rintro v (hvP | ⟨_, u, hu_in, ⟨w⟩⟩)
      · exact Or.inl hvP
      · have hu_K : u ∈ V(wallCompass (deleteVertices G_i X) W) \ V(W.perimeter) :=
          ⟨insideVerts_subset_wallCompass hW hu_in, hu_in.2⟩
        obtain ⟨hv_K, ⟨w'⟩⟩ := hwalk_stay hu_K w
        exact Or.inr ⟨⟨(wallCompass_le hW).vertexSet_mono hv_K.1, hv_K.2⟩, u, hu_in, ⟨w'⟩⟩
  have hK1_le_G : wallCompass (deleteVertices G_i X) W ≤ G := hK_le_Gi.trans hGi
  have hK2_le_G : wallCompass (deleteVertices G X) W ≤ G :=
    (wallCompass_le hW_G).trans (deleteVertices_le G X)
  refine (Compatible.of_le_le hK1_le_G hK2_le_G).ext hverts_eq ?_
  ext e
  constructor
  · intro he
    obtain ⟨x, y, hxy⟩ := (wallCompass (deleteVertices G_i X) W).exists_isLink_of_mem_edgeSet he
    rw [wallCompass, induce_isLink, hverts_eq] at hxy
    have hxy_ind : ((deleteVertices G X).induce (wallCompassVerts (deleteVertices G X) W)).IsLink e x y := by
      rw [induce_isLink]
      exact ⟨hxy.1.mono hdel_le, hxy.2.1, hxy.2.2⟩
    exact hxy_ind.edge_mem
  · intro he
    obtain ⟨x, y, hxy⟩ := (wallCompass (deleteVertices G X) W).exists_isLink_of_mem_edgeSet he
    rw [wallCompass, induce_isLink, ← hverts_eq] at hxy
    have hx_Gi : x ∈ V(G_i) \ Z_i :=
      ⟨hK_le_Gi.vertexSet_mono hxy.2.1, Set.disjoint_left.mp hdisj_Z hxy.2.1⟩
    have hxy_delG := hxy.1
    rw [deleteVertices_isLink] at hxy_delG
    have he_Gi : e ∈ E(G_i) := hclosed x hx_Gi e hxy_delG.1.edge_mem ⟨y, hxy_delG.1⟩
    have hxy_Gi : G_i.IsLink e x y := (hGi.isLink_iff he_Gi).mpr hxy_delG.1
    have hxy_delGi : (deleteVertices G_i X).IsLink e x y :=
      (deleteVertices_isLink G_i X).mpr ⟨hxy_Gi, hxy_delG.2⟩
    have hxy_ind : ((deleteVertices G_i X).induce (wallCompassVerts (deleteVertices G_i X) W)).IsLink e x y := by
      rw [induce_isLink]
      exact ⟨hxy_delGi, hxy.2.1, hxy.2.2⟩
    exact hxy_ind.edge_mem

/-- The set `D(G_i, V_K, X)` of edges of `G_i` with one end in `V_K` and the other end in `X`
(Step (4) of the proof of (9.8), page 105). -/
def crossEdgesToSet (G_i : Graph α β) (V_K X : Set α) : Set β :=
  {e ∈ E(G_i) | ∃ u ∈ V_K, ∃ x ∈ X, G_i.IsLink e u x}

/-- Step (4) of the proof of **Graph Minors XIII, (9.8)** (pages 104–105):
Given `s = binom(p, 2) + 5` mutually vertex-disjoint compasses `K^1, …, K^s` in `G_i \ X`, where
`|X| < binom(p, 2)` and `|Z_i| ≤ s - 3 = binom(p, 2) + 2`, there is a compass `K^{j₀}` disjoint
from `Z_i` satisfying `2 * (ε(K^{j₀}) + d_{j₀} + |X|) ≤ ε(G_i)`.

Note on the paper's proof (page 105, line 1185): the paper writes *"Since $H^3$ has height
$h' \ge p^2 + 2$ it follows that $\varepsilon(K^3) \ge \varepsilon(H^3) \ge p^2 + 2 \ge |X| + 2$"*,
whereas $H^1, \dots, H^s$ have height $h$ (not $h'$). Using the fact that all $s - 2 = \binom{p}{2} + 3$
remaining compasses $K^j$ ($j \notin \{j_1, j_2\}$) are mutually disjoint subgraphs of $G_i \setminus X$
with $\ge 1$ vertex and $\ge 1$ edge each gives at least $s - 2 \ge |X| + 4$ vertices and $\ge 1$
edge outside $K^{j_1} \cup K^{j_2} \cup X$, establishing the exact same inequality
$\varepsilon(K^{j_1}) + \varepsilon(K^{j_2}) + d_{j_1} + d_{j_2} + 2|X| \le \varepsilon(G_i)$ for all
$h \ge 2$. -/
theorem step4_exists_small_compass
    {p : ℕ} {G_i : Graph α β} (hVGi : V(G_i).Finite) (hEGi : E(G_i).Finite)
    {X Z_i : Set α} (hX_sub : X ⊆ V(G_i)) (hX_card : X.ncard < p.choose 2)
    (hZ_fin : Z_i.Finite) (hZ_card : Z_i.ncard ≤ p.choose 2 + 2)
    (H_sub : Fin (p.choose 2 + 5) → Wall α β)
    (K : Fin (p.choose 2 + 5) → Graph α β)
    (hH_le_K : ∀ j, (H_sub j).graph ≤ K j)
    (hK_le_Gi : ∀ j, K j ≤ G_i)
    (hK_disj_X : ∀ j, Disjoint V(K j) X)
    (hK_disj : Pairwise (fun j₁ j₂ => Disjoint V(K j₁) V(K j₂))) :
    ∃ j₀ : Fin (p.choose 2 + 5),
      Disjoint V(K j₀) Z_i ∧
      2 * (graphSize (K j₀) + (crossEdgesToSet G_i V(K j₀) X).ncard + X.ncard) ≤ graphSize G_i := by
  let s := p.choose 2 + 5
  let J_miss := (Finset.univ : Finset (Fin s)).filter (fun j => Disjoint V(K j) Z_i)
  have hmiss_card : s - Z_i.ncard ≤ J_miss.card := by
    simpa [s] using card_filter_disjoint_ge (Finset.univ : Finset (Fin s)) (fun j => V(K j))
      (fun j₁ _ j₂ _ hne => hK_disj hne) hZ_fin
  have h2_le_miss : 2 ≤ J_miss.card := by omega
  let embM : Fin 2 ↪ J_miss :=
    (Fin.castLEEmb h2_le_miss).trans J_miss.equivFin.symm.toEmbedding
  let j₁ : Fin s := (embM 0).1
  let j₂ : Fin s := (embM 1).1
  have hj₁₂ : j₁ ≠ j₂ := by
    intro heq
    have : embM 0 = embM 1 := Subtype.ext heq
    exact Fin.zero_ne_one (embM.injective this)
  have hj₁_disj_Z : Disjoint V(K j₁) Z_i := (Finset.mem_filter.mp (embM 0).2).2
  have hj₂_disj_Z : Disjoint V(K j₂) Z_i := (Finset.mem_filter.mp (embM 1).2).2
  -- The remaining `s - 2 = p.choose 2 + 3` compasses outside `{j₁, j₂}`
  let J_rest : Finset (Fin s) := Finset.univ \ {j₁, j₂}
  have hpair_card : ({j₁, j₂} : Finset (Fin s)).card = 2 := Finset.card_pair hj₁₂
  have hrest_card : J_rest.card = p.choose 2 + 3 := by
    have hsub : ({j₁, j₂} : Finset (Fin s)) ⊆ Finset.univ := Finset.subset_univ _
    have h2 := Finset.card_sdiff_add_card_eq_card hsub
    simp only [Finset.card_univ, Fintype.card_fin, hpair_card] at h2
    dsimp only [J_rest, s] at h2 ⊢
    omega
  -- Pick one vertex from each `K j` (`j ∈ J_rest`)
  let v_of (j : Fin s) : α := (H_sub j).corner 0
  have hv_of_mem : ∀ j : Fin s, v_of j ∈ V(K j) :=
    fun j => (hH_le_K j).vertexSet_mono ((H_sub j).corner_mem_vertexSet 0)
  have hv_of_inj : Function.Injective v_of := by
    intro a b heq
    by_contra hab
    exact Set.disjoint_left.mp (hK_disj hab) (hv_of_mem a) (heq ▸ hv_of_mem b)
  let R_V : Set α := v_of '' (↑J_rest : Set (Fin s))
  have hRV_card : R_V.ncard = p.choose 2 + 3 := by
    rw [Set.ncard_image_of_injective _ hv_of_inj, Set.ncard_coe_finset, hrest_card]
  have hRV_sub : R_V ⊆ V(G_i) := by
    rintro _ ⟨j, _, rfl⟩
    exact (hK_le_Gi j).vertexSet_mono (hv_of_mem j)
  have hRV_disj_K1 : Disjoint R_V V(K j₁) := by
    rw [Set.disjoint_left]
    rintro _ ⟨j, hj, rfl⟩ hv1
    have hj_ne : j ≠ j₁ := by
      intro rfl
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_insert_self j₁ {j₂})
    exact Set.disjoint_left.mp (hK_disj hj_ne) (hv_of_mem j) hv1
  have hRV_disj_K2 : Disjoint R_V V(K j₂) := by
    rw [Set.disjoint_left]
    rintro _ ⟨j, hj, rfl⟩ hv2
    have hj_ne : j ≠ j₂ := by
      intro rfl
      exact (Finset.mem_sdiff.mp hj).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self j₂))
    exact Set.disjoint_left.mp (hK_disj hj_ne) (hv_of_mem j) hv2
  have hRV_disj_X : Disjoint R_V X := by
    rw [Set.disjoint_left]
    rintro _ ⟨j, _, rfl⟩ hvX
    exact Set.disjoint_left.mp (hK_disj_X j) (hv_of_mem j) hvX
  -- Vertex cardinality bound in `G_i`
  have hV_bound : V(K j₁).ncard + V(K j₂).ncard + 2 * X.ncard + 1 ≤ V(G_i).ncard := by
    have hdisj_12 : Disjoint V(K j₁) V(K j₂) := hK_disj hj₁₂
    have hdisj_12_X : Disjoint (V(K j₁) ∪ V(K j₂)) X :=
      Disjoint.union_left (hK_disj_X j₁) (hK_disj_X j₂)
    have hdisj_12X_RV : Disjoint (V(K j₁) ∪ V(K j₂) ∪ X) R_V :=
      Disjoint.union_left (Disjoint.union_left hRV_disj_K1.symm hRV_disj_K2.symm) hRV_disj_X.symm
    have hsub_V : V(K j₁) ∪ V(K j₂) ∪ X ∪ R_V ⊆ V(G_i) :=
      union_subset (union_subset (union_subset
        (hK_le_Gi j₁).vertexSet_mono (hK_le_Gi j₂).vertexSet_mono) hX_sub) hRV_sub
    have hfin1 : V(K j₁).Finite := hVGi.subset (hK_le_Gi j₁).vertexSet_mono
    have hfin2 : V(K j₂).Finite := hVGi.subset (hK_le_Gi j₂).vertexSet_mono
    have hfinX : X.Finite := hVGi.subset hX_sub
    have hfinRV : R_V.Finite := hVGi.subset hRV_sub
    have hle := ncard_le_ncard hsub_V hVGi
    rw [ncard_union_eq hdisj_12X_RV ((hfin1.union hfin2).union hfinX) hfinRV,
      ncard_union_eq hdisj_12_X (hfin1.union hfin2) hfinX,
      ncard_union_eq hdisj_12 hfin1 hfin2, hRV_card] at hle
    omega
  -- Edge cardinality bound in `G_i`
  have hrest_nonempty : J_rest.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hemp
    rw [hemp, Finset.card_empty] at hrest_card
    omega
  obtain ⟨j₃, hj₃⟩ := hrest_nonempty
  have hj₃_ne_1 : j₃ ≠ j₁ := by
    intro rfl
    exact (Finset.mem_sdiff.mp hj₃).2 (Finset.mem_insert_self j₁ {j₂})
  have hj₃_ne_2 : j₃ ≠ j₂ := by
    intro rfl
    exact (Finset.mem_sdiff.mp hj₃).2 (Finset.mem_insert_of_mem (Finset.mem_singleton_self j₂))
  obtain ⟨e₃, he₃_H⟩ := (H_sub j₃).edgeSet_nonempty
  have he₃_K : e₃ ∈ E(K j₃) := (hH_le_K j₃).edgeSet_mono he₃_H
  let D₁ := crossEdgesToSet G_i V(K j₁) X
  let D₂ := crossEdgesToSet G_i V(K j₂) X
  have hE_disj_12 : Disjoint E(K j₁) E(K j₂) := by
    rw [Set.disjoint_left]
    intro e he₁ he₂
    obtain ⟨x, y, hxy₁⟩ := (K j₁).exists_isLink_of_mem_edgeSet he₁
    obtain ⟨z, w, hxy₂⟩ := (K j₂).exists_isLink_of_mem_edgeSet he₂
    rcases G_i.eq_or_eq_of_isLink_of_isLink (hxy₁.mono (hK_le_Gi j₁)) (hxy₂.mono (hK_le_Gi j₂)) with
      rfl | rfl
    · exact Set.disjoint_left.mp (hK_disj hj₁₂) hxy₁.left_mem hxy₂.left_mem
    · exact Set.disjoint_left.mp (hK_disj hj₁₂) hxy₁.left_mem hxy₂.right_mem
  have hE_disj_K_D : ∀ a b : Fin s, Disjoint E(K a) (crossEdgesToSet G_i V(K b) X) := by
    intro a b
    rw [Set.disjoint_left]
    rintro e heK ⟨_, u, _, x, hxX, hlink⟩
    obtain ⟨z, w, hzw⟩ := (K a).exists_isLink_of_mem_edgeSet heK
    have hzw_Gi := hzw.mono (hK_le_Gi a)
    rcases G_i.eq_or_eq_of_isLink_of_isLink hlink.symm hzw_Gi with rfl | rfl
    · exact Set.disjoint_left.mp (hK_disj_X a) hzw.left_mem hxX
    · exact Set.disjoint_left.mp (hK_disj_X a) hzw.right_mem hxX
  have hD_disj_12 : Disjoint D₁ D₂ := by
    rw [Set.disjoint_left]
    rintro e ⟨_, u₁, hu₁, x₁, _, hlink₁⟩ ⟨_, u₂, hu₂, x₂, hx₂, hlink₂⟩
    rcases G_i.eq_or_eq_of_isLink_of_isLink hlink₁ hlink₂ with rfl | rfl
    · exact Set.disjoint_left.mp (hK_disj hj₁₂) hu₁ hu₂
    · exact Set.disjoint_left.mp (hK_disj_X j₁) hu₁ hx₂
  have he₃_not_union : e₃ ∉ E(K j₁) ∪ E(K j₂) ∪ D₁ ∪ D₂ := by
    obtain ⟨x₃, y₃, hxy₃⟩ := (K j₃).exists_isLink_of_mem_edgeSet he₃_K
    have hxy₃_Gi := hxy₃.mono (hK_le_Gi j₃)
    rintro (((he₁ | he₂) | hd₁) | hd₂)
    · obtain ⟨z, w, hzw⟩ := (K j₁).exists_isLink_of_mem_edgeSet he₁
      rcases G_i.eq_or_eq_of_isLink_of_isLink hxy₃_Gi (hzw.mono (hK_le_Gi j₁)) with rfl | rfl
      · exact Set.disjoint_left.mp (hK_disj hj₃_ne_1) hxy₃.left_mem hzw.left_mem
      · exact Set.disjoint_left.mp (hK_disj hj₃_ne_1) hxy₃.left_mem hzw.right_mem
    · obtain ⟨z, w, hzw⟩ := (K j₂).exists_isLink_of_mem_edgeSet he₂
      rcases G_i.eq_or_eq_of_isLink_of_isLink hxy₃_Gi (hzw.mono (hK_le_Gi j₂)) with rfl | rfl
      · exact Set.disjoint_left.mp (hK_disj hj₃_ne_2) hxy₃.left_mem hzw.left_mem
      · exact Set.disjoint_left.mp (hK_disj hj₃_ne_2) hxy₃.left_mem hzw.right_mem
    · exact Set.disjoint_left.mp (hE_disj_K_D j₃ j₁) he₃_K hd₁
    · exact Set.disjoint_left.mp (hE_disj_K_D j₃ j₂) he₃_K hd₂
  have hE_bound : E(K j₁).ncard + E(K j₂).ncard + D₁.ncard + D₂.ncard + 1 ≤ E(G_i).ncard := by
    have hsub_E : E(K j₁) ∪ E(K j₂) ∪ D₁ ∪ D₂ ∪ {e₃} ⊆ E(G_i) := by
      refine union_subset (union_subset (union_subset (union_subset
        (hK_le_Gi j₁).edgeSet_mono (hK_le_Gi j₂).edgeSet_mono)
        (fun _ h => h.1)) (fun _ h => h.1)) ?_
      rw [singleton_subset_iff]
      exact (hK_le_Gi j₃).edgeSet_mono he₃_K
    have hfinE1 : E(K j₁).Finite := hEGi.subset (hK_le_Gi j₁).edgeSet_mono
    have hfinE2 : E(K j₂).Finite := hEGi.subset (hK_le_Gi j₂).edgeSet_mono
    have hfinD1 : D₁.Finite := hEGi.subset (fun _ h => h.1)
    have hfinD2 : D₂.Finite := hEGi.subset (fun _ h => h.1)
    have hdisj_D1 : Disjoint (E(K j₁) ∪ E(K j₂)) D₁ :=
      Disjoint.union_left (hE_disj_K_D j₁ j₁) (hE_disj_K_D j₂ j₁)
    have hdisj_D2 : Disjoint (E(K j₁) ∪ E(K j₂) ∪ D₁) D₂ :=
      Disjoint.union_left (Disjoint.union_left (hE_disj_K_D j₁ j₂) (hE_disj_K_D j₂ j₂)) hD_disj_12
    have hdisj_e3 : Disjoint (E(K j₁) ∪ E(K j₂) ∪ D₁ ∪ D₂) {e₃} :=
      Set.disjoint_singleton_right.mpr he₃_not_union
    have hle := ncard_le_ncard hsub_E hEGi
    rw [ncard_union_eq hdisj_e3 (((hfinE1.union hfinE2).union hfinD1).union hfinD2) (finite_singleton e₃),
      ncard_union_eq hdisj_D2 ((hfinE1.union hfinE2).union hfinD1) hfinD2,
      ncard_union_eq hdisj_D1 (hfinE1.union hfinE2) hfinD1,
      ncard_union_eq hE_disj_12 hfinE1 hfinE2, ncard_singleton] at hle
    omega
  have hsum_size :
      (graphSize (K j₁) + D₁.ncard + X.ncard) +
        (graphSize (K j₂) + D₂.ncard + X.ncard) ≤ graphSize G_i := by
    dsimp [graphSize]
    omega
  by_cases hle₁ : 2 * (graphSize (K j₁) + D₁.ncard + X.ncard) ≤ graphSize G_i
  · exact ⟨j₁, hj₁_disj_Z, hle₁⟩
  · refine ⟨j₂, hj₂_disj_Z, ?_⟩
    change 2 * (graphSize (K j₂) + D₂.ncard + X.ncard) ≤ graphSize G_i
    omega

/-! ## Step (8) Subgraph Construction and Invariant Preservation (page 105) -/

/-- The subgraph `G_{i+1}` of `G_i` constructed in Step (8) of the proof of **(9.8)** (page 105):
vertex set `V(A) ∪ X` and edges those in `E(A)` together with edges of `G_i` between `V(A)` and `X`. -/
def step8NextGraph (G_i A : Graph α β) (X : Set α) : Graph α β :=
  (G_i.induce (V(A) ∪ X)).restrict (E(A) ∪ crossEdgesToSet G_i V(A) X)

/-- `step8NextGraph G_i A X ≤ G_i` when `A ≤ G_i` and `X ⊆ V(G_i)`. -/
theorem step8NextGraph_le {G_i A : Graph α β} {X : Set α}
    (hA : A ≤ G_i) (hX : X ⊆ V(G_i)) :
    step8NextGraph G_i A X ≤ G_i :=
  restrict_le.trans (G_i.induce_le (union_subset hA.vertexSet_mono hX))

/-- `V(step8NextGraph G_i A X) = V(A) ∪ X`. -/
@[simp] theorem vertexSet_step8NextGraph (G_i A : Graph α β) (X : Set α) :
    V(step8NextGraph G_i A X) = V(A) ∪ X := rfl

/-- `A ≤ step8NextGraph G_i A X` when `A ≤ G_i`. -/
theorem le_step8NextGraph {G_i A : Graph α β} {X : Set α} (hA : A ≤ G_i) :
    A ≤ step8NextGraph G_i A X := by
  refine ⟨subset_union_left, fun e x y hlink => ?_⟩
  dsimp [step8NextGraph]
  rw [restrict_isLink, induce_isLink]
  exact ⟨Or.inl hlink.edge_mem, hlink.mono hA, Or.inl hlink.left_mem, Or.inl hlink.right_mem⟩

/-- Size bound in Step (8) of the proof of **(9.8)** (page 105):
`ε(G_{i+1}) ≤ ε(A) + d_1 + |X| ≤ ε(K^1) + d_1 + |X|`. -/
theorem graphSize_step8NextGraph_le
    {G_i K₁ A : Graph α β} {X : Set α}
    (hVGi : V(G_i).Finite) (hEGi : E(G_i).Finite)
    (hAK : A ≤ K₁) (hKGi : K₁ ≤ G_i) :
    graphSize (step8NextGraph G_i A X) ≤
      graphSize K₁ + (crossEdgesToSet G_i V(K₁) X).ncard + X.ncard := by
  have hfinVK : V(K₁).Finite := hVGi.subset hKGi.vertexSet_mono
  have hfinEK : E(K₁).Finite := hEGi.subset hKGi.edgeSet_mono
  have hfinD : (crossEdgesToSet G_i V(K₁) X).Finite := hEGi.subset (fun _ h => h.1)
  have hV_le : (V(A) ∪ X).ncard ≤ V(K₁).ncard + X.ncard := by
    calc (V(A) ∪ X).ncard ≤ V(A).ncard + X.ncard := ncard_union_le V(A) X
      _ ≤ V(K₁).ncard + X.ncard :=
          Nat.add_le_add_right (ncard_le_ncard hAK.vertexSet_mono hfinVK) X.ncard
  have hE_sub : E(step8NextGraph G_i A X) ⊆ E(K₁) ∪ crossEdgesToSet G_i V(K₁) X := by
    intro e he
    obtain ⟨x, y, hxy⟩ := (step8NextGraph G_i A X).exists_isLink_of_mem_edgeSet he
    dsimp [step8NextGraph] at hxy
    rw [restrict_isLink] at hxy
    rcases hxy.1 with heA | ⟨heGi, u, huA, z, hzX, hlink⟩
    · exact Or.inl (hAK.edgeSet_mono heA)
    · exact Or.inr ⟨heGi, u, hAK.vertexSet_mono huA, z, hzX, hlink⟩
  have hE_le : E(step8NextGraph G_i A X).ncard ≤
      E(K₁).ncard + (crossEdgesToSet G_i V(K₁) X).ncard := by
    calc E(step8NextGraph G_i A X).ncard
        ≤ (E(K₁) ∪ crossEdgesToSet G_i V(K₁) X).ncard :=
          ncard_le_ncard hE_sub (hfinEK.union hfinD)
      _ ≤ E(K₁).ncard + (crossEdgesToSet G_i V(K₁) X).ncard := ncard_union_le _ _
  rw [graphSize, graphSize, vertexSet_step8NextGraph]
  omega

/-- Verification of Condition (2)(ii) in Step (8) of the proof of **Graph Minors XIII, (9.8)**
(page 105):
"Let us verify (ii). Let $v \in V(G_{i+1} \setminus Z_{i+1})$, and let $e \in E(G)$ be incident with
$v$, and suppose for a contradiction that $e \notin E(G_{i+1})$..." -/
theorem step8_closed_outside_Z
    {G G_i : Graph α β} {H_i H₁ : Wall α β} {Z_i X : Set α}
    {S : Society α β} {𝒜 : Set (Graph α β)} {A : Graph α β}
    (hGi : G_i ≤ G) (hHi : H_i.graph ≤ G_i)
    (hclosed : ∀ v ∈ V(G_i) \ Z_i, ∀ e ∈ E(G), G.Inc e v → e ∈ E(G_i))
    (hsub₁ : IsProperSubwallOf H₁ H_i)
    (hdisj_Z : Disjoint V(wallCompass (subgraphUnion G_i (deleteVertices G_i X) H_i.graph) H₁) Z_i)
    (hS : IsWallSociety (subgraphUnion G_i (deleteVertices G_i X) H_i.graph) H₁ S)
    (hdiv_S : IsSocietyDivision S 𝒜)
    (hint : IsInteriorMember H₁ 𝒜 A) :
    ∀ v ∈ V(step8NextGraph G_i A X) \ (X ∪ divBoundary S A),
      ∀ e ∈ E(G), G.Inc e v → e ∈ E(step8NextGraph G_i A X) := by
  let G' := subgraphUnion G_i (deleteVertices G_i X) H_i.graph
  let K₁ := wallCompass G' H₁
  have hdel_le_Gi : deleteVertices G_i X ≤ G_i := deleteVertices_le G_i X
  have hG'_le_Gi : G' ≤ G_i := subgraphUnion_le hdel_le_Gi hHi
  have hdel_le_G' : deleteVertices G_i X ≤ G' := le_subgraphUnion_left hdel_le_Gi hHi
  have hHi_G' : H_i.graph ≤ G' := le_subgraphUnion_right hdel_le_Gi hHi
  have hH₁_G' : H₁.graph ≤ G' := hsub₁.graph_le.trans hHi_G'
  have hK₁_le_G' : K₁ ≤ G' := wallCompass_le hH₁_G'
  have hK₁_le_Gi : K₁ ≤ G_i := hK₁_le_G'.trans hG'_le_Gi
  have hA_le_K₁ : A ≤ K₁ := by
    dsimp [K₁, G']
    rw [← hS.1]
    exact hdiv_S.sub_of_mem hint.1
  have hA_le_Gi : A ≤ G_i := hA_le_K₁.trans hK₁_le_Gi
  intro v hv e heG ⟨w, hlinkG⟩
  rw [vertexSet_step8NextGraph] at hv
  rcases hv with ⟨hvA | hvX, hv_not_Z'⟩
  · have hv_not_X : v ∉ X := fun h => hv_not_Z' (Or.inl h)
    have hv_not_bd : v ∉ divBoundary S A := fun h => hv_not_Z' (Or.inr h)
    have hvK₁ : v ∈ V(K₁) := hA_le_K₁.vertexSet_mono hvA
    have hv_not_Zi : v ∉ Z_i := Set.disjoint_left.mp hdisj_Z hvK₁
    have hv_Gi : v ∈ V(G_i) := hK₁_le_Gi.vertexSet_mono hvK₁
    have he_Gi : e ∈ E(G_i) := hclosed v ⟨hv_Gi, hv_not_Zi⟩ e heG ⟨w, hlinkG⟩
    have hlink_Gi : G_i.IsLink e v w := (hGi.isLink_iff he_Gi).mpr hlinkG
    by_cases hwX : w ∈ X
    · -- Edge `e` links `v ∈ V(A)` to `w ∈ X`, so `e ∈ crossEdgesToSet G_i V(A) X ⊆ E(G_{i+1})`
      have he_cross : e ∈ crossEdgesToSet G_i V(A) X := ⟨he_Gi, v, hvA, w, hwX, hlink_Gi⟩
      have hlink_next : (step8NextGraph G_i A X).IsLink e v w := by
        dsimp [step8NextGraph]
        rw [restrict_isLink, induce_isLink]
        exact ⟨Or.inr he_cross, hlink_Gi, Or.inl hvA, Or.inr hwX⟩
      exact hlink_next.edge_mem
    · -- Both `v ∉ X` and `w ∉ X`, so `e ∈ E(G_i \ X) ⊆ E(G')`
      have hlink_del : (deleteVertices G_i X).IsLink e v w :=
        (deleteVertices_isLink G_i X).mpr ⟨hlink_Gi, hv_not_X, hwX⟩
      have hlink_G' : G'.IsLink e v w := hlink_del.mono hdel_le_G'
      have hv_not_perim : v ∉ V(H₁.perimeter) := Set.disjoint_left.mp hint.2 hvA
      have hwK₁ : w ∈ V(K₁) := by
        by_cases hw_perim : w ∈ V(H₁.perimeter)
        · exact perimeter_subset_wallCompass hH₁_G' hw_perim
        · have hlink_delP : (deleteVertices G' V(H₁.perimeter)).IsLink e v w :=
            (deleteVertices_isLink G' V(H₁.perimeter)).mpr ⟨hlink_G', hv_not_perim, hw_perim⟩
          exact (wallCompass_walk_mem hH₁_G' ⟨hvK₁, hv_not_perim⟩
            (GraphWalk.cons hlink_delP (GraphWalk.nil hlink_delP.right_mem))).1
      have hlink_K₁ : K₁.IsLink e v w := by
        dsimp [K₁, wallCompass]
        rw [induce_isLink]
        exact ⟨hlink_G', hvK₁, hwK₁⟩
      have hlink_S : S.G.IsLink e v w := by
        rw [hS.1]
        exact hlink_K₁
      have he_A : e ∈ E(A) := by
        by_contra he_not_A
        exact hv_not_bd ⟨hvA, Or.inr ⟨e, ⟨hlink_S.edge_mem, he_not_A⟩, ⟨w, hlink_S⟩⟩⟩
      exact (le_step8NextGraph hA_le_Gi).edgeSet_mono he_A
  · exact absurd (Or.inl hvX) hv_not_Z'

/-! ## (9.8) and Algorithm (9.9): Finding a Flat Wall with a Rural Division (pages 103–106) -/

/-- **Graph Minors XIII, Algorithm (9.9)** (pages 104–105):
"(9.9) Algorithm.
*Input:* A graph $G$.
*Output:* Either
(i) a branch-decomposition of $G$ of width $\le \omega$, or
(ii) a model of $K_p$ in $G$, or
(iii) a subset $X \subseteq V$ with $|X| < \binom{p}{2}$ and a flat wall $H$ in $G \setminus X$ of
height $h$, and a rural division $\mathcal{A}$ of the society of $H$ in $G \setminus X$, and a
branch-decomposition of width $\le \omega$ of each interior member of $\mathcal{A}$."

Recursive step of Algorithm (9.9) (Steps (2)–(8) of the proof of (9.8), pages 104–105), proved by
strong induction on `graphSize G_i = |E(G_i)| + |V(G_i)| + 1`. -/
theorem theorem_9_9_proof
    {p h ω : ℕ} (h2 : 2 ≤ h) (heven : Even h)
    {G : Graph α β} (hVG : V(G).Finite) (hEG : E(G).Finite)
    (h72_A : ∀ A : Graph α β, A ≤ G →
      (∃ W : Wall α β,
        IsWallIn A W ∧
        W.height = Classical.choose.{1} (theorem_9_6_proof.{u, v} p (p.choose 2 + 5) h h2 heven)) ∨
        GraphBranchWidthLE A ω) :
    ∀ (n : ℕ) (G_i : Graph α β),
      graphSize G_i = n →
      ∀ (Z_i : Set α) (H_i : Wall α β),
        G_i ≤ G →
        Z_i ⊆ V(G_i) →
        Z_i.ncard ≤ p.choose 2 + 2 →
        (∀ v ∈ V(G_i) \ Z_i, ∀ e ∈ E(G), G.Inc e v → e ∈ E(G_i)) →
        H_i.graph ≤ G_i →
        H_i.height = Classical.choose.{1} (theorem_9_6_proof.{u, v} p (p.choose 2 + 5) h h2 heven) →
        HasGraphModel (GM16.completeGraph p) G ∨
          ∃ (X : Set α) (H_flat : Wall α β) (S : Society α β) (𝒜 : Set (Graph α β)),
            X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
            IsFlatWallIn (deleteVertices G X) H_flat ∧ H_flat.height = h ∧
            IsWallSociety (deleteVertices G X) H_flat S ∧
            IsRuralDivision S 𝒜 ∧
            ∀ A : Graph α β, IsInteriorMember H_flat 𝒜 A → GraphBranchWidthLE A ω := by
  let s := p.choose 2 + 5
  let h' := Classical.choose.{1} (theorem_9_6_proof.{u, v} p s h h2 heven)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G_i hn Z_i H_i hGi hZi_sub hZi_card hclosed hHi hHi_height
    have hVGi : V(G_i).Finite := hVG.subset hGi.vertexSet_mono
    have hEGi : E(G_i).Finite := hEG.subset hGi.edgeSet_mono
    have hZi_fin : Z_i.Finite := hVGi.subset hZi_sub
    -- Step (3): Apply (9.7) to `G_i, H_i`
    rcases (Classical.choose_spec.{1} (theorem_9_6_proof.{u, v} p s h h2 heven)).2.2
        hHi hHi_height with
      hModel_Gi | ⟨X, H_flat, hX_sub, hX_fin, hX_card, hH_disj, hH_props⟩
    · exact Or.inl (hModel_Gi.mono_right hGi)
    · -- Step (4): Let `K j` be the compass of `H_flat j` in `(G_i \ X) ∪ H_i`
      let G' := subgraphUnion G_i (deleteVertices G_i X) H_i.graph
      have hdel_le_Gi : deleteVertices G_i X ≤ G_i := deleteVertices_le G_i X
      have hG'_le_Gi : G' ≤ G_i := subgraphUnion_le hdel_le_Gi hHi
      have hHi_G' : H_i.graph ≤ G' := le_subgraphUnion_right hdel_le_Gi hHi
      let K : Fin s → Graph α β := fun j => wallCompass G' (H_flat j)
      have hH_le_K : ∀ j : Fin s, (H_flat j).graph ≤ K j :=
        fun j => wall_le_wallCompass ((hH_props j).1.graph_le.trans hHi_G')
      have hK_le_Gi : ∀ j : Fin s, K j ≤ G_i :=
        fun j => (wallCompass_le ((hH_props j).1.graph_le.trans hHi_G')).trans hG'_le_Gi
      have hK_disj_X : ∀ j : Fin s, Disjoint V(K j) X :=
        fun j => disjoint_wallCompass_deleted_of_dividing hHi (hH_props j).1
          (hH_props j).2.2.2.1 (hH_props j).2.2.2.2
      have hK_disj : Pairwise (fun j₁ j₂ : Fin s => Disjoint V(K j₁) V(K j₂)) := by
        intro j₁ j₂ hj₁₂
        exact disjoint_compass_of_dividingSubwalls hHi_G'
          (hH_props j₁).1 (hH_props j₂).1
          (hH_props j₁).2.2.2.1 (hH_props j₂).2.2.2.1
          (hH_disj hj₁₂)
      obtain ⟨j₀, hj₀_disj_Z, hj₀_size⟩ :=
        step4_exists_small_compass hVGi hEGi hX_sub hX_card hZi_fin hZi_card
          H_flat K hH_le_K hK_le_Gi hK_disj_X hK_disj
      -- Step (5): Apply (8.6) to obtain a rural division `𝒜` of the society of `H_flat j₀`
      let H₁ := H_flat j₀
      have hH₁_G' : H₁.graph ≤ G' := (hH_props j₀).1.graph_le.trans hHi_G'
      have hVG' : V(G').Finite := hVGi.subset hG'_le_Gi.vertexSet_mono
      have hEG' : E(G').Finite := hEGi.subset hG'_le_Gi.edgeSet_mono
      let S := wallSociety hVG' hEG' hH₁_G'
      have hS_wall : IsWallSociety G' H₁ S := isWallSociety_wallSociety hVG' hEG' hH₁_G'
      obtain ⟨𝒜, h𝒜_rural⟩ :=
        exists_isRuralDivision_of_isFlatWallIn (hH_props j₀).2.2.1 hS_wall
      -- Step (6)-(7): Test whether every interior `A ∈ 𝒜` has branch-width `≤ ω`
      by_cases hall_bw : ∀ A : Graph α β, IsInteriorMember H₁ 𝒜 A → GraphBranchWidthLE A ω
      · -- Stop! Verify that `H₁` and `𝒜` satisfy (iii) in `G \ X`
        have hH₁_delGi : H₁.graph ≤ deleteVertices G_i X :=
          wall_le_deleteVertices_of_disjoint
            ((hH_props j₀).1.graph_le.trans hHi) (hH_props j₀).2.2.2.2
        have hK_eq_delGi : wallCompass G' H₁ = wallCompass (deleteVertices G_i X) H₁ :=
          wallCompass_union_eq_of_dividing hHi (hH_props j₀).1
            (hH_props j₀).2.2.2.1 (hH_props j₀).2.2.2.2
        have hj₀_disj_Z' : Disjoint V(wallCompass (deleteVertices G_i X) H₁) Z_i := by
          rwa [← hK_eq_delGi]
        have hK_eq_delG :
            wallCompass (deleteVertices G_i X) H₁ = wallCompass (deleteVertices G X) H₁ :=
          wallCompass_eq_of_closed_outside_Z hGi hclosed hH₁_delGi hj₀_disj_Z'
        have hK_eq : wallCompass G' H₁ = wallCompass (deleteVertices G X) H₁ :=
          hK_eq_delGi.trans hK_eq_delG
        have hH₁_delG : H₁.graph ≤ deleteVertices G X :=
          wall_le_deleteVertices_of_disjoint
            (((hH_props j₀).1.graph_le.trans hHi).trans hGi) (hH_props j₀).2.2.2.2
        have hflat_delG : IsFlatWallIn (deleteVertices G X) H₁ := by
          refine ⟨hH₁_delG, ?_⟩
          rw [← hK_eq]
          exact (hH_props j₀).2.2.1.2
        have hS_delG : IsWallSociety (deleteVertices G X) H₁ S :=
          ⟨hS_wall.1.trans hK_eq, hS_wall.2⟩
        exact Or.inr ⟨X, H₁, S, 𝒜, hX_sub.trans hGi.vertexSet_mono, hX_fin, hX_card,
          hflat_delG, (hH_props j₀).2.1, hS_delG, h𝒜_rural, hall_bw⟩
      · -- Step (8): Some interior `A ∈ 𝒜` has a wall `H_{i+1}` of height `h'`
        obtain ⟨A, hA_not⟩ := not_forall.mp hall_bw
        obtain ⟨hint_A, hnot_bw_A⟩ := not_imp.mp hA_not
        have hA_le_K : A ≤ K j₀ := by
          dsimp [K, H₁, G']
          rw [← hS_wall.1]
          exact h𝒜_rural.isDivision.sub_of_mem hint_A.1
        have hA_le_Gi : A ≤ G_i := hA_le_K.trans (hK_le_Gi j₀)
        have hA_le_G : A ≤ G := hA_le_Gi.trans hGi
        obtain ⟨H_next, hH_next_A, hH_next_h⟩ :
            ∃ W : Wall α β, IsWallIn A W ∧ W.height = h' := by
          rcases h72_A A hA_le_G with hwall | hbw
          · exact hwall
          · exact absurd hbw hnot_bw_A
        let G_next := step8NextGraph G_i A X
        let Z_next := X ∪ divBoundary S A
        have hG_next_le_Gi : G_next ≤ G_i := step8NextGraph_le hA_le_Gi hX_sub
        have hG_next_le_G : G_next ≤ G := hG_next_le_Gi.trans hGi
        have hZ_next_sub : Z_next ⊆ V(G_next) := by
          rw [vertexSet_step8NextGraph]
          rintro v (hvX | hvbd)
          · exact Or.inr hvX
          · exact Or.inl hvbd.1
        have hZ_next_card : Z_next.ncard ≤ p.choose 2 + 2 := by
          have hbd_le : (divBoundary S A).ncard ≤ 3 :=
            h𝒜_rural.isDivision.boundary_ncard_le_three hint_A.1
          calc (X ∪ divBoundary S A).ncard
              ≤ X.ncard + (divBoundary S A).ncard := ncard_union_le X (divBoundary S A)
            _ ≤ p.choose 2 + 2 := by omega
        have hG_next_size :
            graphSize G_next ≤
              graphSize (K j₀) + (crossEdgesToSet G_i V(K j₀) X).ncard + X.ncard :=
          graphSize_step8NextGraph_le hVGi hEGi hA_le_K (hK_le_Gi j₀)
        have hG_next_lt : graphSize G_next < n := by
          have hpos : 0 < graphSize G_next := by
            dsimp [graphSize]; omega
          omega
        have hclosed_next :
            ∀ v ∈ V(G_next) \ Z_next, ∀ e ∈ E(G), G.Inc e v → e ∈ E(G_next) :=
          step8_closed_outside_Z hGi hHi hclosed
            (hH_props j₀).1 hj₀_disj_Z hS_wall h𝒜_rural.isDivision hint_A
        have hH_next_G_next : H_next.graph ≤ G_next :=
          hH_next_A.trans (le_step8NextGraph hA_le_Gi)
        exact ih (graphSize G_next) hG_next_lt G_next rfl Z_next H_next
          hG_next_le_G hZ_next_sub hZ_next_card hclosed_next hH_next_G_next hH_next_h

/-- Uniform version of the mathematical guarantee of Algorithm (7.2)
(`exists_wall_or_branchDecomposition` in `Section7a.lean`): for any even `h' ≥ 2`, there exists
`ω : ℕ` (depending only on `h'`, prior to the vertex and edge types `α, β`) such that every finite
graph `G : Graph α β` either contains a wall of height `h'` or has branch-width `≤ ω`. -/
theorem exists_wall_or_branchWidth_le_uniform (h' : ℕ) (h2 : 2 ≤ h') (heven : Even h') :
    ∃ ω : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β),
      V(G).Finite → E(G).Finite →
      (∃ W : Wall α β, IsWallIn G W ∧ W.height = h') ∨ GraphBranchWidthLE G ω := by
  rcases isPlanarGraph_elementaryWall h' with ⟨θ, hθ6, _, hH_grid⟩
  let ω₁ := 20 ^ (θ ^ 4 * (2 * θ - 1))
  have hω_pos : 0 < θ ^ 4 * (2 * θ - 1) :=
    Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have hω2 : 2 ≤ ω₁ := by
    calc 2 ≤ 20 ^ 1 := by decide
      _ ≤ 20 ^ (θ ^ 4 * (2 * θ - 1)) := Nat.pow_le_pow_right (by decide) hω_pos
  refine ⟨3 * ω₁, ?_⟩
  intro α β G hVG hEG
  by_cases hbw : GraphBranchWidthLE G (3 * ω₁)
  · exact Or.inr hbw
  · left
    have hnot_ω₁ : ¬ GraphBranchWidthLE G (ω₁ - 1) := by
      intro hle
      apply hbw
      rcases hle with hle1 | ⟨ι, hfin, T, τ, hbd, hw⟩
      · exact Or.inl hle1
      · exact Or.inr ⟨ι, hfin, T, τ, hbd, hw.trans (by omega)⟩
    have hbw_gt : ¬ GM10.branchWidth (graphToHypergraph G hVG hEG) ≤ ω₁ - 1 :=
      fun h => hnot_ω₁ ((graphBranchWidthLE_iff_branchWidth_le G hVG hEG (ω₁ - 1)).mpr h)
    have hθ_le : ω₁ ≤ GM10.tangleNumber (graphToHypergraph G hVG hEG) := by
      have hle := branchWidth_le_tangleNumber (graphToHypergraph G hVG hEG)
      omega
    obtain ⟨𝒯, h𝒯⟩ := GM10.exists_isTangle_of_le_tangleNumber
      (G := graphToHypergraph G hVG hEG) (θ := ω₁) (by omega) hθ_le
    have hH_eq : graphToHypergraph G hVG hEG = Hypergraph.ofGraph G hVG hEG := rfl
    rw [hH_eq] at h𝒯
    have hGraph : (Hypergraph.ofGraph G hVG hEG).IsGraph := graphToHypergraph_isGraph G hVG hEG
    obtain ⟨W, hW⟩ := RST94.theorem_5_7 hGraph h𝒯 (g := θ) (by omega) le_rfl
    obtain ⟨ηe, hm, _⟩ := RST94.grid_model hW (by omega)
    have hminor : IsIsoMinor (elementaryWall h') G :=
      hH_grid.trans
        (isIsoMinor_of_isMinorModel (GM01.gridGraph θ) G
          (Set.toFinite _) (Set.toFinite _) hVG hEG _ ηe hm)
    exact exists_wall_of_isIsoMinor_elementaryWall hVG hEG h2 heven hminor

/-- **Graph Minors XIII, (9.8)** (page 104):
"For all $p \ge 0$ and $h \ge 2$, even, there exists $\omega \ge 0$ such that there is an algorithm
as in (9.9), with running time $O(v\varepsilon)$ for fixed $p, h$." -/
theorem theorem_9_8_proof
    (p h : ℕ) (h2 : 2 ≤ h) (heven : Even h) :
    ∃ ω : ℕ,
      ∀ {α : Type u} {β : Type v} {G : Graph α β},
        V(G).Finite → E(G).Finite →
        GraphBranchWidthLE G ω ∨
          HasGraphModel (GM16.completeGraph p) G ∨
          ∃ (X : Set α) (H_flat : Wall α β) (S : Society α β) (𝒜 : Set (Graph α β)),
            X ⊆ V(G) ∧ X.Finite ∧ X.ncard < p.choose 2 ∧
            IsFlatWallIn (deleteVertices G X) H_flat ∧ H_flat.height = h ∧
            IsWallSociety (deleteVertices G X) H_flat S ∧
            IsRuralDivision S 𝒜 ∧
            ∀ A : Graph α β, IsInteriorMember H_flat 𝒜 A → GraphBranchWidthLE A ω := by
  let s := p.choose 2 + 5
  let h' := Classical.choose.{1} (theorem_9_6_proof.{u, v} p s h h2 heven)
  have hh'_spec := Classical.choose_spec.{1} (theorem_9_6_proof.{u, v} p s h h2 heven)
  have hh'_ge2 : 2 ≤ h' := by
    have := hh'_spec.1
    omega
  obtain ⟨ω, h72⟩ := exists_wall_or_branchWidth_le_uniform.{u, v} h' hh'_ge2 hh'_spec.2.1
  refine ⟨ω, ?_⟩
  intro α β G hVG hEG
  -- Step (1): Apply (7.2) to `G`
  rcases h72 G hVG hEG with ⟨H₁, hH₁_G, hH₁_h⟩ | hbw_G
  · right
    have h72_A : ∀ A : Graph α β, A ≤ G →
        (∃ W : Wall α β, IsWallIn A W ∧ W.height = h') ∨ GraphBranchWidthLE A ω :=
      fun A hAG => h72 A (hVG.subset hAG.vertexSet_mono) (hEG.subset hAG.edgeSet_mono)
    exact theorem_9_9_proof h2 heven hVG hEG h72_A
      (graphSize G) G rfl ∅ H₁ le_rfl (empty_subset _) (by simp)
      (fun _ _ _ he _ => he) hH₁_G hH₁_h
  · exact Or.inl hbw_G

/-- Bridge theorem concluding `GM13Theorem98Statement` from `theorem_9_8_proof` for Section 10. -/
theorem theorem_9_8_parallel :
    GM13Theorem98Statement.{u, v} := by
  intro p h h2 heven
  obtain ⟨ω, h98⟩ := theorem_9_8_proof p h h2 heven
  refine ⟨ω, ?_⟩
  intro α β G hVG hEG
  rcases h98 hVG hEG with
    hbw | hModel | ⟨X, H_flat, S, 𝒜, hX_sub, _, hX_card, hflat, hheight, hS, h𝒜, hall_bw⟩
  · exact Or.inl hbw
  · exact Or.inr (Or.inl hModel)
  · exact Or.inr (Or.inr ⟨X, H_flat, S, 𝒜, hX_sub, hX_card, hflat, hheight, hS, h𝒜, hall_bw⟩)

end GraphMinor.GM13
