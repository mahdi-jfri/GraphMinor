module

public import GraphMinor.GM22.Section7d2b

/-!
# Graph Minors XXII – Section 7.4 (Part 2c): Bad Disc Structure and Free Chords

This file proves the structural classification and free-chord existence inside a bad disc `D A`
used in the proof of **Claim (2)** of **Theorem 7.4** from Robertson and Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*, J. Combin. Theory Ser. B **102**
(2012), 530–563 (page 553):

- `exists_free_subdisc_of_one_arc` and `exists_free_subdisc_of_two_arcs`: splitting a closed disc
  `D₀` along one or two proper `I`-arcs meeting at a boundary point yields a closed subdisc `E ⊆ D₀`
  containing the arcs and boundary points and whose interior avoids the arcs.
- `bad_member_three_cases`: any bad member `A ∈ 𝒜` under `(J1)`–`(J7)` with
  `(Set.range (πS A) ∩ Γ.V).Nonempty` satisfies one of three structural cases **(A)**, **(B)**,
  or **(C)**.
- `exists_free_subdisc_of_bad` and `exists_chord_of_bad`: for any bad member `A ∈ 𝒜` with
  `(Set.range (πS A) ∩ Γ.V).Nonempty` and any two distinct points
  `s₁, s₂ ∈ (Γ.interSet (D A)).V ∪ Set.range (πS A)`, there is a line `L_arc ⊆ D A` with ends
  `s₁, s₂` such that `L_arc \ {s₁, s₂} ⊆ (D A \ subBd (D A)) \ Γ.U`.
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric unitInterval Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Free Subdiscs from One or Two Proper `I`-Arcs -/

omit [T2Space S] in
/-- If `D₀` is a closed disc, `L ⊆ D₀` is a proper `I`-arc with ends `s_u ≠ s_v` on `discBd D₀`
(`L ∩ discBd D₀ = {s_u, s_v}`), and `s_w ∈ D₀`, then there is a closed disc `E ⊆ D₀` such that
`L ∪ {s_w} ⊆ E` and `E \ discBd E ⊆ (D₀ \ discBd D₀) \ L`. -/
theorem exists_free_subdisc_of_one_arc {D₀ L : Set S} {s_u s_v s_w : S}
    (hD₀ : IsClosedDisc D₀) (hL : IsLineWithEnds L s_u s_v) (hLD₀ : L ⊆ D₀)
    (huv : s_u ≠ s_v) (hmeet : L ∩ discBd D₀ = {s_u, s_v}) (hw : s_w ∈ D₀) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ D₀ ∧ L ∪ {s_w} ⊆ E ∧
      E \ discBd E ⊆ (D₀ \ discBd D₀) \ L := by
  obtain ⟨E₁, E₂, hE₁, hE₂, hU, hI, hE₁_int, hE₂_int, _, _, _⟩ :=
    disc_iArc_split_subdiscs hD₀ hL hLD₀ huv hmeet
  have hE₁_sub : E₁ ⊆ D₀ := hU ▸ subset_union_left
  have hE₂_sub : E₂ ⊆ D₀ := hU ▸ subset_union_right
  have hL_E₁ : L ⊆ E₁ := hI ▸ inter_subset_left
  have hL_E₂ : L ⊆ E₂ := hI ▸ inter_subset_right
  rcases (hU ▸ hw : s_w ∈ E₁ ∪ E₂) with hw₁ | hw₂
  · exact ⟨E₁, hE₁, hE₁_sub, union_subset hL_E₁ (singleton_subset_iff.mpr hw₁), hE₁_int⟩
  · exact ⟨E₂, hE₂, hE₂_sub, union_subset hL_E₂ (singleton_subset_iff.mpr hw₂), hE₂_int⟩

omit [T2Space S] in
/-- If `D₀` is a closed disc, `s_u, s_v, s_w` are distinct points on `discBd D₀`, `L₁ ⊆ D₀` is a
proper `I`-arc with ends `s_u, s_w` (`L₁ ∩ discBd D₀ = {s_u, s_w}`), `L₂ ⊆ D₀` is a proper `I`-arc
with ends `s_w, s_v` (`L₂ ∩ discBd D₀ = {s_w, s_v}`), and `L₁ ∩ L₂ = {s_w}`, then there is a
closed disc `F ⊆ D₀` such that `L₁ ∪ L₂ ⊆ F` and
`F \ discBd F ⊆ (D₀ \ discBd D₀) \ (L₁ ∪ L₂)`. -/
theorem exists_free_subdisc_of_two_arcs {D₀ L₁ L₂ : Set S} {s_u s_v s_w : S}
    (hD₀ : IsClosedDisc D₀)
    (hL₁ : IsLineWithEnds L₁ s_u s_w) (hL₁D₀ : L₁ ⊆ D₀) (huw : s_u ≠ s_w)
    (hmeet₁ : L₁ ∩ discBd D₀ = {s_u, s_w})
    (hL₂ : IsLineWithEnds L₂ s_w s_v) (hL₂D₀ : L₂ ⊆ D₀) (hwv : s_w ≠ s_v)
    (hmeet₂ : L₂ ∩ discBd D₀ = {s_w, s_v})
    (hinter : L₁ ∩ L₂ = {s_w}) :
    ∃ F : Set S, IsClosedDisc F ∧ F ⊆ D₀ ∧ L₁ ∪ L₂ ⊆ F ∧
      F \ discBd F ⊆ (D₀ \ discBd D₀) \ (L₁ ∪ L₂) := by
  obtain ⟨E₁, E₂, hE₁, hE₂, hU, hI, hE₁_int, hE₂_int, hb₁, hb₂, hsplit⟩ :=
    disc_iArc_split_subdiscs hD₀ hL₁ hL₁D₀ huw hmeet₁
  have hsw_L₁ : s_w ∈ L₁ := by
    have : s_w ∈ ({s_u, s_w} : Set S) := Or.inr rfl
    rw [← hmeet₁] at this
    exact this.1
  have hsw_L₂ : s_w ∈ L₂ := by
    have : s_w ∈ ({s_w, s_v} : Set S) := Or.inl rfl
    rw [← hmeet₂] at this
    exact this.1
  have hL₂_diff_eq : L₂ \ L₁ = L₂ \ {s_w} := by
    ext x
    constructor
    · rintro ⟨hx₂, hx₁⟩
      exact ⟨hx₂, fun hxw => hx₁ (mem_singleton_iff.mp hxw ▸ hsw_L₁)⟩
    · rintro ⟨hx₂, hxw⟩
      refine ⟨hx₂, fun hx₁ => hxw ?_⟩
      have : x ∈ L₁ ∩ L₂ := ⟨hx₁, hx₂⟩
      rwa [hinter] at this
  have hL₂_pre : IsPreconnected (L₂ \ L₁) := by
    rw [hL₂_diff_eq]
    exact IsLineWithEnds.isPreconnected_diff_left hL₂
  have hE_ex : ∃ E : Set S, IsClosedDisc E ∧ E ⊆ D₀ ∧ L₁ ⊆ E ∧ L₂ ⊆ E ∧
      E \ discBd E ⊆ (D₀ \ discBd D₀) \ L₁ ∧ discBd E ⊆ discBd D₀ ∪ L₁ := by
    rcases hsplit L₂ hL₂D₀ hL₂_pre with h₂₁ | h₂₂
    · exact ⟨E₁, hE₁, hU ▸ subset_union_left, hI ▸ inter_subset_left, h₂₁, hE₁_int, hb₁⟩
    · exact ⟨E₂, hE₂, hU ▸ subset_union_right, hI ▸ inter_subset_right, h₂₂, hE₂_int, hb₂⟩
  obtain ⟨E, hE, hED₀, hL₁E, hL₂E, hE_int, hE_bd⟩ := hE_ex
  have hmeet₂_E : L₂ ∩ discBd E = {s_w, s_v} := by
    apply Subset.antisymm
    · intro x ⟨hx₂, hx_bdE⟩
      rcases hE_bd hx_bdE with hx_bdD₀ | hx₁
      · exact hmeet₂ ▸ ⟨hx₂, hx_bdD₀⟩
      · have hx_inter : x ∈ L₁ ∩ L₂ := ⟨hx₁, hx₂⟩
        rw [hinter, mem_singleton_iff] at hx_inter
        exact Or.inl hx_inter
    · intro x hx
      have hx_L₂_bdD₀ : x ∈ L₂ ∩ discBd D₀ := hmeet₂.symm ▸ hx
      refine ⟨hx_L₂_bdD₀.1, ?_⟩
      by_contra hx_not_bdE
      exact (hE_int ⟨hL₂E hx_L₂_bdD₀.1, hx_not_bdE⟩).1.2 hx_L₂_bdD₀.2
  obtain ⟨F₁, F₂, hF₁, hF₂, hFU, hFI, hF₁_int, hF₂_int, _, _, hF_split⟩ :=
    disc_iArc_split_subdiscs hE hL₂ hL₂E hwv hmeet₂_E
  have hL₁_diff_eq : L₁ \ L₂ = L₁ \ {s_w} := by
    ext x
    constructor
    · rintro ⟨hx₁, hx₂⟩
      exact ⟨hx₁, fun hxw => hx₂ (mem_singleton_iff.mp hxw ▸ hsw_L₂)⟩
    · rintro ⟨hx₁, hxw⟩
      refine ⟨hx₁, fun hx₂ => hxw ?_⟩
      have : x ∈ L₁ ∩ L₂ := ⟨hx₁, hx₂⟩
      rwa [hinter] at this
  have hL₁_pre : IsPreconnected (L₁ \ L₂) := by
    rw [hL₁_diff_eq]
    exact IsLineWithEnds.isPreconnected_diff_right hL₁
  rcases hF_split L₁ hL₁E hL₁_pre with h₁₁ | h₁₂
  · refine ⟨F₁, hF₁, (hFU ▸ subset_union_left).trans hED₀,
      union_subset h₁₁ (hFI ▸ inter_subset_left), ?_⟩
    intro x hx
    have hx' := hF₁_int hx
    have hx'' := hE_int hx'.1
    exact ⟨hx''.1, fun h => h.elim hx''.2 hx'.2⟩
  · refine ⟨F₂, hF₂, (hFU ▸ subset_union_right).trans hED₀,
      union_subset h₁₂ (hFI ▸ inter_subset_right), ?_⟩
    intro x hx
    have hx' := hF₂_int hx
    have hx'' := hE_int hx'.1
    exact ⟨hx''.1, fun h => h.elim hx''.2 hx'.2⟩

/-! ## 2. Classification of Bad Members `A ∈ 𝒜` -/

/-- A 1-vertex path `IsGraphPathWithEnds G P u u` has `V(P) = {u}` and `E(P) = ∅`. -/
theorem isGraphPathWithEnds_self_V_E {G P : Graph α β} {u : α}
    (hP : IsGraphPathWithEnds G P u u) : V(P) = {u} ∧ E(P) = ∅ := by
  obtain ⟨_, W, hW, hV, hE⟩ := hP
  cases W with
  | nil _ =>
    refine ⟨?_, ?_⟩
    · rw [hV]; ext x; simp [GraphWalk.support_nil]
    · rw [hE]; ext e; simp [GraphWalk.edges_nil]
  | cons _ r =>
    exfalso
    exact (List.nodup_cons.mp hW).1 r.end_mem_support

/-- The internal vertices of a path `P` in `G` with ends `a, b` are contained in `V(P) \ {a, b}`. -/
theorem IsGraphPathWithEnds.pathInternalVerts_subset {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) :
    pathInternalVerts G P ⊆ V(P) \ {a, b} := by
  rintro x ⟨hxV, hx_not_end⟩
  refine ⟨hxV, ?_⟩
  rintro (rfl | rfl)
  · exact hx_not_end ⟨b, hP⟩
  · exact hx_not_end ⟨a, IsGraphPathWithEnds.symm hP⟩

/-- For any `G : Graph α β` and `u ∈ V(G)`, `Graph.noEdge {u} β` is a path in `G` from `u` to `u`
with empty `pathInternalVerts`. -/
theorem exists_trivial_path_self {G : Graph α β} {u : α} (hu : u ∈ V(G)) :
    ∃ P : Graph α β, IsGraphPathWithEnds G P u u ∧ pathInternalVerts G P = ∅ := by
  let P : Graph α β := Graph.noEdge {u} β
  have hPG : P ≤ G := ⟨singleton_subset_iff.mpr hu, fun _ _ _ h => False.elim h⟩
  have hVP : V(P) = {u} := rfl
  have hP : IsGraphPathWithEnds G P u u :=
    ⟨hPG, .nil (mem_singleton u), List.nodup_singleton u,
      by ext x; exact mem_singleton_iff.trans List.mem_singleton.symm,
      by ext e; exact iff_of_false id List.not_mem_nil⟩
  refine ⟨P, hP, ?_⟩
  ext x
  simp only [mem_empty_iff_false, iff_false]
  intro hx
  have hxV : x ∈ V(P) := hx.1
  rw [hVP, mem_singleton_iff] at hxV
  subst x
  exact hx.2 ⟨u, hP⟩

/-- If `E(G).Finite` and `vertexValency G v = 0`, then `E(G) = E(G.deleteVerts {v})`. -/
theorem edgeSet_eq_deleteVerts_singleton_of_vertexValency_eq_zero {G : Graph α β} {v : α}
    (hfin : E(G).Finite) (hval0 : vertexValency G v = 0) :
    E(G) = E(G.deleteVerts {v}) := by
  refine Subset.antisymm (fun e he => ?_) Graph.deleteVerts_le.edgeSet_mono
  by_contra he_del
  obtain ⟨x, y, hL⟩ := G.exists_isLink_of_mem_edgeSet he
  have hxv_or_yv : x = v ∨ y = v := by
    by_contra hnot
    push Not at hnot
    have hL_del : (G.deleteVerts {v}).IsLink e x y := by
      rw [deleteVerts_isLink]
      exact ⟨hL, hnot.1, hnot.2⟩
    exact he_del hL_del.edge_mem
  have hv_link : ∃ w, G.IsLink e v w := by
    rcases hxv_or_yv with rfl | rfl
    · exact ⟨y, hL⟩
    · exact ⟨x, hL.symm⟩
  obtain ⟨w, hvw⟩ := hv_link
  unfold vertexValency at hval0
  by_cases hwv : w = v
  · subst w
    have hpos : 0 < {e' ∈ E(G) | G.IsLink e' v v}.ncard :=
      (Set.ncard_pos (hfin.subset fun _ h => h.1)).mpr ⟨e, he, hvw⟩
    omega
  · have hpos : 0 < {e' ∈ E(G) | ∃ w ≠ v, G.IsLink e' v w}.ncard :=
      (Set.ncard_pos (hfin.subset fun _ h => h.1)).mpr ⟨e, he, w, hwv, hvw⟩
    omega

omit [TopologicalSpace S] [T2Space S] in
/-- If `πLen A = 3` and `Function.Injective (πS A)`, and `s_u, s_v ∈ Set.range (πS A)` with
`s_u ≠ s_v`, then there exists `s_w ∈ Set.range (πS A)` distinct from `s_u` and `s_v` such that
`Set.range (πS A) = {s_u, s_v, s_w}`. -/
theorem range_πS_eq_triple_of_len_three {πLen : Graph α β → ℕ}
    {πS : ∀ A : Graph α β, Fin (πLen A) → S} {A : Graph α β}
    (hlen3 : πLen A = 3) (hinj : Function.Injective (πS A))
    {s_u s_v : S} (hu : s_u ∈ Set.range (πS A)) (hv : s_v ∈ Set.range (πS A)) (huv : s_u ≠ s_v) :
    ∃ s_w : S, s_u ≠ s_w ∧ s_v ≠ s_w ∧ Set.range (πS A) = {s_u, s_v, s_w} := by
  have hcard3 : (Set.range (πS A)).ncard = 3 := by
    rw [Set.ncard_range_of_injective hinj, Nat.card_fin, hlen3]
  have hsub_ne : ¬ Set.range (πS A) ⊆ {s_u, s_v} := by
    intro hsub
    have hle2 : (Set.range (πS A)).ncard ≤ 2 :=
      (Set.ncard_le_ncard hsub (Set.toFinite {s_u, s_v})).trans (Set.ncard_pair huv).le
    omega
  obtain ⟨s_w, hw, hw_not⟩ := Set.not_subset.mp hsub_ne
  have huw : s_u ≠ s_w := fun h => hw_not (Or.inl h.symm)
  have hvw : s_v ≠ s_w := fun h => hw_not (Or.inr h.symm)
  refine ⟨s_w, huw, hvw, ?_⟩
  have hsub : ({s_u, s_v, s_w} : Set S) ⊆ Set.range (πS A) := by
    rintro x (rfl | rfl | rfl)
    · exact hu
    · exact hv
    · exact hw
  have hcard_triple : ({s_u, s_v, s_w} : Set S).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [huv, huw]), Set.ncard_pair hvw]
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm

/-- Under `(J1)`–`(J7)`, every bad member `A ∈ 𝒜` with `(Set.range (πS A) ∩ Γ.V).Nonempty`
satisfies one of three structural cases **(A)**, **(B)**, or **(C)**. -/
theorem bad_member_three_cases {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hJ7 : ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T)
    {A : Graph α β} (hA : A ∈ 𝒜) (hbad : IsBadMember ιV ιE Γ πLen πS A)
    (hne : (Set.range (πS A) ∩ Γ.V).Nonempty) :
    let GA := (Γ.toEmbeddedGraph ιV ιE) ⊓ A
    let πBar := ιV '' Set.range (πS A)
    (V(GA) ⊆ πBar ∧ E(GA) = ∅ ∧
      ∃ s_u ∈ Set.range (πS A) ∩ Γ.V, ∃ s_v ∈ Set.range (πS A), s_u ≠ s_v) ∨
    (πLen A = 3 ∧ ∃ s_u s_v s_w : S,
      s_u ≠ s_v ∧ s_u ≠ s_w ∧ s_v ≠ s_w ∧
      Set.range (πS A) = {s_u, s_v, s_w} ∧
      s_u ∈ Γ.V ∧ s_v ∈ Γ.V ∧
      ∃ GA₀ ≤ GA, IsGraphPathWithEnds GA₀ GA₀ (ιV s_u) (ιV s_v) ∧
        ιV s_w ∉ V(GA₀) ∧ V(GA) ⊆ V(GA₀) ∪ {ιV s_w} ∧ E(GA) = E(GA₀)) ∨
    (πLen A = 3 ∧ ∃ s_u s_v s_w : S,
      s_u ≠ s_v ∧ s_u ≠ s_w ∧ s_v ≠ s_w ∧
      Set.range (πS A) = {s_u, s_v, s_w} ∧
      s_u ∈ Γ.V ∧ s_v ∈ Γ.V ∧ s_w ∈ Γ.V ∧
      IsGraphPathWithEnds GA GA (ιV s_u) (ιV s_v) ∧ ιV s_w ∈ V(GA)) := by
  intro GA πBar
  obtain ⟨s₀, hs₀_π, hs₀_V⟩ := hne
  have hs₀_GA : ιV s₀ ∈ V(GA) := by
    rcases hs₀_π with ⟨i, rfl⟩
    exact ⟨⟨πS A i, hs₀_V, rfl⟩, ((hJ.π_valid A hA).2.2.2 i).1⟩
  have hnot_sub_singleton : ¬ Set.range (πS A) ⊆ {s₀} := by
    intro hsub
    apply hbad
    refine ⟨hsub.trans (singleton_subset_iff.mpr hs₀_V), ?_⟩
    rintro u ⟨s₁, hs₁, rfl⟩ v ⟨s₂, hs₂, rfl⟩
    have hs₁₀ : s₁ = s₀ := mem_singleton_iff.mp (hsub hs₁)
    have hs₂₀ : s₂ = s₀ := mem_singleton_iff.mp (hsub hs₂)
    subst hs₁₀ hs₂₀
    obtain ⟨P, hP, hP_int⟩ := exists_trivial_path_self hs₀_GA
    exact ⟨P, hP, by rw [hP_int]; exact Set.empty_disjoint _⟩
  rcases hJ7.structure_Γ_inter_A A hA with ⟨hV, hE⟩ | ⟨u, hu, v, hv, hP⟩ |
      ⟨hlen3, hπ_V, v, hv, hval0, u₁, hu₁, u₂, hu₂, hP⟩ | ⟨_, hgood⟩
  · -- Alternative 1: `V(GA) ⊆ πBar ∧ E(GA) = ∅`.
    obtain ⟨s_v, hsv_π, hsv_ne⟩ := Set.not_subset.mp hnot_sub_singleton
    exact Or.inl ⟨hV, hE, s₀, ⟨hs₀_π, hs₀_V⟩, s_v, hsv_π, Ne.symm hsv_ne⟩
  · -- Alternative 2: `IsGraphPathWithEnds GA GA u v`.
    by_cases huv : u = v
    · subst huv
      obtain ⟨hV_eq, hE_eq⟩ := isGraphPathWithEnds_self_V_E hP
      obtain ⟨s_v, hsv_π, hsv_ne⟩ := Set.not_subset.mp hnot_sub_singleton
      exact Or.inl ⟨hV_eq ▸ singleton_subset_iff.mpr hu, hE_eq,
        s₀, ⟨hs₀_π, hs₀_V⟩, s_v, hsv_π, Ne.symm hsv_ne⟩
    · rcases hu with ⟨s_u, hsu_π, rfl⟩
      rcases hv with ⟨s_v, hsv_π, rfl⟩
      have hsu_ne_sv : s_u ≠ s_v := fun h => huv (congrArg ιV h)
      have hsu_V : s_u ∈ Γ.V := by
        rcases (IsGraphPathWithEnds.left_mem hP).1 with ⟨s', hs', hs'_eq⟩
        exact (ιV.injective hs'_eq) ▸ hs'
      have hsv_V : s_v ∈ Γ.V := by
        rcases (IsGraphPathWithEnds.right_mem hP).1 with ⟨s', hs', hs'_eq⟩
        exact (ιV.injective hs'_eq) ▸ hs'
      have hnot_sub_pair : ¬ Set.range (πS A) ⊆ {s_u, s_v} := by
        intro hsub
        apply hbad
        have hπBar_eq : ιV '' Set.range (πS A) = {ιV s_u, ιV s_v} := by
          refine Subset.antisymm ?_ ?_
          · rintro _ ⟨s, hs, rfl⟩
            rcases hsub hs with rfl | rfl <;> simp
          · rintro _ (rfl | rfl)
            · exact ⟨s_u, hsu_π, rfl⟩
            · exact ⟨s_v, hsv_π, rfl⟩
        refine ⟨hsub.trans (by rintro _ (rfl | rfl) <;> assumption), ?_⟩
        intro x hx y hy
        by_cases hxy : x = y
        · subst hxy
          have hx_GA : x ∈ V(GA) := by
            rw [hπBar_eq] at hx
            rcases hx with rfl | rfl
            · exact IsGraphPathWithEnds.left_mem hP
            · exact IsGraphPathWithEnds.right_mem hP
          obtain ⟨P₀, hP₀, hP₀_int⟩ := exists_trivial_path_self hx_GA
          exact ⟨P₀, hP₀, by rw [hP₀_int]; exact Set.empty_disjoint _⟩
        · rw [hπBar_eq] at hx hy
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact (hxy rfl).elim
          · refine ⟨GA, hP, ?_⟩
            rw [hπBar_eq]
            exact Disjoint.mono_left (IsGraphPathWithEnds.pathInternalVerts_subset hP)
              disjoint_sdiff_left
          · refine ⟨GA, IsGraphPathWithEnds.symm hP, ?_⟩
            rw [hπBar_eq, Set.pair_comm (ιV s_u) (ιV s_v)]
            exact Disjoint.mono_left
              (IsGraphPathWithEnds.pathInternalVerts_subset (IsGraphPathWithEnds.symm hP))
              disjoint_sdiff_left
          · exact (hxy rfl).elim
      obtain ⟨s_w, hsw_π, hsw_not⟩ := Set.not_subset.mp hnot_sub_pair
      have hsu_ne_sw : s_u ≠ s_w := fun h => hsw_not (Or.inl h.symm)
      have hsv_ne_sw : s_v ≠ s_w := fun h => hsw_not (Or.inr h.symm)
      have hlen3 : πLen A = 3 := by
        have hle3 := (hJ.π_valid A hA).2.1
        have hinj := (hJ.π_valid A hA).2.2.1
        have hcard_eq : (Set.range (πS A)).ncard = πLen A := by
          rw [Set.ncard_range_of_injective hinj, Nat.card_fin]
        have hsub3 : ({s_u, s_v, s_w} : Set S) ⊆ Set.range (πS A) := by
          rintro _ (rfl | rfl | rfl) <;> assumption
        have hcard3 : ({s_u, s_v, s_w} : Set S).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by simp [hsu_ne_sv, hsu_ne_sw]),
            Set.ncard_pair hsv_ne_sw]
        have hge3 : 3 ≤ πLen A := by
          rw [← hcard3, ← hcard_eq]
          exact Set.ncard_le_ncard hsub3 (Set.toFinite _)
        omega
      obtain ⟨s_w', hsu_w', hsv_w', hrange_eq⟩ :=
        range_πS_eq_triple_of_len_three hlen3 (hJ.π_valid A hA).2.2.1 hsu_π hsv_π hsu_ne_sv
      by_cases hsw'_GA : ιV s_w' ∈ V(GA)
      · right; right
        have hsw'_V : s_w' ∈ Γ.V := by
          rcases hsw'_GA.1 with ⟨s', hs', hs'_eq⟩
          exact (ιV.injective hs'_eq) ▸ hs'
        exact ⟨hlen3, s_u, s_v, s_w', hsu_ne_sv, hsu_w', hsv_w', hrange_eq,
          hsu_V, hsv_V, hsw'_V, hP, hsw'_GA⟩
      · right; left
        exact ⟨hlen3, s_u, s_v, s_w', hsu_ne_sv, hsu_w', hsv_w', hrange_eq,
          hsu_V, hsv_V, GA, le_rfl, hP, hsw'_GA, subset_union_left, rfl⟩
  · -- Alternative 3: `GA.deleteVerts {v}` is a path between `u₁` and `u₂`.
    have hGA_E_fin : E(GA).Finite :=
      hJ.finite_E.subset ((inf_le_right : GA ≤ A).edgeSet_mono.trans
        (hJ.le_of_mem_𝒜 A hA).edgeSet_mono)
    have hE_eq_del : E(GA) = E(GA.deleteVerts {v}) :=
      edgeSet_eq_deleteVerts_singleton_of_vertexValency_eq_zero hGA_E_fin hval0
    by_cases hu₁₂ : u₁ = u₂
    · subst hu₁₂
      obtain ⟨hV_del, hE_del⟩ := isGraphPathWithEnds_self_V_E hP
      have hV_sub : V(GA) ⊆ πBar := by
        intro x hx
        by_cases hxv : x = v
        · exact hxv ▸ hv
        · have hx_del : x ∈ V(GA.deleteVerts {v}) := by
            rw [vertexSet_deleteVerts]
            exact ⟨hx, hxv⟩
          rw [hV_del, mem_singleton_iff] at hx_del
          exact hx_del ▸ hu₁.1
      have hE_empty : E(GA) = ∅ := hE_eq_del.trans hE_del
      obtain ⟨s_v, hsv_π, hsv_ne⟩ := Set.not_subset.mp hnot_sub_singleton
      exact Or.inl ⟨hV_sub, hE_empty, s₀, ⟨hs₀_π, hs₀_V⟩, s_v, hsv_π, Ne.symm hsv_ne⟩
    · rcases hu₁.1 with ⟨s_u, hsu_π, rfl⟩
      rcases hu₂.1 with ⟨s_v, hsv_π, rfl⟩
      rcases hv with ⟨s_w, hsw_π, rfl⟩
      have hsu_ne_sv : s_u ≠ s_v := fun h => hu₁₂ (congrArg ιV h)
      have hsu_ne_sw : s_u ≠ s_w := fun h => hu₁.2 (congrArg ιV h)
      have hsv_ne_sw : s_v ≠ s_w := fun h => hu₂.2 (congrArg ιV h)
      have hrange_eq : Set.range (πS A) = {s_u, s_v, s_w} := by
        obtain ⟨s_w', _, _, hreq⟩ :=
          range_πS_eq_triple_of_len_three hlen3 (hJ.π_valid A hA).2.2.1 hsu_π hsv_π hsu_ne_sv
        have hsw_mem : s_w ∈ ({s_u, s_v, s_w'} : Set S) := hreq ▸ hsw_π
        rcases hsw_mem with rfl | rfl | rfl
        · exact (hsu_ne_sw rfl).elim
        · exact (hsv_ne_sw rfl).elim
        · exact hreq
      right; left
      refine ⟨hlen3, s_u, s_v, s_w, hsu_ne_sv, hsu_ne_sw, hsv_ne_sw, hrange_eq,
        hπ_V hsu_π, hπ_V hsv_π, GA.deleteVerts {ιV s_w}, Graph.deleteVerts_le, hP,
        fun h => by rw [vertexSet_deleteVerts] at h; exact h.2 rfl, ?_, hE_eq_del⟩
      intro x hx
      by_cases hxw : x = ιV s_w
      · exact Or.inr hxw
      · left
        rw [vertexSet_deleteVerts]
        exact ⟨hx, hxw⟩
  · -- Alternative 4: `IsGoodMember` contradicts `hbad`.
    exact (hbad hgood).elim

/-! ## 3. Free Subdisc and Chord inside a Bad Disc `D A` -/

/-- For any `A ∈ 𝒜` under `(J1)`–`(J6)` and `H_A := Γ.interSet (D A)`, we have:
1. `D A ∩ Γ.U = H_A.U`,
2. `H_A.U ∩ subBd (D A) ⊆ Set.range (πS A)`,
3. `x ∈ H_A.V ↔ ιV x ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A)`,
4. `e ∈ H_A.E ↔ ιE e ∈ E((Γ.toEmbeddedGraph ιV ιE) ⊓ A)`. -/
theorem interSet_DA_properties {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    {A : Graph α β} (hA : A ∈ 𝒜) :
    let H_A := Γ.interSet (D A)
    let GA := (Γ.toEmbeddedGraph ιV ιE) ⊓ A
    D A ∩ Γ.U = H_A.U ∧
    H_A.U ∩ subBd (D A) ⊆ Set.range (πS A) ∧
    (∀ x : S, x ∈ H_A.V ↔ ιV x ∈ V(GA)) ∧
    (∀ e : Set S, e ∈ H_A.E ↔ ιE e ∈ E(GA)) := by
  intro H_A GA
  have hD_disc := (hJ.disc_D A hA).1
  have hD_closed : IsClosed (D A) := hD_disc.isCompact.isClosed
  have hD_norm := (hJ.disc_D A hA).2.1
  have hH_sub : H_A.IsSubdrawing Γ := GM11.interSet_isSub
  have hU_eq : D A ∩ Γ.U = H_A.U := by
    refine Subset.antisymm ?_ (subset_inter (GM11.interSet_U_subset hD_closed) hH_sub.U_subset)
    rintro x ⟨hxD, hxU⟩
    by_cases hxV : x ∈ Γ.V
    · exact H_A.V_subset_U ((GM11.mem_interSet_V_iff hD_closed).mpr ⟨hxV, hxD⟩)
    · obtain ⟨e, he, hxe⟩ := Γ.exists_edge_of_mem hxU hxV
      have he_disj_bd : Disjoint e (subBd (D A)) := by
        rw [Set.disjoint_left]
        intro y hye hy_bd
        have hyV : y ∈ Γ.V := hD_norm ⟨hy_bd, (he.2.1 hye).1⟩
        exact (he.2.1 hye).2 hyV
      have he_disj_fr : Disjoint e (frontier (D A)) := by
        rwa [← Surface.subBd_eq_frontier]
      have he_sub : e ⊆ D A :=
        isPreconnected_subset_of_disjoint_frontier' he.2.2.1.isConnected.isPreconnected
          hD_closed he_disj_fr hxe hxD
      have he_HA : e ∈ H_A.E := GM11.mem_interSet_E_iff.mpr ⟨he, he_sub⟩
      exact H_A.closure_subset_U he_HA (subset_closure hxe)
  have hbd_sub : H_A.U ∩ subBd (D A) ⊆ Set.range (πS A) := by
    intro x ⟨hxU, hx_bd⟩
    have hxV : x ∈ Γ.V := hD_norm ⟨hx_bd, hH_sub.U_subset hxU⟩
    have hxG : ιV x ∈ V(R_G.G.toGraph) :=
      (hJ.Γ_le.trans Graph.deleteVerts_le).vertexSet_mono ⟨x, hxV, rfl⟩
    rw [hJ.π_bar_eq_bd_inter A hA]
    exact ⟨hx_bd, hxG⟩
  have hV_iff : ∀ x : S, x ∈ H_A.V ↔ ιV x ∈ V(GA) := by
    intro x
    change x ∈ H_A.V ↔ ιV x ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A)
    rw [← hJ.Γ_inter_D A hA]
    change x ∈ H_A.V ↔ ιV x ∈ ιV '' H_A.V
    exact (ιV.injective.mem_set_image).symm
  have hE_iff : ∀ e : Set S, e ∈ H_A.E ↔ ιE e ∈ E(GA) := by
    intro e
    change e ∈ H_A.E ↔ ιE e ∈ E((Γ.toEmbeddedGraph ιV ιE) ⊓ A)
    rw [← hJ.Γ_inter_D A hA]
    change e ∈ H_A.E ↔ ιE e ∈ ιE '' H_A.E
    exact (ιE.injective.mem_set_image).symm
  exact ⟨hU_eq, hbd_sub, hV_iff, hE_iff⟩

set_option maxHeartbeats 400000 in
/-- Under `(J1)`–`(J7)`, for any bad member `A ∈ 𝒜` with `(Set.range (πS A) ∩ Γ.V).Nonempty`,
there is a closed subdisc `E ⊆ D A` such that `(Γ.interSet (D A)).V ∪ Set.range (πS A) ⊆ E` and
`E \ discBd E ⊆ (D A \ subBd (D A)) \ Γ.U`. -/
theorem exists_free_subdisc_of_bad {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hJ7 : ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T)
    {A : Graph α β} (hA : A ∈ 𝒜) (hbad : IsBadMember ιV ιE Γ πLen πS A)
    (hne : (Set.range (πS A) ∩ Γ.V).Nonempty) :
    ∃ E : Set S, IsClosedDisc E ∧ E ⊆ D A ∧
      (Γ.interSet (D A)).V ∪ Set.range (πS A) ⊆ E ∧
      E \ discBd E ⊆ (D A \ subBd (D A)) \ Γ.U := by
  let H_A := Γ.interSet (D A)
  let GA := (Γ.toEmbeddedGraph ιV ιE) ⊓ A
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hD_disc : IsClosedDisc (D A) := (hJ.disc_D A hA).1
  have hD_closed : IsClosed (D A) := hD_disc.isCompact.isClosed
  have hbd_eq : subBd (D A) = discBd (D A) := IsClosedDisc.subBd_eq_discBd hS hD_disc
  obtain ⟨hU_eq, hbd_sub, hV_iff, hE_iff⟩ := interSet_DA_properties hJ hA
  have hπ_sub_bd : Set.range (πS A) ⊆ subBd (D A) := by
    rw [hJ.π_bar_eq_bd_inter A hA]
    exact inter_subset_left
  have hπ_sub_discBd : Set.range (πS A) ⊆ discBd (D A) := hbd_eq ▸ hπ_sub_bd
  have hπ_sub_D : Set.range (πS A) ⊆ D A := hπ_sub_discBd.trans (Surface.discBd_subset (D A))
  have hHA_V_sub_D : H_A.V ⊆ D A :=
    fun x hx => ((GM11.mem_interSet_V_iff hD_closed).mp hx).2
  have hHA_U_sub_D : H_A.U ⊆ D A := GM11.interSet_U_subset hD_closed
  rcases bad_member_three_cases hJ hJ7 hA hbad hne with
      ⟨hV_sub, hE_empty, _⟩ |
      ⟨_, s_u, s_v, s_w, hsu_ne_sv, hsu_ne_sw, hsv_ne_sw, hrange_eq,
        _, _, GA₀, hGA₀_le, hP₀, hsw_not_GA₀, hV_GA_sub, hE_GA_eq⟩ |
      ⟨_, s_u, s_v, s_w, hsu_ne_sv, hsu_ne_sw, hsv_ne_sw, hrange_eq,
        _, _, _, hP, hsw_GA⟩
  · -- Case (A): `V(GA) ⊆ πBar ∧ E(GA) = ∅`.
    have hHA_E_empty : H_A.E = ∅ := by
      ext e
      simp only [mem_empty_iff_false, iff_false]
      intro he
      have := (hE_iff e).mp he
      rw [hE_empty] at this
      exact this
    have hHA_V_sub_π : H_A.V ⊆ Set.range (πS A) := by
      intro x hx
      rcases hV_sub ((hV_iff x).mp hx) with ⟨s, hs, hs_eq⟩
      exact (ιV.injective hs_eq) ▸ hs
    have hHA_U_sub_bd : H_A.U ⊆ subBd (D A) := by
      rw [Drawing.U_eq, hHA_E_empty]
      simp only [mem_empty_iff_false, iUnion_of_empty, iUnion_empty, union_empty]
      exact hHA_V_sub_π.trans hπ_sub_bd
    refine ⟨D A, hD_disc, Subset.rfl, union_subset hHA_V_sub_D hπ_sub_D, ?_⟩
    rw [← hbd_eq]
    intro x ⟨hxD, hx_not_bd⟩
    refine ⟨⟨hxD, hx_not_bd⟩, fun hxU => ?_⟩
    have hx_HA : x ∈ H_A.U := hU_eq ▸ ⟨hxD, hxU⟩
    exact hx_not_bd (hHA_U_sub_bd hx_HA)
  · -- Case (B): `GA₀` is a path from `ιV s_u` to `ιV s_v` avoiding `ιV s_w`.
    have hP₀_HA : IsGraphPathWithEnds (H_A.toEmbeddedGraph ιV ιE) GA₀ (ιV s_u) (ιV s_v) := by
      rw [hJ.Γ_inter_D A hA]
      exact hP₀.mono hGA₀_le
    obtain ⟨hGA₀_le_HA, W_GA₀, hW_simple, hW_V, hW_E⟩ := hP₀_HA
    obtain ⟨W, hW_supp_eq, hW_edges_eq⟩ := W_GA₀.exists_transfer
      (fun _ _ _ _ hl => hl.mono hGA₀_le_HA)
      (fun _ hx => hGA₀_le_HA.vertexSet_mono (W_GA₀.mem_vertexSet_of_mem_support hx))
    obtain ⟨W₀, hsupp, hedges⟩ := exists_walk_toGraph_of_toEmbeddedGraph W
    have hW₀_simple : W₀.IsSimple := by
      unfold GraphWalk.IsSimple at hW_simple ⊢
      rw [← hW_supp_eq, hsupp] at hW_simple
      exact List.Nodup.of_map _ hW_simple
    let P_draw := GM11.walkDrawing H_A W₀
    have hP_sub : P_draw.IsSubdrawing H_A := GM11.walkDrawing_isSubdrawing H_A W₀
    have hP_path : P_draw.IsPathBetween s_u s_v := GM11.walkDrawing_isPathBetween H_A hW₀_simple
    have hP_line : IsLineWithEnds P_draw.U s_u s_v := GM11.isLine_of_isPathBetween hP_path hsu_ne_sv
    have hP_V : ∀ x, x ∈ P_draw.V ↔ ιV x ∈ V(GA₀) := by
      intro x
      rw [GM11.walkDrawing_V, mem_ofPred_eq, hW_V, mem_ofPred_eq, ← hW_supp_eq, hsupp,
        List.mem_map_of_injective ιV.injective]
    have hP_E : P_draw.E = H_A.E := by
      ext e
      rw [GM11.walkDrawing_E, mem_ofPred_eq, hE_iff, hE_GA_eq, hW_E, mem_ofPred_eq, ← hW_edges_eq,
        hedges, List.mem_map_of_injective ιE.injective]
    have hHA_U_sub : H_A.U ⊆ P_draw.U ∪ {s_w} := by
      rw [H_A.U_eq, P_draw.U_eq, hP_E]
      rintro x (hxV | hxE)
      · rcases hV_GA_sub ((hV_iff x).mp hxV) with hx_GA₀ | hx_w
        · exact Or.inl (Or.inl ((hP_V x).mpr hx_GA₀))
        · exact Or.inr (ιV.injective hx_w)
      · exact Or.inl (Or.inr hxE)
    have hsw_not_PU : s_w ∉ P_draw.U := by
      intro hsw_PU
      rw [GM11.mem_walkDrawing_U] at hsw_PU
      rcases hsw_PU with hsw_supp | ⟨e, he, hsw_cl⟩
      · exact hsw_not_GA₀ ((hP_V s_w).mp (by rw [GM11.walkDrawing_V]; exact hsw_supp))
      · have he_HA : e ∈ H_A.E := by rw [← hP_E, GM11.walkDrawing_E]; exact he
        have he_P : e ∈ P_draw.E := by rw [GM11.walkDrawing_E]; exact he
        have hsw_bd : s_w ∈ subBd (D A) := hπ_sub_bd (hrange_eq ▸ by simp)
        have hsw_V : s_w ∈ Γ.V :=
          (hJ.disc_D A hA).2.1 ⟨hsw_bd, GM11.interSet_isSub.U_subset (H_A.closure_subset_U he_HA hsw_cl)⟩
        have hsw_HAV : s_w ∈ H_A.V :=
          (GM11.mem_interSet_V_iff hD_closed).mpr ⟨hsw_V, Surface.discBd_subset (D A) (hbd_eq ▸ hsw_bd)⟩
        have hsw_PV : s_w ∈ P_draw.V := by
          have : s_w ∈ closure e ∩ H_A.V := ⟨hsw_cl, hsw_HAV⟩
          rw [← hP_sub.closure_inter_V he_P] at this
          exact this.2
        exact hsw_not_GA₀ ((hP_V s_w).mp hsw_PV)
    have hmeet : P_draw.U ∩ discBd (D A) = {s_u, s_v} := by
      refine Subset.antisymm ?_ ?_
      · intro x ⟨hxPU, hx_bd⟩
        have hx_π : x ∈ Set.range (πS A) := hbd_sub ⟨hP_sub.U_subset hxPU, hbd_eq.symm ▸ hx_bd⟩
        rw [hrange_eq] at hx_π
        rcases hx_π with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact (hsw_not_PU hxPU).elim
      · rintro x (rfl | rfl)
        · exact ⟨P_draw.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₀.start_mem_support),
            hπ_sub_discBd (hrange_eq ▸ by simp)⟩
        · exact ⟨P_draw.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₀.end_mem_support),
            hπ_sub_discBd (hrange_eq ▸ by simp)⟩
    have hsw_D : s_w ∈ D A := hπ_sub_D (by rw [hrange_eq]; simp)
    obtain ⟨E, hE, hED, hPU_w_sub, hE_int⟩ :=
      exists_free_subdisc_of_one_arc hD_disc hP_line (hP_sub.U_subset.trans hHA_U_sub_D)
        hsu_ne_sv hmeet hsw_D
    refine ⟨E, hE, hED, union_subset ?_ ?_, ?_⟩
    · exact (H_A.V_subset_U.trans hHA_U_sub).trans hPU_w_sub
    · rw [hrange_eq]
      rintro x (rfl | rfl | rfl)
      · exact hPU_w_sub (Or.inl (P_draw.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₀.start_mem_support)))
      · exact hPU_w_sub (Or.inl (P_draw.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₀.end_mem_support)))
      · exact hPU_w_sub (Or.inr rfl)
    · intro x hx
      have hx' := hE_int hx
      rw [← hbd_eq] at hx'
      refine ⟨hx'.1, fun hxU => ?_⟩
      have hx_HA : x ∈ H_A.U := hU_eq ▸ ⟨hx'.1.1, hxU⟩
      rcases hHA_U_sub hx_HA with hxPU | rfl
      · exact hx'.2 hxPU
      · exact hx'.1.2 (hπ_sub_bd (hrange_eq ▸ by simp))
  · -- Case (C): `GA` is a path from `ιV s_u` to `ιV s_v` containing `ιV s_w`.
    have hP_HA : IsGraphPathWithEnds (H_A.toEmbeddedGraph ιV ιE) GA (ιV s_u) (ιV s_v) := by
      rw [hJ.Γ_inter_D A hA]
      exact hP
    obtain ⟨hGA_le_HA, W_GA, hW_simple, hW_V, hW_E⟩ := hP_HA
    obtain ⟨W, hW_supp_eq, hW_edges_eq⟩ := W_GA.exists_transfer
      (fun _ _ _ _ hl => hl.mono hGA_le_HA)
      (fun _ hx => hGA_le_HA.vertexSet_mono (W_GA.mem_vertexSet_of_mem_support hx))
    obtain ⟨W₀, hsupp, hedges⟩ := exists_walk_toGraph_of_toEmbeddedGraph W
    have hW₀_simple : W₀.IsSimple := by
      unfold GraphWalk.IsSimple at hW_simple ⊢
      rw [← hW_supp_eq, hsupp] at hW_simple
      exact List.Nodup.of_map _ hW_simple
    have hsw_supp : s_w ∈ W₀.support := by
      have : ιV s_w ∈ W.support := by
        rw [hW_supp_eq]
        change ιV s_w ∈ {x | x ∈ W_GA.support}
        rw [← hW_V]
        exact hsw_GA
      rwa [hsupp, List.mem_map_of_injective ιV.injective] at this
    obtain ⟨W₁, W₂, hW₀_eq⟩ := W₀.exists_append_of_mem hsw_supp
    have hnd_append : (W₁.support ++ W₂.support.tail).Nodup := by
      have hnd : (W₁.append W₂).support.Nodup := hW₀_eq ▸ hW₀_simple
      rwa [GraphWalk.support_append] at hnd
    have hW₁_simple : W₁.IsSimple := (List.nodup_append.mp hnd_append).1
    have hW₂_simple : W₂.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [W₂.support_eq_cons]
      refine List.nodup_cons.mpr ⟨fun h => ?_, (List.nodup_append.mp hnd_append).2.1⟩
      exact (List.nodup_append.mp hnd_append).2.2 s_w W₁.end_mem_support s_w h rfl
    let P₁ := GM11.walkDrawing H_A W₁
    let P₂ := GM11.walkDrawing H_A W₂
    have hP₁_sub : P₁.IsSubdrawing H_A := GM11.walkDrawing_isSubdrawing H_A W₁
    have hP₂_sub : P₂.IsSubdrawing H_A := GM11.walkDrawing_isSubdrawing H_A W₂
    have hP₁_line : IsLineWithEnds P₁.U s_u s_w :=
      GM11.isLine_of_isPathBetween (GM11.walkDrawing_isPathBetween H_A hW₁_simple) hsu_ne_sw
    have hP₂_line : IsLineWithEnds P₂.U s_w s_v :=
      GM11.isLine_of_isPathBetween (GM11.walkDrawing_isPathBetween H_A hW₂_simple) hsv_ne_sw.symm
    have hP₁₂_V_inter : P₁.V ∩ P₂.V = {s_w} := by
      rw [GM11.walkDrawing_V, GM11.walkDrawing_V]
      ext x
      simp only [mem_inter_iff, mem_ofPred_eq, mem_singleton_iff]
      constructor
      · rintro ⟨hx₁, hx₂⟩
        rw [W₂.support_eq_cons] at hx₂
        rcases List.mem_cons.mp hx₂ with rfl | hx₂_tail
        · rfl
        · exact ((List.nodup_append.mp hnd_append).2.2 x hx₁ x hx₂_tail rfl).elim
      · rintro rfl
        exact ⟨W₁.end_mem_support, W₂.start_mem_support⟩
    have hP₁₂_E_disj : Disjoint P₁.E P₂.E := by
      rw [GM11.walkDrawing_E, GM11.walkDrawing_E, Set.disjoint_left]
      intro e he₁ he₂
      have hed_nd : (W₁.edges ++ W₂.edges).Nodup := by
        have := hW₀_eq ▸ hW₀_simple.edges_nodup
        rwa [GraphWalk.edges_append] at this
      exact (List.nodup_append.mp hed_nd).2.2 e he₁ e he₂ rfl
    have hP₁₂_U_inter : P₁.U ∩ P₂.U = {s_w} :=
      (GM11.U_inter_of_disjoint hP₁_sub hP₂_sub hP₁₂_E_disj).trans hP₁₂_V_inter
    have hP₁₂_V_union : P₁.V ∪ P₂.V = H_A.V := by
      rw [GM11.walkDrawing_V, GM11.walkDrawing_V]
      ext x
      simp only [mem_union, mem_ofPred_eq, ← GraphWalk.mem_support_append, ← hW₀_eq]
      rw [hV_iff]
      change x ∈ W₀.support ↔ ιV x ∈ V(GA)
      rw [hW_V, mem_ofPred_eq, ← hW_supp_eq, hsupp, List.mem_map_of_injective ιV.injective]
    have hP₁₂_E_union : P₁.E ∪ P₂.E = H_A.E := by
      rw [GM11.walkDrawing_E, GM11.walkDrawing_E]
      ext e
      simp only [mem_union, mem_ofPred_eq, ← List.mem_append, ← GraphWalk.edges_append, ← hW₀_eq]
      rw [hE_iff]
      change e ∈ W₀.edges ↔ ιE e ∈ E(GA)
      rw [hW_E, mem_ofPred_eq, ← hW_edges_eq, hedges, List.mem_map_of_injective ιE.injective]
    have hP₁₂_U_union : P₁.U ∪ P₂.U = H_A.U := by
      rw [P₁.U_eq, P₂.U_eq, H_A.U_eq, ← hP₁₂_V_union, ← hP₁₂_E_union, Set.biUnion_union]
      ac_rfl
    have hsv_not_P₁U : s_v ∉ P₁.U := by
      intro hsv_P₁U
      have hsv_P₂U : s_v ∈ P₂.U :=
        P₂.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₂.end_mem_support)
      have : s_v ∈ P₁.U ∩ P₂.U := ⟨hsv_P₁U, hsv_P₂U⟩
      rw [hP₁₂_U_inter, mem_singleton_iff] at this
      exact hsv_ne_sw this
    have hsu_not_P₂U : s_u ∉ P₂.U := by
      intro hsu_P₂U
      have hsu_P₁U : s_u ∈ P₁.U :=
        P₁.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₁.start_mem_support)
      have : s_u ∈ P₁.U ∩ P₂.U := ⟨hsu_P₁U, hsu_P₂U⟩
      rw [hP₁₂_U_inter, mem_singleton_iff] at this
      exact hsu_ne_sw this
    have hmeet₁ : P₁.U ∩ discBd (D A) = {s_u, s_w} := by
      refine Subset.antisymm ?_ ?_
      · intro x ⟨hxP₁, hx_bd⟩
        have hx_π : x ∈ Set.range (πS A) := hbd_sub ⟨hP₁_sub.U_subset hxP₁, hbd_eq.symm ▸ hx_bd⟩
        rw [hrange_eq] at hx_π
        rcases hx_π with rfl | rfl | rfl
        · exact Or.inl rfl
        · exact (hsv_not_P₁U hxP₁).elim
        · exact Or.inr rfl
      · rintro x (rfl | rfl)
        · exact ⟨P₁.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₁.start_mem_support),
            hπ_sub_discBd (hrange_eq ▸ by simp)⟩
        · exact ⟨P₁.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₁.end_mem_support),
            hπ_sub_discBd (hrange_eq ▸ by simp)⟩
    have hmeet₂ : P₂.U ∩ discBd (D A) = {s_w, s_v} := by
      refine Subset.antisymm ?_ ?_
      · intro x ⟨hxP₂, hx_bd⟩
        have hx_π : x ∈ Set.range (πS A) := hbd_sub ⟨hP₂_sub.U_subset hxP₂, hbd_eq.symm ▸ hx_bd⟩
        rw [hrange_eq] at hx_π
        rcases hx_π with rfl | rfl | rfl
        · exact (hsu_not_P₂U hxP₂).elim
        · exact Or.inr rfl
        · exact Or.inl rfl
      · rintro x (rfl | rfl)
        · exact ⟨P₂.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₂.start_mem_support),
            hπ_sub_discBd (hrange_eq ▸ by simp)⟩
        · exact ⟨P₂.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₂.end_mem_support),
            hπ_sub_discBd (hrange_eq ▸ by simp)⟩
    obtain ⟨F, hF, hFD, hP₁₂_sub_F, hF_int⟩ :=
      exists_free_subdisc_of_two_arcs hD_disc
        hP₁_line (hP₁_sub.U_subset.trans hHA_U_sub_D) hsu_ne_sw hmeet₁
        hP₂_line (hP₂_sub.U_subset.trans hHA_U_sub_D) hsv_ne_sw.symm hmeet₂
        hP₁₂_U_inter
    rw [hP₁₂_U_union] at hP₁₂_sub_F hF_int
    refine ⟨F, hF, hFD, union_subset (H_A.V_subset_U.trans hP₁₂_sub_F) ?_, ?_⟩
    · rw [hrange_eq]
      rintro x (rfl | rfl | rfl)
      · exact hP₁₂_sub_F (hP₁_sub.U_subset (P₁.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₁.start_mem_support)))
      · exact hP₁₂_sub_F (hP₂_sub.U_subset (P₂.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₂.end_mem_support)))
      · exact hP₁₂_sub_F (hP₁_sub.U_subset (P₁.V_subset_U (by rw [GM11.walkDrawing_V]; exact W₁.end_mem_support)))
    · intro x hx
      have hx' := hF_int hx
      rw [← hbd_eq] at hx'
      exact ⟨hx'.1, fun hxU => hx'.2 (hU_eq ▸ ⟨hx'.1.1, hxU⟩)⟩

/-- Under `(J1)`–`(J7)`, for any bad member `A ∈ 𝒜` with `(Set.range (πS A) ∩ Γ.V).Nonempty`
and any two distinct points `s₁, s₂ ∈ (Γ.interSet (D A)).V ∪ Set.range (πS A)`, there is a line
`L_arc ⊆ D A` with ends `s₁, s₂` such that `L_arc \ {s₁, s₂} ⊆ (D A \ subBd (D A)) \ Γ.U`. -/
theorem exists_chord_of_bad {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hJ7 : ConditionJ7 ιV ιE R_G.G.toGraph W 𝒜 πLen πS Γ T)
    {A : Graph α β} (hA : A ∈ 𝒜) (hbad : IsBadMember ιV ιE Γ πLen πS A)
    (hne : (Set.range (πS A) ∩ Γ.V).Nonempty)
    {s₁ s₂ : S} (hs₁ : s₁ ∈ (Γ.interSet (D A)).V ∪ Set.range (πS A))
    (hs₂ : s₂ ∈ (Γ.interSet (D A)).V ∪ Set.range (πS A)) (hs₁₂ : s₁ ≠ s₂) :
    ∃ L_arc : Set S, IsLineWithEnds L_arc s₁ s₂ ∧ L_arc ⊆ D A ∧
      L_arc \ {s₁, s₂} ⊆ (D A \ subBd (D A)) \ Γ.U := by
  obtain ⟨E, hE, hED, hsubE, hE_int⟩ := exists_free_subdisc_of_bad hJ hJ7 hA hbad hne
  obtain ⟨L_arc, hLine, hLE, hL_int⟩ :=
    exists_chord_in_closedDisc hE (hsubE hs₁) (hsubE hs₂) hs₁₂
  exact ⟨L_arc, hLine, hLE.trans hED, hL_int.trans hE_int⟩

end GraphMinor.GM22
