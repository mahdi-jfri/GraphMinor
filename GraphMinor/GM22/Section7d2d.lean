module

public import GraphMinor.GM22.Section7d2c

/-!
# Graph Minors XXII – Section 7.4 (Part 2d): Augmenting Paths in Bad Members

This file proves the graph-theoretic augmenting-path construction (`exists_augmenting_path_of_bad`)
and the `(J7)` preservation lemmas (`structure_of_path_plus_πBar`, `structure_Γ_inter_A_of_sub_πBar`,
`isGoodMember_of_three_paths`) used in the proof of **Claim (2)** of **Theorem 7.4** from
Robertson and Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012), 530–563 (page 553).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric unitInterval Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM11
  GraphMinor.GM12 GraphMinor.GM14

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Path Ends and Internal Vertices -/

omit [TopologicalSpace S] [T2Space S] in
/-- For any path `P` in `G` with ends `a, b`, every end of `P` in `G` belongs to `{a, b}`. -/
theorem IsGraphPathWithEnds.pathEnds_subset_pair {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) :
    pathEnds G P ⊆ {a, b} := by
  intro x ⟨y, hP'⟩
  by_contra hx_not
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hx_not
  rcases hx_not with ⟨hxa, hxb⟩
  have hxV := IsGraphPathWithEnds.left_mem hP'
  obtain ⟨_, W, hW, hVP, _⟩ := hP
  obtain ⟨_, W', hW', _, hEP'⟩ := hP'
  -- In `W'`, any two edges of `P` incident with the start vertex `x` are equal.
  have huniq_x : ∀ {e₁ e₂ u₁ u₂}, P.IsLink e₁ x u₁ → P.IsLink e₂ x u₂ → e₁ = e₂ := by
    intro e₁ e₂ u₁ u₂ hl₁ hl₂
    cases W' with
    | nil _ =>
      have he₁ : e₁ ∈ E(P) := hl₁.edge_mem
      rw [hEP'] at he₁
      exact (List.not_mem_nil he₁).elim
    | @cons _ z _ e₀ h₀ rest =>
      have hx_not_rest : x ∉ rest.support := (List.nodup_cons.mp hW').1
      have heq_e₀ : ∀ {e u}, P.IsLink e x u → e = e₀ := by
        intro e u hl
        have he : e ∈ E(P) := hl.edge_mem
        rw [hEP', mem_ofPred_eq] at he
        rcases List.mem_cons.mp he with rfl | he_rest
        · rfl
        · exact (hx_not_rest (walk_isLink_mem_support rest he_rest hl).1).elim
      exact (heq_e₀ hl₁).trans (heq_e₀ hl₂).symm
  -- In `W`, since `x ∈ V(P)` with `x ≠ a` and `x ≠ b`, `x` is incident with two distinct edges.
  have hxW : x ∈ W.support := by rwa [hVP] at hxV
  obtain ⟨W₁, W₂, hW_eq⟩ := W.exists_append_of_mem hxW
  have hex_first : ∀ {u v : α} (W₀ : GraphWalk P u v), u ≠ v →
      ∃ e w, e ∈ W₀.edges ∧ P.IsLink e u w := by
    intro u v W₀ huv
    cases W₀ with
    | nil _ => exact (huv rfl).elim
    | @cons _ w _ e h _ => exact ⟨e, w, List.mem_cons_self, h⟩
  obtain ⟨e₁, u₁, he₁_rev, hl₁⟩ := hex_first W₁.reverse hxa
  obtain ⟨e₂, u₂, he₂, hl₂⟩ := hex_first W₂ hxb
  have he₁ : e₁ ∈ W₁.edges := by
    rw [GraphWalk.edges_reverse, List.mem_reverse] at he₁_rev
    exact he₁_rev
  have he₁₂ : e₁ = e₂ := huniq_x hl₁ hl₂
  have hed_nd : (W₁.edges ++ W₂.edges).Nodup := by
    have := hW_eq ▸ hW.edges_nodup
    rwa [GraphWalk.edges_append] at this
  exact (List.nodup_append.mp hed_nd).2.2 e₁ he₁ e₂ he₂ he₁₂

omit [TopologicalSpace S] [T2Space S] in
/-- For any path `P` in `G` with ends `a, b`, `pathInternalVerts G P = V(P) \ {a, b}`. -/
theorem IsGraphPathWithEnds.pathInternalVerts_eq {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) :
    pathInternalVerts G P = V(P) \ {a, b} :=
  Subset.antisymm (IsGraphPathWithEnds.pathInternalVerts_subset hP)
    (fun _ ⟨hxV, hx_not⟩ => ⟨hxV, fun hend => hx_not (IsGraphPathWithEnds.pathEnds_subset_pair hP hend)⟩)

omit [TopologicalSpace S] [T2Space S] in
/-- Every path `P` in `G` between distinct ends `a ≠ b` has at least one edge. -/
theorem IsGraphPathWithEnds.edgeSet_nonempty_of_ne {G P : Graph α β} {a b : α}
    (hP : IsGraphPathWithEnds G P a b) (hab : a ≠ b) :
    E(P).Nonempty := by
  obtain ⟨_, W, _, _, _⟩ := hP
  cases W with
  | nil _ => exact (hab rfl).elim
  | @cons _ _ _ e h _ => exact ⟨e, h.edge_mem⟩

omit [TopologicalSpace S] [T2Space S] in
/-- No path `P` in `G` has a loop. -/
theorem IsGraphPathWithEnds.not_isLink_self {G P : Graph α β} {u v e z}
    (hP : IsGraphPathWithEnds G P u v) (hl : P.IsLink e z z) : False := by
  obtain ⟨_, W, hW, _, hEP⟩ := hP
  have he : e ∈ W.edges := by
    have heE := hl.edge_mem
    rwa [hEP] at heE
  have hind : ∀ {a b : α} (W₀ : GraphWalk P a b), W₀.IsSimple → e ∈ W₀.edges → False := by
    intro a b W₀
    induction W₀ with
    | nil _ => exact fun _ h => List.not_mem_nil h
    | @cons x y _ f hf rest ih =>
      intro hnd hef
      rcases List.mem_cons.mp hef with rfl | hef_rest
      · rcases hf.eq_and_eq_or_eq_and_eq hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          exact (List.nodup_cons.mp hnd).1 rest.start_mem_support
      · exact ih (List.nodup_cons.mp hnd).2 hef_rest
  exact hind W hW he

omit [TopologicalSpace S] [T2Space S] in
/-- If `P` is a path in `G` and `H ≤ G` meets `V(P)` in at most one vertex `z`, then `E(P)` and
`E(H)` are disjoint. -/
theorem disjoint_edgeSet_of_inter_vertexSet_sub_singleton
    {G P H : Graph α β} {u v z : α}
    (hP : IsGraphPathWithEnds G P u v) (hHG : H ≤ G)
    (hV : V(P) ∩ V(H) ⊆ {z}) :
    Disjoint E(P) E(H) := by
  rw [Set.disjoint_left]
  intro e heP heH
  obtain ⟨a, b, hlP⟩ := P.exists_isLink_of_mem_edgeSet heP
  obtain ⟨a', b', hlH⟩ := H.exists_isLink_of_mem_edgeSet heH
  have hl1 : G.IsLink e a b := hlP.mono hP.1
  have hl2 : G.IsLink e a' b' := hlH.mono hHG
  have haH : a ∈ V(H) := by
    rcases hl1.eq_and_eq_or_eq_and_eq hl2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hlH.left_mem
    · exact hlH.right_mem
  have hbH : b ∈ V(H) := by
    rcases hl1.eq_and_eq_or_eq_and_eq hl2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hlH.right_mem
    · exact hlH.left_mem
  have ha : a = z := mem_singleton_iff.mp (hV ⟨hlP.left_mem, haH⟩)
  have hb : b = z := mem_singleton_iff.mp (hV ⟨hlP.right_mem, hbH⟩)
  subst a b
  exact IsGraphPathWithEnds.not_isLink_self hP hlP

/-! ## 2. Preservation of `ConditionJ7.structure_Γ_inter_A` -/

omit [T2Space S] in
/-- If `πLen A₀ ≤ 3` and `πS A₀` is injective, `GA₀' := (Γ'.toEmbeddedGraph ιV ιE) ⊓ A₀`, and
`P ≤ GA₀'` is a path with ends `u, v ∈ ιV '' Set.range (πS A₀)` such that
`V(GA₀') ⊆ V(P) ∪ (ιV '' Set.range (πS A₀))` and `E(GA₀') = E(P)`, then `A₀` satisfies
`ConditionJ7.structure_Γ_inter_A` for `Γ'`. -/
theorem structure_of_path_plus_πBar
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ' : Drawing S} {A₀ : Graph α β}
    (hπ_le3 : πLen A₀ ≤ 3) (hπ_inj : Function.Injective (πS A₀))
    {P : Graph α β} {u v : α}
    (hP_le : P ≤ (Γ'.toEmbeddedGraph ιV ιE) ⊓ A₀)
    (hu : u ∈ ιV '' Set.range (πS A₀)) (hv : v ∈ ιV '' Set.range (πS A₀))
    (hP : IsGraphPathWithEnds P P u v)
    (hV_sub : V((Γ'.toEmbeddedGraph ιV ιE) ⊓ A₀) ⊆ V(P) ∪ (ιV '' Set.range (πS A₀)))
    (hE_eq : E((Γ'.toEmbeddedGraph ιV ιE) ⊓ A₀) = E(P)) :
    let GA₀' := (Γ'.toEmbeddedGraph ιV ιE) ⊓ A₀
    let πBar₀ := ιV '' Set.range (πS A₀)
    (V(GA₀') ⊆ πBar₀ ∧ E(GA₀') = ∅) ∨
    (∃ u ∈ πBar₀, ∃ v ∈ πBar₀, IsGraphPathWithEnds GA₀' GA₀' u v) ∨
    (πLen A₀ = 3 ∧ Set.range (πS A₀) ⊆ Γ'.V ∧
      ∃ w ∈ πBar₀, vertexValency GA₀' w = 0 ∧
        ∃ u₁ ∈ πBar₀ \ {w}, ∃ u₂ ∈ πBar₀ \ {w},
          IsGraphPathWithEnds (GA₀'.deleteVerts {w}) (GA₀'.deleteVerts {w}) u₁ u₂) ∨
    (πLen A₀ = 3 ∧ IsGoodMember ιV ιE Γ' πLen πS A₀) := by
  intro GA₀' πBar₀
  by_cases huv : u = v
  · subst v
    obtain ⟨hVP, hEP⟩ := isGraphPathWithEnds_self_V_E hP
    left
    exact ⟨hV_sub.trans (union_subset (hVP ▸ singleton_subset_iff.mpr hu) Subset.rfl),
      hE_eq.trans hEP⟩
  · by_cases hV_eq : V(GA₀') ⊆ V(P)
    · right; left
      have hGA₀'_eq_P : GA₀' = P :=
        (Compatible.of_le_le le_rfl hP_le).ext
          (Subset.antisymm hV_eq hP_le.vertexSet_mono) hE_eq
      exact ⟨u, hu, v, hv, hGA₀'_eq_P.symm ▸ hP⟩
    · obtain ⟨w, hw_GA₀', hw_not_P⟩ := Set.not_subset.mp hV_eq
      have hw_π : w ∈ πBar₀ := by
        rcases hV_sub hw_GA₀' with hwP | hwπ
        · exact (hw_not_P hwP).elim
        · exact hwπ
      rcases hu with ⟨s_u, hsu_π, rfl⟩
      rcases hv with ⟨s_v, hsv_π, rfl⟩
      rcases hw_π with ⟨s_w, hsw_π, rfl⟩
      have hsu_ne_sv : s_u ≠ s_v := fun h => huv (congrArg ιV h)
      have hsu_ne_sw : s_u ≠ s_w := fun h => hw_not_P (h ▸ IsGraphPathWithEnds.left_mem hP)
      have hsv_ne_sw : s_v ≠ s_w := fun h => hw_not_P (h ▸ IsGraphPathWithEnds.right_mem hP)
      have hlen3 : πLen A₀ = 3 := by
        have hcard_eq : (Set.range (πS A₀)).ncard = πLen A₀ := by
          rw [Set.ncard_range_of_injective hπ_inj, Nat.card_fin]
        have hsub3 : ({s_u, s_v, s_w} : Set S) ⊆ Set.range (πS A₀) := by
          rintro _ (rfl | rfl | rfl) <;> assumption
        have hcard3 : ({s_u, s_v, s_w} : Set S).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by simp [hsu_ne_sv, hsu_ne_sw]),
            Set.ncard_pair hsv_ne_sw]
        have hge3 : 3 ≤ πLen A₀ := by
          rw [← hcard3, ← hcard_eq]
          exact Set.ncard_le_ncard hsub3 (Set.toFinite _)
        omega
      have hrange_eq : Set.range (πS A₀) = {s_u, s_v, s_w} := by
        obtain ⟨s_w', _, _, hreq⟩ :=
          range_πS_eq_triple_of_len_three hlen3 hπ_inj hsu_π hsv_π hsu_ne_sv
        have hsw_mem : s_w ∈ ({s_u, s_v, s_w'} : Set S) := hreq ▸ hsw_π
        rcases hsw_mem with rfl | rfl | rfl
        · exact (hsu_ne_sw rfl).elim
        · exact (hsv_ne_sw rfl).elim
        · exact hreq
      have hsu_V' : s_u ∈ Γ'.V := by
        rcases (hP_le.vertexSet_mono (IsGraphPathWithEnds.left_mem hP)).1 with ⟨s', hs', hs'_eq⟩
        exact (ιV.injective hs'_eq) ▸ hs'
      have hsv_V' : s_v ∈ Γ'.V := by
        rcases (hP_le.vertexSet_mono (IsGraphPathWithEnds.right_mem hP)).1 with ⟨s', hs', hs'_eq⟩
        exact (ιV.injective hs'_eq) ▸ hs'
      have hsw_V' : s_w ∈ Γ'.V := by
        rcases hw_GA₀'.1 with ⟨s', hs', hs'_eq⟩
        exact (ιV.injective hs'_eq) ▸ hs'
      have hπ_sub_V' : Set.range (πS A₀) ⊆ Γ'.V := by
        rw [hrange_eq]
        rintro _ (rfl | rfl | rfl) <;> assumption
      have hno_link_w : ∀ e x, ¬ GA₀'.IsLink e (ιV s_w) x := by
        intro e x hL
        have heP : e ∈ E(P) := hE_eq ▸ hL.edge_mem
        obtain ⟨a, b, hLP⟩ := P.exists_isLink_of_mem_edgeSet heP
        have hL' : GA₀'.IsLink e a b := hLP.mono hP_le
        rcases hL.eq_and_eq_or_eq_and_eq hL' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hw_not_P hLP.left_mem
        · exact hw_not_P hLP.right_mem
      have hval0 : vertexValency GA₀' (ιV s_w) = 0 := by
        unfold vertexValency
        have h1 : {e ∈ E(GA₀') | GA₀'.IsLink e (ιV s_w) (ιV s_w)} = ∅ := by
          ext e
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
          exact fun _ => hno_link_w e (ιV s_w)
        have h2 : {e ∈ E(GA₀') | ∃ z ≠ ιV s_w, GA₀'.IsLink e (ιV s_w) z} = ∅ := by
          ext e
          simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_exists]
          exact fun _ z _ => hno_link_w e z
        rw [h1, h2, Set.ncard_empty]
      have hdel_eq_P : GA₀'.deleteVerts {ιV s_w} = P := by
        refine (Compatible.of_le_le Graph.deleteVerts_le hP_le).ext ?_ ?_
        · refine Subset.antisymm ?_ ?_
          · intro x hx
            rw [vertexSet_deleteVerts] at hx
            rcases hV_sub hx.1 with hxP | ⟨s, hs, rfl⟩
            · exact hxP
            · rw [hrange_eq] at hs
              rcases hs with rfl | rfl | rfl
              · exact IsGraphPathWithEnds.left_mem hP
              · exact IsGraphPathWithEnds.right_mem hP
              · exact (hx.2 rfl).elim
          · intro x hxP
            rw [vertexSet_deleteVerts]
            exact ⟨hP_le.vertexSet_mono hxP, fun h => hw_not_P (h ▸ hxP)⟩
        · refine Subset.antisymm (Graph.deleteVerts_le.edgeSet_mono.trans hE_eq.subset) ?_
          intro e heP
          obtain ⟨a, b, hLP⟩ := P.exists_isLink_of_mem_edgeSet heP
          have hL_del : (GA₀'.deleteVerts {ιV s_w}).IsLink e a b := by
            rw [deleteVerts_isLink]
            exact ⟨hLP.mono hP_le, fun h => hw_not_P (h ▸ hLP.left_mem),
              fun h => hw_not_P (h ▸ hLP.right_mem)⟩
          exact hL_del.edge_mem
      right; right; left
      refine ⟨hlen3, hπ_sub_V', ιV s_w, ⟨s_w, hsw_π, rfl⟩, hval0,
        ιV s_u, ⟨⟨s_u, hsu_π, rfl⟩, fun h => hsu_ne_sw (ιV.injective h)⟩,
        ιV s_v, ⟨⟨s_v, hsv_π, rfl⟩, fun h => hsv_ne_sw (ιV.injective h)⟩, ?_⟩
      rwa [hdel_eq_P]

/-- Under `(J1)`–`(J7)`, if `A₀ ∈ 𝒜`, `Γ.V ⊆ Γ'.V`, `GA₀ := (Γ.toEmbeddedGraph ιV ιE) ⊓ A₀`,
`GA₀' := (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀`, `GA₀ ≤ GA₀'`, `V(GA₀') ⊆ V(GA₀) ∪ (ιV' '' Set.range (πS A₀))`,
and `E(GA₀') = E(GA₀)`, then `A₀` satisfies `ConditionJ7.structure_Γ_inter_A` for `Γ'`. -/
theorem structure_Γ_inter_A_of_sub_πBar {q : ℕ}
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
    {Γ' : Drawing S} {ιV' : S ↪ α} {ιE' : Set S ↪ β}
    (hV_mono : Γ.V ⊆ Γ'.V)
    {A₀ : Graph α β} (hA₀ : A₀ ∈ 𝒜)
    (hιV' : ∀ s ∈ Set.range (πS A₀), ιV' s = ιV s)
    (hGA₀_le : (Γ.toEmbeddedGraph ιV ιE) ⊓ A₀ ≤ (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀)
    (hV_sub : V((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀) ⊆
      V((Γ.toEmbeddedGraph ιV ιE) ⊓ A₀) ∪ (ιV' '' Set.range (πS A₀)))
    (hE_eq : E((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀) = E((Γ.toEmbeddedGraph ιV ιE) ⊓ A₀)) :
    let GA₀' := (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A₀
    let πBar₀ := ιV' '' Set.range (πS A₀)
    (V(GA₀') ⊆ πBar₀ ∧ E(GA₀') = ∅) ∨
    (∃ u ∈ πBar₀, ∃ v ∈ πBar₀, IsGraphPathWithEnds GA₀' GA₀' u v) ∨
    (πLen A₀ = 3 ∧ Set.range (πS A₀) ⊆ Γ'.V ∧
      ∃ w ∈ πBar₀, vertexValency GA₀' w = 0 ∧
        ∃ u₁ ∈ πBar₀ \ {w}, ∃ u₂ ∈ πBar₀ \ {w},
          IsGraphPathWithEnds (GA₀'.deleteVerts {w}) (GA₀'.deleteVerts {w}) u₁ u₂) ∨
    (πLen A₀ = 3 ∧ IsGoodMember ιV' ιE' Γ' πLen πS A₀) := by
  intro GA₀' πBar₀
  let GA₀ := (Γ.toEmbeddedGraph ιV ιE) ⊓ A₀
  have hπBar₀_eq : ιV' '' Set.range (πS A₀) = ιV '' Set.range (πS A₀) := image_congr hιV'
  have hπBar₀_eq' : πBar₀ = ιV '' Set.range (πS A₀) := hπBar₀_eq
  rcases hJ7.structure_Γ_inter_A A₀ hA₀ with ⟨hV, hE⟩ | ⟨u, hu, v, hv, hP⟩ |
      ⟨_, _, w, hw, hval0, u₁, hu₁, u₂, hu₂, hP⟩ | ⟨hlen3, hgood⟩
  · left
    exact ⟨hV_sub.trans (union_subset (hπBar₀_eq' ▸ hV) Subset.rfl), hE_eq.trans hE⟩
  · exact structure_of_path_plus_πBar (hJ.π_valid A₀ hA₀).2.1 (hJ.π_valid A₀ hA₀).2.2.1
      hGA₀_le (hπBar₀_eq ▸ hu) (hπBar₀_eq ▸ hv) hP hV_sub hE_eq
  · have hGA₀_E_fin : E(GA₀).Finite :=
      hJ.finite_E.subset ((inf_le_right : GA₀ ≤ A₀).edgeSet_mono.trans
        (hJ.le_of_mem_𝒜 A₀ hA₀).edgeSet_mono)
    have hE_del : E(GA₀) = E(GA₀.deleteVerts {w}) :=
      edgeSet_eq_deleteVerts_singleton_of_vertexValency_eq_zero hGA₀_E_fin hval0
    have hV_sub_del : V(GA₀') ⊆ V(GA₀.deleteVerts {w}) ∪ πBar₀ := by
      refine hV_sub.trans (union_subset ?_ subset_union_right)
      intro x hx
      by_cases hxw : x = w
      · exact Or.inr (hxw ▸ (hπBar₀_eq' ▸ hw))
      · left
        rw [vertexSet_deleteVerts]
        exact ⟨hx, hxw⟩
    exact structure_of_path_plus_πBar (hJ.π_valid A₀ hA₀).2.1 (hJ.π_valid A₀ hA₀).2.2.1
      (Graph.deleteVerts_le.trans hGA₀_le)
      (hπBar₀_eq ▸ hu₁.1) (hπBar₀_eq ▸ hu₂.1) hP hV_sub_del (hE_eq.trans hE_del)
  · right; right; right
    have hπBar_sub_GA₀ : πBar₀ ⊆ V(GA₀) := by
      rw [hπBar₀_eq']
      rintro _ ⟨s, ⟨i, rfl⟩, rfl⟩
      exact ⟨⟨πS A₀ i, hgood.1 ⟨i, rfl⟩, rfl⟩, ((hJ.π_valid A₀ hA₀).2.2.2 i).1⟩
    have hGA₀'_eq : GA₀' = GA₀ :=
      (Compatible.of_le_le le_rfl hGA₀_le).ext
        (Subset.antisymm (hV_sub.trans (union_subset Subset.rfl hπBar_sub_GA₀))
          hGA₀_le.vertexSet_mono)
        hE_eq
    refine ⟨hlen3, hgood.1.trans hV_mono, ?_⟩
    change ∀ u ∈ πBar₀, ∀ v ∈ πBar₀, ∃ P : Graph α β,
      IsGraphPathWithEnds GA₀' P u v ∧ Disjoint (pathInternalVerts GA₀' P) πBar₀
    rw [hGA₀'_eq, hπBar₀_eq']
    exact hgood.2

omit [T2Space S] in
/-- If `Set.range (πS A) = {s_u, s_v, s_w} ⊆ Γ'.V` with `s_u, s_v, s_w` pairwise distinct,
`Set.range (πS A)` embeds into `V(A)`, and for each of the 3 pairs `(s_u, s_v)`, `(s_u, s_w)`,
`(s_v, s_w)` there is a path in `GA' := (Γ'.toEmbeddedGraph ιV ιE) ⊓ A` between them avoiding the
third point, then `IsGoodMember ιV ιE Γ' πLen πS A` holds. -/
theorem isGoodMember_of_three_paths
    {ιV : S ↪ α} {ιE : Set S ↪ β} {Γ' : Drawing S}
    {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S} {A : Graph α β}
    {s_u s_v s_w : S}
    (hrange : Set.range (πS A) = {s_u, s_v, s_w})
    (hπ_V' : Set.range (πS A) ⊆ Γ'.V)
    (hπ_A : ιV '' Set.range (πS A) ⊆ V(A))
    (hP_uv : ∃ P, IsGraphPathWithEnds ((Γ'.toEmbeddedGraph ιV ιE) ⊓ A) P (ιV s_u) (ιV s_v) ∧
      ιV s_w ∉ V(P))
    (hP_uw : ∃ P, IsGraphPathWithEnds ((Γ'.toEmbeddedGraph ιV ιE) ⊓ A) P (ιV s_u) (ιV s_w) ∧
      ιV s_v ∉ V(P))
    (hP_vw : ∃ P, IsGraphPathWithEnds ((Γ'.toEmbeddedGraph ιV ιE) ⊓ A) P (ιV s_v) (ιV s_w) ∧
      ιV s_u ∉ V(P)) :
    IsGoodMember ιV ιE Γ' πLen πS A := by
  let GA' := (Γ'.toEmbeddedGraph ιV ιE) ⊓ A
  let πBar := ιV '' Set.range (πS A)
  have hπBar_eq : πBar = {ιV s_u, ιV s_v, ιV s_w} := by
    change ιV '' Set.range (πS A) = {ιV s_u, ιV s_v, ιV s_w}
    rw [hrange, Set.image_insert_eq, Set.image_pair]
  have hdisj_of_avoid : ∀ {a b c : α} {P : Graph α β},
      πBar = {a, b, c} → IsGraphPathWithEnds GA' P a b → c ∉ V(P) →
      Disjoint (pathInternalVerts GA' P) πBar := by
    intro a b c P hbar hP hc
    refine Disjoint.mono_left (IsGraphPathWithEnds.pathInternalVerts_subset hP) ?_
    rw [hbar, Set.disjoint_left]
    rintro x ⟨hxP, hx_not_ab⟩ (rfl | rfl | rfl)
    · exact hx_not_ab (Or.inl rfl)
    · exact hx_not_ab (Or.inr rfl)
    · exact hc hxP
  refine ⟨hπ_V', fun x hx y hy => ?_⟩
  by_cases hxy : x = y
  · subst y
    have hx_GA' : x ∈ V(GA') := by
      rcases hx with ⟨s, hs, rfl⟩
      exact ⟨⟨s, hπ_V' hs, rfl⟩, hπ_A ⟨s, hs, rfl⟩⟩
    obtain ⟨P, hP, hP_int⟩ := exists_trivial_path_self hx_GA'
    exact ⟨P, hP, by rw [hP_int]; exact Set.empty_disjoint _⟩
  · obtain ⟨P₁, hP₁, hw₁⟩ := hP_uv
    obtain ⟨P₂, hP₂, hv₂⟩ := hP_uw
    obtain ⟨P₃, hP₃, hu₃⟩ := hP_vw
    have hx' : x ∈ ({ιV s_u, ιV s_v, ιV s_w} : Set α) := hπBar_eq ▸ hx
    have hy' : y ∈ ({ιV s_u, ιV s_v, ιV s_w} : Set α) := hπBar_eq ▸ hy
    rcases hx' with rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl
    · exact (hxy rfl).elim
    · exact ⟨P₁, hP₁, hdisj_of_avoid hπBar_eq hP₁ hw₁⟩
    · exact ⟨P₂, hP₂, hdisj_of_avoid (by rw [hπBar_eq]; ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto) hP₂ hv₂⟩
    · exact ⟨P₁, hP₁.symm, hdisj_of_avoid (by rw [hπBar_eq]; ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto) hP₁.symm hw₁⟩
    · exact (hxy rfl).elim
    · exact ⟨P₃, hP₃, hdisj_of_avoid (by rw [hπBar_eq]; ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto) hP₃ hu₃⟩
    · exact ⟨P₂, hP₂.symm, hdisj_of_avoid (by rw [hπBar_eq]; ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto) hP₂.symm hv₂⟩
    · exact ⟨P₃, hP₃.symm, hdisj_of_avoid (by rw [hπBar_eq]; ext; simp only [mem_insert_iff, mem_singleton_iff]; tauto) hP₃.symm hu₃⟩
    · exact (hxy rfl).elim

/-! ## 3. Augmenting Path Existence for Bad Members -/

set_option maxHeartbeats 400000 in
/-- Under `(J1)`–`(J7)`, for any bad member `A ∈ 𝒜` with `(Set.range (πS A) ∩ Γ.V).Nonempty`,
there exist `s₁, s₂ : S` and a path `Q` in `A.deleteVerts W` with ends `ιV s₁` and `ιV s₂` such
that:
1. `s₁ ≠ s₂`, `s₁ ∈ (Γ.interSet (D A)).V`, and `s₂ ∈ (Γ.interSet (D A)).V ∪ Set.range (πS A)`,
2. `E(Q).Nonempty` and `Disjoint E(Q) E((Γ.toEmbeddedGraph ιV ιE) ⊓ A)`,
3. `V(Q) ∩ (V((Γ.toEmbeddedGraph ιV ιE) ⊓ A) ∪ (ιV '' Set.range (πS A))) ⊆ {ιV s₁, ιV s₂}`,
4. For any drawing `Γ'` with `Γ.V ∪ {s₁, s₂} ⊆ Γ'.V` and
   `(Γ'.toEmbeddedGraph ιV ιE) ⊓ A = subgraphUnion (A.deleteVerts W) ((Γ.toEmbeddedGraph ιV ιE) ⊓ A) Q`,
   `A` satisfies `ConditionJ7.structure_Γ_inter_A` for `Γ'`. -/
theorem exists_augmenting_path_of_bad {q : ℕ}
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
    ∃ (s₁ s₂ : S) (Q : Graph α β),
      s₁ ≠ s₂ ∧
      s₁ ∈ (Γ.interSet (D A)).V ∧
      s₂ ∈ (Γ.interSet (D A)).V ∪ Set.range (πS A) ∧
      IsGraphPathWithEnds (A.deleteVerts W) Q (ιV s₁) (ιV s₂) ∧
      E(Q).Nonempty ∧
      Disjoint E(Q) E(GA) ∧
      V(Q) ∩ (V(GA) ∪ πBar) ⊆ {ιV s₁, ιV s₂} ∧
      ∀ (Γ' : Drawing S) (ιV' : S ↪ α) (ιE' : Set S ↪ β),
        (∀ s ∈ Set.range (πS A), ιV' s = ιV s) →
        Γ.V ∪ {s₁, s₂} ⊆ Γ'.V →
        (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A = subgraphUnion (A.deleteVerts W) GA Q →
        let GA' := (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A
        (V(GA') ⊆ πBar ∧ E(GA') = ∅) ∨
        (∃ u ∈ πBar, ∃ v ∈ πBar, IsGraphPathWithEnds GA' GA' u v) ∨
        (πLen A = 3 ∧ Set.range (πS A) ⊆ Γ'.V ∧
          ∃ w ∈ πBar, vertexValency GA' w = 0 ∧
            ∃ u₁ ∈ πBar \ {w}, ∃ u₂ ∈ πBar \ {w},
              IsGraphPathWithEnds (GA'.deleteVerts {w}) (GA'.deleteVerts {w}) u₁ u₂) ∨
        (πLen A = 3 ∧ IsGoodMember ιV' ιE' Γ' πLen πS A) := by
  intro GA πBar
  obtain ⟨_, _, hV_iff, _⟩ := interSet_DA_properties hJ hA
  have hπ_A : πBar ⊆ V(A) := by
    rintro _ ⟨s, ⟨i, rfl⟩, rfl⟩
    exact ((hJ.π_valid A hA).2.2.2 i).1
  have hGA_le_Adel : GA ≤ A.deleteVerts W := by
    refine ⟨?_, ?_⟩
    · intro x ⟨hxΓ, hxA⟩
      rw [vertexSet_deleteVerts]
      have hx_del := hJ.Γ_le.vertexSet_mono hxΓ
      rw [vertexSet_deleteVerts] at hx_del
      exact ⟨hxA, hx_del.2⟩
    · intro e x y hL
      rw [deleteVerts_isLink]
      have hLΓ : (Γ.toEmbeddedGraph ιV ιE).IsLink e x y := hL.mono inf_le_left
      have hx_del := hJ.Γ_le.vertexSet_mono hLΓ.left_mem
      have hy_del := hJ.Γ_le.vertexSet_mono hLΓ.right_mem
      rw [vertexSet_deleteVerts] at hx_del hy_del
      exact ⟨hL.mono inf_le_right, hx_del.2, hy_del.2⟩
  rcases bad_member_three_cases hJ hJ7 hA hbad hne with
    ⟨hV_GA, hE_GA, s_u, ⟨hsu_π, hsu_V⟩, s_v, hsv_π, hsu_ne_sv⟩ |
    ⟨hlen3, s_u, s_v, s_w, hsu_ne_sv, hsu_ne_sw, hsv_ne_sw, hrange_eq, hsu_V, hsv_V,
      GA₀, hGA₀_le, hP₀, hsw_not_GA₀, hV_GA_sub, hE_GA_eq⟩ |
    ⟨hlen3, s_u, s_v, s_w, hsu_ne_sv, hsu_ne_sw, hsv_ne_sw, hrange_eq, hsu_V, hsv_V, hsw_V,
      hP, hsw_GA⟩
  · -- Case (A): `V(GA) ⊆ πBar ∧ E(GA) = ∅`.
    obtain ⟨Q, hQ, hQ_disj⟩ :=
      hJ7.path_in_A A hA (ιV s_u) ⟨s_u, hsu_π, rfl⟩ (ιV s_v) ⟨s_v, hsv_π, rfl⟩
    have hsu_GA : ιV s_u ∈ V(GA) := ⟨⟨s_u, hsu_V, rfl⟩, hπ_A ⟨s_u, hsu_π, rfl⟩⟩
    have hsu_HAV : s_u ∈ (Γ.interSet (D A)).V := (hV_iff s_u).mpr hsu_GA
    have hQ_ne : E(Q).Nonempty :=
      IsGraphPathWithEnds.edgeSet_nonempty_of_ne hQ (fun h => hsu_ne_sv (ιV.injective h))
    have hQ_πBar : V(Q) ∩ πBar ⊆ {ιV s_u, ιV s_v} := by
      intro x ⟨hxQ, hxπ⟩
      by_contra hx_not
      exact Set.disjoint_left.mp hQ_disj
        (IsGraphPathWithEnds.pathInternalVerts_eq hQ ▸ ⟨hxQ, hx_not⟩) hxπ
    refine ⟨s_u, s_v, Q, hsu_ne_sv, hsu_HAV, Or.inr hsv_π, hQ, hQ_ne,
      by rw [hE_GA]; exact Set.disjoint_empty _,
      by rw [union_eq_right.mpr hV_GA]; exact hQ_πBar, ?_⟩
    intro Γ' ιV' ιE' hιV' _ hGA'_eq
    have hπBar' : ιV' '' Set.range (πS A) = πBar := image_congr hιV'
    have hQ_le_GA' : Q ≤ (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A := by
      rw [hGA'_eq]
      exact le_subgraphUnion_right hGA_le_Adel hQ.1
    have hV_GA'_sub : V((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A) ⊆ V(Q) ∪ (ιV' '' Set.range (πS A)) := by
      rw [hπBar', hGA'_eq, vertexSet_subgraphUnion]
      exact union_subset (hV_GA.trans subset_union_right) subset_union_left
    have hE_GA'_eq : E((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A) = E(Q) := by
      rw [hGA'_eq, edgeSet_subgraphUnion hGA_le_Adel hQ.1, hE_GA, empty_union]
    have hres := structure_of_path_plus_πBar (hJ.π_valid A hA).2.1 (hJ.π_valid A hA).2.2.1
      hQ_le_GA' (hπBar' ▸ ⟨s_u, hsu_π, rfl⟩) (hπBar' ▸ ⟨s_v, hsv_π, rfl⟩)
      (hQ.of_le le_rfl) hV_GA'_sub hE_GA'_eq
    dsimp only at hres ⊢
    rwa [hπBar'] at hres
  · -- Case (B): `GA₀ ≤ GA` is a path from `ιV s_u` to `ιV s_v` avoiding `ιV s_w`.
    have hsu_π : s_u ∈ Set.range (πS A) := by rw [hrange_eq]; simp
    have hsv_π : s_v ∈ Set.range (πS A) := by rw [hrange_eq]; simp
    have hsw_π : s_w ∈ Set.range (πS A) := by rw [hrange_eq]; simp
    obtain ⟨P, hP, hP_disj⟩ :=
      hJ7.path_in_A A hA (ιV s_u) ⟨s_u, hsu_π, rfl⟩ (ιV s_w) ⟨s_w, hsw_π, rfl⟩
    have hP_πBar : V(P) ∩ πBar ⊆ {ιV s_u, ιV s_w} := by
      intro x ⟨hxP, hxπ⟩
      by_contra hx_not
      exact Set.disjoint_left.mp hP_disj
        (IsGraphPathWithEnds.pathInternalVerts_eq hP ▸ ⟨hxP, hx_not⟩) hxπ
    obtain ⟨x, hx_GA₀, y, hy_w, Q, hQP, hQ_ft⟩ :=
      hP.exists_isFromToPathWithEnds (IsGraphPathWithEnds.left_mem hP₀) (mem_singleton (ιV s_w))
    have hy_eq : y = ιV s_w := mem_singleton_iff.mp hy_w
    subst y
    rcases hQ_ft with ⟨hQ, hQ_inter_GA₀, hQ_inter_w⟩
    have hx_GA : x ∈ V(GA) := hGA₀_le.vertexSet_mono hx_GA₀
    rcases hx_GA.1 with ⟨s₁, hs₁_V, hs₁_eq⟩
    have hx_eq : x = ιV s₁ := hs₁_eq.symm
    subst x
    have hs₁_HAV : s₁ ∈ (Γ.interSet (D A)).V := (hV_iff s₁).mpr hx_GA
    have hs₁_ne_sw : s₁ ≠ s_w := fun h => hsw_not_GA₀ (h ▸ hx_GA₀)
    have hQ_ne : E(Q).Nonempty :=
      IsGraphPathWithEnds.edgeSet_nonempty_of_ne hQ (fun h => hs₁_ne_sw (ιV.injective h))
    have hQ_inter_GA : V(Q) ∩ V(GA) ⊆ {ιV s₁, ιV s_w} := by
      intro z ⟨hzQ, hzGA⟩
      rcases hV_GA_sub hzGA with hzGA₀ | hzw
      · left
        have hz_mem : z ∈ V(Q) ∩ V(GA₀) := ⟨hzQ, hzGA₀⟩
        rwa [hQ_inter_GA₀, mem_singleton_iff] at hz_mem
      · right
        exact hzw
    have hQ_inter_πBar : V(Q) ∩ πBar ⊆ {ιV s₁, ιV s_w} := by
      intro z ⟨hzQ, hzπ⟩
      have hz_uw : z ∈ ({ιV s_u, ιV s_w} : Set α) := hP_πBar ⟨hQP.vertexSet_mono hzQ, hzπ⟩
      rcases hz_uw with rfl | rfl
      · left
        have hsu_mem : ιV s_u ∈ V(Q) ∩ V(GA₀) := ⟨hzQ, IsGraphPathWithEnds.left_mem hP₀⟩
        rwa [hQ_inter_GA₀, mem_singleton_iff] at hsu_mem
      · exact Or.inr rfl
    have hQ_disj_E : Disjoint E(Q) E(GA) := by
      rw [hE_GA_eq]
      exact disjoint_edgeSet_of_inter_vertexSet_sub_singleton hQ
        (hGA₀_le.trans hGA_le_Adel) hQ_inter_GA₀.subset
    refine ⟨s₁, s_w, Q, hs₁_ne_sw, hs₁_HAV, Or.inr hsw_π, hQ, hQ_ne, hQ_disj_E,
      by rw [inter_union_distrib_left]; exact union_subset hQ_inter_GA hQ_inter_πBar, ?_⟩
    intro Γ' ιV' ιE' hιV' hV'_sub hGA'_eq
    let GA' := (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A
    have hπBar' : ιV' '' Set.range (πS A) = πBar := image_congr hιV'
    have hGA₀_le_Adel : GA₀ ≤ A.deleteVerts W := hGA₀_le.trans hGA_le_Adel
    have hGA₀_le_GA' : GA₀ ≤ GA' := by
      change GA₀ ≤ (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A
      rw [hGA'_eq]
      exact hGA₀_le.trans (le_subgraphUnion_left hGA_le_Adel hQ.1)
    have hQ_le_GA' : Q ≤ GA' := by
      change Q ≤ (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A
      rw [hGA'_eq]
      exact le_subgraphUnion_right hGA_le_Adel hQ.1
    have hGA'_eq_union₀ : GA' = subgraphUnion GA' GA₀ Q := by
      refine (Compatible.of_le_le le_rfl (subgraphUnion_le hGA₀_le_GA' hQ_le_GA')).ext ?_ ?_
      · change V((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A) = V(subgraphUnion GA' GA₀ Q)
        rw [hGA'_eq, vertexSet_subgraphUnion, vertexSet_subgraphUnion]
        refine Subset.antisymm (union_subset ?_ subset_union_right)
          (union_subset (hGA₀_le.vertexSet_mono.trans subset_union_left) subset_union_right)
        refine hV_GA_sub.trans (union_subset subset_union_left ?_)
        exact singleton_subset_iff.mpr (Or.inr (IsGraphPathWithEnds.right_mem hQ))
      · change E((Γ'.toEmbeddedGraph ιV' ιE') ⊓ A) = E(subgraphUnion GA' GA₀ Q)
        rw [hGA'_eq, edgeSet_subgraphUnion hGA_le_Adel hQ.1,
          edgeSet_subgraphUnion hGA₀_le_GA' hQ_le_GA', hE_GA_eq]
    have hGA₀_Q_inter : V(GA₀) ∩ V(Q) = {ιV s₁} := by
      rw [Set.inter_comm, hQ_inter_GA₀]
    by_cases hs₁_u : s₁ = s_u
    · subst hs₁_u
      right; left
      refine ⟨ιV s_v, ⟨s_v, hsv_π, rfl⟩, ιV s_w, ⟨s_w, hsw_π, rfl⟩, ?_⟩
      have hpath : IsGraphPathWithEnds GA' (subgraphUnion GA' GA₀ Q) (ιV s_v) (ιV s_w) :=
        IsGraphPathWithEnds.subgraphUnion (hP₀.symm.mono hGA₀_le_GA')
          (hQ.of_le hQ_le_GA') hGA₀_Q_inter
      rwa [← hGA'_eq_union₀] at hpath
    · by_cases hs₁_v : s₁ = s_v
      · subst hs₁_v
        right; left
        refine ⟨ιV s_u, ⟨s_u, hsu_π, rfl⟩, ιV s_w, ⟨s_w, hsw_π, rfl⟩, ?_⟩
        have hpath : IsGraphPathWithEnds GA' (subgraphUnion GA' GA₀ Q) (ιV s_u) (ιV s_w) :=
          IsGraphPathWithEnds.subgraphUnion (hP₀.mono hGA₀_le_GA')
            (hQ.of_le hQ_le_GA') hGA₀_Q_inter
        rwa [← hGA'_eq_union₀] at hpath
      · right; right; right
        refine ⟨hlen3, ?_⟩
        have hπ_V' : Set.range (πS A) ⊆ Γ'.V := by
          rw [hrange_eq]
          rintro _ (rfl | rfl | rfl)
          · exact hV'_sub (Or.inl hsu_V)
          · exact hV'_sub (Or.inl hsv_V)
          · exact hV'_sub (Or.inr (Or.inr rfl))
        obtain ⟨P₁, P₂, hP₁_le, hP₂_le, hP₁, hP₂, _, hP₁₂_inter, _⟩ :=
          hP₀.exists_split_at hx_GA₀
        have hP₁_GA' : P₁ ≤ GA' := hP₁_le.trans hGA₀_le_GA'
        have hP₂_GA' : P₂ ≤ GA' := hP₂_le.trans hGA₀_le_GA'
        have hP₁_Q_inter : V(P₁) ∩ V(Q) = {ιV s₁} := by
          refine Subset.antisymm ?_
            (singleton_subset_iff.mpr ⟨IsGraphPathWithEnds.right_mem hP₁,
              IsGraphPathWithEnds.left_mem hQ⟩)
          rw [← hGA₀_Q_inter]
          exact inter_subset_inter_left _ hP₁_le.vertexSet_mono
        have hP₂_Q_inter : V(P₂) ∩ V(Q) = {ιV s₁} := by
          refine Subset.antisymm ?_
            (singleton_subset_iff.mpr ⟨IsGraphPathWithEnds.left_mem hP₂,
              IsGraphPathWithEnds.left_mem hQ⟩)
          rw [← hGA₀_Q_inter]
          exact inter_subset_inter_left _ hP₂_le.vertexSet_mono
        have hsv_not_P₁Q : ιV' s_v ∉ V(subgraphUnion GA' P₁ Q) := by
          rw [hιV' s_v hsv_π, vertexSet_subgraphUnion]
          rintro (hsv_P₁ | hsv_Q)
          · have : ιV s_v ∈ V(P₁) ∩ V(P₂) := ⟨hsv_P₁, IsGraphPathWithEnds.right_mem hP₂⟩
            rw [hP₁₂_inter, mem_singleton_iff] at this
            exact hs₁_v (ιV.injective this.symm)
          · have : ιV s_v ∈ V(Q) ∩ V(GA₀) := ⟨hsv_Q, IsGraphPathWithEnds.right_mem hP₀⟩
            rw [hQ_inter_GA₀, mem_singleton_iff] at this
            exact hs₁_v (ιV.injective this.symm)
        have hsu_not_P₂Q : ιV' s_u ∉ V(subgraphUnion GA' P₂ Q) := by
          rw [hιV' s_u hsu_π, vertexSet_subgraphUnion]
          rintro (hsu_P₂ | hsu_Q)
          · have : ιV s_u ∈ V(P₁) ∩ V(P₂) := ⟨IsGraphPathWithEnds.left_mem hP₁, hsu_P₂⟩
            rw [hP₁₂_inter, mem_singleton_iff] at this
            exact hs₁_u (ιV.injective this.symm)
          · have : ιV s_u ∈ V(Q) ∩ V(GA₀) := ⟨hsu_Q, IsGraphPathWithEnds.left_mem hP₀⟩
            rw [hQ_inter_GA₀, mem_singleton_iff] at this
            exact hs₁_u (ιV.injective this.symm)
        have hP_uv' : IsGraphPathWithEnds GA' GA₀ (ιV' s_u) (ιV' s_v) := by
          rw [hιV' s_u hsu_π, hιV' s_v hsv_π]
          exact hP₀.mono hGA₀_le_GA'
        have hP_uw' : IsGraphPathWithEnds GA' (subgraphUnion GA' P₁ Q) (ιV' s_u) (ιV' s_w) := by
          rw [hιV' s_u hsu_π, hιV' s_w hsw_π]
          exact IsGraphPathWithEnds.subgraphUnion (hP₁.mono hGA₀_le_GA') (hQ.of_le hQ_le_GA')
            hP₁_Q_inter
        have hP_vw' : IsGraphPathWithEnds GA' (subgraphUnion GA' P₂ Q) (ιV' s_v) (ιV' s_w) := by
          rw [hιV' s_v hsv_π, hιV' s_w hsw_π]
          exact IsGraphPathWithEnds.subgraphUnion (hP₂.symm.mono hGA₀_le_GA') (hQ.of_le hQ_le_GA')
            hP₂_Q_inter
        have hsw_not_GA₀' : ιV' s_w ∉ V(GA₀) := by
          rwa [hιV' s_w hsw_π]
        exact isGoodMember_of_three_paths hrange_eq hπ_V' (hπBar' ▸ hπ_A)
          ⟨GA₀, hP_uv', hsw_not_GA₀'⟩
          ⟨subgraphUnion GA' P₁ Q, hP_uw', hsv_not_P₁Q⟩
          ⟨subgraphUnion GA' P₂ Q, hP_vw', hsu_not_P₂Q⟩
  · -- Case (C): `GA` is a path from `ιV s_u` to `ιV s_v` containing `ιV s_w`.
    have hsu_π : s_u ∈ Set.range (πS A) := by rw [hrange_eq]; simp
    have hsv_π : s_v ∈ Set.range (πS A) := by rw [hrange_eq]; simp
    have hsw_π : s_w ∈ Set.range (πS A) := by rw [hrange_eq]; simp
    obtain ⟨GA₁, GA₂, hGA₁_le, hGA₂_le, hGA₁, hGA₂, hGA_union, hGA₁₂_inter, _⟩ :=
      hP.exists_split_at hsw_GA
    obtain ⟨P, hP_Adel, hP_disj⟩ :=
      hJ7.path_in_A A hA (ιV s_u) ⟨s_u, hsu_π, rfl⟩ (ιV s_v) ⟨s_v, hsv_π, rfl⟩
    have hsw_not_P : ιV s_w ∉ V(P) := by
      intro hsw_P
      have hsw_int : ιV s_w ∈ pathInternalVerts (A.deleteVerts W) P := by
        rw [IsGraphPathWithEnds.pathInternalVerts_eq hP_Adel]
        refine ⟨hsw_P, ?_⟩
        rintro (h | h)
        · exact hsu_ne_sw (ιV.injective h.symm)
        · exact hsv_ne_sw (ιV.injective h.symm)
      exact Set.disjoint_left.mp hP_disj hsw_int ⟨s_w, hsw_π, rfl⟩
    obtain ⟨x, hx_GA₁, y, hy_GA₂, Q, hQP, hQ_ft⟩ :=
      hP_Adel.exists_isFromToPathWithEnds
        (IsGraphPathWithEnds.left_mem hGA₁) (IsGraphPathWithEnds.right_mem hGA₂)
    rcases hQ_ft with ⟨hQ, hQ_inter_GA₁, hQ_inter_GA₂⟩
    have hx_GA : x ∈ V(GA) := hGA₁_le.vertexSet_mono hx_GA₁
    have hy_GA : y ∈ V(GA) := hGA₂_le.vertexSet_mono hy_GA₂
    rcases hx_GA.1 with ⟨s₁, hs₁_V, hs₁_eq⟩
    rcases hy_GA.1 with ⟨s₂, hs₂_V, hs₂_eq⟩
    have hx_eq : x = ιV s₁ := hs₁_eq.symm
    have hy_eq : y = ιV s₂ := hs₂_eq.symm
    subst x y
    have hs₁_HAV : s₁ ∈ (Γ.interSet (D A)).V := (hV_iff s₁).mpr hx_GA
    have hs₂_HAV : s₂ ∈ (Γ.interSet (D A)).V := (hV_iff s₂).mpr hy_GA
    have hsw_not_Q : ιV s_w ∉ V(Q) := fun h => hsw_not_P (hQP.vertexSet_mono h)
    have hs₁_ne_sw : s₁ ≠ s_w := fun h => hsw_not_Q (h ▸ IsGraphPathWithEnds.left_mem hQ)
    have hs₂_ne_sw : s₂ ≠ s_w := fun h => hsw_not_Q (h ▸ IsGraphPathWithEnds.right_mem hQ)
    have hs₁_ne_s₂ : s₁ ≠ s₂ := by
      intro h
      subst h
      have : ιV s₁ ∈ V(GA₁) ∩ V(GA₂) := ⟨hx_GA₁, hy_GA₂⟩
      rw [hGA₁₂_inter, mem_singleton_iff] at this
      exact hs₁_ne_sw (ιV.injective this)
    have hQ_ne : E(Q).Nonempty :=
      IsGraphPathWithEnds.edgeSet_nonempty_of_ne hQ (fun h => hs₁_ne_s₂ (ιV.injective h))
    have hV_GA_eq : V(GA) = V(GA₁) ∪ V(GA₂) := by
      rw [← vertexSet_subgraphUnion GA GA₁ GA₂, hGA_union]
    have hE_GA_eq : E(GA) = E(GA₁) ∪ E(GA₂) := by
      rw [← edgeSet_subgraphUnion hGA₁_le hGA₂_le, hGA_union]
    have hQ_inter_GA : V(Q) ∩ V(GA) ⊆ {ιV s₁, ιV s₂} := by
      rw [hV_GA_eq, inter_union_distrib_left, hQ_inter_GA₁, hQ_inter_GA₂]
      rfl
    have hπBar_sub_GA : πBar ⊆ V(GA) := by
      rintro _ ⟨s, hs, rfl⟩
      rw [hrange_eq] at hs
      rcases hs with rfl | rfl | rfl
      · exact IsGraphPathWithEnds.left_mem hP
      · exact IsGraphPathWithEnds.right_mem hP
      · exact hsw_GA
    have hQ_disj_E : Disjoint E(Q) E(GA) := by
      rw [hE_GA_eq]
      exact Disjoint.union_right
        (disjoint_edgeSet_of_inter_vertexSet_sub_singleton hQ
          (hGA₁_le.trans hGA_le_Adel) hQ_inter_GA₁.subset)
        (disjoint_edgeSet_of_inter_vertexSet_sub_singleton hQ
          (hGA₂_le.trans hGA_le_Adel) hQ_inter_GA₂.subset)
    refine ⟨s₁, s₂, Q, hs₁_ne_s₂, hs₁_HAV, Or.inl hs₂_HAV, hQ, hQ_ne, hQ_disj_E,
      by rw [union_eq_left.mpr hπBar_sub_GA]; exact hQ_inter_GA, ?_⟩
    intro Γ' ιV' ιE' hιV' hV'_sub hGA'_eq
    let GA' := (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A
    have hπBar' : ιV' '' Set.range (πS A) = πBar := image_congr hιV'
    right; right; right
    refine ⟨hlen3, ?_⟩
    have hπ_V' : Set.range (πS A) ⊆ Γ'.V := by
      rw [hrange_eq]
      rintro _ (rfl | rfl | rfl)
      · exact hV'_sub (Or.inl hsu_V)
      · exact hV'_sub (Or.inl hsv_V)
      · exact hV'_sub (Or.inl hsw_V)
    have hGA_le_GA' : GA ≤ GA' := by
      change GA ≤ (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A
      rw [hGA'_eq]
      exact le_subgraphUnion_left hGA_le_Adel hQ.1
    have hQ_le_GA' : Q ≤ GA' := by
      change Q ≤ (Γ'.toEmbeddedGraph ιV' ιE') ⊓ A
      rw [hGA'_eq]
      exact le_subgraphUnion_right hGA_le_Adel hQ.1
    have hsv_not_GA₁ : ιV' s_v ∉ V(GA₁) := by
      rw [hιV' s_v hsv_π]
      intro hsv_GA₁
      have : ιV s_v ∈ V(GA₁) ∩ V(GA₂) := ⟨hsv_GA₁, IsGraphPathWithEnds.right_mem hGA₂⟩
      rw [hGA₁₂_inter, mem_singleton_iff] at this
      exact hsv_ne_sw (ιV.injective this)
    have hsu_not_GA₂ : ιV' s_u ∉ V(GA₂) := by
      rw [hιV' s_u hsu_π]
      intro hsu_GA₂
      have : ιV s_u ∈ V(GA₁) ∩ V(GA₂) := ⟨IsGraphPathWithEnds.left_mem hGA₁, hsu_GA₂⟩
      rw [hGA₁₂_inter, mem_singleton_iff] at this
      exact hsu_ne_sw (ιV.injective this)
    obtain ⟨GA₁a, GA₁b, hGA₁a_le, hGA₁b_le, hGA₁a, hGA₁b, _, hGA₁ab_inter, _⟩ :=
      hGA₁.exists_split_at hx_GA₁
    obtain ⟨GA₂a, GA₂b, hGA₂a_le, hGA₂b_le, hGA₂a, hGA₂b, _, hGA₂ab_inter, _⟩ :=
      hGA₂.exists_split_at hy_GA₂
    have hGA₁a_GA' : GA₁a ≤ GA' := (hGA₁a_le.trans hGA₁_le).trans hGA_le_GA'
    have hGA₂b_GA' : GA₂b ≤ GA' := (hGA₂b_le.trans hGA₂_le).trans hGA_le_GA'
    have hsw_not_GA₁a : ιV s_w ∉ V(GA₁a) := by
      intro hsw_1a
      have : ιV s_w ∈ V(GA₁a) ∩ V(GA₁b) := ⟨hsw_1a, IsGraphPathWithEnds.right_mem hGA₁b⟩
      rw [hGA₁ab_inter, mem_singleton_iff] at this
      exact hs₁_ne_sw (ιV.injective this.symm)
    have hsw_not_GA₂b : ιV s_w ∉ V(GA₂b) := by
      intro hsw_2b
      have : ιV s_w ∈ V(GA₂a) ∩ V(GA₂b) := ⟨IsGraphPathWithEnds.left_mem hGA₂a, hsw_2b⟩
      rw [hGA₂ab_inter, mem_singleton_iff] at this
      exact hs₂_ne_sw (ιV.injective this.symm)
    have hGA₁a_Q_inter : V(GA₁a) ∩ V(Q) = {ιV s₁} := by
      refine Subset.antisymm ?_
        (singleton_subset_iff.mpr ⟨IsGraphPathWithEnds.right_mem hGA₁a,
          IsGraphPathWithEnds.left_mem hQ⟩)
      rw [Set.inter_comm, ← hQ_inter_GA₁]
      exact inter_subset_inter_right _ hGA₁a_le.vertexSet_mono
    have hP_u_s₂ : IsGraphPathWithEnds GA' (subgraphUnion GA' GA₁a Q) (ιV s_u) (ιV s₂) :=
      IsGraphPathWithEnds.subgraphUnion (hGA₁a.mono (hGA₁_le.trans hGA_le_GA'))
        (hQ.of_le hQ_le_GA') hGA₁a_Q_inter
    have hGA₁a_GA₂b_disj : V(GA₁a) ∩ V(GA₂b) = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
      intro hz1a hz2b
      have hz_w : z ∈ V(GA₁) ∩ V(GA₂) :=
        ⟨hGA₁a_le.vertexSet_mono hz1a, hGA₂b_le.vertexSet_mono hz2b⟩
      rw [hGA₁₂_inter, mem_singleton_iff] at hz_w
      exact hsw_not_GA₁a (hz_w ▸ hz1a)
    have hGA₁aQ_GA₂b_inter : V(subgraphUnion GA' GA₁a Q) ∩ V(GA₂b) = {ιV s₂} := by
      rw [vertexSet_subgraphUnion, union_inter_distrib_right, hGA₁a_GA₂b_disj, empty_union]
      refine Subset.antisymm ?_
        (singleton_subset_iff.mpr ⟨IsGraphPathWithEnds.right_mem hQ,
          IsGraphPathWithEnds.left_mem hGA₂b⟩)
      rw [← hQ_inter_GA₂]
      exact inter_subset_inter_right _ hGA₂b_le.vertexSet_mono
    have hP_uv' : IsGraphPathWithEnds GA'
        (subgraphUnion GA' (subgraphUnion GA' GA₁a Q) GA₂b) (ιV' s_u) (ιV' s_v) := by
      rw [hιV' s_u hsu_π, hιV' s_v hsv_π]
      exact IsGraphPathWithEnds.subgraphUnion hP_u_s₂ (hGA₂b.mono (hGA₂_le.trans hGA_le_GA'))
        hGA₁aQ_GA₂b_inter
    have hsw_not_P_uv' : ιV' s_w ∉ V(subgraphUnion GA' (subgraphUnion GA' GA₁a Q) GA₂b) := by
      rw [hιV' s_w hsw_π, vertexSet_subgraphUnion, vertexSet_subgraphUnion]
      rintro ((h | h) | h)
      · exact hsw_not_GA₁a h
      · exact hsw_not_Q h
      · exact hsw_not_GA₂b h
    have hP_uw' : IsGraphPathWithEnds GA' GA₁ (ιV' s_u) (ιV' s_w) := by
      rw [hιV' s_u hsu_π, hιV' s_w hsw_π]
      exact hGA₁.mono hGA_le_GA'
    have hP_vw' : IsGraphPathWithEnds GA' GA₂ (ιV' s_v) (ιV' s_w) := by
      rw [hιV' s_v hsv_π, hιV' s_w hsw_π]
      exact hGA₂.symm.mono hGA_le_GA'
    exact isGoodMember_of_three_paths hrange_eq hπ_V' (hπBar' ▸ hπ_A)
      ⟨subgraphUnion GA' (subgraphUnion GA' GA₁a Q) GA₂b, hP_uv', hsw_not_P_uv'⟩
      ⟨GA₁, hP_uw', hsv_not_GA₁⟩
      ⟨GA₂, hP_vw', hsu_not_GA₂⟩

end GraphMinor.GM22
