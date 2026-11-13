module

public import GraphMinor.GM22.Section4Basic

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 4 (Part 2): Component Connection and Theorem 4.1

This file completes the proof of **4.1** (`theorem_4_1`) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 537–538).

Given a finely subdivided $T$-variant $D_3$ of $D$ from `exists_pullback_fine_subdiv`, we construct
pairwise disjoint subdrawings $H_i$ ($i \in \operatorname{Fin} k$) of $D_3$ corresponding to the
connected components $C_i$ of $(L' \cap (\Gamma' \setminus E(K))).\text{comapEmbed}$, connect each
$V(C_i)$ within $H_i$ by adding minimal chords inside $W_i \cap T$, and apply **2.6** (`theorem_2_6`)
together with `PullbackTo.pullback` to obtain $L \subseteq G$.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric unitInterval Classical Graph
  GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09
  GraphMinor.GM11 GraphMinor.GM16

local notation "𝕀" => unitInterval

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]

/-! ## 1. Subdrawing Helpers and Walk Step Extraction -/

omit [T2Space S] in
theorem _root_.GraphMinor.Surface.Drawing.IsSubdrawing.U_inter_V {N D₁ : Drawing S}
    (hsub : N.IsSubdrawing D₁) :
    N.U ∩ D₁.V = N.V := by
  refine Subset.antisymm ?_ (subset_inter N.V_subset_U hsub.1)
  rintro x ⟨hxU, hxV⟩
  rw [N.U_eq] at hxU
  rcases hxU with hxNV | hxE
  · exact hxNV
  · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxE
    have hx_cap : x ∈ closure e ∩ D₁.V := ⟨hxe, hxV⟩
    rw [← hsub.closure_inter_V he] at hx_cap
    exact hx_cap.2

omit [T2Space S] in
theorem _root_.GraphMinor.Surface.Drawing.IsSubdrawing.toGraph_le {N D₁ : Drawing S}
    (hsub : N.IsSubdrawing D₁) :
    N.toGraph ≤ D₁.toGraph :=
  ⟨hsub.1, fun _ _ _ hl => (hsub.isLink_iff hl.1).mp hl⟩

theorem subdivEdgeSplit_isSubdrawing_self {N D₁ : Drawing S} (hsub : N.IsSubdrawing D₁)
    {e : Set S} (heN : e ∈ N.E) (he₁ : e ∈ D₁.E)
    {u v v₀ : S} (hcapN : closure e ∩ N.V = {u, v}) (hcap₁ : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    (subdivEdgeSplit N heN hcapN huv₀ hv₀v hL₁ hL₂ hU hI).IsSubdrawing
      (subdivEdgeSplit D₁ he₁ hcap₁ huv₀ hv₀v hL₁ hL₂ hU hI) := by
  refine ⟨?_, ?_⟩
  · rw [subdivEdgeSplit_V, subdivEdgeSplit_V]
    exact insert_subset_insert hsub.1
  · rw [subdivEdgeSplit_E, subdivEdgeSplit_E]
    exact union_subset_union_left _ (sdiff_le_sdiff_right hsub.2)

theorem subdivEdgeSplit_isSubdrawing_other {M D₁ : Drawing S} (hsub : M.IsSubdrawing D₁)
    {e : Set S} (he₁ : e ∈ D₁.E) (heM : e ∉ M.E)
    {u v v₀ : S} (hcap₁ : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    M.IsSubdrawing (subdivEdgeSplit D₁ he₁ hcap₁ huv₀ hv₀v hL₁ hL₂ hU hI) := by
  refine ⟨?_, ?_⟩
  · rw [subdivEdgeSplit_V]
    exact hsub.1.trans (subset_insert v₀ D₁.V)
  · rw [subdivEdgeSplit_E]
    intro f hf
    exact Or.inl ⟨hsub.2 hf, fun hfe => heM (hfe ▸ hf)⟩

theorem glue_lineDrawing_isSubdrawing_self {N D₁ : Drawing S} (hsub : N.IsSubdrawing D₁)
    {x y : S} (hxy : x ≠ y) {J : Set S} (hJ : IsLineWithEnds J x y)
    (hmeet_N : N.U ∩ (lineDrawing hJ hxy).U ⊆ N.V ∩ (lineDrawing hJ hxy).V)
    (hmeet_D : D₁.U ∩ (lineDrawing hJ hxy).U ⊆ D₁.V ∩ (lineDrawing hJ hxy).V) :
    (N.glue (lineDrawing hJ hxy) hmeet_N).IsSubdrawing
      (D₁.glue (lineDrawing hJ hxy) hmeet_D) := by
  refine ⟨union_subset_union_left _ hsub.1, ?_⟩
  rw [Drawing.glue_E, Drawing.glue_E]
  exact union_subset_union_left _ hsub.2

theorem glue_lineDrawing_isSubdrawing_other {M D₁ : Drawing S} (hsub : M.IsSubdrawing D₁)
    {x y : S} (hxy : x ≠ y) {J : Set S} (hJ : IsLineWithEnds J x y)
    (hmeet_D : D₁.U ∩ (lineDrawing hJ hxy).U ⊆ D₁.V ∩ (lineDrawing hJ hxy).V) :
    M.IsSubdrawing (D₁.glue (lineDrawing hJ hxy) hmeet_D) := by
  refine ⟨hsub.1.trans subset_union_left, ?_⟩
  rw [Drawing.glue_E]
  exact hsub.2.trans subset_union_left

omit [TopologicalSpace S] [T2Space S] in
/-- Along any walk in a graph `C` from a vertex satisfying `P` to a vertex not satisfying `P`,
there is a link step from a vertex satisfying `P` to a vertex not satisfying `P`. -/
theorem exists_link_step_of_walk {C : Graph S (Set S)} {P : S → Prop} {a b : S}
    (W : GraphWalk C a b) (ha : P a) (hb : ¬ P b) :
    ∃ e u v, C.IsLink e u v ∧ P u ∧ ¬ P v := by
  induction W with
  | nil _ => exact (hb ha).elim
  | @cons x y z e hl _ ih =>
    by_cases hy : P y
    · exact ih hy hb
    · exact ⟨e, x, y, hl, ha, hy⟩

/-! ## 2. Phase 2 State and Component Connection Operations -/

/-- Bundled state for Phase 2 of the proof of **4.1**: a `T`-variant `D_cur` of `D` together with
pairwise disjoint subdrawings `H : Fin k → Drawing S` corresponding to the components `C i`. -/
private structure Phase2State (h p : ℕ) (D D' : Drawing S) (K : Graph α β)
    (ιV : S ↪ α) (ιE : Set S ↪ β) {k : ℕ} (C : Fin k → Graph S (Set S)) : Type w where
  D_cur : Drawing S
  H : Fin k → Drawing S
  pb : PullbackTo h p D K ιV ιE D_cur
  DV_sub : D.V ⊆ D_cur.V
  D'V_sub : D'.V ⊆ D_cur.V
  EE_sub : D.E ∩ D'.E ⊆ D_cur.E
  C_le : ∀ i, C i ≤ D'.toGraph
  edge_T_line : ∀ f ∈ D_cur.E \ (D.E ∩ D'.E),
    closure f ⊆ insulatedSet D (ιV ⁻¹' V(K)) h ∧ IsLineEdge D_cur f
  isSubdrawing : ∀ i, (H i).IsSubdrawing D_cur
  VC_sub : ∀ i, V(C i) ⊆ (H i).V
  EC_inter_sub : ∀ i, E(C i) ∩ D.E ⊆ (H i).E
  U_inter_W_sub : ∀ i, D_cur.U ∩ (V(C i) ∪ ⋃ e ∈ E(C i), closure e) ⊆ (H i).U
  disj_E_EK : ∀ i, Disjoint (H i).E (ιE ⁻¹' E(K))
  disj_U_W : ∀ i j, i ≠ j → Disjoint (H i).U (V(C j) ∪ ⋃ e ∈ E(C j), closure e)
  pairwise_disj_U : Pairwise (Disjoint on fun i => (H i).U)
  V_inter_VK : ∀ i, (H i).V ∩ (ιV ⁻¹' V(K)) = V(C i) ∩ (ιV ⁻¹' V(K))

/-- Constructing the initial `Phase2State` from `D₃` produced by `exists_pullback_fine_subdiv`. -/
private noncomputable def Phase2State.init {h p : ℕ} (hh : 1 ≤ h)
    {D D' D₂ D₃ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hVar' : IsVariant D D' (insulatedSet D (ιV ⁻¹' V(K)) h))
    {k : ℕ} (C : Fin k → Graph S (Set S))
    (hC_le : ∀ i, C i ≤ D'.toGraph)
    (hC_disj_EK : ∀ i, Disjoint E(C i) (ιE ⁻¹' E(K)))
    (hW_disj : Pairwise (Disjoint on fun i => V(C i) ∪ ⋃ e ∈ E(C i), closure e))
    (hDV₂ : D.V ⊆ D₂.V) (hD'V₂ : D'.V ⊆ D₂.V)
    (hPB₃ : PullbackTo h p D K ιV ιE D₃)
    (hV₂₃ : D₂.V ⊆ D₃.V)
    (hEE₃ : D.E ∩ D'.E ⊆ D₃.E)
    (h_fine₃ : ∀ f ∈ D₃.E \ (D.E ∩ D'.E),
      closure f ⊆ insulatedSet D (ιV ⁻¹' V(K)) h ∧
      IsLineEdge D₃ f ∧
      ∀ i : Fin k, (closure f ∩ (V(C i) ∪ ⋃ e ∈ E(C i), closure e)).Nonempty →
        Disjoint (closure f)
          ((D₂.V \ (V(C i) ∪ ⋃ e ∈ E(C i), closure e)) ∪
            ⋃ j ∈ ({i}ᶜ : Set (Fin k)), (V(C j) ∪ ⋃ e ∈ E(C j), closure e)))
    (h_disj₃ : ∀ f₁ ∈ D₃.E \ (D.E ∩ D'.E), ∀ f₂ ∈ D₃.E \ (D.E ∩ D'.E),
      ∀ i j : Fin k, i ≠ j →
        (closure f₁ ∩ (V(C i) ∪ ⋃ e ∈ E(C i), closure e)).Nonempty →
        (closure f₂ ∩ (V(C j) ∪ ⋃ e ∈ E(C j), closure e)).Nonempty →
        Disjoint (closure f₁) (closure f₂)) :
    Phase2State h p D D' K ιV ιE C :=
  let W : Fin k → Set S := fun i => V(C i) ∪ ⋃ e ∈ E(C i), closure e
  let E_init : Fin k → Set (Set S) := fun i =>
    (E(C i) ∩ D.E) ∪ {f ∈ D₃.E \ (D.E ∩ D'.E) | (closure f ∩ W i).Nonempty}
  let H_init : Fin k → Drawing S := fun i => D₃.span (D₃.V ∩ W i) (E_init i)
  have hEC_sub_D' : ∀ i, E(C i) ⊆ D'.E := fun i => (hC_le i).edgeSet_mono
  have hE_init_sub : ∀ i, E_init i ⊆ D₃.E := by
    intro i f hf
    rcases hf with ⟨hfC, hfD⟩ | ⟨hf₃, _⟩
    · exact hEE₃ ⟨hfD, hEC_sub_D' i hfC⟩
    · exact hf₃.1
  have hH_E : ∀ i, (H_init i).E = E_init i := by
    intro i
    change (D₃.span (D₃.V ∩ W i) (E_init i)).E = E_init i
    rw [D₃.span_E]
    exact inter_eq_left.mpr (hE_init_sub i)
  have hW_inter_D'V : ∀ i, W i ∩ D'.V = V(C i) := by
    intro i
    refine Subset.antisymm ?_ (subset_inter subset_union_left (hC_le i).vertexSet_mono)
    rintro x ⟨hxV | hxE, hxD'V⟩
    · exact hxV
    · obtain ⟨e, heC, hxe⟩ := mem_iUnion₂.mp hxE
      obtain ⟨u, v, hl⟩ := (C i).exists_isLink_of_mem_edgeSet heC
      have hl' : D'.toGraph.IsLink e u v := (hC_le i).isLink_mono hl
      have hx_uv : x ∈ ({u, v} : Set S) := hl'.2.2.2 ▸ ⟨hxe, hxD'V⟩
      rcases hx_uv with rfl | rfl
      · exact hl.left_mem
      · exact hl.right_mem
  have hH_U_sub : ∀ i, (H_init i).U ⊆ (D₃.V ∩ W i) ∪ ⋃ f ∈ E_init i, closure f := by
    intro i x hx
    change x ∈ D₃.spanU (D₃.V ∩ W i) (E_init i) at hx
    rcases hx with (⟨hx, _⟩ | hx_ends) | hx_cl
    · exact Or.inl hx
    · obtain ⟨f, ⟨hf, _⟩, hxf, _⟩ := mem_iUnion₂.mp hx_ends
      exact Or.inr (mem_iUnion₂.mpr ⟨f, hf, hxf⟩)
    · obtain ⟨f, ⟨hf, _⟩, hxf⟩ := mem_iUnion₂.mp hx_cl
      exact Or.inr (mem_iUnion₂.mpr ⟨f, hf, hxf⟩)
  have h_disj_U_W : ∀ i j, i ≠ j → Disjoint (H_init i).U (W j) := by
    intro i j hij
    rw [disjoint_left]
    intro x hxU hxWj
    rcases hH_U_sub i hxU with ⟨_, hxWi⟩ | hx_cl
    · exact disjoint_left.mp (hW_disj hij) hxWi hxWj
    · obtain ⟨f, hf_init, hxf⟩ := mem_iUnion₂.mp hx_cl
      rcases hf_init with ⟨hfC, _⟩ | ⟨hf_diff, hne_Wi⟩
      · have hxWi : x ∈ W i := Or.inr (mem_iUnion₂.mpr ⟨f, hfC, hxf⟩)
        exact disjoint_left.mp (hW_disj hij) hxWi hxWj
      · have hdisj_B := (h_fine₃ f hf_diff).2.2 i hne_Wi
        exact disjoint_left.mp hdisj_B hxf (Or.inr (mem_iUnion₂.mpr ⟨j, hij.symm, hxWj⟩))
  { D_cur := D₃
    H := H_init
    pb := hPB₃
    DV_sub := hDV₂.trans hV₂₃
    D'V_sub := hD'V₂.trans hV₂₃
    EE_sub := hEE₃
    C_le := hC_le
    edge_T_line := fun f hf => ⟨(h_fine₃ f hf).1, (h_fine₃ f hf).2.1⟩
    isSubdrawing := fun i => D₃.span_isSubdrawing _ _
    VC_sub := fun i x hx => Or.inl ⟨⟨hV₂₃ (hD'V₂ ((hC_le i).vertexSet_mono hx)), Or.inl hx⟩,
      hV₂₃ (hD'V₂ ((hC_le i).vertexSet_mono hx))⟩
    EC_inter_sub := fun i f hf => by rw [hH_E i]; exact Or.inl hf
    U_inter_W_sub := by
      intro i x ⟨hxU, hxWi⟩
      rw [D₃.U_eq] at hxU
      rcases hxU with hxV₃ | hxE₃
      · exact Or.inl (Or.inl ⟨⟨hxV₃, hxWi⟩, hxV₃⟩)
      · obtain ⟨f, hf₃, hxf⟩ := mem_iUnion₂.mp hxE₃
        by_cases hf_inter : f ∈ D.E ∩ D'.E
        · by_cases hxD'V : x ∈ D'.V
          · have hxV₃ : x ∈ D₃.V := hV₂₃ (hD'V₂ hxD'V)
            exact Or.inl (Or.inl ⟨⟨hxV₃, hxWi⟩, hxV₃⟩)
          · have hxf_in : x ∈ f := by
              rw [← D'.closure_diff_V hf_inter.2]
              exact ⟨hxf, hxD'V⟩
            rcases hxWi with hxVC | hxEC
            · exact (hxD'V ((hC_le i).vertexSet_mono hxVC)).elim
            · obtain ⟨e', he'C, hxe'⟩ := mem_iUnion₂.mp hxEC
              have hxe'_in : x ∈ e' := by
                rw [← D'.closure_diff_V (hEC_sub_D' i he'C)]
                exact ⟨hxe', hxD'V⟩
              obtain rfl : f = e' := D'.edge_eq_of_mem hf_inter.2 (hEC_sub_D' i he'C) hxf_in hxe'_in
              exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨Or.inl ⟨he'C, hf_inter.1⟩, hf₃⟩, hxf⟩)
        · exact Or.inr (mem_iUnion₂.mpr ⟨f, ⟨Or.inr ⟨⟨hf₃, hf_inter⟩, ⟨x, hxf, hxWi⟩⟩, hf₃⟩, hxf⟩)
    disj_E_EK := by
      intro i
      rw [hH_E i, disjoint_left]
      rintro f (⟨hfC, _⟩ | ⟨⟨_, hf_not_inter⟩, _⟩) hfK
      · exact disjoint_left.mp (hC_disj_EK i) hfC hfK
      · have hf_D : f ∈ D.E := hEK hfK
        have hf_D' : f ∈ D'.E := hVar'.preimage_EK_subset hh hEK hComp hfK
        exact hf_not_inter ⟨hf_D, hf_D'⟩
    disj_U_W := h_disj_U_W
    pairwise_disj_U := by
      intro i j hij
      rw [onFun, disjoint_left]
      intro x hxi hxj
      rcases hH_U_sub i hxi with ⟨_, hxWi⟩ | hx_cli
      · exact disjoint_right.mp (h_disj_U_W j i hij.symm) hxWi hxj
      · obtain ⟨f₁, hf₁_init, hxf₁⟩ := mem_iUnion₂.mp hx_cli
        rcases hf₁_init with ⟨hf₁C, _⟩ | ⟨hf₁_diff, hne₁⟩
        · have hxWi : x ∈ W i := Or.inr (mem_iUnion₂.mpr ⟨f₁, hf₁C, hxf₁⟩)
          exact disjoint_right.mp (h_disj_U_W j i hij.symm) hxWi hxj
        · rcases hH_U_sub j hxj with ⟨_, hxWj⟩ | hx_clj
          · exact disjoint_left.mp (h_disj_U_W i j hij) hxi hxWj
          · obtain ⟨f₂, hf₂_init, hxf₂⟩ := mem_iUnion₂.mp hx_clj
            rcases hf₂_init with ⟨hf₂C, _⟩ | ⟨hf₂_diff, hne₂⟩
            · have hxWj : x ∈ W j := Or.inr (mem_iUnion₂.mpr ⟨f₂, hf₂C, hxf₂⟩)
              exact disjoint_left.mp (h_disj_U_W i j hij) hxi hxWj
            · exact disjoint_left.mp (h_disj₃ f₁ hf₁_diff f₂ hf₂_diff i j hij hne₁ hne₂) hxf₁ hxf₂
    V_inter_VK := by
      intro i
      refine Subset.antisymm ?_ ?_
      · rintro x ⟨hxV_Hi, hxK⟩
        have hxD'V : x ∈ D'.V := hVar'.preimage_VK_subset hh hVK hxK
        have hxD₂V : x ∈ D₂.V := hDV₂ (hVK hxK)
        have hxU_Hi : x ∈ (H_init i).U := (H_init i).V_subset_U hxV_Hi
        have hxWi : x ∈ W i := by
          rcases hH_U_sub i hxU_Hi with ⟨_, hxWi⟩ | hx_cl
          · exact hxWi
          · obtain ⟨f, hf_init, hxf⟩ := mem_iUnion₂.mp hx_cl
            rcases hf_init with ⟨hfC, _⟩ | ⟨hf_diff, hne_Wi⟩
            · exact Or.inr (mem_iUnion₂.mpr ⟨f, hfC, hxf⟩)
            · by_contra hx_not_Wi
              exact disjoint_left.mp ((h_fine₃ f hf_diff).2.2 i hne_Wi) hxf (Or.inl ⟨hxD₂V, hx_not_Wi⟩)
        exact ⟨(hW_inter_D'V i).subset ⟨hxWi, hxD'V⟩, hxK⟩
      · rintro x ⟨hxVC, hxK⟩
        exact ⟨Or.inl ⟨⟨hV₂₃ (hDV₂ (hVK hxK)), Or.inl hxVC⟩, hV₂₃ (hDV₂ (hVK hxK))⟩, hxK⟩ }

/-- Operation A: Adding a point `x₀ ∈ (st.H i).U ∩ T` that misses all edges in `D.E ∩ D'.E`
as a vertex of `st.H i` and `st.D_cur`. -/
private theorem Phase2State.addPoint [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D' : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    {k : ℕ} {C : Fin k → Graph S (Set S)}
    (st : Phase2State h p D D' K ιV ιE C) (i : Fin k)
    {x₀ : S} (hx₀U : x₀ ∈ (st.H i).U)
    (hx₀T : x₀ ∈ insulatedSet D (ιV ⁻¹' V(K)) h)
    (hx₀_no_inter : ∀ f ∈ D.E ∩ D'.E, x₀ ∉ f) :
    ∃ st' : Phase2State h p D D' K ιV ιE C,
      st'.D_cur.U = st.D_cur.U ∧
      (st'.H i).U = (st.H i).U ∧
      (st'.H i).V = insert x₀ (st.H i).V ∧
      x₀ ∈ (st'.H i).V ∧
      (∀ j ≠ i, st'.H j = st.H j) ∧
      (∀ a b : S, Nonempty (GraphWalk (st.H i).toGraph a b) →
        Nonempty (GraphWalk (st'.H i).toGraph a b)) ∧
      (∀ f ∈ (st.H i).E, x₀ ∉ f → f ∈ (st'.H i).E) ∧
      (x₀ ∉ (st.H i).V → ∃ e ∈ (st.H i).E, ∃ u v : S,
        x₀ ∈ e ∧ (st.H i).toGraph.IsLink e u v ∧
        Nonempty (GraphWalk (st'.H i).toGraph u x₀)) := by
  by_cases hx₀V : x₀ ∈ (st.H i).V
  · refine ⟨st, rfl, rfl, (insert_eq_of_mem hx₀V).symm, hx₀V, fun _ _ => rfl,
      fun _ _ h => h, fun _ hf _ => hf, fun h_abs => (h_abs hx₀V).elim⟩
  · obtain ⟨e, he_Hi, hx₀e⟩ := (st.H i).exists_edge_of_mem hx₀U hx₀V
    have he_D : e ∈ st.D_cur.E := (st.isSubdrawing i).2 he_Hi
    have he_not_inter : e ∉ D.E ∩ D'.E := fun h_inter => hx₀_no_inter e h_inter hx₀e
    obtain ⟨heT, u, v, huv, hcap_D, hL⟩ := st.edge_T_line e ⟨he_D, he_not_inter⟩
    have hcap_Hi : closure e ∩ (st.H i).V = {u, v} := by
      rw [(st.isSubdrawing i).closure_inter_V he_Hi, hcap_D]
    have hx₀_not_DV : x₀ ∉ st.D_cur.V := (he_D.2.1 hx₀e).2
    have hu_DV : u ∈ st.D_cur.V := (hcap_D.symm.subset (Or.inl rfl)).2
    have hv_DV : v ∈ st.D_cur.V := (hcap_D.symm.subset (Or.inr rfl)).2
    have hux₀ : u ≠ x₀ := fun h => hx₀_not_DV (h ▸ hu_DV)
    have hx₀v : x₀ ≠ v := fun h => hx₀_not_DV (h ▸ hv_DV)
    obtain ⟨L₁, L₂, hL₁, hL₂, hU, hI₀⟩ := hL.split (subset_closure hx₀e) hux₀.symm hx₀v
    have hI : L₁ ∩ L₂ ⊆ {u, x₀} ∩ {x₀, v} := by
      rw [hI₀]
      rintro z rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
    let D_next := subdivEdgeSplit st.D_cur he_D hcap_D hux₀ hx₀v hL₁ hL₂ hU hI
    let Hi_next := subdivEdgeSplit (st.H i) he_Hi hcap_Hi hux₀ hx₀v hL₁ hL₂ hU hI
    let H_next : Fin k → Drawing S := Function.update st.H i Hi_next
    have hE_D_next : D_next.E = (st.D_cur.E \ {e}) ∪ {L₁ \ {u, x₀}, L₂ \ {x₀, v}} :=
      subdivEdgeSplit_E st.D_cur he_D hcap_D hux₀ hx₀v hL₁ hL₂ hU hI
    have hE_Hi_next : Hi_next.E = ((st.H i).E \ {e}) ∪ {L₁ \ {u, x₀}, L₂ \ {x₀, v}} :=
      subdivEdgeSplit_E (st.H i) he_Hi hcap_Hi hux₀ hx₀v hL₁ hL₂ hU hI
    have hV_D_next : D_next.V = insert x₀ st.D_cur.V :=
      subdivEdgeSplit_V st.D_cur he_D hcap_D hux₀ hx₀v hL₁ hL₂ hU hI
    have hV_Hi_next : Hi_next.V = insert x₀ (st.H i).V :=
      subdivEdgeSplit_V (st.H i) he_Hi hcap_Hi hux₀ hx₀v hL₁ hL₂ hU hI
    have hU_D_next : D_next.U = st.D_cur.U :=
      subdivEdgeSplit_U st.D_cur he_D hcap_D hux₀ hx₀v hL₁ hL₂ hU hI
    have hU_Hi_next : Hi_next.U = (st.H i).U :=
      subdivEdgeSplit_U (st.H i) he_Hi hcap_Hi hux₀ hx₀v hL₁ hL₂ hU hI
    have hU_all : ∀ j, (H_next j).U = (st.H j).U := by
      intro j
      dsimp only [H_next]
      rcases eq_or_ne j i with hji | hji
      · subst j
        rw [Function.update_self, hU_Hi_next]
      · rw [Function.update_of_ne hji]
    let st' : Phase2State h p D D' K ιV ιE C :=
      { D_cur := D_next
        H := H_next
        pb := subdivEdgeSplit_pullbackTo hh h31 hVK_fin hEK_fin hVK hEK hComp st.pb
          he_D heT hcap_D hux₀ hx₀v hL₁ hL₂ hU hI
        DV_sub := st.DV_sub.trans (hV_D_next.symm ▸ subset_insert x₀ st.D_cur.V)
        D'V_sub := st.D'V_sub.trans (hV_D_next.symm ▸ subset_insert x₀ st.D_cur.V)
        EE_sub := by
          intro f hf
          rw [hE_D_next]
          exact Or.inl ⟨st.EE_sub hf, fun hfe => he_not_inter (hfe ▸ hf)⟩
        C_le := st.C_le
        edge_T_line := by
          rintro f ⟨hf_next, hf_not_inter⟩
          have hf_next' := hf_next
          rw [hE_D_next] at hf_next'
          rcases hf_next' with ⟨hf_cur, _⟩ | (rfl | rfl)
          · obtain ⟨hfT, hf_line⟩ := st.edge_T_line f ⟨hf_cur, hf_not_inter⟩
            exact ⟨hfT, (IsLineEdge.iff_of_mem hf_cur hf_next).mp hf_line⟩
          · refine ⟨?_, isLineEdge_of_sdiff_pair hux₀ hL₁ hf_next⟩
            rw [closure_sdiff_pair hL₁]
            exact (subset_union_left.trans hU.le).trans heT
          · refine ⟨?_, isLineEdge_of_sdiff_pair hx₀v hL₂ hf_next⟩
            rw [closure_sdiff_pair hL₂]
            exact (subset_union_right.trans hU.le).trans heT
        isSubdrawing := by
          intro j
          dsimp only [H_next]
          rcases eq_or_ne j i with hji | hji
          · subst j
            rw [Function.update_self]
            exact subdivEdgeSplit_isSubdrawing_self (st.isSubdrawing i) he_Hi he_D
              hcap_Hi hcap_D hux₀ hx₀v hL₁ hL₂ hU hI
          · rw [Function.update_of_ne hji]
            have he_not_Hj : e ∉ (st.H j).E := by
              intro he_Hj
              have hx₀_Hj : x₀ ∈ (st.H j).U :=
                (st.H j).closure_subset_U he_Hj (subset_closure hx₀e)
              exact disjoint_left.mp (st.pairwise_disj_U hji.symm) hx₀U hx₀_Hj
            exact subdivEdgeSplit_isSubdrawing_other (st.isSubdrawing j) he_D he_not_Hj
              hcap_D hux₀ hx₀v hL₁ hL₂ hU hI
        VC_sub := by
          intro j
          dsimp only [H_next]
          rcases eq_or_ne j i with hji | hji
          · subst j
            rw [Function.update_self, hV_Hi_next]
            exact (st.VC_sub i).trans (subset_insert x₀ _)
          · rw [Function.update_of_ne hji]
            exact st.VC_sub j
        EC_inter_sub := by
          intro j
          dsimp only [H_next]
          rcases eq_or_ne j i with hji | hji
          · subst j
            rw [Function.update_self, hE_Hi_next]
            intro f hf
            have hf_inter : f ∈ D.E ∩ D'.E := ⟨hf.2, (st.C_le i).edgeSet_mono hf.1⟩
            exact Or.inl ⟨st.EC_inter_sub i hf, fun hfe => hx₀_no_inter f hf_inter (hfe ▸ hx₀e)⟩
          · rw [Function.update_of_ne hji]
            exact st.EC_inter_sub j
        U_inter_W_sub := by
          intro j
          rw [hU_D_next, hU_all j]
          exact st.U_inter_W_sub j
        disj_E_EK := by
          intro j
          dsimp only [H_next]
          rcases eq_or_ne j i with hji | hji
          · subst j
            rw [Function.update_self, hE_Hi_next, disjoint_left]
            rintro f (⟨hf_Hi, _⟩ | (rfl | rfl)) hfK
            · exact disjoint_left.mp (st.disj_E_EK i) hf_Hi hfK
            · have h_not_T := IsVariant.not_closure_subset_T_of_mem_preimage_EK hh hEK hComp hfK
              rw [closure_sdiff_pair hL₁] at h_not_T
              exact h_not_T ((subset_union_left.trans hU.le).trans heT)
            · have h_not_T := IsVariant.not_closure_subset_T_of_mem_preimage_EK hh hEK hComp hfK
              rw [closure_sdiff_pair hL₂] at h_not_T
              exact h_not_T ((subset_union_right.trans hU.le).trans heT)
          · rw [Function.update_of_ne hji]
            exact st.disj_E_EK j
        disj_U_W := by
          intro j₁ j₂ hj
          rw [hU_all j₁]
          exact st.disj_U_W j₁ j₂ hj
        pairwise_disj_U := by
          intro j₁ j₂ hj
          rw [onFun, hU_all j₁, hU_all j₂]
          exact st.pairwise_disj_U hj
        V_inter_VK := by
          intro j
          dsimp only [H_next]
          rcases eq_or_ne j i with hji | hji
          · subst j
            rw [Function.update_self, hV_Hi_next, ← st.V_inter_VK i]
            have hx₀_not_VK : x₀ ∉ ιV ⁻¹' V(K) :=
              disjoint_left.mp (IsVariant.disjoint_T_preimage_VK D K ιV hh) hx₀T
            ext z
            simp only [mem_inter_iff, mem_insert_iff]
            exact ⟨fun ⟨hz, hzK⟩ => ⟨hz.resolve_left fun h => by subst h; exact hx₀_not_VK hzK, hzK⟩,
              fun ⟨hz, hzK⟩ => ⟨Or.inr hz, hzK⟩⟩
          · rw [Function.update_of_ne hji]
            exact st.V_inter_VK j }
    refine ⟨st', hU_D_next, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change (H_next i).U = (st.H i).U
      rw [hU_all i]
    · change (H_next i).V = insert x₀ (st.H i).V
      dsimp only [H_next]
      rw [Function.update_self, hV_Hi_next]
    · change x₀ ∈ (H_next i).V
      dsimp only [H_next]
      rw [Function.update_self, hV_Hi_next]
      exact mem_insert x₀ _
    · intro j hji
      exact Function.update_of_ne hji _ _
    · intro a b ⟨W⟩
      change Nonempty (GraphWalk (H_next i).toGraph a b)
      dsimp only [H_next]
      rw [Function.update_self]
      exact subdivEdgeSplit_walk (st.H i) he_Hi hcap_Hi hux₀ hx₀v hL₁ hL₂ hU hI W
    · intro f hf hx₀_not_f
      change f ∈ (H_next i).E
      dsimp only [H_next]
      rw [Function.update_self, hE_Hi_next]
      exact Or.inl ⟨hf, fun hfe => hx₀_not_f (hfe ▸ hx₀e)⟩
    · intro _
      have hu_Hi : u ∈ (st.H i).V := (hcap_Hi.symm.subset (Or.inl rfl)).2
      have hv_Hi : v ∈ (st.H i).V := (hcap_Hi.symm.subset (Or.inr rfl)).2
      have hl_e : (st.H i).toGraph.IsLink e u v := ⟨he_Hi, hu_Hi, hv_Hi, hcap_Hi⟩
      have hl_left : (H_next i).toGraph.IsLink (L₁ \ {u, x₀}) u x₀ := by
        dsimp only [H_next]
        rw [Function.update_self]
        exact subdivEdgeSplit_isLink_left (st.H i) he_Hi hcap_Hi hux₀ hx₀v hL₁ hL₂ hU hI
      exact ⟨e, he_Hi, u, v, hx₀e, hl_e, ⟨.cons hl_left (.nil hl_left.right_mem)⟩⟩

/-- Operation B: Adding a chord `J ⊆ W i ∩ T` with endpoints `x, y ∈ (st.H i).V` and
`J ∩ st.D_cur.U = {x, y}` to both `st.D_cur` and `st.H i`. -/
private theorem Phase2State.addChord [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D' : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    {k : ℕ} {C : Fin k → Graph S (Set S)}
    (st : Phase2State h p D D' K ιV ιE C) (i : Fin k)
    {x y : S} (hxy : x ≠ y) (hxV : x ∈ (st.H i).V) (hyV : y ∈ (st.H i).V)
    {J : Set S} (hJ : IsLineWithEnds J x y)
    (hJT : J ⊆ insulatedSet D (ιV ⁻¹' V(K)) h)
    (hJW : J ⊆ V(C i) ∪ ⋃ e ∈ E(C i), closure e)
    (hJU : J ∩ st.D_cur.U = {x, y}) :
    ∃ st' : Phase2State h p D D' K ιV ιE C,
      (st'.H i).V = (st.H i).V ∧
      (∀ j ≠ i, st'.H j = st.H j) ∧
      (∀ a b : S, Nonempty (GraphWalk (st.H i).toGraph a b) →
        Nonempty (GraphWalk (st'.H i).toGraph a b)) ∧
      Nonempty (GraphWalk (st'.H i).toGraph x y) := by
  have hxDV : x ∈ st.D_cur.V := (st.isSubdrawing i).1 hxV
  have hyDV : y ∈ st.D_cur.V := (st.isSubdrawing i).1 hyV
  obtain ⟨D_next, hPB_next, hU_D_next, hV_D_next, hE_D_next, he_J_mem, hcl_J⟩ :=
    st.pb.addChord hh h31 hVK_fin hEK_fin hVK hEK hComp hxy hxDV hyDV hJ hJT hJU
  have hxy_sub_Hi : ({x, y} : Set S) ⊆ (st.H i).V := by
    rintro z (rfl | rfl) <;> assumption
  have hmeet_Hi : (st.H i).U ∩ (lineDrawing hJ hxy).U ⊆
      (st.H i).V ∩ (lineDrawing hJ hxy).V := by
    change (st.H i).U ∩ J ⊆ (st.H i).V ∩ {x, y}
    intro z ⟨hzU_Hi, hzJ⟩
    have hz_xy : z ∈ ({x, y} : Set S) :=
      hJU ▸ ⟨hzJ, (st.isSubdrawing i).U_subset hzU_Hi⟩
    exact ⟨hxy_sub_Hi hz_xy, hz_xy⟩
  let Hi_next := (st.H i).glue (lineDrawing hJ hxy) hmeet_Hi
  let H_next : Fin k → Drawing S := Function.update st.H i Hi_next
  have hU_Hi_next : Hi_next.U = (st.H i).U ∪ J := rfl
  have hV_Hi_next : Hi_next.V = (st.H i).V := union_eq_left.mpr hxy_sub_Hi
  have hE_Hi_next : Hi_next.E = (st.H i).E ∪ {J \ {x, y}} := by
    change ((st.H i).glue (lineDrawing hJ hxy) hmeet_Hi).E = _
    rw [Drawing.glue_E, lineDrawing_E]
  let st' : Phase2State h p D D' K ιV ιE C :=
    { D_cur := D_next
      H := H_next
      pb := hPB_next
      DV_sub := hV_D_next.symm ▸ st.DV_sub
      D'V_sub := hV_D_next.symm ▸ st.D'V_sub
      EE_sub := st.EE_sub.trans (hE_D_next.symm ▸ subset_union_left)
      C_le := st.C_le
      edge_T_line := by
        rintro f ⟨hf_next, hf_not_inter⟩
        have hf_next' := hf_next
        rw [hE_D_next] at hf_next'
        rcases hf_next' with hf_cur | rfl
        · obtain ⟨hfT, hf_line⟩ := st.edge_T_line f ⟨hf_cur, hf_not_inter⟩
          exact ⟨hfT, (IsLineEdge.iff_of_mem hf_cur hf_next).mp hf_line⟩
        · exact ⟨hcl_J.symm ▸ hJT, isLineEdge_of_sdiff_pair hxy hJ hf_next⟩
      isSubdrawing := by
        intro j
        dsimp only [H_next]
        rcases eq_or_ne j i with hji | hji
        · subst j
          rw [Function.update_self]
          refine ⟨?_, ?_⟩
          · rw [hV_Hi_next, hV_D_next]
            exact (st.isSubdrawing i).1
          · rw [hE_Hi_next, hE_D_next]
            exact union_subset_union_left _ (st.isSubdrawing i).2
        · rw [Function.update_of_ne hji]
          refine ⟨?_, ?_⟩
          · rw [hV_D_next]
            exact (st.isSubdrawing j).1
          · rw [hE_D_next]
            exact (st.isSubdrawing j).2.trans subset_union_left
      VC_sub := by
        intro j
        dsimp only [H_next]
        rcases eq_or_ne j i with hji | hji
        · subst j
          rw [Function.update_self, hV_Hi_next]
          exact st.VC_sub i
        · rw [Function.update_of_ne hji]
          exact st.VC_sub j
      EC_inter_sub := by
        intro j
        dsimp only [H_next]
        rcases eq_or_ne j i with hji | hji
        · subst j
          rw [Function.update_self, hE_Hi_next]
          exact (st.EC_inter_sub i).trans subset_union_left
        · rw [Function.update_of_ne hji]
          exact st.EC_inter_sub j
      U_inter_W_sub := by
        intro j
        dsimp only [H_next]
        rcases eq_or_ne j i with hji | hji
        · subst j
          rw [Function.update_self, hU_D_next, hU_Hi_next]
          rintro z ⟨hzU | hzJ, hzWi⟩
          · exact Or.inl (st.U_inter_W_sub i ⟨hzU, hzWi⟩)
          · exact Or.inr hzJ
        · rw [Function.update_of_ne hji, hU_D_next]
          rintro z ⟨hzU | hzJ, hzWj⟩
          · exact st.U_inter_W_sub j ⟨hzU, hzWj⟩
          · exfalso
            have hz_Hi_or : z ∈ (st.H i).U ∨ z ∈ J := Or.inr hzJ
            have hzWi : z ∈ V(C i) ∪ ⋃ e ∈ E(C i), closure e := hJW hzJ
            have hW_disj : Disjoint (V(C i) ∪ ⋃ e ∈ E(C i), closure e)
                (V(C j) ∪ ⋃ e ∈ E(C j), closure e) := by
              rw [disjoint_left]
              intro w hw_i hw_j
              have hw_D'U : w ∈ D'.U := by
                rcases hw_i with hwV | hwE
                · exact D'.V_subset_U ((st.C_le i).vertexSet_mono hwV)
                · obtain ⟨e, heC, hwe⟩ := mem_iUnion₂.mp hwE
                  exact D'.closure_subset_U ((st.C_le i).edgeSet_mono heC) hwe
              by_cases hw_D'V : w ∈ D'.V
              · have hw_VCj : w ∈ V(C j) := by
                  rcases hw_j with hwV | hwE
                  · exact hwV
                  · obtain ⟨e, heC, hwe⟩ := mem_iUnion₂.mp hwE
                    obtain ⟨u, v, hl⟩ := (C j).exists_isLink_of_mem_edgeSet heC
                    have hl' := (st.C_le j).isLink_mono hl
                    have : w ∈ ({u, v} : Set S) := hl'.2.2.2 ▸ ⟨hwe, hw_D'V⟩
                    rcases this with rfl | rfl
                    · exact hl.left_mem
                    · exact hl.right_mem
                exact disjoint_left.mp (st.disj_U_W j i hji)
                  ((st.H j).V_subset_U (st.VC_sub j hw_VCj)) hw_i
              · rcases hw_i with hwV | hwE_i
                · exact hw_D'V ((st.C_le i).vertexSet_mono hwV)
                · rcases hw_j with hwV | hwE_j
                  · exact hw_D'V ((st.C_le j).vertexSet_mono hwV)
                  · obtain ⟨e₁, he₁C, hwe₁⟩ := mem_iUnion₂.mp hwE_i
                    obtain ⟨e₂, he₂C, hwe₂⟩ := mem_iUnion₂.mp hwE_j
                    have h₁ : w ∈ e₁ := by
                      rw [← D'.closure_diff_V ((st.C_le i).edgeSet_mono he₁C)]
                      exact ⟨hwe₁, hw_D'V⟩
                    have h₂ : w ∈ e₂ := by
                      rw [← D'.closure_diff_V ((st.C_le j).edgeSet_mono he₂C)]
                      exact ⟨hwe₂, hw_D'V⟩
                    obtain rfl : e₁ = e₂ := D'.edge_eq_of_mem
                      ((st.C_le i).edgeSet_mono he₁C) ((st.C_le j).edgeSet_mono he₂C) h₁ h₂
                    obtain ⟨u, v, hl⟩ := (C j).exists_isLink_of_mem_edgeSet he₂C
                    have hu_Wi : u ∈ V(C i) ∪ ⋃ e ∈ E(C i), closure e := by
                      have hl' := (st.C_le j).isLink_mono hl
                      have hu_cl : u ∈ closure e₁ := (hl'.2.2.2.symm.subset (Or.inl rfl)).1
                      exact Or.inr (mem_iUnion₂.mpr ⟨e₁, he₁C, hu_cl⟩)
                    exact disjoint_left.mp (st.disj_U_W j i hji)
                      ((st.H j).V_subset_U (st.VC_sub j hl.left_mem)) hu_Wi
            exact disjoint_left.mp hW_disj hzWi hzWj
      disj_E_EK := by
        intro j
        dsimp only [H_next]
        rcases eq_or_ne j i with hji | hji
        · subst j
          rw [Function.update_self, hE_Hi_next, disjoint_left]
          rintro f (hf_Hi | rfl) hfK
          · exact disjoint_left.mp (st.disj_E_EK i) hf_Hi hfK
          · exact IsVariant.not_closure_subset_T_of_mem_preimage_EK hh hEK hComp hfK
              (hcl_J.symm ▸ hJT)
        · rw [Function.update_of_ne hji]
          exact st.disj_E_EK j
      disj_U_W := by
        intro j₁ j₂ hj
        dsimp only [H_next]
        rcases eq_or_ne j₁ i with hj₁ | hj₁
        · subst j₁
          rw [Function.update_self, hU_Hi_next]
          refine (st.disj_U_W i j₂ hj).union_left ?_
          rw [disjoint_left]
          intro z hzJ hzWj₂
          have hzWi : z ∈ V(C i) ∪ ⋃ e ∈ E(C i), closure e := hJW hzJ
          have hz_Hj₂ : z ∈ (st.H j₂).U := by
            by_cases hz_DU : z ∈ st.D_cur.U
            · have hz_xy : z ∈ ({x, y} : Set S) := hJU ▸ ⟨hzJ, hz_DU⟩
              have hz_Hi : z ∈ (st.H i).U := (st.H i).V_subset_U (hxy_sub_Hi hz_xy)
              exact (disjoint_left.mp (st.disj_U_W i j₂ hj) hz_Hi hzWj₂).elim
            · exfalso
              rcases hzWj₂ with hzV | hzE
              · exact hz_DU (st.D_cur.V_subset_U (st.D'V_sub ((st.C_le j₂).vertexSet_mono hzV)))
              · obtain ⟨e, heC, hze⟩ := mem_iUnion₂.mp hzE
                obtain ⟨u, v, hl⟩ := (C j₂).exists_isLink_of_mem_edgeSet heC
                have hl' := (st.C_le j₂).isLink_mono hl
                by_cases hz_D'V : z ∈ D'.V
                · exact hz_DU (st.D_cur.V_subset_U (st.D'V_sub hz_D'V))
                · have hze_in : z ∈ e := by
                    rw [← D'.closure_diff_V hl'.1]
                    exact ⟨hze, hz_D'V⟩
                  rcases hzWi with hzVi | hzEi
                  · exact hz_D'V ((st.C_le i).vertexSet_mono hzVi)
                  · obtain ⟨e', he'C, hze'⟩ := mem_iUnion₂.mp hzEi
                    have hze'_in : z ∈ e' := by
                      rw [← D'.closure_diff_V ((st.C_le i).edgeSet_mono he'C)]
                      exact ⟨hze', hz_D'V⟩
                    obtain rfl : e = e' := D'.edge_eq_of_mem hl'.1
                      ((st.C_le i).edgeSet_mono he'C) hze_in hze'_in
                    have hu_Wi : u ∈ V(C i) ∪ ⋃ e ∈ E(C i), closure e :=
                      Or.inr (mem_iUnion₂.mpr ⟨e, he'C, (hl'.2.2.2.symm.subset (Or.inl rfl)).1⟩)
                    exact disjoint_left.mp (st.disj_U_W j₂ i hj.symm)
                      ((st.H j₂).V_subset_U (st.VC_sub j₂ hl.left_mem)) hu_Wi
          exact disjoint_right.mp (st.disj_U_W j₂ i hj.symm) hzWi hz_Hj₂
        · rw [Function.update_of_ne hj₁]
          exact st.disj_U_W j₁ j₂ hj
      pairwise_disj_U := by
        intro j₁ j₂ hj
        rw [onFun]
        dsimp only [H_next]
        rcases eq_or_ne j₁ i with hj₁ | hj₁ <;> rcases eq_or_ne j₂ i with hj₂ | hj₂
        · subst j₁; subst j₂; exact (hj rfl).elim
        · subst j₁
          rw [Function.update_self, Function.update_of_ne hj₂, hU_Hi_next]
          exact (st.pairwise_disj_U hj).union_left
            ((st.disj_U_W j₂ i hj.symm).symm.mono_left hJW)
        · subst j₂
          rw [Function.update_of_ne hj₁, Function.update_self, hU_Hi_next]
          exact (st.pairwise_disj_U hj).union_right
            ((st.disj_U_W j₁ i hj₁).mono_right hJW)
        · rw [Function.update_of_ne hj₁, Function.update_of_ne hj₂]
          exact st.pairwise_disj_U hj
      V_inter_VK := by
        intro j
        dsimp only [H_next]
        rcases eq_or_ne j i with hji | hji
        · subst j
          rw [Function.update_self, hV_Hi_next]
          exact st.V_inter_VK i
        · rw [Function.update_of_ne hji]
          exact st.V_inter_VK j }
  refine ⟨st', ?_, ?_, ?_, ?_⟩
  · change (H_next i).V = (st.H i).V
    dsimp only [H_next]
    rw [Function.update_self, hV_Hi_next]
  · intro j hji
    exact Function.update_of_ne hji _ _
  · intro a b ⟨W⟩
    change Nonempty (GraphWalk (H_next i).toGraph a b)
    dsimp only [H_next]
    rw [Function.update_self]
    have hsub : (st.H i).IsSubdrawing Hi_next :=
      ⟨hV_Hi_next.symm.subset, hE_Hi_next.symm ▸ subset_union_left⟩
    obtain ⟨W', _, _⟩ := hsub.exists_walk_up W
    exact ⟨W'⟩
  · change Nonempty (GraphWalk (H_next i).toGraph x y)
    dsimp only [H_next]
    rw [Function.update_self]
    have hl_J : Hi_next.toGraph.IsLink (J \ {x, y}) x y :=
      isLink_of_sdiff_pair hxy hJ (hE_Hi_next.symm ▸ Or.inr rfl)
    exact ⟨.cons hl_J (.nil hl_J.right_mem)⟩

/-- One step of connecting `V(C i)` in `st.H i`: if `u₀ ∈ V(C i)` cannot reach all of `V(C i)` in
`(st.H i).toGraph`, we can add up to two points and a chord inside `W i ∩ T` to strictly decrease
`{v ∈ (st.H i).V | ¬ Nonempty (GraphWalk (st.H i).toGraph u₀ v)}.ncard`. -/
private theorem Phase2State.connectStep [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D' : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hVar' : IsVariant D D' (insulatedSet D (ιV ⁻¹' V(K)) h))
    {k : ℕ} {C : Fin k → Graph S (Set S)}
    (st : Phase2State h p D D' K ιV ιE C) (i : Fin k)
    (hC_conn : IsGraphConnected (C i))
    {u₀ v_bad : S} (hu₀ : u₀ ∈ V(C i)) (hv_bad : v_bad ∈ V(C i))
    (h_unreach : ¬ Nonempty (GraphWalk (st.H i).toGraph u₀ v_bad)) :
    ∃ st' : Phase2State h p D D' K ιV ιE C,
      (∀ j ≠ i, st'.H j = st.H j) ∧
      {v ∈ (st'.H i).V | ¬ Nonempty (GraphWalk (st'.H i).toGraph u₀ v)}.ncard <
        {v ∈ (st.H i).V | ¬ Nonempty (GraphWalk (st.H i).toGraph u₀ v)}.ncard := by
  let P : S → Prop := fun v => Nonempty (GraphWalk (st.H i).toGraph u₀ v)
  have hu₀_P : P u₀ := ⟨.nil (st.VC_sub i hu₀)⟩
  obtain ⟨W_C⟩ := hC_conn.2 u₀ hu₀ v_bad hv_bad
  obtain ⟨e', u', v', hl_C, hu'_P, hv'_not_P⟩ := exists_link_step_of_walk W_C hu₀_P h_unreach
  have he'C : e' ∈ E(C i) := hl_C.edge_mem
  have hl_D' : D'.toGraph.IsLink e' u' v' := (st.C_le i).isLink_mono hl_C
  have he'D' : e' ∈ D'.E := hl_D'.1
  have he'_not_D : e' ∉ D.E := by
    intro he'D
    have he'_Hi : e' ∈ (st.H i).E := st.EC_inter_sub i ⟨he'C, he'D⟩
    have he'_Dcur : e' ∈ st.D_cur.E := (st.isSubdrawing i).2 he'_Hi
    have hl_Dcur : st.D_cur.toGraph.IsLink e' u' v' :=
      (D'.toGraph_isLink_eq_of_mem he'D' he'_Dcur u' v').mp hl_D'
    have hl_Hi : (st.H i).toGraph.IsLink e' u' v' :=
      ((st.isSubdrawing i).isLink_iff he'_Hi).mpr hl_Dcur
    obtain ⟨W_u'⟩ := hu'_P
    exact hv'_not_P ⟨W_u'.append (.cons hl_Hi (.nil hl_Hi.right_mem))⟩
  have he'T : closure e' ⊆ insulatedSet D (ιV ⁻¹' V(K)) h :=
    hVar'.edge_subset_of_mem_diff_right e' ⟨he'D', he'_not_D⟩
  have he'W : closure e' ⊆ V(C i) ∪ ⋃ e ∈ E(C i), closure e :=
    fun z hz => Or.inr (mem_iUnion₂.mpr ⟨e', he'C, hz⟩)
  have hcl_no_inter : ∀ z ∈ closure e', ∀ f ∈ D.E ∩ D'.E, z ∉ f := by
    intro z hz f ⟨hfD, hfD'⟩ hzf
    have hfe' : f ≠ e' := fun h => he'_not_D (h ▸ hfD)
    have hz_D'V : z ∈ D'.V :=
      closure_inter_subset_V hfD' he'D' hfe' ⟨subset_closure hzf, hz⟩
    exact (hfD'.2.1 hzf).2 hz_D'V
  have hu'v' : u' ≠ v' := fun h => hv'_not_P (h ▸ hu'_P)
  have hL_e' : IsLineWithEnds (closure e') u' v' := by
    rcases D'.edge_cond e' he'D' with ⟨a, b, _, hcap, hL⟩ | ⟨a, hcap, _⟩
    · have hab_eq : ({a, b} : Set S) = {u', v'} := hcap.symm.trans hl_D'.2.2.2
      have hu'_ab : u' = a ∨ u' = b := by
        have : u' ∈ ({u', v'} : Set S) := Or.inl rfl
        rwa [← hab_eq] at this
      have hv'_ab : v' = a ∨ v' = b := by
        have : v' ∈ ({u', v'} : Set S) := Or.inr rfl
        rwa [← hab_eq] at this
      rcases hu'_ab with rfl | rfl <;> rcases hv'_ab with rfl | rfl
      · exact (hu'v' rfl).elim
      · exact hL
      · exact hL.symm
      · exact (hu'v' rfl).elim
    · exfalso
      have h_eq : ({u', v'} : Set S) = {a} := hl_D'.2.2.2.symm.trans hcap
      have hu'a : u' = a := by
        have : u' ∈ ({u', v'} : Set S) := Or.inl rfl
        rwa [h_eq] at this
      have hv'a : v' = a := by
        have : v' ∈ ({u', v'} : Set S) := Or.inr rfl
        rwa [h_eq] at this
      exact hu'v' (hu'a.trans hv'a.symm)
  let V₁ : Set S := {v ∈ (st.H i).V | P v}
  let V₂ : Set S := {v ∈ (st.H i).V | ¬ P v}
  let E₁ : Set (Set S) := {f ∈ (st.H i).E | closure f ∩ (st.H i).V ⊆ V₁}
  let E₂ : Set (Set S) := (st.H i).E \ E₁
  let A₁ : Set S := V₁ ∪ ⋃ f ∈ E₁, closure f
  let A₂ : Set S := V₂ ∪ ⋃ f ∈ E₂, closure f
  have hE₂_ends : ∀ f ∈ E₂, closure f ∩ (st.H i).V ⊆ V₂ := by
    rintro f ⟨hf_Hi, hf_not_E₁⟩ z ⟨hz_cl, hz_V⟩
    refine ⟨hz_V, fun hz_P => hf_not_E₁ ⟨hf_Hi, ?_⟩⟩
    obtain ⟨a, b, hl_f⟩ := (st.H i).toGraph.exists_isLink_of_mem_edgeSet hf_Hi
    have hcap_f : closure f ∩ (st.H i).V = {a, b} := hl_f.2.2.2
    have hz_ab : z ∈ ({a, b} : Set S) := hcap_f ▸ ⟨hz_cl, hz_V⟩
    obtain ⟨W_z⟩ := hz_P
    have ha_P : P a := by
      rcases hz_ab with rfl | rfl
      · exact ⟨W_z⟩
      · exact ⟨W_z.append (.cons hl_f.symm (.nil hl_f.left_mem))⟩
    have hb_P : P b := by
      rcases hz_ab with rfl | rfl
      · exact ⟨W_z.append (.cons hl_f (.nil hl_f.right_mem))⟩
      · exact ⟨W_z⟩
    intro w hw
    rw [hcap_f] at hw
    rcases hw with rfl | rfl
    · exact ⟨hl_f.left_mem, ha_P⟩
    · exact ⟨hl_f.right_mem, hb_P⟩
  have hA₁_inter_V : A₁ ∩ (st.H i).V = V₁ := by
    refine Subset.antisymm ?_ (subset_inter subset_union_left fun _ h => h.1)
    rintro z ⟨hz_V₁ | hz_E₁, hz_V⟩
    · exact hz_V₁
    · obtain ⟨f, hf_E₁, hzf⟩ := mem_iUnion₂.mp hz_E₁
      exact hf_E₁.2 ⟨hzf, hz_V⟩
  have hA₂_inter_V : A₂ ∩ (st.H i).V = V₂ := by
    refine Subset.antisymm ?_ (subset_inter subset_union_left fun _ h => h.1)
    rintro z ⟨hz_V₂ | hz_E₂, hz_V⟩
    · exact hz_V₂
    · obtain ⟨f, hf_E₂, hzf⟩ := mem_iUnion₂.mp hz_E₂
      exact hE₂_ends f hf_E₂ ⟨hzf, hz_V⟩
  have hA_disj : Disjoint A₁ A₂ := by
    rw [disjoint_left]
    intro z hz₁ hz₂
    by_cases hz_V : z ∈ (st.H i).V
    · have hz_V₁ : z ∈ V₁ := hA₁_inter_V.subset ⟨hz₁, hz_V⟩
      have hz_V₂ : z ∈ V₂ := hA₂_inter_V.subset ⟨hz₂, hz_V⟩
      exact hz_V₂.2 hz_V₁.2
    · rcases hz₁ with hz_V₁ | hz_E₁
      · exact hz_V hz_V₁.1
      · rcases hz₂ with hz_V₂ | hz_E₂
        · exact hz_V hz_V₂.1
        · obtain ⟨f₁, hf₁, hzf₁⟩ := mem_iUnion₂.mp hz_E₁
          obtain ⟨f₂, hf₂, hzf₂⟩ := mem_iUnion₂.mp hz_E₂
          have h₁ : z ∈ f₁ := by
            rw [← (st.H i).closure_diff_V hf₁.1]
            exact ⟨hzf₁, hz_V⟩
          have h₂ : z ∈ f₂ := by
            rw [← (st.H i).closure_diff_V hf₂.1]
            exact ⟨hzf₂, hz_V⟩
          obtain rfl : f₁ = f₂ := (st.H i).edge_eq_of_mem hf₁.1 hf₂.1 h₁ h₂
          exact hf₂.2 hf₁
  have hA_union : A₁ ∪ A₂ = (st.H i).U := by
    rw [(st.H i).U_eq]
    ext z
    simp only [A₁, A₂, mem_union, mem_iUnion]
    constructor
    · rintro ((hzV₁ | ⟨f, hf₁, hzf⟩) | (hzV₂ | ⟨f, hf₂, hzf⟩))
      · exact Or.inl hzV₁.1
      · exact Or.inr ⟨f, hf₁.1, hzf⟩
      · exact Or.inl hzV₂.1
      · exact Or.inr ⟨f, hf₂.1, hzf⟩
    · rintro (hzV | ⟨f, hf, hzf⟩)
      · by_cases hzP : P z
        · exact Or.inl (Or.inl ⟨hzV, hzP⟩)
        · exact Or.inr (Or.inl ⟨hzV, hzP⟩)
      · by_cases hf₁ : f ∈ E₁
        · exact Or.inl (Or.inr ⟨f, hf₁, hzf⟩)
        · exact Or.inr (Or.inr ⟨f, ⟨hf, hf₁⟩, hzf⟩)
  have hA₁_cl : IsClosed A₁ := by
    refine IsClosed.union ((st.H i).finite_V.subset fun _ h => h.1).isClosed ?_
    exact ((st.H i).finite_edges.subset fun _ h => h.1).isClosed_biUnion fun _ _ => isClosed_closure
  have hA₂_cl : IsClosed A₂ := by
    refine IsClosed.union ((st.H i).finite_V.subset fun _ h => h.1).isClosed ?_
    exact ((st.H i).finite_edges.subset sdiff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨g, hg, hrange_g, hg0, hg1⟩ := hL_e'.exists_arc
  have hu'_A₁ : u' ∈ A₁ := Or.inl ⟨st.VC_sub i hl_C.left_mem, hu'_P⟩
  have hv'_A₂ : v' ∈ A₂ := Or.inl ⟨st.VC_sub i hl_C.right_mem, hv'_not_P⟩
  let S₂ : Set ℝ := Icc (0 : ℝ) 1 ∩ (extI g) ⁻¹' A₂
  have hS₂_comp : IsCompact S₂ :=
    isCompact_Icc.inter_right (hA₂_cl.preimage (continuous_extI hg.1))
  have h1_S₂ : (1 : ℝ) ∈ S₂ := by
    refine ⟨unitInterval.one_mem, ?_⟩
    change extI g 1 ∈ A₂
    rw [extI_of_mem g unitInterval.one_mem]
    exact hg1.symm ▸ hv'_A₂
  let t₂ : ℝ := sInf S₂
  have ht₂_mem : t₂ ∈ S₂ := hS₂_comp.sInf_mem ⟨1, h1_S₂⟩
  have ht₂_0 : 0 ≤ t₂ := ht₂_mem.1.1
  have ht₂_1 : t₂ ≤ 1 := ht₂_mem.1.2
  let S₁ : Set ℝ := Icc (0 : ℝ) t₂ ∩ (extI g) ⁻¹' A₁
  have hS₁_comp : IsCompact S₁ :=
    isCompact_Icc.inter_right (hA₁_cl.preimage (continuous_extI hg.1))
  have h0_S₁ : (0 : ℝ) ∈ S₁ := by
    refine ⟨⟨le_rfl, ht₂_0⟩, ?_⟩
    change extI g 0 ∈ A₁
    rw [extI_of_mem g unitInterval.zero_mem]
    exact hg0.symm ▸ hu'_A₁
  let t₁ : ℝ := sSup S₁
  have ht₁_mem : t₁ ∈ S₁ := hS₁_comp.sSup_mem ⟨0, h0_S₁⟩
  have ht₁_0 : 0 ≤ t₁ := ht₁_mem.1.1
  have ht₁_t₂ : t₁ ≤ t₂ := ht₁_mem.1.2
  let x := extI g t₁
  let y := extI g t₂
  have hx_A₁ : x ∈ A₁ := ht₁_mem.2
  have hy_A₂ : y ∈ A₂ := ht₂_mem.2
  have hxy : x ≠ y := fun heq => disjoint_left.mp hA_disj hx_A₁ (heq.symm ▸ hy_A₂)
  have ht₁_lt_t₂ : t₁ < t₂ := lt_of_le_of_ne ht₁_t₂ fun h => hxy (congrArg (extI g) h)
  let J : Set S := extI g '' Icc t₁ t₂
  have hJ_line : IsLineWithEnds J x y :=
    isLineWithEnds_extI_Icc hg ht₁_0 ht₁_lt_t₂ ht₂_1
  have hJ_sub_cl : J ⊆ closure e' := by
    rw [← hrange_g]
    rintro z ⟨t, ht, rfl⟩
    have ht_Icc : t ∈ Icc (0 : ℝ) 1 := ⟨ht₁_0.trans ht.1, ht.2.trans ht₂_1⟩
    exact ⟨⟨t, ht_Icc⟩, (extI_of_mem g ht_Icc).symm⟩
  have hJT : J ⊆ insulatedSet D (ιV ⁻¹' V(K)) h := hJ_sub_cl.trans he'T
  have hJW : J ⊆ V(C i) ∪ ⋃ e ∈ E(C i), closure e := hJ_sub_cl.trans he'W
  have hx_HiU : x ∈ (st.H i).U := hA_union ▸ Or.inl hx_A₁
  have hy_HiU : y ∈ (st.H i).U := hA_union ▸ Or.inr hy_A₂
  have hJU : J ∩ st.D_cur.U = {x, y} := by
    refine Subset.antisymm ?_ ?_
    · rintro z ⟨⟨t, ht, rfl⟩, hz_DU⟩
      have hz_HiU : extI g t ∈ (st.H i).U :=
        st.U_inter_W_sub i ⟨hz_DU, hJW ⟨t, ht, rfl⟩⟩
      rw [← hA_union] at hz_HiU
      rcases hz_HiU with hz_A₁ | hz_A₂
      · have ht_S₁ : t ∈ S₁ := ⟨⟨ht₁_0.trans ht.1, ht.2⟩, hz_A₁⟩
        have ht_le : t ≤ t₁ := le_csSup hS₁_comp.bddAbove ht_S₁
        obtain rfl : t = t₁ := le_antisymm ht_le ht.1
        exact Or.inl rfl
      · have ht_S₂ : t ∈ S₂ := ⟨⟨ht₁_0.trans ht.1, ht.2.trans ht₂_1⟩, hz_A₂⟩
        have ht_ge : t₂ ≤ t := csInf_le hS₂_comp.bddBelow ht_S₂
        obtain rfl : t = t₂ := le_antisymm ht.2 ht_ge
        exact Or.inr rfl
    · rintro z (rfl | rfl)
      · exact ⟨⟨t₁, ⟨le_rfl, ht₁_t₂⟩, rfl⟩, (st.isSubdrawing i).U_subset hx_HiU⟩
      · exact ⟨⟨t₂, ⟨ht₁_t₂, le_rfl⟩, rfl⟩, (st.isSubdrawing i).U_subset hy_HiU⟩
  have hxT : x ∈ insulatedSet D (ιV ⁻¹' V(K)) h := hJT hJ_line.left_mem
  have hyT : y ∈ insulatedSet D (ιV ⁻¹' V(K)) h := hJT hJ_line.right_mem
  have hx_no_inter : ∀ f ∈ D.E ∩ D'.E, x ∉ f :=
    hcl_no_inter x (hJ_sub_cl hJ_line.left_mem)
  have hy_no_inter : ∀ f ∈ D.E ∩ D'.E, y ∉ f :=
    hcl_no_inter y (hJ_sub_cl hJ_line.right_mem)
  obtain ⟨st₁, hU_D₁, hU_Hi₁, hV_Hi₁, hxV₁, hH_other₁, hwalk₁, hE_keep₁, hnew₁⟩ :=
    st.addPoint hh h31 hVK_fin hEK_fin hVK hEK hComp i hx_HiU hxT hx_no_inter
  have hx_reach₁ : Nonempty (GraphWalk (st₁.H i).toGraph u₀ x) := by
    by_cases hxV : x ∈ (st.H i).V
    · have hx_V₁ : x ∈ V₁ := hA₁_inter_V.subset ⟨hx_A₁, hxV⟩
      exact hwalk₁ u₀ x hx_V₁.2
    · obtain ⟨f₁, hf₁_Hi, a₁, b₁, hxf₁, hl_f₁, ⟨W_a₁x⟩⟩ := hnew₁ hxV
      have ha₁_V₁ : a₁ ∈ V₁ := by
        rcases hx_A₁ with hxV₁' | hx_E₁
        · exact (hxV hxV₁'.1).elim
        · obtain ⟨f₁', hf₁'_E₁, hxf₁'⟩ := mem_iUnion₂.mp hx_E₁
          have hxf₁'_in : x ∈ f₁' := by
            rw [← (st.H i).closure_diff_V hf₁'_E₁.1]
            exact ⟨hxf₁', hxV⟩
          obtain rfl : f₁ = f₁' := (st.H i).edge_eq_of_mem hf₁_Hi hf₁'_E₁.1 hxf₁ hxf₁'_in
          exact hf₁'_E₁.2 ⟨(hl_f₁.2.2.2.symm.subset (Or.inl rfl)).1, hl_f₁.left_mem⟩
      obtain ⟨W_u₀a₁⟩ := hwalk₁ u₀ a₁ ha₁_V₁.2
      exact ⟨W_u₀a₁.append W_a₁x⟩
  have hy_HiU₁ : y ∈ (st₁.H i).U := hU_Hi₁.symm ▸ hy_HiU
  obtain ⟨st₂, hU_D₂, _, hV_Hi₂, hyV₂, hH_other₂, hwalk₂, _, hnew₂⟩ :=
    st₁.addPoint hh h31 hVK_fin hEK_fin hVK hEK hComp i hy_HiU₁ hyT hy_no_inter
  have hxV₂ : x ∈ (st₂.H i).V := by
    rw [hV_Hi₂]
    exact Or.inr hxV₁
  have hx_reach₂ : Nonempty (GraphWalk (st₂.H i).toGraph u₀ x) := hwalk₂ u₀ x hx_reach₁
  obtain ⟨w₀, hw₀_V₂, hw₀_reach₂⟩ :
      ∃ w₀ ∈ V₂, Nonempty (GraphWalk (st₂.H i).toGraph y w₀) := by
    by_cases hyV : y ∈ (st.H i).V
    · have hy_V₂ : y ∈ V₂ := hA₂_inter_V.subset ⟨hy_A₂, hyV⟩
      exact ⟨y, hy_V₂, ⟨.nil hyV₂⟩⟩
    · have hy_not_V₁ : y ∉ (st₁.H i).V := by
        rw [hV_Hi₁]
        rintro (hyx | hyV')
        · exact hxy hyx.symm
        · exact hyV hyV'
      obtain ⟨f₂, hf₂_Hi₁, a₂, b₂, hyf₂, hl_f₂, ⟨W_a₂y⟩⟩ := hnew₂ hy_not_V₁
      rcases hy_A₂ with hyV₂' | hy_E₂
      · exact (hyV hyV₂'.1).elim
      · obtain ⟨e₂, he₂_E₂, hye₂⟩ := mem_iUnion₂.mp hy_E₂
        have hye₂_in : y ∈ e₂ := by
          rw [← (st.H i).closure_diff_V he₂_E₂.1]
          exact ⟨hye₂, hyV⟩
        have hx_not_e₂ : x ∉ e₂ := fun hxe₂ =>
          disjoint_left.mp hA_disj hx_A₁ (Or.inr (mem_iUnion₂.mpr ⟨e₂, he₂_E₂, subset_closure hxe₂⟩))
        have he₂_Hi₁ : e₂ ∈ (st₁.H i).E := hE_keep₁ e₂ he₂_E₂.1 hx_not_e₂
        obtain rfl : f₂ = e₂ := (st₁.H i).edge_eq_of_mem hf₂_Hi₁ he₂_Hi₁ hyf₂ hye₂_in
        obtain ⟨u₂, v₂, hl_e₂⟩ := (st.H i).toGraph.exists_isLink_of_mem_edgeSet he₂_E₂.1
        have hl_e₂_Hi₁ : (st₁.H i).toGraph.IsLink f₂ u₂ v₂ :=
          ((st.H i).toGraph_isLink_eq_of_mem he₂_E₂.1 hf₂_Hi₁ u₂ v₂).mp hl_e₂
        have ha₂_uv : a₂ = u₂ ∨ a₂ = v₂ := by
          have h_eq : ({a₂, b₂} : Set S) = {u₂, v₂} := hl_f₂.2.2.2.symm.trans hl_e₂_Hi₁.2.2.2
          have : a₂ ∈ ({a₂, b₂} : Set S) := Or.inl rfl
          rwa [h_eq] at this
        have ha₂_V₂ : a₂ ∈ V₂ := by
          rcases ha₂_uv with rfl | rfl
          · exact hE₂_ends f₂ he₂_E₂ ⟨(hl_e₂.2.2.2.symm.subset (Or.inl rfl)).1, hl_e₂.left_mem⟩
          · exact hE₂_ends f₂ he₂_E₂ ⟨(hl_e₂.2.2.2.symm.subset (Or.inr rfl)).1, hl_e₂.right_mem⟩
        exact ⟨a₂, ha₂_V₂, ⟨W_a₂y.reverse⟩⟩
  have hJU₂ : J ∩ st₂.D_cur.U = {x, y} := by
    rw [hU_D₂, hU_D₁, hJU]
  obtain ⟨st₃, hV_Hi₃, hH_other₃, hwalk₃, ⟨W_xy₃⟩⟩ :=
    st₂.addChord hh h31 hVK_fin hEK_fin hVK hEK hComp i hxy hxV₂ hyV₂ hJ_line hJT hJW hJU₂
  refine ⟨st₃, fun j hj => (hH_other₃ j hj).trans ((hH_other₂ j hj).trans (hH_other₁ j hj)), ?_⟩
  obtain ⟨W_u₀x₃⟩ := hwalk₃ u₀ x hx_reach₂
  have hy_reach₃ : Nonempty (GraphWalk (st₃.H i).toGraph u₀ y) := ⟨W_u₀x₃.append W_xy₃⟩
  obtain ⟨W_u₀y₃⟩ := hy_reach₃
  obtain ⟨W_yw₀₃⟩ := hwalk₃ y w₀ hw₀_reach₂
  have hw₀_reach₃ : Nonempty (GraphWalk (st₃.H i).toGraph u₀ w₀) := ⟨W_u₀y₃.append W_yw₀₃⟩
  have hV₂_fin : V₂.Finite := (st.H i).finite_V.subset fun _ h => h.1
  refine ncard_lt_ncard ?_ hV₂_fin
  rw [ssubset_iff_subset_ne]
  refine ⟨?_, ?_⟩
  · rintro z ⟨hzV₃, hz_unreach₃⟩
    rw [hV_Hi₃, hV_Hi₂, hV_Hi₁] at hzV₃
    rcases hzV₃ with rfl | rfl | hzV
    · exact (hz_unreach₃ ⟨W_u₀y₃⟩).elim
    · exact (hz_unreach₃ ⟨W_u₀x₃⟩).elim
    · refine ⟨hzV, fun hz_reach => hz_unreach₃ ?_⟩
      exact hwalk₃ u₀ z (hwalk₂ u₀ z (hwalk₁ u₀ z hz_reach))
  · intro h_eq
    have hw₀_in : w₀ ∈ {v ∈ (st₃.H i).V | ¬ Nonempty (GraphWalk (st₃.H i).toGraph u₀ v)} := by
      rw [h_eq]
      exact hw₀_V₂
    exact hw₀_in.2 hw₀_reach₃

/-- Connecting a single component `V(C i)` in `st.H i` by induction on the number of unreachable
vertices in `(st.H i).V`. -/
private theorem Phase2State.connectComponent [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D' : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hVar' : IsVariant D D' (insulatedSet D (ιV ⁻¹' V(K)) h))
    {k : ℕ} {C : Fin k → Graph S (Set S)}
    (st : Phase2State h p D D' K ιV ιE C) (i : Fin k)
    (hC_conn : IsGraphConnected (C i))
    {u₀ : S} (hu₀ : u₀ ∈ V(C i)) :
    ∃ st' : Phase2State h p D D' K ιV ιE C,
      (∀ j ≠ i, st'.H j = st.H j) ∧
      ∀ v ∈ V(C i), Nonempty (GraphWalk (st'.H i).toGraph u₀ v) := by
  suffices ∀ n : ℕ, ∀ st_cur : Phase2State h p D D' K ιV ιE C,
      {v ∈ (st_cur.H i).V | ¬ Nonempty (GraphWalk (st_cur.H i).toGraph u₀ v)}.ncard ≤ n →
      ∃ st' : Phase2State h p D D' K ιV ιE C,
        (∀ j ≠ i, st'.H j = st_cur.H j) ∧
        ∀ v ∈ V(C i), Nonempty (GraphWalk (st'.H i).toGraph u₀ v) by
    exact this _ st le_rfl
  intro n
  induction n with
  | zero =>
    intro st_cur hle
    have hfin : {v ∈ (st_cur.H i).V | ¬ Nonempty (GraphWalk (st_cur.H i).toGraph u₀ v)}.Finite :=
      (st_cur.H i).finite_V.subset fun _ h => h.1
    have hempty : {v ∈ (st_cur.H i).V | ¬ Nonempty (GraphWalk (st_cur.H i).toGraph u₀ v)} = ∅ :=
      (ncard_eq_zero (s := _) hfin).mp (Nat.le_zero.mp hle)
    refine ⟨st_cur, fun _ _ => rfl, fun v hv => ?_⟩
    by_contra h_unreach
    have : v ∈ ({v ∈ (st_cur.H i).V | ¬ Nonempty (GraphWalk (st_cur.H i).toGraph u₀ v)} : Set S) :=
      ⟨st_cur.VC_sub i hv, h_unreach⟩
    rw [hempty] at this
    exact this
  | succ m ih =>
    intro st_cur hle
    by_cases h_all : ∀ v ∈ V(C i), Nonempty (GraphWalk (st_cur.H i).toGraph u₀ v)
    · exact ⟨st_cur, fun _ _ => rfl, h_all⟩
    · obtain ⟨v_bad, hv_bad, h_unreach⟩ :
          ∃ v ∈ V(C i), ¬ Nonempty (GraphWalk (st_cur.H i).toGraph u₀ v) := by
        by_contra h_none
        exact h_all fun v hv => by_contra fun hn => h_none ⟨v, hv, hn⟩
      obtain ⟨st_next, h_other_next, h_lt⟩ :=
        st_cur.connectStep hh h31 hVK_fin hEK_fin hVK hEK hComp hVar' i hC_conn hu₀ hv_bad h_unreach
      obtain ⟨st', h_other', h_reach'⟩ := ih st_next (Nat.le_of_lt_succ (lt_of_lt_of_le h_lt hle))
      exact ⟨st', fun j hj => (h_other' j hj).trans (h_other_next j hj), h_reach'⟩

/-- Connecting all components `C i` (`i : Fin k`) one by one. -/
private theorem Phase2State.connectAll [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D' : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hVar' : IsVariant D D' (insulatedSet D (ιV ⁻¹' V(K)) h))
    {k : ℕ} {C : Fin k → Graph S (Set S)}
    (st₀ : Phase2State h p D D' K ιV ιE C)
    (hC_conn : ∀ i, IsGraphConnected (C i))
    (u₀ : Fin k → S) (hu₀ : ∀ i, u₀ i ∈ V(C i)) :
    ∃ st' : Phase2State h p D D' K ιV ιE C,
      ∀ i : Fin k, ∀ v ∈ V(C i), Nonempty (GraphWalk (st'.H i).toGraph (u₀ i) v) := by
  suffices ∀ F : Set (Fin k), F.Finite →
      ∃ st' : Phase2State h p D D' K ιV ιE C,
        ∀ i ∈ F, ∀ v ∈ V(C i), Nonempty (GraphWalk (st'.H i).toGraph (u₀ i) v) by
    obtain ⟨st', h_all⟩ := this univ finite_univ
    exact ⟨st', fun i => h_all i (mem_univ i)⟩
  intro F hF
  refine Set.Finite.induction_on F hF ?_ ?_
  · exact ⟨st₀, fun _ h => h.elim⟩
  · rintro i₀ F hi₀_not_F _ ⟨st_cur, h_cur⟩
    obtain ⟨st_next, h_other, h_reach_i₀⟩ :=
      st_cur.connectComponent hh h31 hVK_fin hEK_fin hVK hEK hComp hVar' i₀ (hC_conn i₀) (hu₀ i₀)
    refine ⟨st_next, ?_⟩
    rintro i (rfl | hiF)
    · exact h_reach_i₀
    · have hij : i ≠ i₀ := fun h => hi₀_not_F (h ▸ hiF)
      rw [h_other i hij]
      exact h_cur i hiF

/-! ## 3. Proof of Theorem 4.1 -/

/-- Normalized form of **4.1** in which `ιV ⁻¹' V(K) ⊆ D.V` and `ιE ⁻¹' E(K) ⊆ D.E`. -/
theorem lemma_4_1_normalized [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G₀ Γ₀ K₀ L₀ : Graph α β), V(G₀).Finite → E(G₀).Finite →
      Γ₀ ≤ G₀ → K₀ ≤ G₀ → V(G₀) = V(Γ₀) ∪ V(K₀) → E(G₀) = E(Γ₀) ∪ E(K₀) →
      ∀ (D₂ : Drawing S) (ιV₀ : S ↪ α) (ιE₀ : Set S ↪ β), Γ₀ = D₂.toEmbeddedGraph ιV₀ ιE₀ →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV₀ ⁻¹' (V(Γ₀) ∩ V(K₀))) h v₀ →
      ∀ Z₀ ⊆ V(K₀), Z₀.ncard ≤ p → L₀ ≤ G₀ →
      ∃ L₀' ≤ G₀.deleteVerts {ιV₀ v₀},
        HasSameEffectOn L₀' L₀ Z₀ ∧ subgraphInter G₀ L₀' K₀ ≤ L₀)
    (G Γ K G' Γ' L' : Graph α β)
    (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hΓG : Γ ≤ G) (hKG : K ≤ G)
    (hVG_union : V(G) = V(Γ) ∪ V(K)) (hEG_union : E(G) = E(Γ) ∪ E(K))
    (hΓ'G' : Γ' ≤ G') (hKG' : K ≤ G')
    (hVG'_union : V(G') = V(Γ') ∪ V(K)) (hEG'_union : E(G') = E(Γ') ∪ E(K))
    (_hInter : subgraphInter G Γ K = subgraphInter G' Γ' K)
    (D D' : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β)
    (hΓ : Γ = D.toEmbeddedGraph ιV ιE) (hΓ' : Γ' = D'.toEmbeddedGraph ιV ιE)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hVar : IsVariant D D' (insulatedSet D (ιV ⁻¹' (V(Γ) ∩ V(K))) h))
    (Z : Set α) (hZK : Z ⊆ V(K)) (hZp : Z.ncard ≤ p) (hL' : L' ≤ G') :
    ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' := by
  have hY_eq : ιV ⁻¹' (V(Γ) ∩ V(K)) = ιV ⁻¹' V(K) := by
    ext v
    simp only [mem_preimage, mem_inter_iff, hΓ, Drawing.toEmbeddedGraph, mem_image]
    exact ⟨fun ⟨_, hvK⟩ => hvK, fun hvK => ⟨⟨v, hVK hvK, rfl⟩, hvK⟩⟩
  rw [hY_eq] at hVar
  have hVK_fin : V(K).Finite := hVG.subset hKG.vertexSet_mono
  have hEK_fin : E(K).Finite := hEG.subset hKG.edgeSet_mono
  have hComp : (D.toEmbeddedGraph ιV ιE).Compatible K :=
    hΓ ▸ Compatible.of_le_le hΓG hKG
  have hComp' : (D'.toEmbeddedGraph ιV ιE).Compatible K :=
    hΓ' ▸ Compatible.of_le_le hΓ'G' hKG'
  have hG_eq : G = graphUnion (D.toEmbeddedGraph ιV ιE) K :=
    eq_graphUnion_of_le (hΓ ▸ hΓG) hKG (hΓ ▸ hVG_union) (hΓ ▸ hEG_union)
  have hG'_eq : G' = graphUnion (D'.toEmbeddedGraph ιV ιE) K :=
    eq_graphUnion_of_le (hΓ' ▸ hΓ'G') hKG' (hΓ' ▸ hVG'_union) (hΓ' ▸ hEG'_union)
  let Γ'_rem := Γ'.restrict (E(Γ') \ E(K))
  let A_L := subgraphInter G' L' Γ'_rem
  let K_L := subgraphInter G' L' K
  have hΓ'_rem_le : Γ'_rem ≤ G' := restrict_le.trans hΓ'G'
  have hA_L_le_Γ' : A_L ≤ Γ' :=
    (subgraphInter_le_right hL' hΓ'_rem_le).trans restrict_le
  have hA_L_le_L' : A_L ≤ L' := subgraphInter_le_left hL' hΓ'_rem_le
  have hK_L_le_L' : K_L ≤ L' := subgraphInter_le_left hL' hKG'
  have hK_L_le_K : K_L ≤ K := subgraphInter_le_right hL' hKG'
  have hVL' : V(L') = V(A_L) ∪ V(K_L) := by
    refine Subset.antisymm ?_ (union_subset hA_L_le_L'.vertexSet_mono hK_L_le_L'.vertexSet_mono)
    intro x hx
    have hxG' : x ∈ V(G') := hL'.vertexSet_mono hx
    rw [hVG'_union] at hxG'
    rcases hxG' with hxΓ' | hxK
    · exact Or.inl ⟨hx, hxΓ'⟩
    · exact Or.inr ⟨hx, hxK⟩
  have hEL' : E(L') = E(A_L) ∪ E(K_L) := by
    refine Subset.antisymm ?_ (union_subset hA_L_le_L'.edgeSet_mono hK_L_le_L'.edgeSet_mono)
    intro e he
    obtain ⟨x, y, hl⟩ := L'.exists_isLink_of_mem_edgeSet he
    have hlG' : G'.IsLink e x y := hL'.isLink_mono hl
    by_cases heK : e ∈ E(K)
    · have hlK : K.IsLink e x y := (hKG'.isLink_iff heK).mpr hlG'
      have hl_KL : K_L.IsLink e x y := by
        unfold K_L subgraphInter
        rw [restrict_isLink, induce_isLink]
        exact ⟨⟨he, heK⟩, hlG', ⟨hl.left_mem, hlK.left_mem⟩, ⟨hl.right_mem, hlK.right_mem⟩⟩
      exact Or.inr hl_KL.edge_mem
    · have heΓ' : e ∈ E(Γ') := (hEG'_union ▸ hlG'.edge_mem).resolve_right heK
      have hlΓ' : Γ'.IsLink e x y := (hΓ'G'.isLink_iff heΓ').mpr hlG'
      have hl_rem : Γ'_rem.IsLink e x y := by
        unfold Γ'_rem
        rw [restrict_isLink]
        exact ⟨⟨heΓ', heK⟩, hlΓ'⟩
      have hl_AL : A_L.IsLink e x y := by
        unfold A_L subgraphInter
        rw [restrict_isLink, induce_isLink]
        exact ⟨⟨he, hl_rem.edge_mem⟩, hlG', ⟨hl.left_mem, hlΓ'.left_mem⟩, ⟨hl.right_mem, hlΓ'.right_mem⟩⟩
      exact Or.inl hl_AL.edge_mem
  have hDisj_EA_EK : Disjoint E(A_L) E(K) := by
    rw [disjoint_left]
    intro e heA heK
    have he_rem : e ∈ E(Γ'_rem) := (subgraphInter_le_right hL' hΓ'_rem_le).edgeSet_mono heA
    obtain ⟨x, y, hl_rem⟩ := Γ'_rem.exists_isLink_of_mem_edgeSet he_rem
    rw [restrict_isLink] at hl_rem
    exact hl_rem.1.2 heK
  let H' := A_L.comapEmbed ιV ιE
  have hA_L_emb : A_L ≤ D'.toGraph.mapEmbed ιV ιE := by
    rw [← toEmbeddedGraph_eq_mapEmbed, ← hΓ']
    exact hA_L_le_Γ'
  obtain ⟨hH'_map, hH'_le⟩ := mapEmbed_comapEmbed_of_le ιV ιE hA_L_emb
  have hDisj_EH'_EK : Disjoint E(H') (ιE ⁻¹' E(K)) := by
    rw [disjoint_left]
    intro e heH' heK
    have heA : ιE e ∈ E(A_L) := hH'_map ▸ mem_image_of_mem ιE heH'
    exact disjoint_left.mp hDisj_EA_EK heA heK
  have hVH'_fin : V(H').Finite := D'.finite_V.subset hH'_le.vertexSet_mono
  have hCompH'_fin : (graphComponents H').Finite := by
    refine (hVH'_fin.image (compOf H')).subset fun M hM => ?_
    obtain ⟨v, hv⟩ := hM.2.1.1
    exact ⟨v, hM.1.vertexSet_mono hv, (hM.eq_compOf_of_mem hv).symm⟩
  have : Finite (graphComponents H') := hCompH'_fin
  obtain ⟨k, ⟨e_comp⟩⟩ := Finite.exists_equiv_fin (graphComponents H')
  let C : Fin k → Graph S (Set S) := fun i => (e_comp.symm i).1
  have hC_mem : ∀ i : Fin k, C i ∈ graphComponents H' := fun i => (e_comp.symm i).2
  have hC_inj : Function.Injective C := fun i j hij => e_comp.symm.injective (Subtype.ext hij)
  have hC_surj : ∀ M ∈ graphComponents H', ∃ i : Fin k, C i = M := by
    intro M hM
    exact ⟨e_comp ⟨M, hM⟩, congrArg Subtype.val (e_comp.symm_apply_apply ⟨M, hM⟩)⟩
  have hC_le : ∀ i, C i ≤ D'.toGraph := fun i => (hC_mem i).1.trans hH'_le
  have hC_conn : ∀ i, IsGraphConnected (C i) := fun i => (hC_mem i).2.1
  have hC_disj_EK : ∀ i, Disjoint E(C i) (ιE ⁻¹' E(K)) :=
    fun i => hDisj_EH'_EK.mono_left (hC_mem i).1.edgeSet_mono
  let W : Fin k → Set S := fun i => V(C i) ∪ ⋃ e ∈ E(C i), closure e
  have hW_cl : ∀ i, IsClosed (W i) := by
    intro i
    refine IsClosed.union (D'.finite_V.subset (hC_le i).vertexSet_mono).isClosed ?_
    exact (D'.finite_edges.subset (hC_le i).edgeSet_mono).isClosed_biUnion fun _ _ => isClosed_closure
  have hW_disj : Pairwise (Disjoint on W) := by
    intro i j hij
    have hC_ne : C i ≠ C j := fun h => hij (hC_inj h)
    have hV_disj : Disjoint V(C i) V(C j) :=
      (hC_mem i).disjoint_vertexSet_of_ne (hC_mem j) hC_ne
    have hE_disj : Disjoint E(C i) E(C j) :=
      (hC_mem i).disjoint_edgeSet_of_ne (hC_mem j) hC_ne
    rw [onFun, disjoint_left]
    intro z hzi hzj
    by_cases hz_D'V : z ∈ D'.V
    · have hz_VCi : z ∈ V(C i) := by
        rcases hzi with hzV | hzE
        · exact hzV
        · obtain ⟨e, heC, hze⟩ := mem_iUnion₂.mp hzE
          obtain ⟨u, v, hl⟩ := (C i).exists_isLink_of_mem_edgeSet heC
          have hl' := (hC_le i).isLink_mono hl
          have : z ∈ ({u, v} : Set S) := hl'.2.2.2 ▸ ⟨hze, hz_D'V⟩
          rcases this with rfl | rfl
          · exact hl.left_mem
          · exact hl.right_mem
      have hz_VCj : z ∈ V(C j) := by
        rcases hzj with hzV | hzE
        · exact hzV
        · obtain ⟨e, heC, hze⟩ := mem_iUnion₂.mp hzE
          obtain ⟨u, v, hl⟩ := (C j).exists_isLink_of_mem_edgeSet heC
          have hl' := (hC_le j).isLink_mono hl
          have : z ∈ ({u, v} : Set S) := hl'.2.2.2 ▸ ⟨hze, hz_D'V⟩
          rcases this with rfl | rfl
          · exact hl.left_mem
          · exact hl.right_mem
      exact disjoint_left.mp hV_disj hz_VCi hz_VCj
    · rcases hzi with hzV | hzE_i
      · exact hz_D'V ((hC_le i).vertexSet_mono hzV)
      · rcases hzj with hzV | hzE_j
        · exact hz_D'V ((hC_le j).vertexSet_mono hzV)
        · obtain ⟨e₁, he₁C, hze₁⟩ := mem_iUnion₂.mp hzE_i
          obtain ⟨e₂, he₂C, hze₂⟩ := mem_iUnion₂.mp hzE_j
          have h₁ : z ∈ e₁ := by
            rw [← D'.closure_diff_V ((hC_le i).edgeSet_mono he₁C)]
            exact ⟨hze₁, hz_D'V⟩
          have h₂ : z ∈ e₂ := by
            rw [← D'.closure_diff_V ((hC_le j).edgeSet_mono he₂C)]
            exact ⟨hze₂, hz_D'V⟩
          obtain rfl : e₁ = e₂ := D'.edge_eq_of_mem
            ((hC_le i).edgeSet_mono he₁C) ((hC_le j).edgeSet_mono he₂C) h₁ h₂
          exact disjoint_left.mp hE_disj he₁C he₂C
  obtain ⟨D₁, hPB₁, hDV₁, hD'V₁, hEE₁, hcl₁⟩ :=
    exists_pullback_add_vertices hh h31 hVK_fin hEK_fin hVK hEK hComp hVar
  obtain ⟨D₂, hPB₂, hDV₂, hD'V₂, hEE₂, hcl₂⟩ :=
    exists_pullback_subdiv_loops hh h31 hVK_fin hEK_fin hVK hEK hComp hPB₁ hDV₁ hD'V₁ hEE₁ hcl₁
  obtain ⟨D₃, hPB₃, _, hV₂₃, hEE₃, h_fine₃, h_disj₃⟩ :=
    exists_pullback_fine_subdiv hh h31 hVK_fin hEK_fin hVK hEK hComp hPB₂ hEE₂ hcl₂ W hW_cl hW_disj
  let st₀ := Phase2State.init hh hVK hEK hComp hVar C hC_le hC_disj_EK hW_disj
    hDV₂ hD'V₂ hPB₃ hV₂₃ hEE₃ h_fine₃ h_disj₃
  let u₀ : Fin k → S := fun i => (hC_conn i).1.choose
  have hu₀ : ∀ i, u₀ i ∈ V(C i) := fun i => (hC_conn i).1.choose_spec
  obtain ⟨st_fin, h_reach_fin⟩ :=
    st₀.connectAll hh h31 hVK_fin hEK_fin hVK hEK hComp hVar hC_conn u₀ hu₀
  let M : Fin k → Graph S (Set S) := fun i => compOf (st_fin.H i).toGraph (u₀ i)
  have hM_comp : ∀ i, M i ∈ graphComponents (st_fin.H i).toGraph :=
    fun i => isGraphComponent_compOf (st_fin.VC_sub i (hu₀ i))
  have hM_le_Hi : ∀ i, M i ≤ (st_fin.H i).toGraph := fun i => (hM_comp i).1
  have hM_le_D : ∀ i, M i ≤ st_fin.D_cur.toGraph :=
    fun i => (hM_le_Hi i).trans (st_fin.isSubdrawing i).toGraph_le
  have hVC_sub_VM : ∀ i, V(C i) ⊆ V(M i) :=
    fun i v hv => ⟨st_fin.VC_sub i hv, h_reach_fin i v hv⟩
  have hVM_inter_VK : ∀ i, V(M i) ∩ (ιV ⁻¹' V(K)) = V(C i) ∩ (ιV ⁻¹' V(K)) := by
    intro i
    refine Subset.antisymm ?_ (inter_subset_inter_left _ (hVC_sub_VM i))
    rw [← st_fin.V_inter_VK i]
    exact inter_subset_inter_left _ (hM_le_Hi i).vertexSet_mono
  have hM_disj_V : Pairwise (Disjoint on fun i => V(M i)) := by
    intro i j hij
    refine (st_fin.pairwise_disj_U hij).mono ?_ ?_
    · exact (hM_le_Hi i).vertexSet_mono.trans (st_fin.H i).V_subset_U
    · exact (hM_le_Hi j).vertexSet_mono.trans (st_fin.H j).V_subset_U
  have hbot_le : (⊥ : Graph S (Set S)) ≤ st_fin.D_cur.toGraph := bot_le
  let H_final : Graph S (Set S) := subgraphUnionFamily st_fin.D_cur.toGraph ⊥ M
  have hH_final_le : H_final ≤ st_fin.D_cur.toGraph :=
    subgraphUnionFamily_le hbot_le hM_le_D
  have hM_le_H_final : ∀ i, M i ≤ H_final :=
    fun i => le_subgraphUnionFamily_right hbot_le hM_le_D i
  have hM_in_comp_H_final : ∀ i, M i ∈ graphComponents H_final := by
    intro i
    refine ⟨hM_le_H_final i, (hM_comp i).2.1, fun N hMN hNH hN_conn => ?_⟩
    have hwalk_sub : ∀ {a b : S}, GraphWalk N a b → a ∈ V(M i) → b ∈ V(M i) := by
      intro a b W
      induction W with
      | nil _ => exact fun ha => ha
      | @cons x y z e hl _ ih =>
        intro hx_Mi
        have hl_H : H_final.IsLink e x y := hNH.isLink_mono hl
        rw [isLink_subgraphUnionFamily_iff hbot_le hM_le_D] at hl_H
        rcases hl_H with ⟨he_bot | he_U, hl_D⟩
        · exact he_bot.elim
        · obtain ⟨j, he_Mj⟩ := mem_iUnion.mp he_U
          have hl_Mj : (M j).IsLink e x y := ((hM_le_D j).isLink_iff he_Mj).mpr hl_D
          obtain rfl : j = i := by_contra fun hji =>
            disjoint_left.mp (hM_disj_V hji) hl_Mj.left_mem hx_Mi
          exact ih hl_Mj.right_mem
    have hVN_sub : V(N) ⊆ V(M i) := by
      have hu₀_M : u₀ i ∈ V(M i) := hVC_sub_VM i (hu₀ i)
      intro v hv
      obtain ⟨W⟩ := hN_conn.2 (u₀ i) (hMN.vertexSet_mono hu₀_M) v hv
      exact hwalk_sub W hu₀_M
    have hN_le_Mi : N ≤ M i := by
      refine ⟨hVN_sub, fun e x y hl => ?_⟩
      have hl_H : H_final.IsLink e x y := hNH.isLink_mono hl
      rw [isLink_subgraphUnionFamily_iff hbot_le hM_le_D] at hl_H
      rcases hl_H with ⟨he_bot | he_U, hl_D⟩
      · exact he_bot.elim
      · obtain ⟨j, he_Mj⟩ := mem_iUnion.mp he_U
        have hl_Mj : (M j).IsLink e x y := ((hM_le_D j).isLink_iff he_Mj).mpr hl_D
        obtain rfl : j = i := by_contra fun hji =>
          disjoint_left.mp (hM_disj_V hji) hl_Mj.left_mem (hVN_sub hl.left_mem)
        exact hl_Mj
    exact le_antisymm hN_le_Mi hMN
  have h_comp_H_final_iff : ∀ N, N ∈ graphComponents H_final ↔ ∃ i, N = M i := by
    intro N
    constructor
    · intro hN
      obtain ⟨x, hxN⟩ := hN.2.1.1
      have hxH : x ∈ V(H_final) := hN.1.vertexSet_mono hxN
      rcases hxH with hx_bot | hx_U
      · exact hx_bot.elim
      · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx_U
        refine ⟨i, ?_⟩
        by_contra hne
        exact disjoint_left.mp
          (hN.disjoint_vertexSet_of_ne (hM_in_comp_H_final i) hne) hxN hxi
    · rintro ⟨i, rfl⟩
      exact hM_in_comp_H_final i
  have hSame_H : HasSameEffectOn H_final H' (ιV ⁻¹' V(K)) := by
    ext δ
    simp only [effectOn, mem_ofPred_eq]
    constructor
    · rintro ⟨hne, N, hN, rfl⟩
      rw [h_comp_H_final_iff] at hN
      rcases hN with ⟨i, rfl⟩
      rw [hVM_inter_VK i] at hne ⊢
      exact ⟨hne, C i, hC_mem i, rfl⟩
    · rintro ⟨hne, C', hC', rfl⟩
      obtain ⟨i, rfl⟩ := hC_surj C' hC'
      rw [← hVM_inter_VK i] at hne ⊢
      exact ⟨hne, M i, hM_in_comp_H_final i, rfl⟩
  let A₁ := H_final.mapEmbed ιV ιE
  let Γ₁ := st_fin.D_cur.toEmbeddedGraph ιV ιE
  let G₁ := graphUnion Γ₁ K
  have hComp₁ : Γ₁.Compatible K := st_fin.pb.isVariant.compatible_K hh hEK hComp
  have hA₁_le_Γ₁ : A₁ ≤ Γ₁ := by
    dsimp only [A₁, Γ₁]
    rw [toEmbeddedGraph_eq_mapEmbed]
    exact mapEmbed_mono ιV ιE hH_final_le
  have hA₁_le_G₁ : A₁ ≤ G₁ := hA₁_le_Γ₁.trans (le_graphUnion_left Γ₁ K)
  have hKL_le_G₁ : K_L ≤ G₁ := hK_L_le_K.trans (le_graphUnion_right hComp₁)
  let L₁ := graphUnion A₁ K_L
  have hComp_A₁_KL : A₁.Compatible K_L := Compatible.of_le_le hA₁_le_G₁ hKL_le_G₁
  have hL₁_le_G₁ : L₁ ≤ G₁ := by
    refine ⟨union_subset hA₁_le_G₁.vertexSet_mono hKL_le_G₁.vertexSet_mono, fun e x y hl => ?_⟩
    rw [isLink_graphUnion_of_compatible hComp_A₁_KL] at hl
    rcases hl with hlA | hlK
    · exact hA₁_le_G₁.isLink_mono hlA
    · exact hKL_le_G₁.isLink_mono hlK
  have hSame_A₁_AL : HasSameEffectOn A₁ A_L (ιV '' (ιV ⁻¹' V(K))) := by
    rw [← hH'_map]
    exact (hasSameEffectOn_mapEmbed_iff ιV ιE).mpr hSame_H
  have hVA₁_inter_VK : V(A₁) ∩ V(K) = V(A_L) ∩ V(K) := by
    ext x
    constructor
    · rintro ⟨⟨v, hvH, rfl⟩, hxK⟩
      rcases hvH with hv_bot | hv_U
      · exact hv_bot.elim
      · obtain ⟨i, hvi⟩ := mem_iUnion.mp hv_U
        have hv_in : v ∈ V(C i) ∩ (ιV ⁻¹' V(K)) := hVM_inter_VK i ▸ ⟨hvi, hxK⟩
        have hv_VH' : v ∈ V(H') := (hC_mem i).1.vertexSet_mono hv_in.1
        exact ⟨hH'_map ▸ mem_image_of_mem ιV hv_VH', hxK⟩
    · rintro ⟨hxA, hxK⟩
      rw [← hH'_map] at hxA
      rcases hxA with ⟨v, hvH', rfl⟩
      have hC' : compOf H' v ∈ graphComponents H' := isGraphComponent_compOf hvH'
      have hvC' : v ∈ V(compOf H' v) := self_mem_reachSet hvH'
      obtain ⟨i, hi_eq⟩ := hC_surj (compOf H' v) hC'
      have hv_VM : v ∈ V(M i) := hVC_sub_VM i (hi_eq.symm ▸ hvC')
      exact ⟨mem_image_of_mem ιV (Or.inr (mem_iUnion.mpr ⟨i, hv_VM⟩)), hxK⟩
  have hVA₁_sub_img : V(A₁) ∩ V(K) ⊆ ιV '' (ιV ⁻¹' V(K)) := by
    rintro x ⟨⟨v, _, rfl⟩, hxK⟩
    exact ⟨v, hxK, rfl⟩
  have hSame_A₁_AL_inter : HasSameEffectOn A₁ A_L (V(A₁) ∩ V(K)) := by
    rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn] at hSame_A₁_AL ⊢
    exact fun u hu v hv => hSame_A₁_AL u (hVA₁_sub_img hu) v (hVA₁_sub_img hv)
  have hDisj_EA₁_EK : Disjoint E(A₁) E(K) := by
    rw [disjoint_left]
    rintro _ ⟨e, heH, rfl⟩ heK
    change e ∈ E(subgraphUnionFamily st_fin.D_cur.toGraph ⊥ M) at heH
    rw [edgeSet_subgraphUnionFamily hbot_le hM_le_D] at heH
    rcases heH with he_bot | he_U
    · exact he_bot.elim
    · obtain ⟨i, heMi⟩ := mem_iUnion.mp he_U
      exact disjoint_left.mp (st_fin.disj_E_EK i) ((hM_le_Hi i).edgeSet_mono heMi) heK
  have hDisj_EA₁_EKL : Disjoint E(A₁) E(K_L) :=
    hDisj_EA₁_EK.mono_right hK_L_le_K.edgeSet_mono
  have hDisj_EAL_EKL : Disjoint E(A_L) E(K_L) :=
    hDisj_EA_EK.mono_right hK_L_le_K.edgeSet_mono
  have hVL₁_eq_VL' : V(L₁) ∩ V(K) = V(L') ∩ V(K) := by
    rw [vertexSet_graphUnion, union_inter_distrib_right, hVA₁_inter_VK,
      ← union_inter_distrib_right, ← hVL']
  have hSame_L₁_L'_VL : HasSameEffectOn L₁ L' (V(L₁) ∩ V(K)) := by
    let Z₀ := V(L₁) ∩ V(K)
    have hsep₁ : IsGraphSeparation L₁ A₁ K_L :=
      ⟨le_graphUnion_left A₁ K_L, le_graphUnion_right hComp_A₁_KL, rfl, rfl, hDisj_EA₁_EKL⟩
    have hAB₁_Z₀ : V(A₁) ∩ V(K_L) ⊆ Z₀ :=
      fun _ ⟨hxA₁, hxKL⟩ => ⟨Or.inl hxA₁, hK_L_le_K.vertexSet_mono hxKL⟩
    have hdiv₁ : IsIndexedZDivision L₁ Z₀ (![A₁, K_L] : Fin 2 → Graph α β) :=
      isIndexedZDivision_of_isGraphSeparation hsep₁ hAB₁_Z₀
    have hsep' : IsGraphSeparation L' A_L K_L :=
      ⟨hA_L_le_L', hK_L_le_L', hVL'.symm, hEL'.symm, hDisj_EAL_EKL⟩
    have hAB'_Z₀ : V(A_L) ∩ V(K_L) ⊆ Z₀ := by
      change V(A_L) ∩ V(K_L) ⊆ V(L₁) ∩ V(K)
      rw [hVL₁_eq_VL']
      exact fun _ ⟨hxAL, hxKL⟩ => ⟨hA_L_le_L'.vertexSet_mono hxAL, hK_L_le_K.vertexSet_mono hxKL⟩
    have hdiv' : IsIndexedZDivision L' Z₀ (![A_L, K_L] : Fin 2 → Graph α β) :=
      isIndexedZDivision_of_isGraphSeparation hsep' hAB'_Z₀
    have hZ₀_A₁ : Z₀ ∩ V(A₁) = V(A₁) ∩ V(K) := by
      ext x
      simp only [Z₀, mem_inter_iff]
      exact ⟨fun ⟨⟨_, hxK⟩, hxA⟩ => ⟨hxA, hxK⟩, fun ⟨hxA, hxK⟩ => ⟨⟨Or.inl hxA, hxK⟩, hxA⟩⟩
    have hZ₀_AL : Z₀ ∩ V(A_L) = V(A_L) ∩ V(K) := by
      change (V(L₁) ∩ V(K)) ∩ V(A_L) = V(A_L) ∩ V(K)
      rw [hVL₁_eq_VL']
      ext x
      simp only [mem_inter_iff]
      exact ⟨fun ⟨⟨_, hxK⟩, hxA⟩ => ⟨hxA, hxK⟩,
        fun ⟨hxA, hxK⟩ => ⟨⟨hA_L_le_L'.vertexSet_mono hxA, hxK⟩, hxA⟩⟩
    have h_a : ∀ i : Fin 2,
        (id : α → α) '' (Z₀ ∩ V((![A₁, K_L] : Fin 2 → Graph α β) i)) =
          Z₀ ∩ V((![A_L, K_L] : Fin 2 → Graph α β) i) := by
      intro i
      rw [image_id]
      fin_cases i
      · change Z₀ ∩ V(A₁) = Z₀ ∩ V(A_L)
        rw [hZ₀_A₁, hZ₀_AL, hVA₁_inter_VK]
      · rfl
    have h_b : ∀ u ∈ Z₀, ∀ v ∈ Z₀, u ≠ v → (id : α → α) u = id v →
        ∃ i : Fin 2, u ∈ V((![A₁, K_L] : Fin 2 → Graph α β) i) ∧
          v ∈ V((![A₁, K_L] : Fin 2 → Graph α β) i) :=
      fun _ _ _ _ hne heq => (hne heq).elim
    have h_c : ∀ i : Fin 2,
        ∀ u ∈ Z₀ ∩ V((![A₁, K_L] : Fin 2 → Graph α β) i),
        ∀ v ∈ Z₀ ∩ V((![A₁, K_L] : Fin 2 → Graph α β) i),
        AreConnectedIn ((![A₁, K_L] : Fin 2 → Graph α β) i) u v ↔
          AreConnectedIn (subgraphInter L' L' ((![A_L, K_L] : Fin 2 → Graph α β) i)) u v := by
      intro i u hu v hv
      fin_cases i
      · change AreConnectedIn A₁ u v ↔ AreConnectedIn (subgraphInter L' L' A_L) u v
        have h_inter_AL : subgraphInter L' L' A_L = A_L :=
          le_antisymm (subgraphInter_le_right le_rfl hA_L_le_L')
            (le_subgraphInter le_rfl hA_L_le_L' hA_L_le_L' le_rfl)
        rw [h_inter_AL]
        exact effectOn_eq_iff_areConnectedIn.mp hSame_A₁_AL_inter
          u (hZ₀_A₁ ▸ hu) v (hZ₀_A₁ ▸ hv)
      · change AreConnectedIn K_L u v ↔ AreConnectedIn (subgraphInter L' L' K_L) u v
        have h_inter_KL : subgraphInter L' L' K_L = K_L :=
          le_antisymm (subgraphInter_le_right le_rfl hK_L_le_L')
            (le_subgraphInter le_rfl hK_L_le_L' hK_L_le_L' le_rfl)
        rw [h_inter_KL]
    have ⟨_, hconn_iff⟩ :=
      theorem_2_5_proof le_rfl (hVL₁_eq_VL'.subset.trans inter_subset_left) hdiv'
        inter_subset_left hdiv₁ (fun _ => le_rfl) h_a h_b h_c
    rw [hdiv₁.2.1] at hconn_iff
    exact effectOn_eq_iff_areConnectedIn.mpr hconn_iff
  have hSame_L₁_L'_VK : HasSameEffectOn L₁ L' V(K) := by
    rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
    intro u huK v hvK
    constructor
    · intro hconn
      have hu : u ∈ V(L₁) ∩ V(K) := ⟨hconn.left_mem, huK⟩
      have hv : v ∈ V(L₁) ∩ V(K) := ⟨hconn.right_mem, hvK⟩
      exact (effectOn_eq_iff_areConnectedIn.mp hSame_L₁_L'_VL u hu v hv).mp hconn
    · intro hconn
      have hu : u ∈ V(L₁) ∩ V(K) := hVL₁_eq_VL'.symm ▸ ⟨hconn.left_mem, huK⟩
      have hv : v ∈ V(L₁) ∩ V(K) := hVL₁_eq_VL'.symm ▸ ⟨hconn.right_mem, hvK⟩
      exact (effectOn_eq_iff_areConnectedIn.mp hSame_L₁_L'_VL u hu v hv).mpr hconn
  have hSame_L₁_L'_Z : HasSameEffectOn L₁ L' Z := by
    rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn] at hSame_L₁_L'_VK ⊢
    exact fun u hu v hv => hSame_L₁_L'_VK u (hZK hu) v (hZK hv)
  have hInter_L₁_K : subgraphInter G₁ L₁ K ≤ L' := by
    refine ⟨?_, ?_⟩
    · intro x ⟨hxL₁, hxK⟩
      rcases hxL₁ with hxA₁ | hxKL
      · have hx_in : x ∈ V(A_L) ∩ V(K) := hVA₁_inter_VK ▸ ⟨hxA₁, hxK⟩
        exact hA_L_le_L'.vertexSet_mono hx_in.1
      · exact hK_L_le_L'.vertexSet_mono hxKL
    · intro e x y hl
      unfold subgraphInter at hl
      rw [restrict_isLink, induce_isLink] at hl
      rcases hl with ⟨⟨heL₁, heK⟩, hlG₁, _, _⟩
      have heKL : e ∈ E(K_L) := heL₁.resolve_left (disjoint_right.mp hDisj_EA₁_EK heK)
      exact hK_L_le_L'.isLink_mono ((hKL_le_G₁.isLink_iff heKL).mpr hlG₁)
  obtain ⟨L, hL_le_G, hSame_L_L₁, hInter_L_L₁⟩ :=
    st_fin.pb.pullback Z hZK hZp L₁ hL₁_le_G₁
  rw [← hG_eq] at hL_le_G hInter_L_L₁
  refine ⟨L, hL_le_G, hSame_L_L₁.trans hSame_L₁_L'_Z, ?_⟩
  have hInter_le_Inter : subgraphInter G L K ≤ subgraphInter G₁ L₁ K := by
    have hLK_le_K : subgraphInter G L K ≤ K := subgraphInter_le_right hL_le_G hKG
    refine ⟨subset_inter hInter_L_L₁.vertexSet_mono hLK_le_K.vertexSet_mono, fun e x y hl => ?_⟩
    have hl_L₁ : L₁.IsLink e x y := hInter_L_L₁.isLink_mono hl
    have hl_K : K.IsLink e x y := hLK_le_K.isLink_mono hl
    have hl_G₁ : G₁.IsLink e x y := hL₁_le_G₁.isLink_mono hl_L₁
    unfold subgraphInter
    rw [restrict_isLink, induce_isLink]
    exact ⟨⟨hl_L₁.edge_mem, hl_K.edge_mem⟩, hl_G₁,
      ⟨hl_L₁.left_mem, hl_K.left_mem⟩, ⟨hl_L₁.right_mem, hl_K.right_mem⟩⟩
  exact hInter_le_Inter.trans hInter_L₁_K

/-- **4.1** (Graph Minors XXII, page 537):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$ be
subgraphs of a graph $\Gamma \cup K$, let $\Gamma$ be a drawing in a surface $\Sigma$ and let $T$ be
the set of all points of $\Sigma$ that are $h$-insulated from $V(\Gamma \cap K)$ by $\Gamma$. Let
$\Gamma'$ be a $T$-variant of $\Gamma$ in $\Sigma$ with $\Gamma' \cap K = \Gamma \cap K$, let
$L' \subseteq \Gamma' \cup K$, and let $Z \subseteq V(K)$ with $|Z| \le p$. Then there exists a
subgraph $L$ of $\Gamma \cup K$ with the same effect on $Z$ as $L'$, with $L \cap K \subseteq L'$." -/
theorem theorem_4_1_proof  (p : ℕ) :
    ∃ h ≥ 1, ∀ (S : Type w) [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K G' Γ' L' : Graph α β),
      V(G).Finite → E(G).Finite → V(G').Finite → E(G').Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      Γ' ≤ G' → K ≤ G' → V(G') = V(Γ') ∪ V(K) → E(G') = E(Γ') ∪ E(K) →
      subgraphInter G Γ K = subgraphInter G' Γ' K →
      ∀ (D D' : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β),
      Γ = D.toEmbeddedGraph ιV ιE → Γ' = D'.toEmbeddedGraph ιV ιE →
      IsVariant D D' (insulatedSet D (ιV ⁻¹' (V(Γ) ∩ V(K))) h) →
      ∀ (Z : Set α), Z ⊆ V(K) → Z.ncard ≤ p → L' ≤ G' →
      ∃ L ≤ G, HasSameEffectOn L L' Z ∧ subgraphInter G L K ≤ L' := by
  obtain ⟨h, hh, h31⟩ := theorem_3_1_proof.{u, v, w} p
  refine ⟨h, hh, ?_⟩
  intro S _ _ hS α β G Γ K G' Γ' L' hVG hEG _hVG' _hEG'
    hΓG hKG hVG_union hEG_union hΓ'G' hKG' hVG'_union hEG'_union hInter
    D D' ιV ιE hΓ hΓ' hVar Z hZK hZp hL'
  let _ : DecidableEq (α ⊕ α) := Classical.decEq (α ⊕ α)
  let jV : α ↪ α ⊕ α :=
    { toFun := fun x => if x ∈ V(K) \ V(Γ) then Sum.inr x else Sum.inl x
      inj' := by
        intro x y hxy
        by_cases hx : x ∈ V(K) \ V(Γ) <;> by_cases hy : y ∈ V(K) \ V(Γ) <;>
          simp only [hx, hy, ↓reduceIte, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at hxy <;>
          exact hxy }
  let jE : β ↪ β ⊕ β :=
    { toFun := fun e => if e ∈ E(K) \ E(Γ) then Sum.inr e else Sum.inl e
      inj' := by
        intro e₁ e₂ he
        by_cases h₁ : e₁ ∈ E(K) \ E(Γ) <;> by_cases h₂ : e₂ ∈ E(K) \ E(Γ) <;>
          simp only [h₁, h₂, ↓reduceIte, Sum.inr.injEq, Sum.inl.injEq, reduceCtorEq] at he <;>
          exact he }
  let ιV' : S ↪ α ⊕ α := ιV.trans Embedding.inl
  let ιE' : Set S ↪ β ⊕ β := ιE.trans Embedding.inl
  have hV_inter : V(Γ) ∩ V(K) = V(Γ') ∩ V(K) :=
    congrArg Graph.vertexSet hInter
  have hjV_Γ : ∀ x ∈ V(Γ), jV x = Sum.inl x := by
    intro x hx
    change (if x ∈ V(K) \ V(Γ) then Sum.inr x else Sum.inl x) = Sum.inl x
    have hn : x ∉ V(K) \ V(Γ) := fun h => h.2 hx
    simp only [hn, ↓reduceIte]
  have hjE_Γ : ∀ e ∈ E(Γ), jE e = Sum.inl e := by
    intro e he
    change (if e ∈ E(K) \ E(Γ) then Sum.inr e else Sum.inl e) = Sum.inl e
    have hn : e ∉ E(K) \ E(Γ) := fun h => h.2 he
    simp only [hn, ↓reduceIte]
  have hjV_Γ' : ∀ x ∈ V(Γ'), jV x = Sum.inl x := by
    intro x hx
    change (if x ∈ V(K) \ V(Γ) then Sum.inr x else Sum.inl x) = Sum.inl x
    have hn : x ∉ V(K) \ V(Γ) := by
      rintro ⟨hxK, hx_not_Γ⟩
      have hx_in : x ∈ V(Γ') ∩ V(K) := ⟨hx, hxK⟩
      rw [← hV_inter] at hx_in
      exact hx_not_Γ hx_in.1
    simp only [hn, ↓reduceIte]
  have hjE_Γ' : ∀ e ∈ E(Γ'), jE e = Sum.inl e := by
    intro e he
    change (if e ∈ E(K) \ E(Γ) then Sum.inr e else Sum.inl e) = Sum.inl e
    have hn : e ∉ E(K) \ E(Γ) := by
      rintro ⟨heK, he_not_Γ⟩
      obtain ⟨x, y, hlΓ'⟩ := Γ'.exists_isLink_of_mem_edgeSet he
      have hlG' : G'.IsLink e x y := hΓ'G'.isLink_mono hlΓ'
      have hlK : K.IsLink e x y := (hKG'.isLink_iff heK).mpr hlG'
      have hl_inter' : (subgraphInter G' Γ' K).IsLink e x y := by
        unfold subgraphInter
        rw [restrict_isLink, induce_isLink]
        exact ⟨⟨he, heK⟩, hlG', ⟨hlΓ'.left_mem, hlK.left_mem⟩, ⟨hlΓ'.right_mem, hlK.right_mem⟩⟩
      rw [← hInter] at hl_inter'
      exact he_not_Γ ((subgraphInter_le_left hΓG hKG).isLink_mono hl_inter').edge_mem
    simp only [hn, ↓reduceIte]
  have hΓ_map : Γ.mapEmbed jV jE = D.toEmbeddedGraph ιV' ιE' := by
    rw [hΓ, toEmbeddedGraph_eq_mapEmbed, toEmbeddedGraph_eq_mapEmbed]
    refine Graph.ext ?_ fun e x y => ?_
    · ext z
      simp only [vertexSet_mapEmbed, mem_image]
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨v, hv, ?_⟩
        exact (hjV_Γ (ιV v) (hΓ ▸ mem_image_of_mem ιV hv)).symm
      · rintro ⟨v, hv, rfl⟩
        exact ⟨ιV v, ⟨v, hv, rfl⟩, hjV_Γ (ιV v) (hΓ ▸ mem_image_of_mem ιV hv)⟩
    · constructor
      · rintro ⟨e₁, x₁, y₁, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
        refine ⟨e₀, x₀, y₀, hl₀, ?_, ?_, ?_⟩
        · exact (hjE_Γ (ιE e₀) (hΓ ▸ mem_image_of_mem ιE hl₀.1)).symm
        · exact (hjV_Γ (ιV x₀) (hΓ ▸ mem_image_of_mem ιV hl₀.left_mem)).symm
        · exact (hjV_Γ (ιV y₀) (hΓ ▸ mem_image_of_mem ιV hl₀.right_mem)).symm
      · rintro ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩
        refine ⟨ιE e₀, ιV x₀, ιV y₀, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
        · exact hjE_Γ (ιE e₀) (hΓ ▸ mem_image_of_mem ιE hl₀.1)
        · exact hjV_Γ (ιV x₀) (hΓ ▸ mem_image_of_mem ιV hl₀.left_mem)
        · exact hjV_Γ (ιV y₀) (hΓ ▸ mem_image_of_mem ιV hl₀.right_mem)
  have hΓ'_map : Γ'.mapEmbed jV jE = D'.toEmbeddedGraph ιV' ιE' := by
    rw [hΓ', toEmbeddedGraph_eq_mapEmbed, toEmbeddedGraph_eq_mapEmbed]
    refine Graph.ext ?_ fun e x y => ?_
    · ext z
      simp only [vertexSet_mapEmbed, mem_image]
      constructor
      · rintro ⟨w, ⟨v, hv, rfl⟩, rfl⟩
        refine ⟨v, hv, ?_⟩
        exact (hjV_Γ' (ιV v) (hΓ' ▸ mem_image_of_mem ιV hv)).symm
      · rintro ⟨v, hv, rfl⟩
        exact ⟨ιV v, ⟨v, hv, rfl⟩, hjV_Γ' (ιV v) (hΓ' ▸ mem_image_of_mem ιV hv)⟩
    · constructor
      · rintro ⟨e₁, x₁, y₁, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩, rfl, rfl, rfl⟩
        refine ⟨e₀, x₀, y₀, hl₀, ?_, ?_, ?_⟩
        · exact (hjE_Γ' (ιE e₀) (hΓ' ▸ mem_image_of_mem ιE hl₀.1)).symm
        · exact (hjV_Γ' (ιV x₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.left_mem)).symm
        · exact (hjV_Γ' (ιV y₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.right_mem)).symm
      · rintro ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩
        refine ⟨ιE e₀, ιV x₀, ιV y₀, ⟨e₀, x₀, y₀, hl₀, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
        · exact hjE_Γ' (ιE e₀) (hΓ' ▸ mem_image_of_mem ιE hl₀.1)
        · exact hjV_Γ' (ιV x₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.left_mem)
        · exact hjV_Γ' (ιV y₀) (hΓ' ▸ mem_image_of_mem ιV hl₀.right_mem)
  have hVK' : ιV' ⁻¹' V(K.mapEmbed jV jE) ⊆ D.V := by
    rintro v ⟨y, hyK, hy_eq⟩
    change (if y ∈ V(K) \ V(Γ) then Sum.inr y else Sum.inl y) = Sum.inl (ιV v) at hy_eq
    by_cases hy_diff : y ∈ V(K) \ V(Γ)
    · simp only [hy_diff, ↓reduceIte, reduceCtorEq] at hy_eq
    · simp only [hy_diff, ↓reduceIte, Sum.inl.injEq] at hy_eq
      subst hy_eq
      have hvΓ : ιV v ∈ V(Γ) := by_contra fun hn => hy_diff ⟨hyK, hn⟩
      rw [hΓ] at hvΓ
      exact (ιV.injective.mem_set_image).mp hvΓ
  have hEK' : ιE' ⁻¹' E(K.mapEmbed jV jE) ⊆ D.E := by
    rintro e ⟨b, hbK, hb_eq⟩
    change (if b ∈ E(K) \ E(Γ) then Sum.inr b else Sum.inl b) = Sum.inl (ιE e) at hb_eq
    by_cases hb_diff : b ∈ E(K) \ E(Γ)
    · simp only [hb_diff, ↓reduceIte, reduceCtorEq] at hb_eq
    · simp only [hb_diff, ↓reduceIte, Sum.inl.injEq] at hb_eq
      subst hb_eq
      have heΓ : ιE e ∈ E(Γ) := by_contra fun hn => hb_diff ⟨hbK, hn⟩
      rw [hΓ] at heΓ
      exact (ιE.injective.mem_set_image).mp heΓ
  have hY_eq' : ιV' ⁻¹' (V(Γ.mapEmbed jV jE) ∩ V(K.mapEmbed jV jE)) =
      ιV ⁻¹' (V(Γ) ∩ V(K)) := by
    ext v
    simp only [mem_preimage, mem_inter_iff, vertexSet_mapEmbed]
    constructor
    · rintro ⟨⟨x, hxΓ, hx_eq⟩, ⟨y, hyK, hy_eq⟩⟩
      have hxy : y = x := jV.injective (hy_eq.trans hx_eq.symm)
      subst y
      rw [hjV_Γ x hxΓ] at hx_eq
      obtain rfl : x = ιV v := Sum.inl.inj hx_eq
      exact ⟨hxΓ, hyK⟩
    · rintro ⟨hvΓ, hvK⟩
      have h_eq : jV (ιV v) = ιV' v := hjV_Γ (ιV v) hvΓ
      exact ⟨⟨ιV v, hvΓ, h_eq⟩, ⟨ιV v, hvK, h_eq⟩⟩
  have hVar_map : IsVariant D D'
      (insulatedSet D (ιV' ⁻¹' (V(Γ.mapEmbed jV jE) ∩ V(K.mapEmbed jV jE))) h) := by
    rwa [hY_eq']
  have hInter_map :
      subgraphInter (G.mapEmbed jV jE) (Γ.mapEmbed jV jE) (K.mapEmbed jV jE) =
        subgraphInter (G'.mapEmbed jV jE) (Γ'.mapEmbed jV jE) (K.mapEmbed jV jE) := by
    rw [← mapEmbed_subgraphInter, ← mapEmbed_subgraphInter, hInter]
  obtain ⟨L_img, hL_img_le, hSame_img, hInter_img⟩ :=
    lemma_4_1_normalized (α := α ⊕ α) (β := β ⊕ β) hh (h31 hS)
      (G.mapEmbed jV jE) (Γ.mapEmbed jV jE) (K.mapEmbed jV jE)
      (G'.mapEmbed jV jE) (Γ'.mapEmbed jV jE) (L'.mapEmbed jV jE)
      (hVG.image jV) (hEG.image jE)
      (mapEmbed_mono jV jE hΓG) (mapEmbed_mono jV jE hKG)
      (by rw [vertexSet_mapEmbed, vertexSet_mapEmbed, vertexSet_mapEmbed, ← image_union, hVG_union])
      (by rw [edgeSet_mapEmbed, edgeSet_mapEmbed, edgeSet_mapEmbed, ← image_union, hEG_union])
      (mapEmbed_mono jV jE hΓ'G') (mapEmbed_mono jV jE hKG')
      (by rw [vertexSet_mapEmbed, vertexSet_mapEmbed, vertexSet_mapEmbed, ← image_union, hVG'_union])
      (by rw [edgeSet_mapEmbed, edgeSet_mapEmbed, edgeSet_mapEmbed, ← image_union, hEG'_union])
      hInter_map D D' ιV' ιE' hΓ_map hΓ'_map hVK' hEK' hVar_map
      (jV '' Z) (image_mono hZK) ((ncard_image_of_injective Z jV.injective).symm ▸ hZp)
      (mapEmbed_mono jV jE hL')
  obtain ⟨hL_map, hL_le⟩ := mapEmbed_comapEmbed_of_le jV jE hL_img_le
  let L := L_img.comapEmbed jV jE
  refine ⟨L, hL_le, ?_, ?_⟩
  · rw [← hL_map] at hSame_img
    exact (hasSameEffectOn_mapEmbed_iff jV jE).mp hSame_img
  · apply (mapEmbed_le_iff jV jE).mp
    rw [mapEmbed_subgraphInter, hL_map]
    exact hInter_img

end GraphMinor.GM22
