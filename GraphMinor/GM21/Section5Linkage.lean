module

public import GraphMinor.GM21.Section5ThreeTwo
public import GraphMinor.GM21.NestedSeparations
public import GraphMinor.GM19.CutFragment
public import GraphMinor.GM19.RadialExists
import GraphMinor.GM11.Section4b
import GraphMinor.GM11.Section6
import GraphMinor.GM12.Section4NormalArcDisc
import GraphMinor.GM12.Section4DiscTangency
import GraphMinor.GM12.Section73WalkPointSets
import GraphMinor.Surface.SurfacePull

/-!
# Graph Minors XXI, Section 5: Linkages, topological feasibility, and connecting subdrawings

This file proves the bridge lemmas between linkages in a drawing `Γ` on a surface `S` with
terminals `Γ.V ∩ bd S` and the topological feasibility / connecting-subdrawings conditions of
Graph Minors XII (3.2) in the capped surface `Shat` (`cap : IsCappedSurface S Shat`):

1. `isTopologicallyFeasible_of_linkage`: any linkage `L` in `Γ.toHypergraph` with
   `terminals L = Γ.V ∩ bd S` satisfies `IsTopologicallyFeasible Δ Zs` in `Shat`, where
   `Δ` are the closed cuff discs `closure (cap.cuffDisc C)` of `S` in `Shat` and `Zs` are the
   `cap.emb`-images of the blocks of `linkagePattern L`.
2. `exists_linkage_avoiding_vertex_of_connectingSubdrawings`: if
   `Γ' = deleteVertices (capDrawing hS cap Γ) {cap.emb v}` (`v ∈ Γ.V \ bd S`) satisfies
   `HasConnectingSubdrawings Γ' Z Zs`, then there is a linkage `L'` in `Γ.toHypergraph` with
   `v ∉ L'.vertexSet` and `linkagePattern L' = linkagePattern L`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Topology Function Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM10
  GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14
open GraphMinor.GM19 (IsCappedSurface)

variable {S Shat : Type} [TopologicalSpace S] [TopologicalSpace Shat]

/-! ## 1. Walks in subhypergraphs and lines in drawings -/

/-- `Γ.toHypergraph` is always a graph (every edge has 1 or 2 ends in `Γ.V`). -/
lemma drawing_toHypergraph_isGraph (Γ : Surface.Drawing S) : Γ.toHypergraph.IsGraph := by
  intro e he
  obtain ⟨u, v, _, hu, hv, hcap⟩ := (Γ.toGraph.edge_mem_iff_exists_isLink e).mp he
  have hends : Γ.toHypergraph.ends e = {u, v} := by
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq, Surface.Drawing.toHypergraph]
    rw [← hcap]
    exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨he, h.2, h.1⟩⟩
  rw [hends]
  refine ⟨⟨u, Or.inl rfl⟩, ?_⟩
  exact (ncard_insert_le u {v}).trans (by simp)

/-- Any adjacency in `H.skeleton` for `H ≤ Γ.toHypergraph` gives a link in `Γ.toGraph` via an edge
of `H.edgeSet`. -/
lemma isLink_of_skeleton_adj {Γ : Surface.Drawing S} {H : Hypergraph S (Set S)}
    (hH : H ≤ Γ.toHypergraph) {x y : S} (hadj : H.skeleton.Adj x y) :
    ∃ e ∈ H.edgeSet, Γ.toGraph.IsLink e x y := by
  rcases hadj with ⟨hne, e, hx, hy⟩
  have heH : e ∈ H.edgeSet := H.edge_mem_of_inc hx
  have heΓ : e ∈ Γ.E := hH.edgeSet_subset heH
  have hxΓ : Γ.toHypergraph.Inc e x := Hypergraph.inc_of_le hH hx
  have hyΓ : Γ.toHypergraph.Inc e y := Hypergraph.inc_of_le hH hy
  refine ⟨e, heH, heΓ, hxΓ.2.1, hyΓ.2.1, ?_⟩
  apply Subset.antisymm
  · rintro z ⟨hz_cl, hz_V⟩
    have hz_inc : Γ.toHypergraph.Inc e z := ⟨heΓ, hz_V, hz_cl⟩
    by_contra hnot
    have hzx : z ≠ x := fun h => hnot (Or.inl h)
    have hzy : z ≠ y := fun h => hnot (Or.inr h)
    exact not_inc_of_inc_inc_ne (drawing_toHypergraph_isGraph Γ) hxΓ hyΓ hne hzx hzy hz_inc
  · rintro z (rfl | rfl)
    · exact ⟨hxΓ.2.2, hxΓ.2.1⟩
    · exact ⟨hyΓ.2.2, hyΓ.2.1⟩

/-- Any walk in `H.skeleton` (`H ≤ Γ.toHypergraph`) lifts to a `GraphWalk Γ.toGraph` whose vertices
lie in `H.vertexSet` and whose edges lie in `H.edgeSet`. -/
lemma exists_graphWalk_of_skeleton_walk {Γ : Surface.Drawing S} {H : Hypergraph S (Set S)}
    (hH : H ≤ Γ.toHypergraph) {a b : S} (ha : a ∈ H.vertexSet)
    (W₀ : H.skeleton.Walk a b) :
    ∃ W : GraphWalk Γ.toGraph a b,
      (∀ x ∈ W.support, x ∈ H.vertexSet) ∧
      (∀ e ∈ W.edges, e ∈ H.edgeSet) := by
  induction W₀ with
  | nil =>
    refine ⟨.nil (hH.vertexSet_subset ha), ?_, ?_⟩
    · intro x hx
      rcases List.mem_singleton.mp hx with rfl
      exact ha
    · intro e he
      cases he
  | @cons x y z hadj W' ih =>
    have hy : y ∈ H.vertexSet := by
      rcases hadj with ⟨_, e, _, hy_inc⟩
      exact H.vertex_mem_of_inc hy_inc
    obtain ⟨e, heH, hl⟩ := isLink_of_skeleton_adj hH hadj
    obtain ⟨W₁, hV₁, hE₁⟩ := ih hy
    refine ⟨.cons hl W₁, ?_, ?_⟩
    · intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ha
      · exact hV₁ u hu
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact heH
      · exact hE₁ f hf

/-- If `H ≤ Γ.toHypergraph` and `H.skeleton.Reachable a b`, there is a simple walk
`W : GraphWalk Γ.toGraph a b` with vertices in `H.vertexSet` and edges in `H.edgeSet`. -/
lemma exists_simple_graphWalk_of_reachable [DecidableEq S] {Γ : Surface.Drawing S}
    {H : Hypergraph S (Set S)} (hH : H ≤ Γ.toHypergraph) {a b : S}
    (ha : a ∈ H.vertexSet) (hr : H.skeleton.Reachable a b) :
    ∃ W : GraphWalk Γ.toGraph a b,
      W.IsSimple ∧
      (∀ x ∈ W.support, x ∈ H.vertexSet) ∧
      (∀ e ∈ W.edges, e ∈ H.edgeSet) := by
  obtain ⟨W₀⟩ := hr
  obtain ⟨W₁, hV₁, hE₁⟩ := exists_graphWalk_of_skeleton_walk hH ha W₀
  obtain ⟨W, hWs, hs, he⟩ := GraphMinor.GM11.GraphWalk.exists_isSimple W₁
  exact ⟨W, hWs, fun x hx => hV₁ x (hs x hx), fun e he' => hE₁ e (he e he')⟩

/-- For any walk `W` in `Γ.toGraph`, `(walkDrawing Γ W).U` is the union of `{x | x ∈ W.support}`
and `⋃ e ∈ {e | e ∈ W.edges}, closure e`. -/
lemma walkDrawing_U_eq [T1Space S] (Γ : Surface.Drawing S) {a b : S} (W : GraphWalk Γ.toGraph a b) :
    (walkDrawing Γ W).U =
      {x | x ∈ W.support} ∪ ⋃ e ∈ {e | e ∈ W.edges}, closure e := by
  rw [Surface.Drawing.U_eq, walkDrawing_V, walkDrawing_E]

/-- For a simple walk `W` in `Γ.toGraph` with `a = b`, `(walkDrawing Γ W).U = {a}`. -/
lemma walkDrawing_U_eq_singleton_of_eq [T2Space S] (Γ : Surface.Drawing S) {a b : S}
    (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple) (hab : a = b) :
    (walkDrawing Γ W).U = {a} := by
  cases W with
  | nil h => exact walkDrawing_nil_points h
  | @cons x u y e hl r =>
    exfalso
    exact (List.nodup_cons.mp hW).1 (hab ▸ r.end_mem_support)

/-- For a simple walk `W` in `Γ.toGraph` with `a ≠ b`, `(walkDrawing Γ W).U` is a line with ends
`a` and `b`. -/
lemma walkDrawing_isLineWithEnds [T2Space S] (Γ : Surface.Drawing S) {a b : S}
    (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple) (hab : a ≠ b) :
    IsLineWithEnds (walkDrawing Γ W).U a b := by
  rw [walkDrawing_U_eq]
  exact GraphMinor.GM11.walk_isLine Γ W hW hab

/-- In a drawing `Γ`, if two walks `W₁, W₂` have disjoint vertex supports and disjoint edge sets,
then `(walkDrawing Γ W₁).U` and `(walkDrawing Γ W₂).U` are disjoint. -/
lemma disjoint_walkDrawing_U [T1Space S] {Γ : Surface.Drawing S} {a₁ b₁ a₂ b₂ : S}
    (W₁ : GraphWalk Γ.toGraph a₁ b₁) (W₂ : GraphWalk Γ.toGraph a₂ b₂)
    (hV : Disjoint {x | x ∈ W₁.support} {x | x ∈ W₂.support})
    (hE : Disjoint {e | e ∈ W₁.edges} {e | e ∈ W₂.edges}) :
    Disjoint (walkDrawing Γ W₁).U (walkDrawing Γ W₂).U := by
  have hsub₁ := walkDrawing_isSubdrawing Γ W₁
  have hsub₂ := walkDrawing_isSubdrawing Γ W₂
  rw [disjoint_left]
  intro x hx₁ hx₂
  by_cases hxV : x ∈ Γ.V
  · have hx₁V : x ∈ {z | z ∈ W₁.support} := by
      rcases (mem_walkDrawing_U Γ W₁).mp hx₁ with h | ⟨e, he, hxe⟩
      · exact h
      · exact GraphMinor.GM11.mem_support_of_mem_edges W₁ he hxe hxV
    have hx₂V : x ∈ {z | z ∈ W₂.support} := by
      rcases (mem_walkDrawing_U Γ W₂).mp hx₂ with h | ⟨e, he, hxe⟩
      · exact h
      · exact GraphMinor.GM11.mem_support_of_mem_edges W₂ he hxe hxV
    exact disjoint_left.mp hV hx₁V hx₂V
  · have hx₁E : ∃ e ∈ W₁.edges, x ∈ e := by
      rcases (mem_walkDrawing_U Γ W₁).mp hx₁ with h | ⟨e, he, hxe⟩
      · exact (hxV (W₁.mem_vertexSet_of_mem_support h)).elim
      · have heΓ : e ∈ Γ.E := hsub₁.2 (by rw [walkDrawing_E]; exact he)
        refine ⟨e, he, ?_⟩
        rw [← Γ.closure_diff_V heΓ]
        exact ⟨hxe, hxV⟩
    have hx₂E : ∃ f ∈ W₂.edges, x ∈ f := by
      rcases (mem_walkDrawing_U Γ W₂).mp hx₂ with h | ⟨f, hf, hxf⟩
      · exact (hxV (W₂.mem_vertexSet_of_mem_support h)).elim
      · have hfΓ : f ∈ Γ.E := hsub₂.2 (by rw [walkDrawing_E]; exact hf)
        refine ⟨f, hf, ?_⟩
        rw [← Γ.closure_diff_V hfΓ]
        exact ⟨hxf, hxV⟩
    rcases hx₁E with ⟨e, he, hxe⟩
    rcases hx₂E with ⟨f, hf, hxf⟩
    have heΓ : e ∈ Γ.E := hsub₁.2 (by rw [walkDrawing_E]; exact he)
    have hfΓ : f ∈ Γ.E := hsub₂.2 (by rw [walkDrawing_E]; exact hf)
    have hef : e = f := Γ.edge_eq_of_mem heΓ hfΓ hxe hxf
    subst hef
    exact disjoint_left.mp hE he hf

/-- If `Γ.IsProper`, then for any walk `W` in `Γ.toGraph`,
`(walkDrawing Γ W).U ∩ bd S = {x | x ∈ W.support} ∩ bd S`. -/
lemma walkDrawing_U_inter_bd_eq [T1Space S] {Γ : Surface.Drawing S} (hprop : Γ.IsProper)
    {a b : S} (W : GraphWalk Γ.toGraph a b) :
    (walkDrawing Γ W).U ∩ bd S = {x | x ∈ W.support} ∩ bd S := by
  have hsub := walkDrawing_isSubdrawing Γ W
  apply Subset.antisymm
  · rintro x ⟨hxU, hxB⟩
    have hxV : x ∈ Γ.V := (proper_drawing_inter_subset_bd hprop subset_rfl).subset
      ⟨hsub.U_subset hxU, hxB⟩ |>.1
    refine ⟨?_, hxB⟩
    rcases (mem_walkDrawing_U Γ W).mp hxU with h | ⟨e, he, hxe⟩
    · exact h
    · exact GraphMinor.GM11.mem_support_of_mem_edges W he hxe hxV
  · rintro x ⟨hxW, hxB⟩
    exact ⟨(mem_walkDrawing_U Γ W).mpr (Or.inl hxW), hxB⟩

/-! ## 2. Topological feasibility of a linkage pattern (`isTopologicallyFeasible_of_linkage`) -/

/-- Any linkage `L` in `Γ.toHypergraph` with `terminals L = Γ.V ∩ bd S` satisfies
`IsTopologicallyFeasible Δ Zs` in `Shat`, where `Δ` are the closed cuff discs
`closure (cap.cuffDisc C)` and `Zs` are the `cap.emb`-images of the blocks of `linkagePattern L`. -/
theorem isTopologicallyFeasible_of_linkage
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S} (hprop : Γ.IsProper)
    {L : Hypergraph S (Set S)} (hL : IsLinkage Γ.toHypergraph L)
    (hterm : terminals L = Γ.V ∩ bd S)
    {t n : ℕ} (cuffEquiv : Fin t ≃ cuffs S)
    (B : Fin n → Set S)
    (hB_mem : ∀ j, B j ∈ linkagePattern L)
    (hB_disj : ∀ i j, i ≠ j → Disjoint (B i) (B j)) :
    IsTopologicallyFeasible (fun i => closure (cap.cuffDisc (cuffEquiv i).val))
      (fun j => cap.emb '' (B j)) := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hcl_Shat : IsClosedSurface Shat := cap.isClosedSurface
  have : T2Space Shat := hcl_Shat.2.1
  have : ConnectedSpace Shat := cap.connected
  have hclosed_emb : IsClosedMap cap.emb := cap.isEmbedding.continuous.isClosedMap
  classical
  let Δ : Fin t → Set Shat := fun i => closure (cap.cuffDisc (cuffEquiv i).val)
  let Zs : Fin n → Set Shat := fun j => cap.emb '' (B j)
  have hΔ : ∀ i, IsClosedDisc (Δ i) :=
    fun i => cap.cuffDisc_closedDisc (cuffEquiv i).val (cuffEquiv i).property
  have hΔ_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (Δ i₁) (Δ i₂) := by
    intro i₁ i₂ hne
    exact cap.cuffDisc_disjoint (cuffEquiv i₁).val (cuffEquiv i₁).property
      (cuffEquiv i₂).val (cuffEquiv i₂).property
      (fun h => hne (cuffEquiv.injective (Subtype.ext h)))
  have hΔ_bd : ∀ i, discBd (Δ i) = cap.emb '' (cuffEquiv i).val :=
    fun i => cap.cuffDisc_bd (cuffEquiv i).val (cuffEquiv i).property
  have hbd_eq_iUnion : bd S = ⋃ i : Fin t, (cuffEquiv i).val := by
    rw [← sUnion_cuffs]
    ext x
    simp only [mem_sUnion, mem_iUnion]
    exact ⟨fun ⟨C, hC, hxC⟩ => ⟨cuffEquiv.symm ⟨C, hC⟩, by simpa using hxC⟩,
      fun ⟨i, hxi⟩ => ⟨(cuffEquiv i).val, (cuffEquiv i).property, hxi⟩⟩
  have hemb_inter_Δ : ∀ A : Set S,
      (cap.emb '' A) ∩ (⋃ i : Fin t, Δ i) = cap.emb '' (A ∩ bd S) := by
    intro A
    ext z
    simp only [mem_inter_iff, mem_image, mem_iUnion]
    constructor
    · rintro ⟨⟨x, hxA, rfl⟩, ⟨i, hzΔ⟩⟩
      have hxC : x ∈ (cuffEquiv i).val := by
        dsimp only [Δ] at hzΔ
        rw [cap.closure_cuffDisc hS (cuffEquiv i).property] at hzΔ
        rcases hzΔ with hz_open | ⟨y, hyC, hyx⟩
        · exfalso
          have : cap.emb x ∈ (range cap.emb)ᶜ := by
            rw [cap.compl_eq]
            exact mem_iUnion₂.mpr ⟨(cuffEquiv i).val, (cuffEquiv i).property, hz_open⟩
          exact this (mem_range_self x)
        · rwa [cap.isEmbedding.injective hyx] at hyC
      refine ⟨x, ⟨hxA, ?_⟩, rfl⟩
      rw [hbd_eq_iUnion]
      exact mem_iUnion.mpr ⟨i, hxC⟩
    · rintro ⟨x, ⟨hxA, hxB⟩, rfl⟩
      rw [hbd_eq_iUnion, mem_iUnion] at hxB
      rcases hxB with ⟨i, hxC⟩
      refine ⟨⟨x, hxA, rfl⟩, ⟨i, ?_⟩⟩
      exact Surface.discBd_subset (Δ i) (by rw [hΔ_bd i]; exact mem_image_of_mem _ hxC)
  have hex_walk : ∀ j : Fin n, ∃ (C : Hypergraph S (Set S)) (a b : S)
      (W : GraphWalk Γ.toGraph a b),
      IsComponentOf L C ∧
      B j = terminals L ∩ C.vertexSet ∧
      B j = {a, b} ∧
      W.IsSimple ∧
      (∀ x ∈ W.support, x ∈ C.vertexSet) ∧
      (∀ e ∈ W.edges, e ∈ C.edgeSet) := by
    intro j
    rcases hL.mem_linkagePattern_structure (hB_mem j) with
      ⟨a, ha, hBa, _⟩ | ⟨a, ha, b, hb, hab, hBab, _, _⟩
    · let C := reachableComponent L a
      have hC : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 ha.1
      have haC : a ∈ C.vertexSet := self_mem_reachableComponent ha.1
      have hBC : B j = terminals L ∩ C.vertexSet := by
        have hP : terminals L ∩ C.vertexSet ∈ linkagePattern L := ⟨C, hC, rfl⟩
        by_contra hne
        exact disjoint_left.mp (hL.disjoint_of_mem_linkagePattern (hB_mem j) hP hne)
          (by rw [hBa]; exact rfl) ⟨ha, haC⟩
      have haΓ : a ∈ Γ.V := hL.1.vertexSet_subset ha.1
      refine ⟨C, a, a, .nil haΓ, hC, hBC, by rw [hBa, pair_eq_singleton],
        List.nodup_singleton a, ?_, ?_⟩
      · intro x hx
        rcases List.mem_singleton.mp hx with rfl
        exact haC
      · intro e he
        cases he
    · let C := reachableComponent L a
      have hC : IsComponentOf L C := isComponentOf_reachableComponent hL.2.1 ha.1
      have haC : a ∈ C.vertexSet := self_mem_reachableComponent ha.1
      have hBC : B j = terminals L ∩ C.vertexSet := by
        have hP : terminals L ∩ C.vertexSet ∈ linkagePattern L := ⟨C, hC, rfl⟩
        by_contra hne
        exact disjoint_left.mp (hL.disjoint_of_mem_linkagePattern (hB_mem j) hP hne)
          (by rw [hBab]; exact Or.inl rfl) ⟨ha, haC⟩
      have hbC : b ∈ C.vertexSet := by
        have : b ∈ terminals L ∩ C.vertexSet := by rw [← hBC, hBab]; exact Or.inr rfl
        exact this.2
      have hr : C.skeleton.Reachable a b := hC.2.2.1 a haC b hbC
      obtain ⟨W, hWs, hWV, hWE⟩ :=
        exists_simple_graphWalk_of_reachable (hC.1.trans hL.1) haC hr
      exact ⟨C, a, b, W, hC, hBC, hBab, hWs, hWV, hWE⟩
  choose C a b W hC hBC hBab hWs hWV hWE using hex_walk
  have hC_ne : ∀ i j, i ≠ j → C i ≠ C j := by
    intro i j hij h_eq
    have hBi : (B i).Nonempty := by rw [hBab i]; exact insert_nonempty _ _
    obtain ⟨x, hx⟩ := hBi
    exact disjoint_left.mp (hB_disj i j hij) hx (by rwa [hBC j, ← h_eq, ← hBC i])
  let K : Fin n → Set Shat := fun j => cap.emb '' (walkDrawing Γ (W j)).U
  have hK_closed : ∀ j, IsClosed (K j) :=
    fun j => hclosed_emb _ (walkDrawing Γ (W j)).isClosed_U
  have hK_inter_Δ : ∀ j, K j ∩ (⋃ i, Δ i) = Zs j := by
    intro j
    dsimp only [K, Zs]
    rw [hemb_inter_Δ, walkDrawing_U_inter_bd_eq hprop (W j)]
    congr 1
    apply Subset.antisymm
    · rintro x ⟨hxW, hxB⟩
      have hxC : x ∈ (C j).vertexSet := hWV j x hxW
      have hxΓ : x ∈ Γ.V := (hC j).1.vertexSet_subset hxC |> hL.1.vertexSet_subset
      have hx_term : x ∈ terminals L := by rw [hterm]; exact ⟨hxΓ, hxB⟩
      rw [hBC j]
      exact ⟨hx_term, hxC⟩
    · rw [hBab j]
      rintro x (rfl | rfl)
      · have ha_term : a j ∈ terminals L := by
          have : a j ∈ B j := by rw [hBab j]; exact Or.inl rfl
          rw [hBC j] at this; exact this.1
        rw [hterm] at ha_term
        exact ⟨(W j).start_mem_support, ha_term.2⟩
      · have hb_term : b j ∈ terminals L := by
          have : b j ∈ B j := by rw [hBab j]; exact Or.inr rfl
          rw [hBC j] at this; exact this.1
        rw [hterm] at hb_term
        exact ⟨(W j).end_mem_support, hb_term.2⟩
  have hZs_sub_K : ∀ j, Zs j ⊆ K j := by
    intro j
    rw [← hK_inter_Δ j]
    exact inter_subset_left
  have hK_disj : ∀ i j, i ≠ j → Disjoint (K i) (K j) := by
    intro i j hij
    have hdisj_C := disjoint_of_isComponentOf_ne hL.2.1 (hC i) (hC j) (hC_ne i j hij)
    have hdisj_U : Disjoint (walkDrawing Γ (W i)).U (walkDrawing Γ (W j)).U := by
      apply disjoint_walkDrawing_U (W i) (W j)
      · exact hdisj_C.1.mono (fun x hx => hWV i x hx) (fun x hx => hWV j x hx)
      · exact hdisj_C.2.mono (fun e he => hWE i e he) (fun e he => hWE j e he)
    exact Disjoint.image hdisj_U (cap.isEmbedding.injective.injOn)
      (subset_univ _) (subset_univ _)
  have hex_discs : ∀ F : Set (Fin n), F.Finite →
      ∃ D : Fin n → Set Shat,
        (∀ j ∈ F, IsClosedDisc (D j) ∧ D j ∩ (⋃ i, Δ i) = Zs j ∧
          ∀ k, k ∉ F → Disjoint (D j) (K k)) ∧
        (∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (D i) (D j)) := by
    intro F hF
    induction F, hF using Set.Finite.induction_on with
    | empty =>
      exact ⟨fun _ => ∅, by simp, by simp⟩
    | @insert j₀ F hj₀ hF ih =>
      obtain ⟨D, hD, hDD⟩ := ih
      by_cases hab₀ : a j₀ = b j₀
      · have hU₀ : (walkDrawing Γ (W j₀)).U = {a j₀} :=
          walkDrawing_U_eq_singleton_of_eq Γ (W j₀) (hWs j₀) hab₀
        have hK₀ : K j₀ = {cap.emb (a j₀)} := by
          dsimp only [K]
          rw [hU₀, image_singleton]
        have hZs₀ : Zs j₀ = {cap.emb (a j₀)} := by
          dsimp only [Zs]
          rw [hBab j₀, hab₀, pair_eq_singleton, image_singleton]
        have ha₀_bd : a j₀ ∈ bd S := by
          have : a j₀ ∈ terminals L := by
            have : a j₀ ∈ B j₀ := by rw [hBab j₀]; exact Or.inl rfl
            rw [hBC j₀] at this; exact this.1
          rw [hterm] at this; exact this.2
        rw [hbd_eq_iUnion, mem_iUnion] at ha₀_bd
        rcases ha₀_bd with ⟨i₀, ha₀_i₀⟩
        let z₀ : Shat := cap.emb (a j₀)
        have hz₀_bd : z₀ ∈ discBd (Δ i₀) := by
          rw [hΔ_bd i₀]
          exact mem_image_of_mem _ ha₀_i₀
        let Z_avoid : Set Shat :=
          (⋃ i : {i : Fin t // i ≠ i₀}, Δ i.1) ∪
          (⋃ j ∈ F, D j) ∪
          (⋃ k ∈ (insert j₀ F)ᶜ, K k)
        have hZ_avoid_closed : IsClosed Z_avoid := by
          refine ((isClosed_iUnion_of_finite fun i : {i : Fin t // i ≠ i₀} =>
              (hΔ i.1).isClosed).union
            (hF.isClosed_biUnion fun j hj => (hD j hj).1.isClosed)).union ?_
          exact (toFinite (insert j₀ F)ᶜ).isClosed_biUnion fun k _ => hK_closed k
        have hz₀_not_Z : z₀ ∉ Z_avoid := by
          have hz₀_K : z₀ ∈ K j₀ := by rw [hK₀]; exact rfl
          rintro ((h₁ | h₂) | h₃)
          · obtain ⟨⟨i, hi⟩, hzi⟩ := mem_iUnion.mp h₁
            exact disjoint_left.mp (hΔ_disj i₀ i hi.symm) (Surface.discBd_subset _ hz₀_bd) hzi
          · obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp h₂
            exact disjoint_left.mp ((hD j hj).2.2 j₀ hj₀) hzj hz₀_K
          · obtain ⟨k, hk, hzk⟩ := mem_iUnion₂.mp h₃
            have hkj₀ : j₀ ≠ k := fun h => hk (by simp [h])
            exact disjoint_left.mp (hK_disj j₀ k hkj₀) hz₀_K hzk
        obtain ⟨Q, _, hQ_disc, hQ_Δi₀, hQ_disj_Z, _, _⟩ :=
          exists_disc_touching_boundary_point hcl_Shat (hΔ i₀)
            hZ_avoid_closed hz₀_bd hz₀_not_Z
        have hQ_Δ : Q ∩ (⋃ i, Δ i) = Zs j₀ := by
          rw [hZs₀]
          apply Subset.antisymm
          · rintro x ⟨hxQ, hxΔ⟩
            obtain ⟨i, hxi⟩ := mem_iUnion.mp hxΔ
            by_cases hi : i = i₀
            · subst hi
              exact hQ_Δi₀.subset ⟨hxQ, hxi⟩
            · exfalso
              exact disjoint_left.mp hQ_disj_Z hxQ
                (Or.inl (Or.inl (mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩)))
          · rintro x rfl
            have hxQ : z₀ ∈ Q ∩ Δ i₀ := by rw [hQ_Δi₀]; exact rfl
            exact ⟨hxQ.1, mem_iUnion.mpr ⟨i₀, hxQ.2⟩⟩
        have hQ_D : ∀ j ∈ F, Disjoint Q (D j) := by
          intro j hj
          exact hQ_disj_Z.mono_right fun x hx => Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hj, hx⟩))
        have hQ_K : ∀ k, k ∉ insert j₀ F → Disjoint Q (K k) := by
          intro k hk
          exact hQ_disj_Z.mono_right fun x hx => Or.inr (mem_iUnion₂.mpr ⟨k, hk, hx⟩)
        refine ⟨fun j => if j = j₀ then Q else D j, ?_, ?_⟩
        · intro j hj
          rcases hj with hjj₀ | hj
          · rw [hjj₀]
            simp only [↓reduceIte]
            exact ⟨hQ_disc, hQ_Δ, hQ_K⟩
          · have hjj₀ : j ≠ j₀ := fun h => hj₀ (h ▸ hj)
            simp only [hjj₀, ↓reduceIte]
            exact ⟨(hD j hj).1, (hD j hj).2.1,
              fun k hk => (hD j hj).2.2 k fun hkF => hk (Or.inr hkF)⟩
        · intro i hi j hj hij
          by_cases hij₀ : i = j₀
          · have hjj₀ : j ≠ j₀ := by rw [← hij₀]; exact hij.symm
            simp only [hij₀, hjj₀, ↓reduceIte]
            exact hQ_D j (hj.resolve_left hjj₀)
          · by_cases hjj₀ : j = j₀
            · simp only [hij₀, hjj₀, ↓reduceIte]
              exact (hQ_D i (hi.resolve_left hij₀)).symm
            · simp only [hij₀, hjj₀, ↓reduceIte]
              exact hDD i (hi.resolve_left hij₀) j (hj.resolve_left hjj₀) hij
      · have hline_S : IsLineWithEnds (walkDrawing Γ (W j₀)).U (a j₀) (b j₀) :=
          walkDrawing_isLineWithEnds Γ (W j₀) (hWs j₀) hab₀
        have hline_Cap : IsLineWithEnds (K j₀) (cap.emb (a j₀)) (cap.emb (b j₀)) :=
          hline_S.map_of_embedding cap.isEmbedding
        obtain ⟨α, hα, hα_range, hα0, hα1⟩ := hline_Cap.exists_arc
        have hZs₀ : Zs j₀ = {α 0, α 1} := by
          dsimp only [Zs]
          rw [hBab j₀, image_pair, ← hα0, ← hα1]
        let B_forbid : Set Shat :=
          (⋃ i, Δ i) ∪ (⋃ j ∈ F, D j) ∪ (⋃ k ∈ (insert j₀ F)ᶜ, K k)
        have hB_closed : IsClosed B_forbid := by
          refine ((isClosed_iUnion_of_finite fun i => (hΔ i).isClosed).union
            (hF.isClosed_biUnion fun j hj => (hD j hj).1.isClosed)).union ?_
          exact (toFinite (insert j₀ F)ᶜ).isClosed_biUnion fun k _ => hK_closed k
        have hα0_Δ : α 0 ∈ ⋃ i, Δ i := by
          have : α 0 ∈ K j₀ ∩ (⋃ i, Δ i) := by rw [hK_inter_Δ j₀, hZs₀]; exact Or.inl rfl
          exact this.2
        have hα1_Δ : α 1 ∈ ⋃ i, Δ i := by
          have : α 1 ∈ K j₀ ∩ (⋃ i, Δ i) := by rw [hK_inter_Δ j₀, hZs₀]; exact Or.inr rfl
          exact this.2
        have hmeet : range α ∩ B_forbid ⊆ {α 0, α 1} := by
          rw [hα_range, ← hZs₀]
          rintro x ⟨hxK₀, (hxΔ | hxD) | hxK⟩
          · rw [← hK_inter_Δ j₀]
            exact ⟨hxK₀, hxΔ⟩
          · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hxD
            exact (disjoint_left.mp ((hD j hj).2.2 j₀ hj₀) hxj hxK₀).elim
          · obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hxK
            have hkj₀ : j₀ ≠ k := fun h => hk (by simp [h])
            exact (disjoint_left.mp (hK_disj j₀ k hkj₀) hxK₀ hxk).elim
        obtain ⟨Q, hQ_disc, hQ_B, hQ_bd, _⟩ :=
          exists_normal_arc_disc hcl_Shat hα hB_closed
            (Or.inl (Or.inl hα0_Δ)) (Or.inl (Or.inl hα1_Δ)) hmeet
        have hQ_Δ : Q ∩ (⋃ i, Δ i) = Zs j₀ := by
          rw [hZs₀]
          apply Subset.antisymm
          · rintro x ⟨hxQ, hxΔ⟩
            exact hQ_B.subset ⟨hxQ, Or.inl (Or.inl hxΔ)⟩
          · rintro x (rfl | rfl)
            · exact ⟨Surface.discBd_subset Q (hQ_bd (Or.inl rfl)), hα0_Δ⟩
            · exact ⟨Surface.discBd_subset Q (hQ_bd (Or.inr rfl)), hα1_Δ⟩
        have hQ_D : ∀ j ∈ F, Disjoint Q (D j) := by
          intro j hj
          rw [disjoint_left]
          intro x hxQ hxj
          have hx_ends : x ∈ Zs j₀ := by
            rw [hZs₀]
            exact hQ_B.subset ⟨hxQ, Or.inl (Or.inr (mem_iUnion₂.mpr ⟨j, hj, hxj⟩))⟩
          exact disjoint_left.mp ((hD j hj).2.2 j₀ hj₀) hxj (hZs_sub_K j₀ hx_ends)
        have hQ_K : ∀ k, k ∉ insert j₀ F → Disjoint Q (K k) := by
          intro k hk
          rw [disjoint_left]
          intro x hxQ hxk
          have hx_ends : x ∈ Zs j₀ := by
            rw [hZs₀]
            exact hQ_B.subset ⟨hxQ, Or.inr (mem_iUnion₂.mpr ⟨k, hk, hxk⟩)⟩
          have hkj₀ : j₀ ≠ k := fun h => hk (by simp [h])
          exact disjoint_left.mp (hK_disj j₀ k hkj₀) (hZs_sub_K j₀ hx_ends) hxk
        refine ⟨fun j => if j = j₀ then Q else D j, ?_, ?_⟩
        · intro j hj
          rcases hj with hjj₀ | hj
          · rw [hjj₀]
            simp only [↓reduceIte]
            exact ⟨hQ_disc, hQ_Δ, hQ_K⟩
          · have hjj₀ : j ≠ j₀ := fun h => hj₀ (h ▸ hj)
            simp only [hjj₀, ↓reduceIte]
            exact ⟨(hD j hj).1, (hD j hj).2.1,
              fun k hk => (hD j hj).2.2 k fun hkF => hk (Or.inr hkF)⟩
        · intro i hi j hj hij
          by_cases hij₀ : i = j₀
          · have hjj₀ : j ≠ j₀ := by rw [← hij₀]; exact hij.symm
            simp only [hij₀, hjj₀, ↓reduceIte]
            exact hQ_D j (hj.resolve_left hjj₀)
          · by_cases hjj₀ : j = j₀
            · simp only [hij₀, hjj₀, ↓reduceIte]
              exact (hQ_D i (hi.resolve_left hij₀)).symm
            · simp only [hij₀, hjj₀, ↓reduceIte]
              exact hDD i (hi.resolve_left hij₀) j (hj.resolve_left hjj₀) hij
  obtain ⟨D, hD, hDD⟩ := hex_discs univ (toFinite univ)
  exact ⟨D, fun j => (hD j (mem_univ j)).1,
    fun i j hij => hDD i (mem_univ i) j (mem_univ j) hij,
    fun j => (hD j (mem_univ j)).2.1⟩

/-! ## 3. Constructing a linkage avoiding `v` from connecting subdrawings -/

/-- Any subdrawing `P` of `Γ` satisfies `P.toHypergraph ≤ Γ.toHypergraph`. -/
lemma isSubdrawing_toHypergraph_le {Γ P : Surface.Drawing S} (hP : P.IsSubdrawing Γ) :
    P.toHypergraph ≤ Γ.toHypergraph where
  vertexSet_subset := hP.1
  edgeSet_subset := hP.2
  ends_eq e he := by
    have hcap := hP.closure_inter_V he
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq, Surface.Drawing.toHypergraph]
    constructor
    · rintro ⟨_, hxV, hxcl⟩
      have : x ∈ closure e ∩ P.V := by rw [hcap]; exact ⟨hxcl, hxV⟩
      exact ⟨he, this.2, this.1⟩
    · rintro ⟨_, hxV, hxcl⟩
      exact ⟨hP.2 he, hP.1 hxV, hxcl⟩

/-- If `P₁.IsSubdrawing P₂`, then `P₁.toHypergraph ≤ P₂.toHypergraph`. -/
lemma isSubdrawing_toHypergraph_mono {P₁ P₂ : Surface.Drawing S} (h : P₁.IsSubdrawing P₂) :
    P₁.toHypergraph ≤ P₂.toHypergraph :=
  isSubdrawing_toHypergraph_le h

/-- In a simple walk `W` of `Γ.toGraph`, every edge has `2` ends in `(walkDrawing Γ W).toHypergraph`,
every vertex can reach `b` in `(walkDrawing Γ W).toHypergraph.skeleton`, and the incident edges in
`(walkDrawing Γ W).toHypergraph` have cardinality `0` (if `a = b`), `1` at `a` and `b` (if `a ≠ b`),
and `2` at internal vertices. -/
lemma simple_walkDrawing_properties [T1Space S] (Γ : Surface.Drawing S) {a b : S}
    (W : GraphWalk Γ.toGraph a b) (hW : W.IsSimple) :
    let P := (walkDrawing Γ W).toHypergraph
    (∀ e ∈ P.edgeSet, (P.ends e).ncard = 2) ∧
    (∀ u ∈ P.vertexSet, P.skeleton.Reachable u b) ∧
    ((a = b ∧ P.vertexSet = {a} ∧ P.edgeSet = ∅ ∧ (incidentEdges P a).ncard = 0) ∨
     (a ≠ b ∧ (incidentEdges P a).ncard = 1 ∧ (incidentEdges P b).ncard = 1 ∧
      ∀ u ∈ P.vertexSet, u ≠ a → u ≠ b → (incidentEdges P u).ncard = 2)) := by
  have hinc_iff : ∀ {x y : S} (R : GraphWalk Γ.toGraph x y) {u : S} (hu : u ∈ R.support) (e : Set S),
      e ∈ incidentEdges (walkDrawing Γ R).toHypergraph u ↔ e ∈ R.edges ∧ u ∈ closure e := by
    intro x y R u hu e
    have huV : u ∈ (walkDrawing Γ R).V := by rw [walkDrawing_V]; exact hu
    simp only [incidentEdges, mem_ofPred_eq, Surface.Drawing.toHypergraph, walkDrawing_E]
    exact ⟨fun ⟨he, _, _, hucl⟩ => ⟨he, hucl⟩, fun ⟨he, hucl⟩ => ⟨he, he, huV, hucl⟩⟩
  induction W with
  | @nil v₀ ha =>
    dsimp only
    have hV : (walkDrawing Γ (.nil ha)).toHypergraph.vertexSet = {v₀} := by
      change (walkDrawing Γ (.nil ha)).V = {v₀}
      rw [walkDrawing_V]
      ext x
      simp [GraphWalk.support_nil]
    have hE : (walkDrawing Γ (.nil ha)).toHypergraph.edgeSet = ∅ := by
      change (walkDrawing Γ (.nil ha)).E = ∅
      rw [walkDrawing_E]
      ext e
      simp [GraphWalk.edges_nil]
    refine ⟨?_, ?_, Or.inl ⟨rfl, hV, hE, ?_⟩⟩
    · intro e he
      rw [hE] at he
      exact he.elim
    · intro u hu
      rw [hV, mem_singleton_iff] at hu
      subst hu
      exact SimpleGraph.Reachable.refl u
    · have hemp : incidentEdges (walkDrawing Γ (.nil ha)).toHypergraph v₀ = ∅ := by
        ext e
        simp only [incidentEdges, mem_ofPred_eq, hE, mem_empty_iff_false, false_and]
      rw [hemp, ncard_empty]
  | @cons a c b e₀ hl r ih =>
    have hnd : a ∉ r.support ∧ r.IsSimple := List.nodup_cons.mp hW
    have hac : a ≠ c := fun h => hnd.1 (h ▸ r.start_mem_support)
    have hab : a ≠ b := fun h => hnd.1 (h ▸ r.end_mem_support)
    have he₀_not_r : e₀ ∉ r.edges := fun he₀r =>
      hnd.1 (r.left_mem_support_of_mem_edges he₀r hl)
    obtain ⟨hends_r, hreach_r, hdeg_r⟩ := ih hnd.2
    let P := (walkDrawing Γ (.cons hl r)).toHypergraph
    let Pr := (walkDrawing Γ r).toHypergraph
    have hPr_le : Pr ≤ P := by
      apply isSubdrawing_toHypergraph_mono
      refine ⟨?_, ?_⟩
      · rw [walkDrawing_V, walkDrawing_V]
        intro x hx
        exact List.mem_cons_of_mem a hx
      · rw [walkDrawing_E, walkDrawing_E]
        intro e he
        exact List.mem_cons_of_mem e₀ he
    have hP_le_Γ : P ≤ Γ.toHypergraph :=
      isSubdrawing_toHypergraph_le (walkDrawing_isSubdrawing Γ (.cons hl r))
    have hends_e₀ : P.ends e₀ = {a, c} := by
      have he₀P : e₀ ∈ P.edgeSet := by
        change e₀ ∈ (walkDrawing Γ (.cons hl r)).E
        rw [walkDrawing_E]
        exact List.mem_cons_self
      rw [← hP_le_Γ.ends_eq e₀ he₀P]
      ext x
      simp only [Hypergraph.ends, mem_ofPred_eq, Surface.Drawing.toHypergraph]
      rw [← hl.2.2.2]
      exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨hl.1, h.2, h.1⟩⟩
    have ha_cl : a ∈ closure e₀ := by
      have : a ∈ closure e₀ ∩ Γ.V := by rw [hl.2.2.2]; exact Or.inl rfl
      exact this.1
    have hc_cl : c ∈ closure e₀ := by
      have : c ∈ closure e₀ ∩ Γ.V := by rw [hl.2.2.2]; exact Or.inr rfl
      exact this.1
    have hinc_a : incidentEdges P a = {e₀} := by
      ext e
      rw [hinc_iff (.cons hl r) (GraphWalk.start_mem_support _) e]
      simp only [GraphWalk.edges_cons, List.mem_cons, mem_singleton_iff]
      refine ⟨?_, fun h => ⟨Or.inl h, h ▸ ha_cl⟩⟩
      rintro ⟨rfl | her, hacl⟩
      · rfl
      · exfalso
        exact hnd.1 (GraphMinor.GM11.mem_support_of_mem_edges r her hacl hl.2.1)
    have hinc_c : incidentEdges P c = insert e₀ (incidentEdges Pr c) := by
      ext e
      rw [hinc_iff (.cons hl r) (List.mem_cons_of_mem a r.start_mem_support) e,
        mem_insert_iff, hinc_iff r r.start_mem_support e]
      simp only [GraphWalk.edges_cons, List.mem_cons]
      constructor
      · rintro ⟨rfl | her, hcl⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨her, hcl⟩
      · rintro (rfl | ⟨her, hcl⟩)
        · exact ⟨Or.inl rfl, hc_cl⟩
        · exact ⟨Or.inr her, hcl⟩
    have hinc_other : ∀ u ∈ r.support, u ≠ c → incidentEdges P u = incidentEdges Pr u := by
      intro u hur huc
      have hua : u ≠ a := fun h => hnd.1 (h ▸ hur)
      have hu_not_e₀ : u ∉ closure e₀ := by
        intro hucl
        have huV : u ∈ Γ.V := r.mem_vertexSet_of_mem_support hur
        have : u ∈ closure e₀ ∩ Γ.V := ⟨hucl, huV⟩
        rw [hl.2.2.2] at this
        rcases this with rfl | rfl
        · exact hua rfl
        · exact huc rfl
      ext e
      rw [hinc_iff (.cons hl r) (List.mem_cons_of_mem a hur) e, hinc_iff r hur e]
      simp only [GraphWalk.edges_cons, List.mem_cons]
      refine ⟨fun ⟨h, hcl⟩ => ⟨h.resolve_left fun he => hu_not_e₀ (he ▸ hcl), hcl⟩,
        fun ⟨her, hcl⟩ => ⟨Or.inr her, hcl⟩⟩
    refine ⟨?_, ?_, Or.inr ⟨hab, ?_, ?_, ?_⟩⟩
    · intro e heP
      change e ∈ (walkDrawing Γ (.cons hl r)).E at heP
      rw [walkDrawing_E, mem_ofPred_eq, GraphWalk.edges_cons, List.mem_cons] at heP
      rcases heP with rfl | her
      · rw [hends_e₀, ncard_pair hac]
      · have her' : e ∈ Pr.edgeSet := by
          change e ∈ (walkDrawing Γ r).E
          rw [walkDrawing_E]; exact her
        change (P.ends e).ncard = 2
        rw [hPr_le.ends_eq e her']
        exact hends_r e her'
    · intro u huP
      change u ∈ (walkDrawing Γ (.cons hl r)).V at huP
      rw [walkDrawing_V, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons] at huP
      rcases huP with hua_eq | hur
      · rw [hua_eq]
        have hadj_ac : P.skeleton.Adj a c := by
          refine ⟨hac, e₀, ?_, ?_⟩
          · change e₀ ∈ (walkDrawing Γ (.cons hl r)).E ∧ a ∈ (walkDrawing Γ (.cons hl r)).V ∧ a ∈ closure e₀
            rw [walkDrawing_E, walkDrawing_V]
            exact ⟨List.mem_cons_self, List.mem_cons_self, ha_cl⟩
          · change e₀ ∈ (walkDrawing Γ (.cons hl r)).E ∧ c ∈ (walkDrawing Γ (.cons hl r)).V ∧ c ∈ closure e₀
            rw [walkDrawing_E, walkDrawing_V]
            exact ⟨List.mem_cons_self, List.mem_cons_of_mem a r.start_mem_support, hc_cl⟩
        have hcPr : c ∈ Pr.vertexSet := by
          change c ∈ (walkDrawing Γ r).V
          rw [walkDrawing_V]; exact r.start_mem_support
        exact hadj_ac.reachable.trans (reachable_of_le hPr_le (hreach_r c hcPr))
      · have huPr : u ∈ Pr.vertexSet := by
          change u ∈ (walkDrawing Γ r).V
          rw [walkDrawing_V]; exact hur
        exact reachable_of_le hPr_le (hreach_r u huPr)
    · rw [hinc_a, ncard_singleton]
    · rcases hdeg_r with ⟨rfl, _, hEr, _⟩ | ⟨hcb, hc1, hb1, _⟩
      · have hemp_c : incidentEdges Pr c = ∅ := by
          have hEr' : Pr.edgeSet = ∅ := hEr
          ext e
          simp only [incidentEdges, mem_ofPred_eq, hEr', mem_empty_iff_false, false_and]
        rw [hinc_c, hemp_c, insert_empty_eq, ncard_singleton]
      · rw [hinc_other b r.end_mem_support hcb.symm]
        exact hb1
    · intro u huP hua hub
      change u ∈ (walkDrawing Γ (.cons hl r)).V at huP
      rw [walkDrawing_V, mem_ofPred_eq, GraphWalk.support_cons, List.mem_cons] at huP
      have hur : u ∈ r.support := huP.resolve_left hua
      rcases hdeg_r with ⟨rfl, hVr, _, _⟩ | ⟨hcb, hc1, hb1, hother_r⟩
      · exfalso
        have huPr : u ∈ Pr.vertexSet := by
          change u ∈ (walkDrawing Γ r).V
          rw [walkDrawing_V]; exact hur
        rw [hVr, mem_singleton_iff] at huPr
        exact hub huPr
      · by_cases huc : u = c
        · subst huc
          have he₀_not_inc : e₀ ∉ incidentEdges Pr u := by
            intro h
            have he₀r : e₀ ∈ r.edges := by
              have h1 : e₀ ∈ (walkDrawing Γ r).E := h.1
              rwa [walkDrawing_E] at h1
            exact he₀_not_r he₀r
          rw [hinc_c, ncard_insert_of_notMem he₀_not_inc
            (Pr.edgeSet_finite.subset fun _ h => h.1), hc1]
        · rw [hinc_other u hur huc]
          have huPr : u ∈ Pr.vertexSet := by
            change u ∈ (walkDrawing Γ r).V
            rw [walkDrawing_V]; exact hur
          exact hother_r u huPr huc hub

/-- Every link in `Γ' = deleteVertices (capDrawing hS cap Γ) {cap.emb v}` comes from a link in `Γ`. -/
lemma isLink_pullback_of_deleteVertices_capDrawing [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Surface.Drawing S) (v : S)
    {e' : Set Shat} {x' y' : Shat}
    (hl' : (GM12.deleteVertices (capDrawing hS cap Γ) {cap.emb v}).toGraph.IsLink e' x' y') :
    ∃ (e : Set S) (x y : S),
      cap.emb x = x' ∧ cap.emb y = y' ∧ x ≠ v ∧ y ≠ v ∧
      Γ.toGraph.IsLink e x y := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hclosed_emb : IsClosedMap cap.emb := cap.isEmbedding.continuous.isClosedMap
  let Γ_hat := capDrawing hS cap Γ
  let Γ' := GM12.deleteVertices Γ_hat {cap.emb v}
  have hsub : Γ'.IsSubdrawing Γ_hat := deleteVertices_isSubdrawing Γ_hat {cap.emb v}
  have hl_hat : Γ_hat.toGraph.IsLink e' x' y' := (hsub.isLink_iff hl'.1).mp hl'
  have hx' : x' ∈ Γ'.V := hl'.2.1
  have hy' : y' ∈ Γ'.V := hl'.2.2.1
  rw [deleteVertices_V, capDrawing_V] at hx' hy'
  rcases hx' with ⟨⟨x, hxV, rfl⟩, hxv'⟩
  rcases hy' with ⟨⟨y, hyV, rfl⟩, hyv'⟩
  have hxv : x ≠ v := fun h => hxv' (congrArg cap.emb h)
  have hyv : y ≠ v := fun h => hyv' (congrArg cap.emb h)
  have he'_hat : e' ∈ Γ_hat.E := hl_hat.1
  rw [capDrawing_E] at he'_hat
  rcases he'_hat with ⟨e, heΓ, rfl⟩
  refine ⟨e, x, y, rfl, rfl, hxv, hyv, heΓ, hxV, hyV, ?_⟩
  have hcap := hl_hat.2.2.2
  rw [capDrawing_V, hclosed_emb.closure_image_eq_of_continuous cap.isEmbedding.continuous e,
    ← image_inter cap.isEmbedding.injective] at hcap
  have hpair : cap.emb '' (closure e ∩ Γ.V) = cap.emb '' ({x, y} : Set S) := by
    rw [hcap, image_pair]
  exact image_injective.mpr cap.isEmbedding.injective hpair

/-- Any walk in `Γ' = deleteVertices (capDrawing hS cap Γ) {cap.emb v}` between `cap.emb a` and
`cap.emb b` (`a, b ∈ Γ.V`) pulls back to a walk in `Γ.toGraph` from `a` to `b` whose vertex
support maps into the vertex support of the walk in `Γ'`. -/
lemma exists_graphWalk_pullback_of_deleteVertices_capDrawing [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) (Γ : Surface.Drawing S) (v : S)
    {x' y' : Shat}
    (W' : GraphWalk (GM12.deleteVertices (capDrawing hS cap Γ) {cap.emb v}).toGraph x' y')
    {a b : S} (ha : a ∈ Γ.V) (hb : b ∈ Γ.V) (ha' : cap.emb a = x') (hb' : cap.emb b = y') :
    ∃ W : GraphWalk Γ.toGraph a b,
      ∀ u ∈ W.support, cap.emb u ∈ W'.support := by
  induction W' generalizing a b with
  | nil h =>
    have hab : a = b := cap.isEmbedding.injective (ha'.trans hb'.symm)
    subst hab
    refine ⟨.nil ha, ?_⟩
    intro u hu
    rcases List.mem_singleton.mp hu with rfl
    rw [ha']
    exact List.mem_cons_self
  | @cons u' w' z' e' hl' r' ih =>
    obtain ⟨e, x, y, hx', hy', _, _, hl⟩ :=
      isLink_pullback_of_deleteVertices_capDrawing hS cap Γ v hl'
    have hax : a = x := cap.isEmbedding.injective (ha'.trans hx'.symm)
    subst hax
    obtain ⟨W₁, hW₁⟩ := ih hl.2.2.1 hb hy' hb'
    refine ⟨.cons hl W₁, ?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu
    · rw [hx']
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hW₁ u hu)

/-- If `Γ' = deleteVertices (capDrawing hS cap Γ) {cap.emb v}` (`v ∈ Γ.V`) satisfies
`HasConnectingSubdrawings Γ' (cap.emb '' (Γ.V ∩ bd S)) (fun j => cap.emb '' B j)` for the blocks
`B j` of `linkagePattern L`, then there is a linkage `L'` in `Γ.toHypergraph` with
`v ∉ L'.vertexSet` and `linkagePattern L' = linkagePattern L`. -/
theorem exists_linkage_avoiding_vertex_of_connectingSubdrawings [T2Space Shat]
    (hS : IsSurface S) (cap : IsCappedSurface S Shat) {Γ : Surface.Drawing S} {v : S}
    {L : Hypergraph S (Set S)} (hL : IsLinkage Γ.toHypergraph L)
    {n : ℕ} (B : Fin n ≃ linkagePattern L)
    (hconn : HasConnectingSubdrawings (GM12.deleteVertices (capDrawing hS cap Γ) {cap.emb v})
      (cap.emb '' (Γ.V ∩ bd S)) (fun j => cap.emb '' (B j).val)) :
    ∃ L' : Hypergraph S (Set S),
      IsLinkage Γ.toHypergraph L' ∧
      v ∉ L'.vertexSet ∧
      linkagePattern L' = linkagePattern L := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  classical
  let Γ_hat := capDrawing hS cap Γ
  let Γ' := GM12.deleteVertices Γ_hat {cap.emb v}
  let Z := cap.emb '' (Γ.V ∩ bd S)
  rcases hconn with ⟨H, hH_sub, hH_conn, hH_disj, hH_Z⟩
  have hex_walk : ∀ j : Fin n, ∃ (a b : S) (W : GraphWalk Γ.toGraph a b),
      a ∈ terminals L ∧ b ∈ terminals L ∧
      (B j).val = {a, b} ∧
      W.IsSimple ∧
      (∀ u ∈ W.support, cap.emb u ∈ (H j).V) := by
    intro j
    have hBj : (B j).val ∈ linkagePattern L := (B j).property
    have hEnds : ∃ a ∈ terminals L, ∃ b ∈ terminals L, (B j).val = {a, b} := by
      rcases hL.mem_linkagePattern_structure hBj with
        ⟨a, ha, hBa, _⟩ | ⟨a, ha, b, hb, _, hBab, _, _⟩
      · exact ⟨a, ha, a, ha, by rw [hBa, pair_eq_singleton]⟩
      · exact ⟨a, ha, b, hb, hBab⟩
    rcases hEnds with ⟨a, ha, b, hb, hBab⟩
    have haΓ : a ∈ Γ.V := hL.1.vertexSet_subset ha.1
    have hbΓ : b ∈ Γ.V := hL.1.vertexSet_subset hb.1
    have haHj : cap.emb a ∈ (H j).V := by
      have : cap.emb a ∈ (H j).V ∩ Z := by
        rw [hH_Z j]
        exact mem_image_of_mem _ (by rw [hBab]; exact Or.inl rfl)
      exact this.1
    have hbHj : cap.emb b ∈ (H j).V := by
      have : cap.emb b ∈ (H j).V ∩ Z := by
        rw [hH_Z j]
        exact mem_image_of_mem _ (by rw [hBab]; exact Or.inr rfl)
      exact this.1
    obtain ⟨W_H⟩ := hH_conn j (cap.emb a) haHj (cap.emb b) hbHj
    obtain ⟨W_Γ', hs_Γ', _⟩ := (hH_sub j).exists_walk_up W_H
    obtain ⟨W₀, hW₀⟩ :=
      exists_graphWalk_pullback_of_deleteVertices_capDrawing hS cap Γ v W_Γ' haΓ hbΓ rfl rfl
    obtain ⟨W, hWs, hsW, _⟩ := GraphMinor.GM11.GraphWalk.exists_isSimple W₀
    refine ⟨a, b, W, ha, hb, hBab, hWs, ?_⟩
    intro u hu
    have hu' : cap.emb u ∈ W_Γ'.support := hW₀ u (hsW u hu)
    rw [hs_Γ'] at hu'
    exact W_H.mem_vertexSet_of_mem_support hu'
  choose a b W ha_term hb_term hBab hWs hW_Hj using hex_walk
  let P : Fin n → Hypergraph S (Set S) := fun j => (walkDrawing Γ (W j)).toHypergraph
  have hP_props : ∀ j,
      (∀ e ∈ (P j).edgeSet, ((P j).ends e).ncard = 2) ∧
      (∀ u ∈ (P j).vertexSet, (P j).skeleton.Reachable u (b j)) ∧
      ((a j = b j ∧ (P j).vertexSet = {a j} ∧ (P j).edgeSet = ∅ ∧ (incidentEdges (P j) (a j)).ncard = 0) ∨
       (a j ≠ b j ∧ (incidentEdges (P j) (a j)).ncard = 1 ∧ (incidentEdges (P j) (b j)).ncard = 1 ∧
        ∀ u ∈ (P j).vertexSet, u ≠ a j → u ≠ b j → (incidentEdges (P j) u).ncard = 2)) :=
    fun j => simple_walkDrawing_properties Γ (W j) (hWs j)
  have hP_disj : ∀ i j, i ≠ j → Disjoint (P i).vertexSet (P j).vertexSet := by
    intro i j hij
    rw [disjoint_left]
    intro u hui huj
    change u ∈ (walkDrawing Γ (W i)).V at hui
    change u ∈ (walkDrawing Γ (W j)).V at huj
    rw [walkDrawing_V] at hui huj
    exact disjoint_left.mp (hH_disj i j hij) (hW_Hj i u hui) (hW_Hj j u huj)
  have hP_le_Γ : ∀ j, P j ≤ Γ.toHypergraph :=
    fun j => isSubdrawing_toHypergraph_le (walkDrawing_isSubdrawing Γ (W j))
  let D' : Surface.Drawing S := Γ.span (⋃ j, (walkDrawing Γ (W j)).V) (⋃ j, (walkDrawing Γ (W j)).E)
  let L' : Hypergraph S (Set S) := D'.toHypergraph
  have hD'_sub_Γ : D'.IsSubdrawing Γ := Surface.Drawing.span_isSubdrawing Γ _ _
  have hL'_le_Γ : L' ≤ Γ.toHypergraph := isSubdrawing_toHypergraph_le hD'_sub_Γ
  have hD'_E : D'.E = ⋃ j, (walkDrawing Γ (W j)).E := by
    dsimp only [D']
    rw [Γ.span_E, inter_eq_left]
    refine iUnion_subset fun j => (walkDrawing_isSubdrawing Γ (W j)).2
  have hD'_V : D'.V = ⋃ j, (walkDrawing Γ (W j)).V := by
    apply Subset.antisymm
    · rintro x (⟨hx, _⟩ | hx)
      · exact hx
      · obtain ⟨e, ⟨he, _⟩, hxe, hxV⟩ := mem_iUnion₂.mp hx
        obtain ⟨j, hej⟩ := mem_iUnion.mp he
        rw [walkDrawing_E] at hej
        exact mem_iUnion.mpr ⟨j, by rw [walkDrawing_V]; exact GraphMinor.GM11.mem_support_of_mem_edges (W j) hej hxe hxV⟩
    · intro x hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      exact Or.inl ⟨hx, (walkDrawing_isSubdrawing Γ (W j)).1 hxj⟩
  have hPj_le_L' : ∀ j, P j ≤ L' := by
    intro j
    apply isSubdrawing_toHypergraph_mono
    refine ⟨?_, ?_⟩
    · rw [hD'_V]
      exact subset_iUnion (fun j => (walkDrawing Γ (W j)).V) j
    · rw [hD'_E]
      exact subset_iUnion (fun j => (walkDrawing Γ (W j)).E) j
  have hinc_L'_eq : ∀ j, ∀ u ∈ (P j).vertexSet, incidentEdges L' u = incidentEdges (P j) u := by
    intro j u hu
    apply Subset.antisymm
    · rintro e ⟨heL', hincL'⟩
      change e ∈ D'.E at heL'
      rw [hD'_E] at heL'
      obtain ⟨i, hei⟩ := mem_iUnion.mp heL'
      have hei_Pi : e ∈ (P i).edgeSet := hei
      have hinc_Γ : Γ.toHypergraph.Inc e u := Hypergraph.inc_of_le hL'_le_Γ hincL'
      have hinc_Pi : (P i).Inc e u := by
        have : u ∈ (P i).ends e := by
          rw [← (hP_le_Γ i).ends_eq e hei_Pi]
          exact hinc_Γ
        exact this
      have hu_Pi : u ∈ (P i).vertexSet := (P i).vertex_mem_of_inc hinc_Pi
      have hij : i = j := by
        by_contra hne
        exact disjoint_left.mp (hP_disj i j hne) hu_Pi hu
      subst hij
      exact ⟨hei_Pi, hinc_Pi⟩
    · exact incidentEdges_subset_of_le (hPj_le_L' j) u
  have hL'_isLinkage : IsLinkage Γ.toHypergraph L' := by
    apply isLinkage_of_deg_le_two_of_reachable_deg_le_one hL'_le_Γ
    · intro e heL'
      change e ∈ D'.E at heL'
      rw [hD'_E] at heL'
      obtain ⟨j, hej⟩ := mem_iUnion.mp heL'
      have hej' : e ∈ (P j).edgeSet := hej
      rw [(hPj_le_L' j).ends_eq e hej']
      exact (hP_props j).1 e hej'
    · intro u huL'
      change u ∈ D'.V at huL'
      rw [hD'_V] at huL'
      obtain ⟨j, huj⟩ := mem_iUnion.mp huL'
      have huj' : u ∈ (P j).vertexSet := huj
      rw [hinc_L'_eq j u huj']
      rcases (hP_props j).2.2 with ⟨_, hVj, _, ha0⟩ | ⟨_, ha1, hb1, hother⟩
      · have : u = a j := by rwa [hVj, mem_singleton_iff] at huj'
        subst this; omega
      · by_cases hua : u = a j
        · subst hua; omega
        · by_cases hub : u = b j
          · subst hub; omega
          · have := hother u huj' hua hub; omega
    · intro u huL'
      change u ∈ D'.V at huL'
      rw [hD'_V] at huL'
      obtain ⟨j, huj⟩ := mem_iUnion.mp huL'
      have huj' : u ∈ (P j).vertexSet := huj
      have hbj_Pj : b j ∈ (P j).vertexSet := by
        change b j ∈ (walkDrawing Γ (W j)).V
        rw [walkDrawing_V]; exact (W j).end_mem_support
      have hbj_L' : b j ∈ L'.vertexSet := (hPj_le_L' j).vertexSet_subset hbj_Pj
      refine ⟨b j, hbj_L', reachable_of_le (hPj_le_L' j) ((hP_props j).2.1 u huj'), ?_⟩
      rw [hinc_L'_eq j (b j) hbj_Pj]
      rcases (hP_props j).2.2 with ⟨hab, _, _, ha0⟩ | ⟨_, _, hb1, _⟩
      · rw [← hab, ha0]; exact Nat.zero_le 1
      · rw [hb1]
  have hv_not_L' : v ∉ L'.vertexSet := by
    intro hvL'
    change v ∈ D'.V at hvL'
    rw [hD'_V] at hvL'
    obtain ⟨j, hvj⟩ := mem_iUnion.mp hvL'
    rw [walkDrawing_V] at hvj
    have hv_Hj : cap.emb v ∈ (H j).V := hW_Hj j v hvj
    have hv_Γ' : cap.emb v ∈ Γ'.V := (hH_sub j).1 hv_Hj
    rw [deleteVertices_V] at hv_Γ'
    exact hv_Γ'.2 rfl
  have hterm_L' : terminals L' = terminals L := by
    apply Subset.antisymm
    · intro u hu
      have huL' : u ∈ L'.vertexSet := hu.1
      have hdeg : (incidentEdges L' u).ncard ≤ 1 := by
        have := hu.2
        rwa [hL'_isLinkage.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl u] at this
      change u ∈ D'.V at huL'
      rw [hD'_V] at huL'
      obtain ⟨j, huj⟩ := mem_iUnion.mp huL'
      have huj' : u ∈ (P j).vertexSet := huj
      rw [hinc_L'_eq j u huj'] at hdeg
      rcases (hP_props j).2.2 with ⟨_, hVj, _, _⟩ | ⟨_, _, _, hother⟩
      · have : u = a j := by rwa [hVj, mem_singleton_iff] at huj'
        subst this; exact ha_term j
      · by_cases hua : u = a j
        · subst hua; exact ha_term j
        · by_cases hub : u = b j
          · subst hub; exact hb_term j
          · have h2 := hother u huj' hua hub
            omega
    · intro u hu
      rw [hL.terminals_eq_sUnion_linkagePattern] at hu
      rcases hu with ⟨B₀, hB₀, huB₀⟩
      let j := B.symm ⟨B₀, hB₀⟩
      have hj : (B j).val = B₀ := congrArg Subtype.val (B.apply_symm_apply ⟨B₀, hB₀⟩)
      rw [← hj, hBab j] at huB₀
      have haj_Pj : a j ∈ (P j).vertexSet := by
        change a j ∈ (walkDrawing Γ (W j)).V
        rw [walkDrawing_V]; exact (W j).start_mem_support
      have hbj_Pj : b j ∈ (P j).vertexSet := by
        change b j ∈ (walkDrawing Γ (W j)).V
        rw [walkDrawing_V]; exact (W j).end_mem_support
      rcases huB₀ with rfl | rfl
      · refine ⟨(hPj_le_L' j).vertexSet_subset haj_Pj, ?_⟩
        rw [hL'_isLinkage.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl (a j),
          hinc_L'_eq j (a j) haj_Pj]
        rcases (hP_props j).2.2 with ⟨_, _, _, ha0⟩ | ⟨_, ha1, _, _⟩
        · omega
        · omega
      · refine ⟨(hPj_le_L' j).vertexSet_subset hbj_Pj, ?_⟩
        rw [hL'_isLinkage.vertexDegree_eq_ncard_incidentEdges_of_le le_rfl (b j),
          hinc_L'_eq j (b j) hbj_Pj]
        rcases (hP_props j).2.2 with ⟨hab, _, _, ha0⟩ | ⟨_, _, hb1, _⟩
        · rw [← hab]; omega
        · omega
  have hpat_sub : linkagePattern L ⊆ linkagePattern L' := by
    intro B₀ hB₀
    let j := B.symm ⟨B₀, hB₀⟩
    have hj : (B j).val = B₀ := congrArg Subtype.val (B.apply_symm_apply ⟨B₀, hB₀⟩)
    rw [← hj, hBab j]
    have haj_Pj : a j ∈ (P j).vertexSet := by
      change a j ∈ (walkDrawing Γ (W j)).V
      rw [walkDrawing_V]; exact (W j).start_mem_support
    have haj_L' : a j ∈ L'.vertexSet := (hPj_le_L' j).vertexSet_subset haj_Pj
    rcases (hP_props j).2.2 with ⟨hab, _, _, ha0⟩ | ⟨hab, _, _, _⟩
    · rw [hab, pair_eq_singleton]
      rw [← hL'_isLinkage.ncard_incidentEdges_eq_zero_iff (hab ▸ haj_L'),
        ← hab, hinc_L'_eq j (a j) haj_Pj]
      exact ha0
    · have haj_term' : a j ∈ terminals L' := by rw [hterm_L']; exact ha_term j
      have hbj_term' : b j ∈ terminals L' := by rw [hterm_L']; exact hb_term j
      rw [hL'_isLinkage.pair_mem_linkagePattern_iff haj_term' hbj_term' hab]
      exact reachable_of_le (hPj_le_L' j) ((hP_props j).2.1 (a j) haj_Pj)
  have hpat_eq : linkagePattern L' = linkagePattern L :=
    (linkagePattern_eq_of_subset hL hL'_isLinkage hterm_L'.le hpat_sub).symm
  exact ⟨L', hL'_isLinkage, hv_not_L', hpat_eq⟩

end GM21
end GraphMinor
