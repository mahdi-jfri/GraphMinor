module

public import GraphMinor.GM21.Section6RestrictPres
public import GraphMinor.GM21.Section2
import GraphMinor.GM21.Section6Angles
import GraphMinor.GM17.CuffOrder
import GraphMinor.GM10.TangleLemmas

/-!
# Graph Minors XXI, Section 6: the linkage on one side of a line

Let `Σ₁` be a side of a proper line `F` with ends `a, b` (`IsSideOfLine`), and let
`G₁ = (Γ ∩ Σ₁) ∪ μ(bd(Σ) ∩ Σ₁)` be the graph of `Σ₁` (`sideGraph`). The proofs of (6.5), (6.6),
(6.7) and of claim (4) of (6.3) in *Graph Minors XXI* (pages 25–29 of the preprint) each say,
without proof, that if `L` is an exhaustive vital `p`-linkage in `G` then `L ∩ G₁` is an exhaustive
vital `(p + 2q)`-linkage in `G₁`. This file proves it (`isExhaustiveLinkage_side`).

The proof finds a separation `(A, G₁)` of `G` with `V(A ∩ G₁) = V(μ(a)) ∪ V(μ(b))`
(`isSeparation_side`), and then applies (2.2) and (2.3). The separation comes from
`isSeparation_subOn`: we must show that an edge of `G` outside `G₁` has no end in `G₁` other than
the vertices of `μ(a)` and `μ(b)`. Such an edge is an edge of `Γ` on the other side, or an edge of
`μ(s)` for a space `s` on the other side. In the second case the only hard point is a vertex of
`μ(s) ∩ μ(F_j^* ∩ Σ₁)`, where `s ⊆ F_j^*`. Reading `F_j^*` as an interval of angles, `s` and
`F_j^* ∩ Σ₁` lie on the two sides of an end of `F_j^* ∩ Σ₁`, and this end is `a` or `b`
(`space_inter_supportGraph_side_subset`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface GraphMinor.GM21.Supports GraphMinor.GM17 GraphMinor.GM19
  Hypergraph

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S] [T2Space S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α} {ιE : Set S → β}
  {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {S₁ S₂ F : Set S} {a b : S}
  (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (h : IsSideOfLine Γ S₁ S₂ F a b)
include hP h

omit [T2Space S] hP in
/-- A point outside `S₁` lies in `S₂`. -/
private theorem mem_right_of_not_mem_K {x : S} (hx : x ∉ S₁) : x ∈ S₂ :=
  ((h.union_eq ▸ mem_univ x : x ∈ S₁ ∪ S₂)).resolve_left hx

/-- **The end of `F_j* ∩ S₁` next to a space on the other side.** Let `s ⊆ F_j*` be a space of
`Γ` that misses `S₁`, and let `F_j* ∩ S₁` be a support. Then a vertex of both `μ(s)` and
`μ(F_j* ∩ S₁)` is a vertex of `μ(a)` or of `μ(b)`. Reading `F_j*` as the angles `[t₀, t₁]`, the
support `F_j* ∩ S₁` is an interval `[c, d]` and `s` an interval `(α, β)` that misses it. Say
`β ≤ c`. The points at angles in `(α, c)` lie in `F_j*` but not in `F_j* ∩ S₁`, so they lie in
`S₂`. Since `S₂` is closed, the point at angle `c` lies in `S₂ ∩ S₁ = F`, so it is `a` or `b`.
Then `s` lies before the angle `c` and `F_j* ∩ S₁` after it, and the vertices common to `μ` of the
two parts are vertices of `μ` of the point at angle `c`
(`supportGraph_inter_vertexSet_subset_of_angle_between`). The case `d ≤ α` is the same. -/
theorem space_inter_supportGraph_side_subset (j : Fin r)
    (hK : IsSupportOfDrawing Γ (F_star j ∩ S₁)) {s : Set S} (hs : s ∈ drawingSpaces Γ)
    (hsF : s ⊆ F_star j) (hsS₁ : Disjoint s S₁) :
    (μ (.space s)).vertexSet ∩ (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ⊆
      (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet := by
  have hS := hP.is_surface
  have hge2 := hP.cuff_vertices_ge_two
  obtain ⟨e₀, e₁, hFe⟩ := hP.supports_isSupport j
  obtain ⟨C, hC, hFC⟩ := exists_cuff_of_supportHasEnds hFe
  set f := cuffHomeo hS hC
  obtain ⟨t₀, -, t₁, ⟨hle, hlt⟩, hends, hFeq, -⟩ := support_eq_cuffPoint_Icc hS hC f hFe hFC
  have hFends := ends_mem_of_supportHasEnds hFe
  have ht₀V : cuffPoint f t₀ ∈ Γ.V := by
    rcases hends with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hFends.2.2.1.1
    · exact hFends.2.2.2.1.1
  have ht₁V : cuffPoint f t₁ ∈ Γ.V := by
    rcases hends with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact hFends.2.2.2.1.1
    · exact hFends.2.2.1.1
  have ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C := ⟨ht₀V, cuffPoint_mem f t₀⟩
  obtain ⟨α₁, β₁, hα, hαβ, hβ, -, -, -, hseq, -⟩ :=
    space_in_support_eq_Ioo hS hge2 hC f hle hlt ht₀ hFeq hs hsF
  obtain ⟨k₀, k₁, hKe⟩ := hK
  obtain ⟨c, d, hc, hcd, hd, hcdends, hKeq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hFeq inter_subset_left hKe
  have hKends := ends_mem_of_supportHasEnds hKe
  have hcV : cuffPoint f c ∈ Γ.V := by
    rcases hcdends with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hKends.2.2.1.1
    · exact hKends.2.2.2.1.1
  have hdV : cuffPoint f d ∈ Γ.V := by
    rcases hcdends with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact hKends.2.2.2.1.1
    · exact hKends.2.2.1.1
  set D := Ico t₀ (t₀ + 2 * Real.pi)
  have hinj : InjOn (cuffPoint f) D := cuffPoint_injOn_Ico f t₀
  have hmemD : ∀ {t : ℝ}, t₀ ≤ t → t ≤ t₁ → t ∈ D := fun h1 h2 => ⟨h1, h2.trans_lt hlt⟩
  have hFt : ∀ {t : ℝ}, t₀ ≤ t → t ≤ t₁ → cuffPoint f t ∈ F_star j := fun h1 h2 => by
    rw [hFeq]; exact ⟨_, ⟨h1, h2⟩, rfl⟩
  -- A point of `F_j*` at an angle outside `[c, d]` lies in `S₂`.
  have hout : ∀ {t : ℝ}, t₀ ≤ t → t ≤ t₁ → t ∉ Icc c d → cuffPoint f t ∈ S₂ := by
    intro t h1 h2 htcd
    refine mem_right_of_not_mem_K h fun htS₁ => htcd ?_
    have hmem : cuffPoint f t ∈ F_star j ∩ S₁ := ⟨hFt h1 h2, htS₁⟩
    rw [hKeq] at hmem
    obtain ⟨t', ht', heq⟩ := hmem
    rw [← hinj (hmemD (hc.trans ht'.1) (ht'.2.trans hd)) (hmemD h1 h2) heq]
    exact ht'
  -- A point at an angle `γ ∈ [c, d]` that is a limit of angles outside `[c, d]` is `a` or `b`.
  have hend : ∀ {γ : ℝ} {X : Set ℝ}, γ ∈ Icc c d → γ ∈ closure X →
      (∀ t ∈ X, t₀ ≤ t ∧ t ≤ t₁ ∧ t ∉ Icc c d) → cuffPoint f γ ∈ Γ.V →
      (μ (.vertex (cuffPoint f γ))).vertexSet ⊆
        (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet := by
    intro γ X hγ hγX hX hγV
    have hγS₂ : cuffPoint f γ ∈ S₂ := by
      have himg : cuffPoint f '' X ⊆ S₂ := by
        rintro _ ⟨t, ht, rfl⟩
        exact hout (hX t ht).1 (hX t ht).2.1 (hX t ht).2.2
      exact closure_minimal himg h.isClosed_right
        (image_closure_subset_closure_image (cuffPoint_continuous f) ⟨γ, hγX, rfl⟩)
    have hγS₁ : cuffPoint f γ ∈ S₁ := by
      have hmem : cuffPoint f γ ∈ F_star j ∩ S₁ := by rw [hKeq]; exact ⟨γ, hγ, rfl⟩
      exact hmem.2
    have hγF : cuffPoint f γ ∈ F := h.inter_eq ▸ ⟨hγS₁, hγS₂⟩
    rcases h.mem_ends_of_mem_V hγF hγV with hγa | hγb
    · rw [hγa]; exact subset_union_left
    · rw [hγb]; exact subset_union_right
  have hsI : μ (.space s) ≤ supportGraph G Γ μ (cuffPoint f '' Icc α₁ β₁) :=
    μ_space_le_supportGraph_of_subset hP j (by rw [hFeq]; exact image_mono (Icc_subset_Icc hα hβ))
      hs (by rw [hseq]; exact image_mono Ioo_subset_Icc_self)
  -- The angles of `s` miss `[c, d]`.
  have hmiss : ∀ t ∈ Ioo α₁ β₁, t ∉ Icc c d := by
    intro t ht htcd
    have hts : cuffPoint f t ∈ s := by rw [hseq]; exact ⟨t, ht, rfl⟩
    have htK : cuffPoint f t ∈ F_star j ∩ S₁ := by rw [hKeq]; exact ⟨t, htcd, rfl⟩
    exact disjoint_left.mp hsS₁ hts htK.2
  have hcase : β₁ ≤ c ∨ d ≤ α₁ := by
    by_contra hne
    push Not at hne
    rcases hcd.lt_or_eq with hcd' | hcd'
    · have hm := hmiss ((max α₁ c + min β₁ d) / 2)
        ⟨by linarith [le_max_left α₁ c, lt_min hαβ hne.2, lt_min hne.1 hcd',
            max_lt (lt_min hαβ hne.2) (lt_min hne.1 hcd')],
          by linarith [min_le_left β₁ d, max_lt (lt_min hαβ hne.2) (lt_min hne.1 hcd')]⟩
      exact hm ⟨by linarith [le_max_right α₁ c, max_lt (lt_min hαβ hne.2) (lt_min hne.1 hcd')],
        by linarith [min_le_right β₁ d, max_lt (lt_min hαβ hne.2) (lt_min hne.1 hcd')]⟩
    · exact hmiss c ⟨by rw [hcd']; exact hne.2, hne.1⟩ ⟨le_rfl, hcd⟩
  rcases hcase with hβc | hdα
  · have hsub := supportGraph_inter_vertexSet_subset_of_angle_between hP j hC f ht₀ ht₁V hle hlt
      hFeq hα hαβ.le hβc le_rfl hcd hd rfl hKeq hcV
    have hcl : c ∈ closure (Ioo α₁ c) := by
      rw [closure_Ioo (hαβ.trans_le hβc).ne]; exact ⟨(hαβ.trans_le hβc).le, le_rfl⟩
    refine fun x hx => hend ⟨le_rfl, hcd⟩ hcl ?_ hcV (hsub ⟨hsI.vertexSet_subset hx.1, hx.2⟩)
    intro t ht
    exact ⟨hα.trans ht.1.le, ht.2.le.trans (hcd.trans hd), fun htcd => (ht.2.trans_le htcd.1).false⟩
  · have hsub := supportGraph_inter_vertexSet_subset_of_angle_between hP j hC f ht₀ ht₁V hle hlt
      hFeq hc hcd le_rfl hdα hαβ.le hβ hKeq rfl hdV
    have hcl : d ∈ closure (Ioo d β₁) := by
      rw [closure_Ioo (hdα.trans_lt hαβ).ne]; exact ⟨le_rfl, (hdα.trans_lt hαβ).le⟩
    refine fun x hx => hend ⟨hcd, le_rfl⟩ hcl ?_ hdV (hsub ⟨hx.2, hsI.vertexSet_subset hx.1⟩)
    intro t ht
    exact ⟨(hc.trans hcd).trans ht.1.le, ht.2.le.trans hβ, fun htcd => (ht.1.trans_le htcd.2).false⟩

omit [T2Space S] in
/-- The ends `a, b` of `F` lie in `S₁` and in some supports, so `μ(a)` and `μ(b)` lie in
`μ(F_j* ∩ S₁)` for some `j`. -/
theorem vertexSet_μ_end_subset {u : S} (hu : u = a ∨ u = b) :
    ∃ j, (μ (.vertex u)).vertexSet ⊆ (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ∧
      u ∈ Γ.V ∩ F_star j := by
  have huV : u ∈ Γ.V := by rcases hu with rfl | rfl; exacts [h.left_mem, h.right_mem]
  have huF : u ∈ F := by
    rcases hu with rfl | rfl; exacts [h.proper.1.left_mem, h.proper.1.right_mem]
  obtain ⟨j, hj⟩ := mem_iUnion.mp (hP.bd_vertices_covered ⟨huV, h.mem_bd_of_mem_V huF huV⟩)
  exact ⟨j, (μ_vertex_le_supportGraph_of_subset hP j inter_subset_left
    ⟨huV, hj, h.line_subset_left huF⟩).vertexSet_subset, huV, hj⟩

/-- **The separation `(A, G₁)`** (Graph Minors XXI, proofs of (6.5)–(6.7) and of claim (4) of
(6.3)). If, for every space `s ⊆ F_j*` that misses `S₁`, the graphs `μ(s)` and `μ(F_j* ∩ S₁)` share
only vertices of `μ(a)` and `μ(b)` (`hspace`; this holds when every nonempty `F_j* ∩ S₁` is a
support, `space_inter_supportGraph_side_subset`), then `G` has a separation `(A, G₁)` with
`V(A ∩ G₁) = V(μ(a)) ∪ V(μ(b))`. We apply `isSeparation_subOn` to the vertex and edge sets of
`G₁`. An edge `e` of `G` outside `G₁` is an edge of `Γ` that misses `S₁`, or an edge of `μ(s)` for
a space `s ⊆ F_j*` that misses `S₁`. In the first case the ends of `e` are vertices of `Γ` in `S₂`,
and those in `G₁` are vertices of `Γ` in `S₁ ∩ S₂ = F`, that is `a` or `b`. In the second case an
end of `e` in `G₁` is a vertex of `Γ` at an end of `s`, which is `a` or `b` as before, or lies in
`μ(F_k* ∩ S₁)`. Then `k = j`, since `H_j` and `H_k` are disjoint for `k ≠ j`, and `hspace`
applies. -/
theorem isSeparation_side_of
    (hspace : ∀ j, (F_star j ∩ S₁).Nonempty → ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j →
      Disjoint s S₁ → (μ (.space s)).vertexSet ∩ (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ⊆
        (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet) :
    ∃ A : Hypergraph α β, G.IsSeparation A (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) ∧
      (A ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁).vertexSet =
        (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet := by
  have hS := hP.is_surface
  set W := (sideSub Γ Γ_sub ιV ιE S₁).vertexSet ∪
    ⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet with hWdef
  set X := (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet with hXdef
  have hWG : W ⊆ G.vertexSet := by
    rintro x (hx | hx)
    · exact (sideSub_le_G hP h.isClosed_left).vertexSet_subset hx
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact (supportGraph_inter_le hP j).vertexSet_subset hj
  have hsuppW : ∀ j, (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ⊆ W := fun j =>
    subset_union_of_subset_right
      (subset_iUnion (fun j => (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet) j) _
  have hXW : X ⊆ W := by
    refine union_subset ?_ ?_
    · obtain ⟨j, hj, -⟩ := vertexSet_μ_end_subset hP h (Or.inl rfl)
      exact hj.trans (hsuppW j)
    · obtain ⟨j, hj, -⟩ := vertexSet_μ_end_subset hP h (Or.inr rfl)
      exact hj.trans (hsuppW j)
  -- `ιV` of a vertex of `Γ` on `F` lies in `X`.
  have hFX : ∀ {u : S}, u ∈ F → u ∈ Γ.V → ιV u ∈ X := by
    intro u huF huV
    rcases h.mem_ends_of_mem_V huF huV with rfl | rfl
    · obtain ⟨j, -, hj⟩ := vertexSet_μ_end_subset hP h (Or.inl rfl)
      exact Or.inl (ιV_mem_μ_vertex hP j hj)
    · obtain ⟨j, -, hj⟩ := vertexSet_μ_end_subset hP h (Or.inr rfl)
      exact Or.inr (ιV_mem_μ_vertex hP j hj)
  -- A vertex of `Γ` whose image is in `W` lies in `S₁`.
  have hWS₁ : ∀ {u : S}, u ∈ Γ.V → ιV u ∈ W → u ∈ S₁ := by
    intro u huV hu
    rcases hu with hu | hu
    · rw [vertexSet_sideSub (S₁ := S₁) hP] at hu
      obtain ⟨u', hu', hequ⟩ := hu
      rw [hP.ιV_injOn hu'.1 huV hequ] at hu'
      exact hu'.2
    · obtain ⟨k, hk⟩ := mem_iUnion.mp hu
      have hΓ : ιV u ∈ Γ_sub.vertexSet := by rw [← hP.ιV_image]; exact ⟨u, huV, rfl⟩
      obtain ⟨u', hu', hequ⟩ := supportGraph_vertexSet_inter_subset hP k inter_subset_left
        ((isClosed_of_isSupportOfDrawing hS (hP.supports_isSupport k)).inter h.isClosed_left)
        ⟨hk, hΓ⟩
      rw [hP.ιV_injOn hu'.1 huV hequ] at hu'
      exact hu'.2.2
  have hF : ∀ e ∈ (sideSub Γ Γ_sub ιV ιE S₁).edgeSet ∪
      ⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet, e ∈ G.edgeSet → G.ends e ⊆ W := by
    rintro e (he | he) -
    · exact (ends_subset_of_le (sideSub_le_G hP h.isClosed_left) he).trans subset_union_left
    · obtain ⟨j, hj⟩ := mem_iUnion.mp he
      exact (ends_subset_of_le (supportGraph_inter_le hP j) hj).trans (hsuppW j)
  have hout : ∀ e ∈ G.edgeSet, e ∉ (sideSub Γ Γ_sub ιV ιE S₁).edgeSet ∪
      ⋃ j, (supportGraph G Γ μ (F_star j ∩ S₁)).edgeSet →
      ∀ x, G.Inc e x → x ∉ W \ X := by
    intro e he heF x hx ⟨hxW, hxX⟩
    have he' := he
    rw [hP.v1_union_E] at he'
    rcases he' with he' | he'
    · -- An edge of `μ(s)` for a space `s ⊆ F_j*`.
      obtain ⟨j, hj⟩ := mem_iUnion.mp he'
      rw [hP.v2_eq j] at hj
      obtain ⟨s, hs, hsF, hes⟩ := exists_space_of_mem_edgeSet hP j subset_rfl hj
      have hsS₁ : Disjoint s S₁ := by
        refine (h.space_subset_or_disjoint hs).resolve_left fun hsS₁ => heF (Or.inr ?_)
        exact mem_iUnion.mpr ⟨j, he, Or.inl (mem_biUnion (x := s) ⟨hs, subset_inter hsF hsS₁⟩ hes)⟩
      have hle := μ_space_le hP j hs hsF
      have hxs : x ∈ (μ (.space s)).vertexSet :=
        (μ (.space s)).vertex_mem_of_inc ((GM10.inc_iff_of_le hle hes).2 hx)
      have hxHj : x ∈ (H j).vertexSet := (hP.μ_space_sub j s hs hsF).vertexSet_subset hxs
      rcases hxW with hxW | hxW
      · -- `x` is a vertex of `Γ` in `S₁`, hence an end of `s`, hence on `F`.
        have hxΓ : x ∈ Γ_sub.vertexSet := (sideSub_le hP h.isClosed_left).vertexSet_subset hxW
        rw [vertexSet_sideSub (S₁ := S₁) hP] at hxW
        obtain ⟨u, ⟨huV, huS₁⟩, rfl⟩ := hxW
        obtain ⟨u₁, u₂, hends⟩ := exists_spaceHasEnds_of_mem_drawingSpaces hS
          hP.cuff_vertices_ge_two hs
        have hint := (hP.v3_space j s hs u₁ u₂ hsF hends).1
        have hmem : ιV u ∈ (μ (.space s)).vertexSet ∩ Γ_sub.vertexSet := ⟨hxs, hxΓ⟩
        rw [hint] at hmem
        have hclS₂ : closure s ⊆ S₂ :=
          closure_minimal (subset_two_of_disjoint h.union_eq hsS₁) h.isClosed_right
        rw [hends.2.2.2.2.2] at hclS₂
        have huS₂ : u ∈ S₂ := by
          rcases hmem with hu | hu
          · rw [hP.ιV_injOn huV hends.2.1.1 hu]; exact hclS₂ (Or.inr (Or.inl rfl))
          · rw [hP.ιV_injOn huV hends.2.2.1.1 hu]; exact hclS₂ (Or.inr (Or.inr rfl))
        exact hxX (hFX (h.inter_eq ▸ ⟨huS₁, huS₂⟩) huV)
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hxW
        by_cases hkj : k = j
        · subst hkj
          have hne : (F_star k ∩ S₁).Nonempty := by
            by_contra hne
            rw [(supportGraph_of_eq_empty G Γ μ (not_nonempty_iff_eq_empty.mp hne)).1] at hk
            exact hk
          exact hxX (hspace k hne s hs hsF hsS₁ ⟨hxs, hk⟩)
        · exact disjoint_left.mp (hP.v1_disjoint hkj)
            ((supportGraph_inter_le_H (S₁ := S₁) hP k).vertexSet_subset hk) hxHj
    · -- An edge of `Γ`.
      rw [← hP.ιE_image] at he'
      obtain ⟨e', he'E, rfl⟩ := he'
      have heS₁ : Disjoint e' S₁ := by
        refine (h.edge_subset_or_disjoint he'E).resolve_left fun heS₁ => heF (Or.inl ?_)
        rw [edgeSet_sideSub (S₁ := S₁) hP]
        exact ⟨e', ⟨he'E, heS₁⟩, rfl⟩
      have heΓ : ιE e' ∈ Γ_sub.edgeSet := by rw [← hP.ιE_image]; exact ⟨e', he'E, rfl⟩
      have hxΓinc : Γ_sub.Inc (ιE e') x := (GM10.inc_iff_of_le hP.drawing_subgraph heΓ).2 hx
      have hxΓ : x ∈ Γ_sub.vertexSet := Γ_sub.vertex_mem_of_inc hxΓinc
      rw [← hP.ιV_image] at hxΓ
      obtain ⟨u, huV, rfl⟩ := hxΓ
      have hucl : u ∈ closure e' := (hP.inc_iff e' he'E u huV).mp hxΓinc
      have huS₂ : u ∈ S₂ := h.closure_subset_right_of_disjoint heS₁ hucl
      exact hxX (hFX (h.inter_eq ▸ ⟨hWS₁ huV hxW, huS₂⟩) huV)
  obtain ⟨hsep, hinter⟩ := isSeparation_subOn hWG hXW hF hout
  exact ⟨_, hsep, hinter⟩

/-- **The separation `(A, G₁)`** when every nonempty `F_j* ∩ S₁` is a support
(`isSeparation_side_of` with `space_inter_supportGraph_side_subset`). -/
theorem isSeparation_side
    (hsupp : ∀ j, (F_star j ∩ S₁).Nonempty → IsSupportOfDrawing Γ (F_star j ∩ S₁)) :
    ∃ A : Hypergraph α β, G.IsSeparation A (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) ∧
      (A ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁).vertexSet =
        (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet :=
  isSeparation_side_of hP h fun j hne _ hs hsF hsS₁ =>
    space_inter_supportGraph_side_subset hP h j (hsupp j hne) hs hsF hsS₁

omit [T2Space S] hP h in
/-- A subgraph of two graphs is a subgraph of their intersection. -/
private theorem le_inter_of_le {M A B : Hypergraph α β} (hA : M ≤ A) (hB : M ≤ B) :
    M ≤ A ∩ B where
  vertexSet_subset := subset_inter hA.vertexSet_subset hB.vertexSet_subset
  edgeSet_subset := subset_inter hA.edgeSet_subset hB.edgeSet_subset
  ends_eq e he := by
    ext x
    simp only [Hypergraph.ends, mem_ofPred_eq]
    show A.Inc e x ∧ B.Inc e x ↔ M.Inc e x
    rw [← GM10.inc_iff_of_le hA he, ← GM10.inc_iff_of_le hB he, and_self]

/-- **The linkage of one side, for any list of graphs `H₁ i`.** Let `hspace` be as in
`isSeparation_side_of`, and let every vertex of every `μ(F_j* ∩ S₁)` be a vertex of some `H₁ i`.
If `L` is an exhaustive vital `p`-linkage in `G` and the presentation has depth at most `d`, then
`L ∩ G₁` is a vital `(p + 2d)`-linkage in `G₁` that contains `Γ ∩ S₁` and whose terminals lie in
the graphs `H₁ i`. -/
theorem isExhaustiveLinkage_side_of {r₁ : ℕ} {H₁ : Fin r₁ → Hypergraph α β} {p d : ℕ}
    (hq : ∀ j, q j ≤ d)
    (hspace : ∀ j, (F_star j ∩ S₁).Nonempty → ∀ s ∈ drawingSpaces Γ, s ⊆ F_star j →
      Disjoint s S₁ → (μ (.space s)).vertexSet ∩ (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ⊆
        (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet)
    (hmemH : ∀ {j x}, x ∈ (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet →
      x ∈ ⋃ i, (H₁ i).vertexSet) {L : Hypergraph α β}
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (hLp : IsPLinkage G L p) :
    IsExhaustiveLinkage (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) (sideSub Γ Γ_sub ιV ιE S₁) r₁ H₁
        (L ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) ∧
      IsPLinkage (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁)
        (L ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) (p + 2 * d) := by
  obtain ⟨A, hsep, hAB⟩ := isSeparation_side_of hP h hspace
  have hLlink : IsLinkage G L := hL.1.1
  obtain ⟨hlink₁, hterm⟩ := theorem_2_2_proof hLlink hsep
  have hvital := (theorem_2_3_proof hLlink hsep).2 hL.1
  rw [hAB] at hterm
  have hXH : (μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet ⊆
      ⋃ i, (H₁ i).vertexSet := by
    refine union_subset ?_ ?_
    · obtain ⟨j, hj, -⟩ := vertexSet_μ_end_subset hP h (Or.inl rfl)
      exact fun x hx => hmemH (hj hx)
    · obtain ⟨j, hj, -⟩ := vertexSet_μ_end_subset hP h (Or.inr rfl)
      exact fun x hx => hmemH (hj hx)
  refine ⟨⟨hvital, le_inter_of_le ((sideSub_le hP h.isClosed_left).trans hL.2.1)
    (sideSub_le_sideGraph hP h.isClosed_left), ?_⟩, hlink₁, ?_⟩
  · intro x hx
    rcases hterm hx with hx' | hx'
    · obtain ⟨j, hj⟩ := mem_iUnion.mp (hL.2.2 hx'.1)
      have hxG₁ : x ∈ (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁).vertexSet := hx.1.2
      rw [vertexSet_sideGraph hP h.isClosed_left] at hxG₁
      rcases hxG₁ with hxΓ | hxK
      · have hxΓ' : x ∈ Γ_sub.vertexSet := (sideSub_le hP h.isClosed_left).vertexSet_subset hxΓ
        rw [vertexSet_sideSub (S₁ := S₁) hP] at hxΓ
        obtain ⟨u, ⟨huV, huS₁⟩, rfl⟩ := hxΓ
        have hmem : ιV u ∈ (H j).vertexSet ∩ Γ_sub.vertexSet := ⟨hj, hxΓ'⟩
        rw [hP.v1_inter_V j] at hmem
        obtain ⟨u', hu', hequ⟩ := hmem
        rw [hP.ιV_injOn hu'.1 huV hequ] at hu'
        exact hmemH ((μ_vertex_le_supportGraph_of_subset hP j inter_subset_left
          ⟨huV, hu'.2, huS₁⟩).vertexSet_subset (ιV_mem_μ_vertex hP j hu'))
      · obtain ⟨k, hk⟩ := mem_iUnion.mp hxK
        exact hmemH hk
    · exact hXH hx'
  · -- At most `p + 2d` terminals.
    have hfinX : ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet).Finite :=
      (μ (.vertex a)).vertexSet_finite.union (μ (.vertex b)).vertexSet_finite
    have hfinT : (terminals L).Finite := L.vertexSet_finite.subset fun x hx => hx.1
    have hcard : ∀ {u : S}, u = a ∨ u = b → (μ (.vertex u)).vertexSet.ncard ≤ d := by
      intro u hu
      obtain ⟨j, -, hj⟩ := vertexSet_μ_end_subset hP h hu
      rw [(hP.μ_vertex_sub j u hj).2.2.1]
      exact hq j
    calc (terminals (L ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁)).ncard
        ≤ ((terminals L \ A.vertexSet) ∪
            ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet)).ncard :=
          ncard_le_ncard hterm ((hfinT.sdiff).union hfinX)
      _ ≤ (terminals L \ A.vertexSet).ncard +
            ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b)).vertexSet).ncard := ncard_union_le _ _
      _ ≤ (terminals L).ncard + ((μ (.vertex a)).vertexSet.ncard +
            (μ (.vertex b)).vertexSet.ncard) :=
          Nat.add_le_add (ncard_le_ncard sdiff_subset hfinT) (ncard_union_le _ _)
      _ ≤ p + (d + d) := Nat.add_le_add hLp.2 (Nat.add_le_add (hcard (Or.inl rfl))
            (hcard (Or.inr rfl)))
      _ = p + 2 * d := by ring

/-- **The linkage of one side** (Graph Minors XXI, proofs of (6.5), (6.6), (6.7) and of claim (4)
of (6.3), pages 25–29 of the preprint: "$L \cap G_i$ is an exhaustive vital $(p + 2q)$-linkage").
Let the presentation have depth at most `d`, and let `L` be an exhaustive vital `p`-linkage in
`G`. Then `L ∩ G₁` is an exhaustive vital `(p + 2d)`-linkage in `G₁`, for the presentation of
`isPresentation_side`. Take the separation `(A, G₁)` of `isSeparation_side`. By (2.2), `L ∩ G₁`
is a linkage in `G₁` whose terminals are terminals of `L` or vertices of
`A ∩ G₁ = μ(a) ∪ μ(b)`, which has at most `2d` vertices. By (2.3) it is vital. It contains
`Γ ∩ S₁`, and each of its terminals lies in some `μ(F_j* ∩ S₁)`. -/
theorem isExhaustiveLinkage_side {r₁ : ℕ} {σ : Fin r₁ → Fin r} {p d : ℕ} (hq : ∀ j, q j ≤ d)
    (hσsup : ∀ i, IsSupportOfDrawing Γ (F_star (σ i) ∩ S₁))
    (hσall : ∀ j, (F_star j ∩ S₁).Nonempty → ∃ i, σ i = j) {L : Hypergraph α β}
    (hL : IsExhaustiveLinkage G Γ_sub r H L) (hLp : IsPLinkage G L p) :
    IsExhaustiveLinkage (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) (sideSub Γ Γ_sub ιV ιE S₁) r₁
        (fun i => supportGraph G Γ μ (F_star (σ i) ∩ S₁))
        (L ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) ∧
      IsPLinkage (sideGraph G Γ Γ_sub ιV ιE F_star μ S₁)
        (L ∩ sideGraph G Γ Γ_sub ιV ιE F_star μ S₁) (p + 2 * d) := by
  refine isExhaustiveLinkage_side_of hP h hq (fun j hne _ hs hsF hsS₁ => ?_) ?_ hL hLp
  · obtain ⟨i, rfl⟩ := hσall j hne
    exact space_inter_supportGraph_side_subset hP h _ (hσsup i) hs hsF hsS₁
  · intro j x hx
    have hne : (F_star j ∩ S₁).Nonempty := by
      by_contra hne
      rw [(supportGraph_of_eq_empty G Γ μ (not_nonempty_iff_eq_empty.mp hne)).1] at hx
      exact hx
    obtain ⟨i, rfl⟩ := hσall j hne
    exact mem_iUnion.mpr ⟨i, hx⟩

end Side
end GM21
end GraphMinor
