module

public import GraphMinor.GM21.Section6GapGeometry
public import GraphMinor.GM21.Section6Angles
import GraphMinor.GM21.Section6RestrictPres

/-!
# Graph Minors XXI, (6.3), claim (4): the two pieces of a support cut by a line

Let a support `F_j*` hold both ends `a, b` of a proper line `F`, and write
`F_j* = f([t₀, t₁])` by angles of its cuff, with `a, b` at angles `x < y` in `[t₀, t₁]`. On the
side `Σ₁` that misses the arc of angles `(x, y)`, the support meets `Σ₁` in the two arcs
`K_a = f([t₀, x])` and `K_b = f([y, t₁])` (`Gap.inter_side_eq_of_mid_disjoint`). This file proves
the facts about `μ(K_a)` and `μ(K_b)` that the correction to claim (4) uses:

* `K_a` and `K_b` are disjoint supports (`disjoint_pieces`, `isSupport_piece_left`,
  `isSupport_piece_right`);
* a space in `K_a ∪ K_b` lies in one of them (`space_subset_piece`);
* `μ(K_a)` and `μ(K_b)` share only vertices of both `μ(a)` and `μ(b)`, and no edge
  (`vertexSet_inter_pieces_subset`, `edgeSet_disjoint_pieces`), by (V4) read on angles;
* a space `s ⊆ F_j*` that misses `Σ₁` lies between `a` and `b`, so `μ(s)` meets `μ(F_j* ∩ Σ₁)`
  only in vertices of `μ(a)` and `μ(b)` (`space_inter_pieces_subset`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Gap

open Set Topology GraphMinor.Surface GraphMinor.GM21.Side GraphMinor.GM21.Supports GraphMinor.GM19

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Surface.Drawing S} {Γ_sub : Hypergraph α β} {ιV : S → α}
  {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
  (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q) (j : Fin r)
  {C : Set S} (hC : C ∈ cuffs S) (f : Circle ≃ₜ C) {t₀ t₁ x y : ℝ}
  (ht₀x : t₀ ≤ x) (hxy : x < y) (hyt₁ : y ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
  (ht₀V : cuffPoint f t₀ ∈ Γ.V) (ht₁V : cuffPoint f t₁ ∈ Γ.V)
  (hxV : cuffPoint f x ∈ Γ.V) (hyV : cuffPoint f y ∈ Γ.V)
  (hF : F_star j = cuffPoint f '' Icc t₀ t₁)
include hP hC ht₀x hxy hyt₁ hlt ht₀V ht₁V hxV hyV hF

omit hP hC ht₀V ht₁V hxV hyV hF in
/-- The two pieces are disjoint. -/
theorem disjoint_pieces : Disjoint (cuffPoint f '' Icc t₀ x) (cuffPoint f '' Icc y t₁) := by
  rw [Set.disjoint_left]
  rintro _ ⟨τ, hτ, rfl⟩ ⟨τ', hτ', hττ'⟩
  have := GM17.cuffPoint_injOn_Ico f t₀ ⟨hτ'.1.trans' (ht₀x.trans hxy.le), hτ'.2.trans_lt hlt⟩
    ⟨hτ.1, hτ.2.trans_lt ((hxy.trans_le hyt₁).trans hlt)⟩ hττ'
  linarith [hτ.2, hτ'.1]

omit hP ht₁V hyV hF in
/-- The piece at angles `[t₀, x]` is a support. -/
theorem isSupport_piece_left (hS : IsSurface S) :
    IsSupportOfDrawing Γ (cuffPoint f '' Icc t₀ x) :=
  ⟨_, _, supportHasEnds_cuffPoint_Icc hS hC f le_rfl ht₀x (hxy.le.trans hyt₁) hlt ht₀V hxV⟩

omit hP ht₀V hxV hF in
/-- The piece at angles `[y, t₁]` is a support. -/
theorem isSupport_piece_right (hS : IsSurface S) :
    IsSupportOfDrawing Γ (cuffPoint f '' Icc y t₁) :=
  ⟨_, _, supportHasEnds_cuffPoint_Icc hS hC f (ht₀x.trans hxy.le) hyt₁ le_rfl hlt hyV ht₁V⟩

omit hP hC ht₀V ht₁V hxV hyV hF in
/-- A connected set inside the two pieces lies in one of them. -/
theorem subset_piece_of_isPreconnected [T2Space S] {s : Set S} (hs : IsPreconnected s)
    (hsub : s ⊆ cuffPoint f '' Icc t₀ x ∪ cuffPoint f '' Icc y t₁) :
    s ⊆ cuffPoint f '' Icc t₀ x ∨ s ⊆ cuffPoint f '' Icc y t₁ := by
  have hcl : ∀ s t : ℝ, IsClosed (cuffPoint f '' Icc s t) := fun s t =>
    (isCompact_Icc.image (GM17.cuffPoint_continuous f)).isClosed
  refine isPreconnected_iff_subset_of_disjoint_closed.mp hs _ _ (hcl _ _) (hcl _ _) hsub ?_
  rw [(disjoint_pieces f ht₀x hxy hyt₁ hlt).inter_eq, inter_empty]

/-- **The pieces share only vertices of `μ(a)` and `μ(b)`.** By (V4) read on angles, a common
vertex of `μ(K_a)` and `μ(K_b)` is a vertex of `μ` of the point at angle `x`, and also of `μ` of
the point at angle `y`. -/
theorem vertexSet_inter_pieces_subset :
    (supportGraph G Γ μ (cuffPoint f '' Icc t₀ x)).vertexSet ∩
        (supportGraph G Γ μ (cuffPoint f '' Icc y t₁)).vertexSet ⊆
      (μ (.vertex (cuffPoint f x))).vertexSet ∩ (μ (.vertex (cuffPoint f y))).vertexSet := by
  have ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C := ⟨ht₀V, GM17.cuffPoint_mem f t₀⟩
  have hle : t₀ ≤ t₁ := ht₀x.trans (hxy.le.trans hyt₁)
  exact subset_inter
    (supportGraph_inter_vertexSet_subset_of_angle_between hP j hC f ht₀ ht₁V hle hlt hF le_rfl
      ht₀x le_rfl hxy.le hyt₁ le_rfl rfl rfl hxV)
    (supportGraph_inter_vertexSet_subset_of_angle_between hP j hC f ht₀ ht₁V hle hlt hF le_rfl
      ht₀x hxy.le le_rfl hyt₁ le_rfl rfl rfl hyV)

omit hyV in
/-- **The pieces share no edge**: `μ(K_b) ≤ μ(f([x, t₁]))`, which shares no edge with `μ(K_a)`
(the edge part of (V4)). -/
theorem edgeSet_disjoint_pieces :
    Disjoint (supportGraph G Γ μ (cuffPoint f '' Icc t₀ x)).edgeSet
      (supportGraph G Γ μ (cuffPoint f '' Icc y t₁)).edgeSet := by
  have ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C := ⟨ht₀V, GM17.cuffPoint_mem f t₀⟩
  have hle : t₀ ≤ t₁ := ht₀x.trans (hxy.le.trans hyt₁)
  have hdis := supportGraph_edgeSet_disjoint_of_angles hP j hC f hlt ht₀ ht₁V hF le_rfl ht₀x
    (hxy.le.trans hyt₁) le_rfl ht₀V hxV
  have hmono := supportGraph_mono hP j (image_Icc_subset j f hF (ht₀x) le_rfl)
    (image_mono (Icc_subset_Icc hxy.le le_rfl))
  exact hdis.mono_right hmono.edgeSet_subset

/-- **A space on the other side lies between `a` and `b`.** Let `s ⊆ F_j*` be a space that misses
`S₁`, where `F_j* ∩ S₁` is the union of the two pieces. Then `μ(s)` meets `μ(F_j* ∩ S₁)` only in
vertices of `μ` of the points at angles `x` and `y`. The angles of `s` lie in `[x, y]`, since `s`
misses both pieces, and (V4) applies at `x` and at `y`. -/
theorem space_inter_pieces_subset [T2Space S] (hS : IsSurface S) {S₁ : Set S}
    (hsplit : F_star j ∩ S₁ = cuffPoint f '' Icc t₀ x ∪ cuffPoint f '' Icc y t₁)
    {s : Set S} (hs : s ∈ drawingSpaces Γ) (hsF : s ⊆ F_star j) (hsS₁ : Disjoint s S₁) :
    (μ (.space s)).vertexSet ∩ (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ⊆
      (μ (.vertex (cuffPoint f x))).vertexSet ∪ (μ (.vertex (cuffPoint f y))).vertexSet := by
  have ht₀ : cuffPoint f t₀ ∈ Γ.V ∩ C := ⟨ht₀V, GM17.cuffPoint_mem f t₀⟩
  have hle : t₀ ≤ t₁ := ht₀x.trans (hxy.le.trans hyt₁)
  obtain ⟨α₁, β₁, hα, hαβ, hβ, -, -, -, hseq, -⟩ :=
    space_in_support_eq_Ioo hS hP.cuff_vertices_ge_two hC f hle hlt ht₀ hF hs hsF
  have hKS₁ : cuffPoint f '' Icc t₀ x ∪ cuffPoint f '' Icc y t₁ ⊆ S₁ :=
    hsplit ▸ inter_subset_right
  -- The angles of `s` lie in `[x, y]`.
  have hxα : x ≤ α₁ := by
    by_contra hlt'
    push Not at hlt'
    set τ := min x ((α₁ + β₁) / 2)
    have hτ1 : α₁ < τ := lt_min hlt' (by linarith)
    have hτ2 : τ < β₁ := (min_le_right _ _).trans_lt (by linarith)
    refine disjoint_left.mp hsS₁ (hseq ▸ ⟨τ, ⟨hτ1, hτ2⟩, rfl⟩) (hKS₁ (Or.inl ⟨τ, ⟨?_, ?_⟩, rfl⟩))
    · linarith
    · exact min_le_left _ _
  have hβy : β₁ ≤ y := by
    by_contra hlt'
    push Not at hlt'
    set τ := max y ((α₁ + β₁) / 2)
    have hτ1 : α₁ < τ := (by linarith : α₁ < (α₁ + β₁) / 2).trans_le (le_max_right _ _)
    have hτ2 : τ < β₁ := max_lt hlt' (by linarith)
    refine disjoint_left.mp hsS₁ (hseq ▸ ⟨τ, ⟨hτ1, hτ2⟩, rfl⟩) (hKS₁ (Or.inr ⟨τ, ⟨?_, ?_⟩, rfl⟩))
    · exact le_max_left _ _
    · linarith
  have hsI : μ (.space s) ≤ supportGraph G Γ μ (cuffPoint f '' Icc α₁ β₁) :=
    Side.μ_space_le_supportGraph_of_subset hP j (image_Icc_subset j f hF hα hβ) hs
      (by rw [hseq]; exact image_mono Ioo_subset_Icc_self)
  -- A vertex of `μ(F_j* ∩ S₁)` is a vertex of `μ` of one of the pieces.
  have hpieces : (supportGraph G Γ μ (F_star j ∩ S₁)).vertexSet ⊆
      (supportGraph G Γ μ (cuffPoint f '' Icc t₀ x)).vertexSet ∪
        (supportGraph G Γ μ (cuffPoint f '' Icc y t₁)).vertexSet := by
    rw [hsplit]
    rintro v ⟨hvG, hv | hv⟩
    · obtain ⟨s', ⟨hs', hs'K⟩, hvs'⟩ := mem_iUnion₂.mp hv
      rcases subset_piece_of_isPreconnected (f := f) (ht₀x := ht₀x) (hxy := hxy) (hyt₁ := hyt₁)
        (hlt := hlt) (isConnected_of_mem_drawingSpaces hs').isPreconnected hs'K with h' | h'
      · exact Or.inl ⟨hvG, Or.inl (mem_biUnion (x := s') ⟨hs', h'⟩ hvs')⟩
      · exact Or.inr ⟨hvG, Or.inl (mem_biUnion (x := s') ⟨hs', h'⟩ hvs')⟩
    · obtain ⟨u, ⟨huV, hu⟩, hvu⟩ := mem_iUnion₂.mp hv
      rcases hu with hu | hu
      · exact Or.inl ⟨hvG, Or.inr (mem_biUnion (x := u) ⟨huV, hu⟩ hvu)⟩
      · exact Or.inr ⟨hvG, Or.inr (mem_biUnion (x := u) ⟨huV, hu⟩ hvu)⟩
  rintro v ⟨hvs, hvK⟩
  rcases hpieces hvK with hv | hv
  · exact Or.inl (supportGraph_inter_vertexSet_subset_of_angle_between hP j hC f ht₀ ht₁V hle
      hlt hF le_rfl ht₀x le_rfl hxα hαβ.le hβ rfl rfl hxV ⟨hv, hsI.vertexSet_subset hvs⟩)
  · exact Or.inr (supportGraph_inter_vertexSet_subset_of_angle_between hP j hC f ht₀ ht₁V hle
      hlt hF hα hαβ.le hβy le_rfl hyt₁ le_rfl rfl rfl hyV ⟨hsI.vertexSet_subset hvs, hv⟩)

end Gap
end GM21
end GraphMinor
