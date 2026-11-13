module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.Section6Supports

/-!
# Section 6 of Graph Minors XXI: Presentations (`(6.1)` and `(6.2)`)

This file formalizes the support-path lemmas `(6.1)` (`theorem_6_1`) and `(6.2)` (`theorem_6_2`)
from Section 6 (pages 22–23 of the preprint) of Robertson and Seymour,
*Graph Minors. XXI. Graphs with unique linkages*, J. Combin. Theory Ser. B 99 (2009), 583–616.
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Function Topology Classical
open GraphMinor.Surface
open GraphMinor.GM17
open GraphMinor.GM19 hiding Drawing
open GraphMinor.GM21.Supports

universe u v w

section Section6

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-! ## 1. Basic Properties of `supportGraph` and Skeleton Walks -/

/-- If `u ∈ Γ.V ∩ I` and `μ (.vertex u) ≤ G`, then `(μ (.vertex u)).vertexSet ⊆ (supportGraph G Γ μ I).vertexSet`. -/
lemma vertex_mu_subset_supportGraph {G : Hypergraph α β} {Γ : Drawing S}
    {μ : BoundaryUnit S → Hypergraph α β} {I : Set S} {u : S}
    (hu : u ∈ Γ.V ∩ I) (hle : μ (.vertex u) ≤ G) :
    (μ (.vertex u)).vertexSet ⊆ (supportGraph G Γ μ I).vertexSet := by
  intro v hv
  exact ⟨hle.vertexSet_subset hv, Or.inr (mem_biUnion hu hv)⟩

/-- If `s ∈ drawingSpaces Γ`, `s ⊆ I`, and `μ (.space s) ≤ G`, then
`(μ (.space s)).skeleton ≤ (supportGraph G Γ μ I).skeleton`. -/
lemma space_skeleton_le_supportGraph_skeleton {G : Hypergraph α β} {Γ : Drawing S}
    {μ : BoundaryUnit S → Hypergraph α β} {I s : Set S}
    (hs : s ∈ drawingSpaces Γ) (hsI : s ⊆ I) (hle : μ (.space s) ≤ G) :
    (μ (.space s)).skeleton ≤ (supportGraph G Γ μ I).skeleton := by
  rintro x y ⟨hne, e, hx, hy⟩
  have he : e ∈ (μ (.space s)).edgeSet := (μ (.space s)).edge_mem_of_inc hx
  have hxG : G.Inc e x := (GM10.inc_iff_of_le hle he).mp hx
  have hyG : G.Inc e y := (GM10.inc_iff_of_le hle he).mp hy
  exact ⟨hne, e, ⟨hxG, Or.inl ⟨s, hs, hsI, hx⟩⟩, ⟨hyG, Or.inl ⟨s, hs, hsI, hy⟩⟩⟩

/-- If `I ⊆ I'`, then `(supportGraph G Γ μ I).skeleton ≤ (supportGraph G Γ μ I').skeleton`. -/
lemma supportGraph_skeleton_mono {G : Hypergraph α β} {Γ : Drawing S}
    {μ : BoundaryUnit S → Hypergraph α β} {I I' : Set S} (hsub : I ⊆ I') :
    (supportGraph G Γ μ I).skeleton ≤ (supportGraph G Γ μ I').skeleton := by
  rintro x y ⟨hne, e, ⟨hxG, hx_u⟩, ⟨hyG, hy_u⟩⟩
  refine ⟨hne, e, ⟨hxG, ?_⟩, ⟨hyG, ?_⟩⟩
  · rcases hx_u with ⟨s, hs, hsI, hx⟩ | ⟨u, ⟨huV, huI⟩, hx⟩
    · exact Or.inl ⟨s, hs, hsI.trans hsub, hx⟩
    · exact Or.inr ⟨u, ⟨huV, hsub huI⟩, hx⟩
  · rcases hy_u with ⟨s, hs, hsI, hy⟩ | ⟨u, ⟨huV, huI⟩, hy⟩
    · exact Or.inl ⟨s, hs, hsI.trans hsub, hy⟩
    · exact Or.inr ⟨u, ⟨huV, hsub huI⟩, hy⟩

/-- Every vertex in the support of a walk `p : M.skeleton.Walk a b` (with `a ∈ M.vertexSet`)
belongs to `M.vertexSet`. -/
lemma mem_vertexSet_of_mem_walk_support_sec6 {M : Hypergraph α β} {a b z : α}
    (ha : a ∈ M.vertexSet) (p : M.skeleton.Walk a b) (hz : z ∈ p.support) :
    z ∈ M.vertexSet := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ ha
  | @cons a c b hadj q ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz'
    · exact ha
    · rcases hadj with ⟨_, e, _, hc_inc⟩
      exact ih (M.vertex_mem_of_inc hc_inc) hz'

/-- For any two subgraphs `M₁, M₂ : Hypergraph α β`, `M₁.skeleton ≤ (M₁ ∪ M₂).skeleton` and
`M₂.skeleton ≤ (M₁ ∪ M₂).skeleton`. -/
lemma skeleton_le_union_left (M₁ M₂ : Hypergraph α β) :
    M₁.skeleton ≤ (M₁ ∪ M₂).skeleton := by
  rintro x y ⟨hne, e, hx, hy⟩
  exact ⟨hne, e, Or.inl hx, Or.inl hy⟩

lemma skeleton_le_union_right (M₁ M₂ : Hypergraph α β) :
    M₂.skeleton ≤ (M₁ ∪ M₂).skeleton := by
  rintro x y ⟨hne, e, hx, hy⟩
  exact ⟨hne, e, Or.inr hx, Or.inr hy⟩

/-- Unpacks `HasDisjointPaths K X Y k` as `k` explicit walks `P i : K.Walk (u i) (v i)` with
pairwise disjoint supports. -/
lemma hasDisjointPaths_iff_walks {V : Type*} (K : SimpleGraph V) (X Y : Set V) (k : ℕ) :
    HasDisjointPaths K X Y k ↔
      ∃ (u v : Fin k → V) (P : ∀ i : Fin k, K.Walk (u i) (v i)),
        (∀ i, u i ∈ X) ∧ (∀ i, v i ∈ Y) ∧ (∀ i, (P i).IsPath) ∧
        (∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support}) := by
  constructor
  · rintro ⟨P, hdisj⟩
    exact ⟨fun i => (P i).first, fun i => (P i).last, fun i => (P i).walk,
      fun i => (P i).first_mem, fun i => (P i).last_mem, fun i => (P i).isPath,
      fun i₁ i₂ hne => @hdisj i₁ i₂ hne⟩
  · rintro ⟨u, v, P, hu, hv, hp, hdisj⟩
    exact ⟨fun i => ⟨u i, v i, P i, hp i, hu i, hv i⟩, fun i₁ i₂ hne => hdisj i₁ i₂ hne⟩

/-- For a single vertex `u ∈ Γ.V`, `(supportGraph G Γ μ {u}).vertexSet ⊆ (μ (.vertex u)).vertexSet`. -/
lemma supportGraph_singleton_vertex_subset {G : Hypergraph α β} {Γ : Drawing S}
    {μ : BoundaryUnit S → Hypergraph α β} {u : S} (hu : u ∈ Γ.V) :
    (supportGraph G Γ μ {u}).vertexSet ⊆ (μ (.vertex u)).vertexSet := by
  rintro v ⟨_, hv | hv⟩
  · exfalso
    rw [mem_iUnion₂] at hv
    rcases hv with ⟨s, ⟨hs, hs_sub⟩, _⟩
    rcases (isConnected_of_mem_drawingSpaces hs).1 with ⟨x, hx⟩
    have hxu : x = u := mem_singleton_iff.mp (hs_sub hx)
    exact (subset_bd_diff_of_mem_drawingSpaces hs hx).2 (hxu ▸ hu)
  · rw [mem_iUnion₂] at hv
    rcases hv with ⟨w, ⟨_, hw_u⟩, hvw⟩
    rw [mem_singleton_iff.mp hw_u] at hvw
    exact hvw

/-- If `u : Fin q → α` maps into a finite set `Z` with `Z.ncard = q` and `u` is injective, then
`Set.range u = Z`. -/
lemma range_eq_of_injective_of_ncard_eq {q : ℕ} {u : Fin q → α} {Z : Set α}
    (hZ_fin : Z.Finite) (hZ_card : Z.ncard = q)
    (hu_mem : ∀ i : Fin q, u i ∈ Z) (hu_inj : Function.Injective u) :
    Set.range u = Z := by
  have hsub : Set.range u ⊆ Z := by rintro _ ⟨i, rfl⟩; exact hu_mem i
  have hcard_range : (Set.range u).ncard = q := by
    rw [← image_univ, (hu_inj.injOn).ncard_image, ncard_univ, Nat.card_fin]
  exact eq_of_subset_of_ncard_le hsub (by omega) hZ_fin

/-- Given `q` mutually vertex-disjoint walks `P i` from `u i` to `v i` with `v i ∈ Z` where
`Z.ncard = q`, the map `v` is injective, `Set.range v = Z`, and any vertex `z ∈ Z` that belongs
to `(P i).support` must equal `v i`. -/
lemma end_eq_of_mem_support_of_disjoint_walks {V : Type*} {G_sk : SimpleGraph V} {q : ℕ}
    {u v : Fin q → V} (P : ∀ i : Fin q, G_sk.Walk (u i) (v i))
    {Z : Set V} (hZ_fin : Z.Finite) (hZ_card : Z.ncard = q)
    (hv_mem : ∀ i : Fin q, v i ∈ Z)
    (hdisj : ∀ i₁ i₂ : Fin q, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support}) :
    Function.Injective v ∧ Set.range v = Z ∧
    ∀ (i : Fin q) {z : V}, z ∈ Z → z ∈ (P i).support → z = v i := by
  have hv_inj : Function.Injective v := by
    intro i₁ i₂ h_eq
    by_contra hne
    have hmem₂ : v i₁ ∈ {x | x ∈ (P i₂).support} := by
      rw [mem_ofPred_eq, h_eq]
      exact (P i₂).end_mem_support
    exact Set.disjoint_left.mp (hdisj i₁ i₂ hne) (P i₁).end_mem_support hmem₂
  have hrange : Set.range v = Z := range_eq_of_injective_of_ncard_eq hZ_fin hZ_card hv_mem hv_inj
  refine ⟨hv_inj, hrange, ?_⟩
  intro i z hz hz_supp
  rw [← hrange] at hz
  rcases hz with ⟨m, rfl⟩
  by_cases him : i = m
  · subst him; rfl
  · exfalso
    exact Set.disjoint_left.mp (hdisj i m him) hz_supp (P m).end_mem_support

/-- Symmetric version for the start vertices `u i ∈ Z`. -/
lemma start_eq_of_mem_support_of_disjoint_walks {V : Type*} {G_sk : SimpleGraph V} {q : ℕ}
    {u v : Fin q → V} (P : ∀ i : Fin q, G_sk.Walk (u i) (v i))
    {Z : Set V} (hZ_fin : Z.Finite) (hZ_card : Z.ncard = q)
    (hu_mem : ∀ i : Fin q, u i ∈ Z)
    (hdisj : ∀ i₁ i₂ : Fin q, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support}) :
    Function.Injective u ∧ Set.range u = Z ∧
    ∀ (i : Fin q) {z : V}, z ∈ Z → z ∈ (P i).support → z = u i := by
  have hu_inj : Function.Injective u := by
    intro i₁ i₂ h_eq
    by_contra hne
    have hmem₂ : u i₁ ∈ {x | x ∈ (P i₂).support} := by
      rw [mem_ofPred_eq, h_eq]
      exact (P i₂).start_mem_support
    exact Set.disjoint_left.mp (hdisj i₁ i₂ hne) (P i₁).start_mem_support hmem₂
  have hrange : Set.range u = Z := range_eq_of_injective_of_ncard_eq hZ_fin hZ_card hu_mem hu_inj
  refine ⟨hu_inj, hrange, ?_⟩
  intro i z hz hz_supp
  rw [← hrange] at hz
  rcases hz with ⟨m, rfl⟩
  by_cases him : i = m
  · subst him; rfl
  · exfalso
    exact Set.disjoint_left.mp (hdisj i m him) hz_supp (P m).start_mem_support

/-! ## 2. Support Intersection Lemma for `(6.1)` -/

/-- Symmetry of `SupportHasEnds`: if `F` is a support of `Γ` with ends `a, b`, then `F` is also a
support of `Γ` with ends `b, a`. -/
lemma supportHasEnds_symm {Γ : Drawing S} {F : Set S} {a b : S}
    (h : SupportHasEnds Γ F a b) : SupportHasEnds Γ F b a := by
  rcases h with ⟨v_pt, hv, hF, ha, hb⟩ | ⟨hsub, hne, ha, hb, hline⟩
  · exact Or.inl ⟨v_pt, hv, hF, hb, ha⟩
  · exact Or.inr ⟨hsub, hne.symm, hb, ha, hline.symm⟩

/-- For a support `F = cuffPoint f '' Icc t₀ t₁` (`t₀ ≤ t₁ < t₀ + 2π`) on a cuff `C`, four vertices
`a, b, a', b'` are in monotone parameter order along `F` (`AreInOrderInSupport`) if there exist
parameters `τa, τb, τa' ≤ τb'` in `Icc t₀ t₁` mapped by `cuffPoint f` to `a, b, a', b'` such that
either `τa ≤ τb ≤ τa' ≤ τb'` or `τb' ≤ τa' ≤ τb ≤ τa`. -/
def AreInOrderInSupport {C : Set S} (f : Circle ≃ₜ C) (t₀ t₁ : ℝ)
    (a b a' b' : S) : Prop :=
  ∃ τa τb τa' τb' : ℝ,
    τa ∈ Icc t₀ t₁ ∧ τb ∈ Icc t₀ t₁ ∧ τa' ∈ Icc t₀ t₁ ∧ τb' ∈ Icc t₀ t₁ ∧
    cuffPoint f τa = a ∧ cuffPoint f τb = b ∧ cuffPoint f τa' = a' ∧ cuffPoint f τb' = b' ∧
    ((τa ≤ τb ∧ τb ≤ τa' ∧ τa' ≤ τb') ∨
     (τb' ≤ τa' ∧ τa' ≤ τb ∧ τb ≤ τa))

/-- When a support `F = cuffPoint f '' Icc t₀ t₁` (`t₀ ≤ t₁ < t₀ + 2π`) on a cuff `C` is parametrized
as a line, and `I, I' ⊆ F` are the supports with ends `a, b` and `a', b'`, the existence of a support
`J ⊆ F` with `SupportHasEnds Γ J b b'`, `I ∩ J = {b}`, and `I' ⊆ J` is equivalent to `a, b, a', b'`
being in monotone parameter order along `F` (`AreInOrderInSupport f t₀ t₁ a b a' b'`). This shows
that the binders `J ⊆ F_star j`, `SupportHasEnds Γ J b b'`, `I ∩ J = {b}`, and `I' ⊆ J` in `(6.1)`
state the paper's hypothesis "Let $a, b, a', b' \in F_1^* \cap V(\Gamma)$ be in order" and ask no
more than that hypothesis. -/
theorem exists_support_J_iff_areInOrderInSupport
    (hS : IsSurface S) {Γ : Drawing S} {C F I I' : Set S} {a b a' b' : S}
    (hC : C ∈ cuffs S) (f : Circle ≃ₜ C)
    {t₀ t₁ : ℝ} (hle : t₀ ≤ t₁) (hlt : t₁ < t₀ + 2 * Real.pi)
    (hF_eq : F = cuffPoint f '' Icc t₀ t₁)
    (hI_sub : I ⊆ F) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F) (hI'_ends : SupportHasEnds Γ I' a' b') :
    (∃ J : Set S, J ⊆ F ∧ SupportHasEnds Γ J b b' ∧ I ∩ J = {b} ∧ I' ⊆ J) ↔
      AreInOrderInSupport f t₀ t₁ a b a' b' := by
  have hends_I := ends_mem_of_supportHasEnds hI_ends
  have hends_I' := ends_mem_of_supportHasEnds hI'_ends
  obtain ⟨α, β, hα_ge, hαβ, hβ_le, hI_ab, hI_eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hF_eq hI_sub hI_ends
  obtain ⟨α', β', hα'_ge, hα'β', hβ'_le, hI'_a'b', hI'_eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hF_eq hI'_sub hI'_ends
  constructor
  · rintro ⟨J, hJ_sub, hJ_ends, hIJ_inter, hI'J⟩
    obtain ⟨γ, δ, hγ_ge, hγδ, hδ_le, hJ_bb', hJ_eq⟩ :=
      subsupport_eq_cuffPoint_Icc hS hC f hle hlt hF_eq hJ_sub hJ_ends
    have hγ_le_α' : γ ≤ α' := by
      have hmem : cuffPoint f α' ∈ cuffPoint f '' Icc γ δ :=
        hJ_eq ▸ hI'J (hI'_eq ▸ ⟨α', ⟨le_rfl, hα'β'⟩, rfl⟩)
      rcases hmem with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
      have h := cuffPoint_injOn_Ico f t₀ ⟨hγ_ge.trans hs1, (hs2.trans hδ_le).trans_lt hlt⟩
        ⟨hα'_ge, (hα'β'.trans hβ'_le).trans_lt hlt⟩ hs_eq
      linarith
    have hβ'_le_δ : β' ≤ δ := by
      have hmem : cuffPoint f β' ∈ cuffPoint f '' Icc γ δ :=
        hJ_eq ▸ hI'J (hI'_eq ▸ ⟨β', ⟨hα'β', le_rfl⟩, rfl⟩)
      rcases hmem with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
      have h := cuffPoint_injOn_Ico f t₀ ⟨hγ_ge.trans hs1, (hs2.trans hδ_le).trans_lt hlt⟩
        ⟨hα'_ge.trans hα'β', hβ'_le.trans_lt hlt⟩ hs_eq
      linarith
    rcases eq_or_lt_of_le hγδ with hγ_eq_δ | hγ_lt_δ
    · -- Degenerate case `γ = δ`: then `α' = β' = γ = δ` and `a' = b' = b`.
      have hα'_eq_γ : α' = γ := by linarith
      have hβ'_eq_γ : β' = γ := by linarith
      have hγ_b : cuffPoint f γ = b := by
        rcases hJ_bb' with ⟨h1, _⟩ | ⟨_, h2⟩
        · exact h1
        · rw [hγ_eq_δ, h2]
      have hγ_a' : cuffPoint f γ = a' := by
        rcases hI'_a'b' with ⟨h1, _⟩ | ⟨_, h2⟩
        · rw [← hα'_eq_γ, h1]
        · rw [← hβ'_eq_γ, h2]
      have hγ_b' : cuffPoint f γ = b' := by
        rcases hI'_a'b' with ⟨_, h2⟩ | ⟨h1, _⟩
        · rw [← hβ'_eq_γ, h2]
        · rw [← hα'_eq_γ, h1]
      rcases hI_ab with ⟨hα_a, hβ_b⟩ | ⟨hα_b, hβ_a⟩
      · have hβ_eq_γ : β = γ :=
          cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hαβ, hβ_le.trans_lt hlt⟩
            ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ (hβ_b.trans hγ_b.symm)
        exact ⟨α, β, α', β', ⟨hα_ge, hαβ.trans hβ_le⟩, ⟨hα_ge.trans hαβ, hβ_le⟩,
          ⟨hα'_ge, hα'β'.trans hβ'_le⟩, ⟨hα'_ge.trans hα'β', hβ'_le⟩,
          hα_a, hβ_b, by rw [hα'_eq_γ, hγ_a'], by rw [hβ'_eq_γ, hγ_b'],
          Or.inl ⟨hαβ, by linarith, hα'β'⟩⟩
      · have hα_eq_γ : α = γ :=
          cuffPoint_injOn_Ico f t₀ ⟨hα_ge, (hαβ.trans hβ_le).trans_lt hlt⟩
            ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ (hα_b.trans hγ_b.symm)
        exact ⟨β, α, β', α', ⟨hα_ge.trans hαβ, hβ_le⟩, ⟨hα_ge, hαβ.trans hβ_le⟩,
          ⟨hα'_ge.trans hα'β', hβ'_le⟩, ⟨hα'_ge, hα'β'.trans hβ'_le⟩,
          hβ_a, hα_b, by rw [hβ'_eq_γ, hγ_a'], by rw [hα'_eq_γ, hγ_b'],
          Or.inr ⟨by linarith, by linarith, hαβ⟩⟩
    · -- Non-degenerate case `γ < δ`.
      rcases hJ_bb' with ⟨hγ_b, hδ_b'⟩ | ⟨hγ_b', hδ_b⟩
      · have hγ_in_I : cuffPoint f γ ∈ cuffPoint f '' Icc α β := by
          rw [← hI_eq, hγ_b]; exact hends_I.2.1
        rcases hγ_in_I with ⟨τb, ⟨hτb1, hτb2⟩, hτb_eq⟩
        have hτb_γ : τb = γ :=
          cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hτb1, (hτb2.trans hβ_le).trans_lt hlt⟩
            ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ hτb_eq
        subst τb
        have hmin_in_IJ : cuffPoint f (min β δ) ∈ I ∩ J := by
          refine ⟨?_, ?_⟩
          · rw [hI_eq]; exact ⟨min β δ, ⟨hτb1.trans (le_min hτb2 hγδ), min_le_left β δ⟩, rfl⟩
          · rw [hJ_eq]; exact ⟨min β δ, ⟨le_min hτb2 hγδ, min_le_right β δ⟩, rfl⟩
        rw [hIJ_inter, mem_singleton_iff, ← hγ_b] at hmin_in_IJ
        have hmin_eq_γ : min β δ = γ :=
          cuffPoint_injOn_Ico f t₀
            ⟨hγ_ge.trans (le_min hτb2 hγδ), ((min_le_left β δ).trans hβ_le).trans_lt hlt⟩
            ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ hmin_in_IJ
        have hβ_eq_γ : β = γ := by
          rcases min_cases β δ with ⟨hmin_β, _⟩ | ⟨hmin_δ, _⟩ <;> linarith
        have hα_a : cuffPoint f α = a := by
          rcases hI_ab with ⟨h1, _⟩ | ⟨h1, h2⟩
          · exact h1
          · have hα_eq_γ : α = γ :=
              cuffPoint_injOn_Ico f t₀ ⟨hα_ge, (hαβ.trans hβ_le).trans_lt hlt⟩
                ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ (h1.trans hγ_b.symm)
            have hα_eq_β : α = β := by linarith
            rw [hα_eq_β, h2]
        have hβ'_eq_δ : β' = δ := by
          have hδ_in_I' : cuffPoint f δ ∈ cuffPoint f '' Icc α' β' := by
            rw [← hI'_eq, hδ_b']; exact hends_I'.2.1
          rcases hδ_in_I' with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
          have hs_δ : s = δ :=
            cuffPoint_injOn_Ico f t₀ ⟨hα'_ge.trans hs1, (hs2.trans hβ'_le).trans_lt hlt⟩
              ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ hs_eq
          linarith
        have hα'_a' : cuffPoint f α' = a' := by
          rcases hI'_a'b' with ⟨h1, _⟩ | ⟨h1, h2⟩
          · exact h1
          · have hα'_eq_δ : α' = δ :=
              cuffPoint_injOn_Ico f t₀ ⟨hα'_ge, (hα'β'.trans hβ'_le).trans_lt hlt⟩
                ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ (h1.trans hδ_b'.symm)
            have hα'_eq_β' : α' = β' := by linarith
            rw [hα'_eq_β', h2]
        exact ⟨α, β, α', β', ⟨hα_ge, hαβ.trans hβ_le⟩, ⟨hα_ge.trans hαβ, hβ_le⟩,
          ⟨hα'_ge, hα'β'.trans hβ'_le⟩, ⟨hα'_ge.trans hα'β', hβ'_le⟩,
          hα_a, by rw [hβ_eq_γ, hγ_b], hα'_a', by rw [hβ'_eq_δ, hδ_b'],
          Or.inl ⟨hαβ, by linarith, hα'β'⟩⟩
      · have hδ_in_I : cuffPoint f δ ∈ cuffPoint f '' Icc α β := by
          rw [← hI_eq, hδ_b]; exact hends_I.2.1
        rcases hδ_in_I with ⟨τb, ⟨hτb1, hτb2⟩, hτb_eq⟩
        have hτb_δ : τb = δ :=
          cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hτb1, (hτb2.trans hβ_le).trans_lt hlt⟩
            ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ hτb_eq
        subst τb
        have hmax_in_IJ : cuffPoint f (max α γ) ∈ I ∩ J := by
          refine ⟨?_, ?_⟩
          · rw [hI_eq]; exact ⟨max α γ, ⟨le_max_left α γ, (max_le hτb1 hγδ).trans hτb2⟩, rfl⟩
          · rw [hJ_eq]; exact ⟨max α γ, ⟨le_max_right α γ, max_le hτb1 hγδ⟩, rfl⟩
        rw [hIJ_inter, mem_singleton_iff, ← hδ_b] at hmax_in_IJ
        have hmax_eq_δ : max α γ = δ :=
          cuffPoint_injOn_Ico f t₀
            ⟨hα_ge.trans (le_max_left α γ), ((max_le hτb1 hγδ).trans hδ_le).trans_lt hlt⟩
            ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ hmax_in_IJ
        have hα_eq_δ : α = δ := by
          rcases max_cases α γ with ⟨hmax_α, _⟩ | ⟨hmax_γ, _⟩ <;> linarith
        have hβ_a : cuffPoint f β = a := by
          rcases hI_ab with ⟨h1, h2⟩ | ⟨_, h2⟩
          · have hβ_eq_δ : β = δ :=
              cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hαβ, hβ_le.trans_lt hlt⟩
                ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ (h2.trans hδ_b.symm)
            have hα_eq_β : α = β := by linarith
            rw [← hα_eq_β, h1]
          · exact h2
        have hα'_eq_γ : α' = γ := by
          have hγ_in_I' : cuffPoint f γ ∈ cuffPoint f '' Icc α' β' := by
            rw [← hI'_eq, hγ_b']; exact hends_I'.2.1
          rcases hγ_in_I' with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
          have hs_γ : s = γ :=
            cuffPoint_injOn_Ico f t₀ ⟨hα'_ge.trans hs1, (hs2.trans hβ'_le).trans_lt hlt⟩
              ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ hs_eq
          linarith
        have hβ'_a' : cuffPoint f β' = a' := by
          rcases hI'_a'b' with ⟨h1, h2⟩ | ⟨_, h2⟩
          · have hβ'_eq_γ : β' = γ :=
              cuffPoint_injOn_Ico f t₀ ⟨hα'_ge.trans hα'β', hβ'_le.trans_lt hlt⟩
                ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ (h2.trans hγ_b'.symm)
            have hα'_eq_β' : α' = β' := by linarith
            rw [← hα'_eq_β', h1]
          · exact h2
        exact ⟨β, α, β', α', ⟨hα_ge.trans hαβ, hβ_le⟩, ⟨hα_ge, hαβ.trans hβ_le⟩,
          ⟨hα'_ge.trans hα'β', hβ'_le⟩, ⟨hα'_ge, hα'β'.trans hβ'_le⟩,
          hβ_a, by rw [hα_eq_δ, hδ_b], hβ'_a', by rw [hα'_eq_γ, hγ_b'],
          Or.inr ⟨hα'β', by linarith, hαβ⟩⟩
  · rintro ⟨τa, τb, τa', τb', hτa, hτb, hτa', hτb', hcp_a, hcp_b, hcp_a', hcp_b', h_ord⟩
    have hbV : cuffPoint f τb ∈ Γ.V := hcp_b.symm ▸ hends_I.2.2.2.1.1
    have hb'V : cuffPoint f τb' ∈ Γ.V := hcp_b'.symm ▸ hends_I'.2.2.2.1.1
    have hI_pair : (α = τa ∧ β = τb) ∨ (α = τb ∧ β = τa) := by
      rcases hI_ab with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨cuffPoint_injOn_Ico f t₀ ⟨hα_ge, (hαβ.trans hβ_le).trans_lt hlt⟩
            ⟨hτa.1, hτa.2.trans_lt hlt⟩ (h1.trans hcp_a.symm),
          cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hαβ, hβ_le.trans_lt hlt⟩
            ⟨hτb.1, hτb.2.trans_lt hlt⟩ (h2.trans hcp_b.symm)⟩
      · right
        exact ⟨cuffPoint_injOn_Ico f t₀ ⟨hα_ge, (hαβ.trans hβ_le).trans_lt hlt⟩
            ⟨hτb.1, hτb.2.trans_lt hlt⟩ (h1.trans hcp_b.symm),
          cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hαβ, hβ_le.trans_lt hlt⟩
            ⟨hτa.1, hτa.2.trans_lt hlt⟩ (h2.trans hcp_a.symm)⟩
    have hI'_pair : (α' = τa' ∧ β' = τb') ∨ (α' = τb' ∧ β' = τa') := by
      rcases hI'_a'b' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨cuffPoint_injOn_Ico f t₀ ⟨hα'_ge, (hα'β'.trans hβ'_le).trans_lt hlt⟩
            ⟨hτa'.1, hτa'.2.trans_lt hlt⟩ (h1.trans hcp_a'.symm),
          cuffPoint_injOn_Ico f t₀ ⟨hα'_ge.trans hα'β', hβ'_le.trans_lt hlt⟩
            ⟨hτb'.1, hτb'.2.trans_lt hlt⟩ (h2.trans hcp_b'.symm)⟩
      · right
        exact ⟨cuffPoint_injOn_Ico f t₀ ⟨hα'_ge, (hα'β'.trans hβ'_le).trans_lt hlt⟩
            ⟨hτb'.1, hτb'.2.trans_lt hlt⟩ (h1.trans hcp_b'.symm),
          cuffPoint_injOn_Ico f t₀ ⟨hα'_ge.trans hα'β', hβ'_le.trans_lt hlt⟩
            ⟨hτa'.1, hτa'.2.trans_lt hlt⟩ (h2.trans hcp_a'.symm)⟩
    rcases h_ord with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · have hI_τ : I = cuffPoint f '' Icc τa τb := by
        rcases hI_pair with ⟨rfl, rfl⟩ | ⟨hα_τb, hβ_τa⟩
        · exact hI_eq
        · have h_eq : τa = τb := by linarith
          rw [hI_eq, hα_τb, hβ_τa, h_eq]
      have hI'_τ : I' = cuffPoint f '' Icc τa' τb' := by
        rcases hI'_pair with ⟨rfl, rfl⟩ | ⟨hα'_τb', hβ'_τa'⟩
        · exact hI'_eq
        · have h_eq : τa' = τb' := by linarith
          rw [hI'_eq, hα'_τb', hβ'_τa', h_eq]
      refine ⟨cuffPoint f '' Icc τb τb', ?_, ?_, ?_, ?_⟩
      · rw [hF_eq]; exact image_mono (Icc_subset_Icc hτb.1 hτb'.2)
      · rw [← hcp_b, ← hcp_b']
        exact supportHasEnds_cuffPoint_Icc hS hC f hτb.1 (h2.trans h3) hτb'.2 hlt hbV hb'V
      · rw [hI_τ, ← hcp_b]
        exact (cuffPoint_Icc_split f hτa.1 h1 (h2.trans h3) hτb'.2 hlt).2
      · rw [hI'_τ]
        exact image_mono (Icc_subset_Icc_left h2)
    · have hI_τ : I = cuffPoint f '' Icc τb τa := by
        rcases hI_pair with ⟨hα_τa, hβ_τb⟩ | ⟨rfl, rfl⟩
        · have h_eq : τa = τb := by linarith
          rw [hI_eq, hα_τa, hβ_τb, h_eq]
        · exact hI_eq
      have hI'_τ : I' = cuffPoint f '' Icc τb' τa' := by
        rcases hI'_pair with ⟨hα'_τa', hβ'_τb'⟩ | ⟨rfl, rfl⟩
        · have h_eq : τa' = τb' := by linarith
          rw [hI'_eq, hα'_τa', hβ'_τb', h_eq]
        · exact hI'_eq
      refine ⟨cuffPoint f '' Icc τb' τb, ?_, ?_, ?_, ?_⟩
      · rw [hF_eq]; exact image_mono (Icc_subset_Icc hτb'.1 hτb.2)
      · rw [← hcp_b, ← hcp_b']
        exact supportHasEnds_symm
          (supportHasEnds_cuffPoint_Icc hS hC f hτb'.1 (h1.trans h2) hτb.2 hlt hb'V hbV)
      · rw [hI_τ, inter_comm, ← hcp_b]
        exact (cuffPoint_Icc_split f hτb'.1 (h1.trans h2) h3 hτa.2 hlt).2
      · rw [hI'_τ]
        exact image_mono (Icc_subset_Icc_right h2)

/-- If `a, b, a', b' ∈ F_star j ∩ Γ.V` are in order in `F_star j` with supports `I, I' ⊆ F_star j`
(encoded by `SupportHasEnds Γ I a b`, `SupportHasEnds Γ I' a' b'`, and an auxiliary support
`J ⊆ F_star j` with `SupportHasEnds Γ J b b'`, `I ∩ J = {b}`, and `I' ⊆ J`; see
`exists_support_J_iff_areInOrderInSupport`), then
`(supportGraph G Γ μ I).vertexSet ∩ (supportGraph G Γ μ I').vertexSet ⊆ (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet`. -/
theorem supportGraph_inter_subset_of_in_order
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {a b a' b' : S} {I I' J : Set S}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' a' b')
    (hJ_sub : J ⊆ F_star j) (hJ_ends : SupportHasEnds Γ J b b')
    (hIJ_inter : I ∩ J = {b}) (hI'J : I' ⊆ J) :
    (supportGraph G Γ μ I).vertexSet ∩ (supportGraph G Γ μ I').vertexSet ⊆
      (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet := by
  have hS := h_pres.is_surface
  rcases h_pres.supports_isSupport j with ⟨endA, endB, hFj_ends⟩
  obtain ⟨C, hC, hFjC⟩ := exists_cuff_of_supportHasEnds hFj_ends
  let f := cuffHomeo hS hC
  have hends_Fj := ends_mem_of_supportHasEnds hFj_ends
  obtain ⟨t₀, ht₀_Ico, t₁, ⟨hle, hlt⟩, h_ab_Fj, hFj_eq, _⟩ :=
    support_eq_cuffPoint_Icc hS hC f hFj_ends hFjC
  have ht₀_mem : cuffPoint f t₀ ∈ Γ.V ∩ C := by
    refine ⟨?_, cuffPoint_mem f t₀⟩
    rcases h_ab_Fj with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · exact hends_Fj.2.2.1.1
    · exact hends_Fj.2.2.2.1.1
  have ht₁V : cuffPoint f t₁ ∈ Γ.V := by
    rcases h_ab_Fj with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]
    · exact hends_Fj.2.2.2.1.1
    · exact hends_Fj.2.2.1.1
  obtain ⟨α, β, hα_ge, hαβ, hβ_le, hI_ab, hI_eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hFj_eq hI_sub hI_ends
  obtain ⟨γ, δ, hγ_ge, hγδ, hδ_le, hJ_bb', hJ_eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hFj_eq hJ_sub hJ_ends
  obtain ⟨α', β', hα'_ge, hα'β', hβ'_le, hI'_a'b', hI'_eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hFj_eq hI'_sub hI'_ends
  have hbV : b ∈ Γ.V := (ends_mem_of_supportHasEnds hI_ends).2.2.2.1.1
  have ha'V : a' ∈ Γ.V := (ends_mem_of_supportHasEnds hI'_ends).2.2.1.1
  -- Since `I' = cuffPoint f '' Icc α' β' ⊆ J = cuffPoint f '' Icc γ δ`, we have `γ ≤ α'` and `β' ≤ δ`.
  have hγ_le_α' : γ ≤ α' := by
    have hmem : cuffPoint f α' ∈ cuffPoint f '' Icc γ δ :=
      hJ_eq ▸ hI'J (hI'_eq ▸ ⟨α', ⟨le_rfl, hα'β'⟩, rfl⟩)
    rcases hmem with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
    have h := cuffPoint_injOn_Ico f t₀ ⟨hγ_ge.trans hs1, (hs2.trans hδ_le).trans_lt hlt⟩
      ⟨hα'_ge, (hα'β'.trans hβ'_le).trans_lt hlt⟩ hs_eq
    linarith
  have hβ'_le_δ : β' ≤ δ := by
    have hmem : cuffPoint f β' ∈ cuffPoint f '' Icc γ δ :=
      hJ_eq ▸ hI'J (hI'_eq ▸ ⟨β', ⟨hα'β', le_rfl⟩, rfl⟩)
    rcases hmem with ⟨s, ⟨hs1, hs2⟩, hs_eq⟩
    have h := cuffPoint_injOn_Ico f t₀ ⟨hγ_ge.trans hs1, (hs2.trans hδ_le).trans_lt hlt⟩
      ⟨hα'_ge.trans hα'β', hβ'_le.trans_lt hlt⟩ hs_eq
    linarith
  -- Distinguish the two orientations of `J = [γ, δ]` with ends `{b, b'}`.
  rcases hJ_bb' with ⟨hγ_b, hδ_b'⟩ | ⟨hγ_b', hδ_b⟩
  · -- Orientation 1: `cuffPoint f γ = b` and `cuffPoint f δ = b'`.
    have hγ_in_I : cuffPoint f γ ∈ cuffPoint f '' Icc α β := by
      rw [← hI_eq, hγ_b]
      exact (ends_mem_of_supportHasEnds hI_ends).2.1
    rcases hγ_in_I with ⟨τb, ⟨hτb1, hτb2⟩, hτb_eq⟩
    have hτb_γ : τb = γ :=
      cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hτb1, (hτb2.trans hβ_le).trans_lt hlt⟩
        ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ hτb_eq
    subst τb
    -- Show `β = γ` using `I ∩ J = {b}`.
    have hmin_in_IJ : cuffPoint f (min β δ) ∈ I ∩ J := by
      refine ⟨?_, ?_⟩
      · rw [hI_eq]; exact ⟨min β δ, ⟨hτb1.trans (le_min hτb2 hγδ), min_le_left β δ⟩, rfl⟩
      · rw [hJ_eq]; exact ⟨min β δ, ⟨le_min hτb2 hγδ, min_le_right β δ⟩, rfl⟩
    rw [hIJ_inter, mem_singleton_iff, ← hγ_b] at hmin_in_IJ
    have hmin_eq_γ : min β δ = γ :=
      cuffPoint_injOn_Ico f t₀
        ⟨(hγ_ge).trans (le_min hτb2 hγδ), ((min_le_left β δ).trans hβ_le).trans_lt hlt⟩
        ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ hmin_in_IJ
    -- Also `b' = cuffPoint f δ` is an end of `I' = [α', β']` with `α' ≤ β' ≤ δ`, so `cuffPoint f α' = a'`.
    have hα'_a' : cuffPoint f α' = a' := by
      rcases hI'_a'b' with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · have hα'_eq_δ : α' = δ :=
          cuffPoint_injOn_Ico f t₀ ⟨hα'_ge, (hα'β'.trans hβ'_le).trans_lt hlt⟩
            ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ (h1.trans hδ_b'.symm)
        have hα'_eq_β' : α' = β' := by linarith
        rw [hα'_eq_β', h2]
    rcases min_cases β δ with ⟨hmin_β, _⟩ | ⟨hmin_δ, _⟩
    · have hβ_eq_γ : β = γ := by linarith
      have hsub_b : (supportGraph G Γ μ I).vertexSet ∩ (supportGraph G Γ μ I').vertexSet ⊆
          (μ (.vertex b)).vertexSet := by
        rw [← hγ_b]
        exact supportGraph_inter_vertexSet_subset_of_angle_between h_pres j hC f ht₀_mem ht₁V
          hle hlt hFj_eq hα_ge hαβ hβ_eq_γ.le hγ_le_α' hα'β' hβ'_le hI_eq hI'_eq (hγ_b.symm ▸ hbV)
      have hsub_a' : (supportGraph G Γ μ I).vertexSet ∩ (supportGraph G Γ μ I').vertexSet ⊆
          (μ (.vertex a')).vertexSet := by
        rw [← hα'_a']
        exact supportGraph_inter_vertexSet_subset_of_angle_between h_pres j hC f ht₀_mem ht₁V
          hle hlt hFj_eq hα_ge hαβ (hβ_eq_γ.le.trans hγ_le_α') le_rfl hα'β' hβ'_le hI_eq hI'_eq
          (hα'_a'.symm ▸ ha'V)
      exact subset_inter hsub_b hsub_a'
    · -- Degenerate case `δ = γ`: then `α' = β' = γ`, so `I' = {b}` and `a' = b`.
      have hα'_eq_γ : α' = γ := by linarith
      have hβ'_eq_γ : β' = γ := by linarith
      have ha'_eq_b : a' = b := by rw [← hα'_a', hα'_eq_γ, hγ_b]
      have hI'_singleton : I' = {b} := by
        rw [hI'_eq, hα'_eq_γ, hβ'_eq_γ, Icc_self, image_singleton, hγ_b]
      rw [hI'_singleton, ha'_eq_b, inter_self]
      exact inter_subset_right.trans (supportGraph_singleton_vertex_subset hbV)
  · -- Orientation 2: `cuffPoint f γ = b'` and `cuffPoint f δ = b`.
    have hδ_in_I : cuffPoint f δ ∈ cuffPoint f '' Icc α β := by
      rw [← hI_eq, hδ_b]
      exact (ends_mem_of_supportHasEnds hI_ends).2.1
    rcases hδ_in_I with ⟨τb, ⟨hτb1, hτb2⟩, hτb_eq⟩
    have hτb_δ : τb = δ :=
      cuffPoint_injOn_Ico f t₀ ⟨hα_ge.trans hτb1, (hτb2.trans hβ_le).trans_lt hlt⟩
        ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ hτb_eq
    subst τb
    -- Use `I ∩ J = {b}`.
    have hmax_in_IJ : cuffPoint f (max α γ) ∈ I ∩ J := by
      refine ⟨?_, ?_⟩
      · rw [hI_eq]; exact ⟨max α γ, ⟨le_max_left α γ, (max_le hτb1 hγδ).trans hτb2⟩, rfl⟩
      · rw [hJ_eq]; exact ⟨max α γ, ⟨le_max_right α γ, max_le hτb1 hγδ⟩, rfl⟩
    rw [hIJ_inter, mem_singleton_iff, ← hδ_b] at hmax_in_IJ
    have hmax_eq_δ : max α γ = δ :=
      cuffPoint_injOn_Ico f t₀
        ⟨hα_ge.trans (le_max_left α γ), ((max_le hτb1 hγδ).trans hδ_le).trans_lt hlt⟩
        ⟨hγ_ge.trans hγδ, hδ_le.trans_lt hlt⟩ hmax_in_IJ
    -- Also `b' = cuffPoint f γ` is an end of `I' = [α', β']` with `γ ≤ α' ≤ β'`, so `cuffPoint f β' = a'`.
    have hβ'_a' : cuffPoint f β' = a' := by
      rcases hI'_a'b' with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hβ'_eq_γ : β' = γ :=
          cuffPoint_injOn_Ico f t₀ ⟨hα'_ge.trans hα'β', hβ'_le.trans_lt hlt⟩
            ⟨hγ_ge, (hγδ.trans hδ_le).trans_lt hlt⟩ (h2.trans hγ_b'.symm)
        have hα'_eq_β' : α' = β' := by linarith
        rw [← hα'_eq_β', h1]
      · exact h2
    rcases max_cases α γ with ⟨hmax_α, _⟩ | ⟨hmax_γ, _⟩
    · have hα_eq_δ : α = δ := by linarith
      have hsub_b : (supportGraph G Γ μ I').vertexSet ∩ (supportGraph G Γ μ I).vertexSet ⊆
          (μ (.vertex b)).vertexSet := by
        rw [← hδ_b]
        exact supportGraph_inter_vertexSet_subset_of_angle_between h_pres j hC f ht₀_mem ht₁V
          hle hlt hFj_eq hα'_ge hα'β' hβ'_le_δ hα_eq_δ.symm.le hαβ hβ_le hI'_eq hI_eq (hδ_b.symm ▸ hbV)
      have hsub_a' : (supportGraph G Γ μ I').vertexSet ∩ (supportGraph G Γ μ I).vertexSet ⊆
          (μ (.vertex a')).vertexSet := by
        rw [← hβ'_a']
        exact supportGraph_inter_vertexSet_subset_of_angle_between h_pres j hC f ht₀_mem ht₁V
          hle hlt hFj_eq hα'_ge hα'β' le_rfl (hβ'_le_δ.trans hα_eq_δ.symm.le) hαβ hβ_le hI'_eq hI_eq
          (hβ'_a'.symm ▸ ha'V)
      rw [inter_comm (supportGraph G Γ μ I).vertexSet]
      exact subset_inter hsub_b hsub_a'
    · -- Degenerate case `γ = δ`: then `α' = β' = δ`, so `I' = {b}` and `a' = b`.
      have hα'_eq_δ : α' = δ := by linarith
      have hβ'_eq_δ : β' = δ := by linarith
      have ha'_eq_b : a' = b := by rw [← hβ'_a', hβ'_eq_δ, hδ_b]
      have hI'_singleton : I' = {b} := by
        rw [hI'_eq, hα'_eq_δ, hβ'_eq_δ, Icc_self, image_singleton, hδ_b]
      rw [hI'_singleton, ha'_eq_b, inter_self]
      exact inter_subset_right.trans (supportGraph_singleton_vertex_subset hbV)

/-! ## 3. Graph Minors XXI, `(6.1)` (`theorem_6_1_proof`) -/

/-- **Graph Minors XXI, (6.1)(i)** (page 22 of the preprint):
"**6.1** *Let* $\Gamma, F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ *be a presentation of* $G$ *in*
$\Sigma$. *Let* $a, b, a', b' \in F_1^* \cap V(\Gamma)$ *be in order and let* $I, I' \subseteq F_1^*$
*be the supports with ends* $a, b$ *and* $a', b'$ *respectively. Let* $|\mu(a)| = q$; *let*
$P_1, \dots, P_q$ *be mutually vertex-disjoint paths of* $\mu(I)$ *between* $V(\mu(a))$ *and*
$V(\mu(b))$; *and let* $P_1', \dots, P_q'$ *be mutually vertex-disjoint paths of* $\mu(I')$ *between*
$V(\mu(a'))$ *and* $V(\mu(b'))$.
(i) *For* $1 \le i, i' \le q$, *if* $v \in V(P_i \cap P_{i'}')$, *then*
$v \in V(\mu(b) \cap \mu(a'))$ *and* $v$ *is an end of* $P_i$ *and of* $P_{i'}'$."

The hypothesis that $a, b, a', b' \in F_j^* \cap V(\Gamma)$ are in order along the support $F_j^*$
(with $I, I' \subseteq F_j^*$ the supports with ends $a, b$ and $a', b'$) is stated by the binders
`hJ_sub : J ⊆ F_star j`, `hJ_ends : SupportHasEnds Γ J b b'`, `hIJ_inter : I ∩ J = {b}`, and
`hI'J : I' ⊆ J`: by `exists_support_J_iff_areInOrderInSupport`, the existence of such a support `J`
is equivalent to $a, b, a', b'$ occurring in monotone parameter order along $F_j^*$. -/
theorem theorem_6_1_i
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {a b a' b' : S} {I I' J : Set S}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' a' b')
    (hJ_sub : J ⊆ F_star j) (hJ_ends : SupportHasEnds Γ J b b')
    (hIJ_inter : I ∩ J = {b}) (hI'J : I' ⊆ J)
    {uP vP uP' vP' : Fin (q j) → α}
    (P : ∀ i : Fin (q j), (supportGraph G Γ μ I).skeleton.Walk (uP i) (vP i))
    (P' : ∀ i : Fin (q j), (supportGraph G Γ μ I').skeleton.Walk (uP' i) (vP' i))
    (huP : ∀ i, uP i ∈ (μ (.vertex a)).vertexSet)
    (hvP : ∀ i, vP i ∈ (μ (.vertex b)).vertexSet)
    (hP_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support})
    (huP' : ∀ i, uP' i ∈ (μ (.vertex a')).vertexSet)
    (_hvP' : ∀ i, vP' i ∈ (μ (.vertex b')).vertexSet)
    (hP'_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P' i₁).support} {x | x ∈ (P' i₂).support})
    (i i' : Fin (q j)) {v : α}
    (hv_P : v ∈ (P i).support) (hv_P' : v ∈ (P' i').support) :
    v ∈ (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet ∧
    v = vP i ∧ v = uP' i' := by
  have hends_I := ends_mem_of_supportHasEnds hI_ends
  have hends_I' := ends_mem_of_supportHasEnds hI'_ends
  have ha_Fj : a ∈ Γ.V ∩ F_star j := ⟨hends_I.2.2.1.1, hI_sub hends_I.1⟩
  have hb_Fj : b ∈ Γ.V ∩ F_star j := ⟨hends_I.2.2.2.1.1, hI_sub hends_I.2.1⟩
  have ha'_Fj : a' ∈ Γ.V ∩ F_star j := ⟨hends_I'.2.2.1.1, hI'_sub hends_I'.1⟩
  have hμa_G : μ (.vertex a) ≤ G := (h_pres.μ_vertex_sub j a ha_Fj).1.trans (h_pres.v1_sub j)
  have hμa'_G : μ (.vertex a') ≤ G := (h_pres.μ_vertex_sub j a' ha'_Fj).1.trans (h_pres.v1_sub j)
  have huP_I : uP i ∈ (supportGraph G Γ μ I).vertexSet :=
    vertex_mu_subset_supportGraph ⟨ha_Fj.1, hends_I.1⟩ hμa_G (huP i)
  have huP'_I' : uP' i' ∈ (supportGraph G Γ μ I').vertexSet :=
    vertex_mu_subset_supportGraph ⟨ha'_Fj.1, hends_I'.1⟩ hμa'_G (huP' i')
  have hv_I : v ∈ (supportGraph G Γ μ I).vertexSet :=
    mem_vertexSet_of_mem_walk_support_sec6 huP_I (P i) hv_P
  have hv_I' : v ∈ (supportGraph G Γ μ I').vertexSet :=
    mem_vertexSet_of_mem_walk_support_sec6 huP'_I' (P' i') hv_P'
  have hv_inter : v ∈ (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet :=
    supportGraph_inter_subset_of_in_order h_pres j hI_sub hI_ends hI'_sub hI'_ends
      hJ_sub hJ_ends hIJ_inter hI'J ⟨hv_I, hv_I'⟩
  have hb_card : (μ (.vertex b)).vertexSet.ncard = q j :=
    (h_pres.μ_vertex_sub j b hb_Fj).2.2.1
  have ha'_card : (μ (.vertex a')).vertexSet.ncard = q j :=
    (h_pres.μ_vertex_sub j a' ha'_Fj).2.2.1
  have hv_eq_vP : v = vP i :=
    (end_eq_of_mem_support_of_disjoint_walks P (μ (.vertex b)).vertexSet_finite
      hb_card hvP hP_disj).2.2 i hv_inter.1 hv_P
  have hv_eq_uP' : v = uP' i' :=
    (start_eq_of_mem_support_of_disjoint_walks P' (μ (.vertex a')).vertexSet_finite
      ha'_card huP' hP'_disj).2.2 i' hv_inter.2 hv_P'
  exact ⟨hv_inter, hv_eq_vP, hv_eq_uP'⟩

/-- **Graph Minors XXI, (6.1)(ii)** (page 22 of the preprint):
"(ii) *If* $a' = b$, *then* $P_1, \dots, P_q$ *can be renumbered so that*
$P_1 \cup P_1', \dots, P_q \cup P_q'$ *are mutually vertex-disjoint paths of* $\mu(I \cup I')$
*between* $V(\mu(a))$ *and* $V(\mu(b'))$."

As in `theorem_6_1_i`, the binders `hJ_sub : J ⊆ F_star j`, `hJ_ends : SupportHasEnds Γ J b b'`,
`hIJ_inter : I ∩ J = {b}`, and `hI'J : I' ⊆ J` state that $a, b, a', b'$ are in order along
$F_j^*$ (see `exists_support_J_iff_areInOrderInSupport`). -/
theorem theorem_6_1_ii
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {a b a' b' : S} {I I' J : Set S}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' a' b')
    (hJ_sub : J ⊆ F_star j) (hJ_ends : SupportHasEnds Γ J b b')
    (hIJ_inter : I ∩ J = {b}) (hI'J : I' ⊆ J)
    {uP vP uP' vP' : Fin (q j) → α}
    (P : ∀ i : Fin (q j), (supportGraph G Γ μ I).skeleton.Walk (uP i) (vP i))
    (P' : ∀ i : Fin (q j), (supportGraph G Γ μ I').skeleton.Walk (uP' i) (vP' i))
    (huP : ∀ i, uP i ∈ (μ (.vertex a)).vertexSet)
    (hvP : ∀ i, vP i ∈ (μ (.vertex b)).vertexSet)
    (hP_path : ∀ i, (P i).IsPath)
    (hP_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support})
    (huP' : ∀ i, uP' i ∈ (μ (.vertex a')).vertexSet)
    (hvP' : ∀ i, vP' i ∈ (μ (.vertex b')).vertexSet)
    (hP'_path : ∀ i, (P' i).IsPath)
    (hP'_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P' i₁).support} {x | x ∈ (P' i₂).support})
    (ha'b : a' = b) :
    ∃ (σ : Equiv.Perm (Fin (q j))) (hσ : ∀ i : Fin (q j), vP (σ i) = uP' i),
      let Q : ∀ i : Fin (q j),
          (supportGraph G Γ μ (I ∪ I')).skeleton.Walk (uP (σ i)) (vP' i) :=
        fun i =>
          ((P (σ i)).mapLe (supportGraph_skeleton_mono subset_union_left)).append
            (((P' i).copy (hσ i).symm rfl).mapLe (supportGraph_skeleton_mono subset_union_right))
      (∀ i : Fin (q j), uP (σ i) ∈ (μ (.vertex a)).vertexSet) ∧
      (∀ i : Fin (q j), vP' i ∈ (μ (.vertex b')).vertexSet) ∧
      (∀ i : Fin (q j), (Q i).IsPath) ∧
      (∀ i₁ i₂ : Fin (q j), i₁ ≠ i₂ →
        Disjoint {x | x ∈ (Q i₁).support} {x | x ∈ (Q i₂).support}) := by
  have hends_I := ends_mem_of_supportHasEnds hI_ends
  have hb_Fj : b ∈ Γ.V ∩ F_star j := ⟨hends_I.2.2.2.1.1, hI_sub hends_I.2.1⟩
  have hb_card : (μ (.vertex b)).vertexSet.ncard = q j :=
    (h_pres.μ_vertex_sub j b hb_Fj).2.2.1
  have huP'_b : ∀ i : Fin (q j), uP' i ∈ (μ (.vertex b)).vertexSet :=
    fun i => ha'b ▸ huP' i
  obtain ⟨hvP_inj, hvP_range, _⟩ :=
    end_eq_of_mem_support_of_disjoint_walks P (μ (.vertex b)).vertexSet_finite hb_card hvP hP_disj
  have hex_σ : ∀ i : Fin (q j), ∃ k : Fin (q j), vP k = uP' i := by
    intro i
    have hmem : uP' i ∈ Set.range vP := hvP_range.symm ▸ huP'_b i
    exact hmem
  choose σ_fun hσ_fun using hex_σ
  have hσ_inj : Function.Injective σ_fun := by
    intro i₁ i₂ h_eq
    have h_uP' : uP' i₁ = uP' i₂ := by rw [← hσ_fun i₁, ← hσ_fun i₂, h_eq]
    have huP'_inj :=
      (start_eq_of_mem_support_of_disjoint_walks P' (μ (.vertex b)).vertexSet_finite hb_card huP'_b hP'_disj).1
    exact huP'_inj h_uP'
  let σ : Equiv.Perm (Fin (q j)) :=
    Equiv.ofBijective σ_fun (Finite.injective_iff_bijective.mp hσ_inj)
  have hσ : ∀ i : Fin (q j), vP (σ i) = uP' i := hσ_fun
  have hle_I : (supportGraph G Γ μ I).skeleton ≤ (supportGraph G Γ μ (I ∪ I')).skeleton :=
    supportGraph_skeleton_mono subset_union_left
  have hle_I' : (supportGraph G Γ μ I').skeleton ≤ (supportGraph G Γ μ (I ∪ I')).skeleton :=
    supportGraph_skeleton_mono subset_union_right
  let Q : ∀ i : Fin (q j), (supportGraph G Γ μ (I ∪ I')).skeleton.Walk (uP (σ i)) (vP' i) :=
    fun i => ((P (σ i)).mapLe hle_I).append (((P' i).copy (hσ i).symm rfl).mapLe hle_I')
  have hQ_supp : ∀ i (z : α), z ∈ (Q i).support ↔ z ∈ (P (σ i)).support ∨ z ∈ (P' i).support := by
    intro i z
    dsimp [Q]
    rw [SimpleGraph.Walk.mem_support_append_iff, SimpleGraph.Walk.support_mapLe_eq_support,
      SimpleGraph.Walk.support_mapLe_eq_support, SimpleGraph.Walk.support_copy]
  refine ⟨σ, hσ, fun i => huP (σ i), hvP', ?_, ?_⟩
  · -- Each `Q i` is a simple path (`IsPath`)
    intro i
    rw [SimpleGraph.Walk.isPath_def]
    dsimp [Q]
    rw [SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_mapLe_eq_support,
      SimpleGraph.Walk.support_mapLe_eq_support, SimpleGraph.Walk.support_copy,
      List.nodup_append']
    refine ⟨(hP_path (σ i)).support_nodup, (hP'_path i).support_nodup.sublist (List.tail_sublist _), ?_⟩
    rw [List.disjoint_left]
    intro z hz₁ hz₂
    have hz₂_supp : z ∈ (P' i).support := List.mem_of_mem_tail hz₂
    have h_i := theorem_6_1_i h_pres j hI_sub hI_ends hI'_sub hI'_ends
      hJ_sub hJ_ends hIJ_inter hI'J P P' huP hvP hP_disj huP' hvP' hP'_disj
      (σ i) i hz₁ hz₂_supp
    have hz_eq : z = uP' i := h_i.2.2
    have hnodup' : (P' i).support.Nodup := (hP'_path i).support_nodup
    rw [← SimpleGraph.Walk.cons_tail_support (P' i), List.nodup_cons] at hnodup'
    exact hnodup'.1 (hz_eq ▸ hz₂)
  · -- Pairwise vertex-disjointness of `Q i₁` and `Q i₂` for `i₁ ≠ i₂`
    intro i₁ i₂ hne
    rw [Set.disjoint_left]
    intro z hz₁ hz₂
    rw [mem_ofPred_eq, hQ_supp i₁ z] at hz₁
    rw [mem_ofPred_eq, hQ_supp i₂ z] at hz₂
    rcases hz₁ with hz₁ | hz₁ <;> rcases hz₂ with hz₂ | hz₂
    · exact Set.disjoint_left.mp (hP_disj (σ i₁) (σ i₂) (σ.injective.ne hne)) hz₁ hz₂
    · have h_i := theorem_6_1_i h_pres j hI_sub hI_ends hI'_sub hI'_ends
        hJ_sub hJ_ends hIJ_inter hI'J P P' huP hvP hP_disj huP' hvP' hP'_disj
        (σ i₁) i₂ hz₁ hz₂
      have hv_eq : vP (σ i₁) = vP (σ i₂) := by
        rw [← h_i.2.1, h_i.2.2, ← hσ i₂]
      exact hne (σ.injective (hvP_inj hv_eq))
    · have h_i := theorem_6_1_i h_pres j hI_sub hI_ends hI'_sub hI'_ends
        hJ_sub hJ_ends hIJ_inter hI'J P P' huP hvP hP_disj huP' hvP' hP'_disj
        (σ i₂) i₁ hz₂ hz₁
      have hv_eq : vP (σ i₂) = vP (σ i₁) := by
        rw [← h_i.2.1, h_i.2.2, ← hσ i₁]
      exact hne.symm (σ.injective (hvP_inj hv_eq))
    · exact Set.disjoint_left.mp (hP'_disj i₁ i₂ hne) hz₁ hz₂

/-- Existential (`HasDisjointPaths`) corollary of `theorem_6_1_ii`. -/
theorem theorem_6_1_ii_exists
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {a b b' : S} {I I' : Set S}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' b b')
    (hII'_inter : I ∩ I' = {b})
    (hP : HasDisjointPaths (supportGraph G Γ μ I).skeleton
      (μ (.vertex a)).vertexSet (μ (.vertex b)).vertexSet (q j))
    (hP' : HasDisjointPaths (supportGraph G Γ μ I').skeleton
      (μ (.vertex b)).vertexSet (μ (.vertex b')).vertexSet (q j)) :
    HasDisjointPaths (supportGraph G Γ μ (I ∪ I')).skeleton
      (μ (.vertex a)).vertexSet (μ (.vertex b')).vertexSet (q j) := by
  rw [hasDisjointPaths_iff_walks] at hP hP' ⊢
  rcases hP with ⟨uP, vP, P, huP, hvP, hP_path, hP_disj⟩
  rcases hP' with ⟨uP', vP', P', huP', hvP', hP'_path, hP'_disj⟩
  obtain ⟨σ, hσ, huQ, hvQ, hQ_path, hQ_disj⟩ :=
    theorem_6_1_ii h_pres j hI_sub hI_ends hI'_sub hI'_ends hI'_sub hI'_ends hII'_inter Subset.rfl
      P P' huP hvP hP_path hP_disj huP' hvP' hP'_path hP'_disj rfl
  exact ⟨fun i => uP (σ i), vP', _, huQ, hvQ, hQ_path, hQ_disj⟩

/-- A path with equal start and end vertices is the nil walk, so its `toSubgraph` is the singleton
subgraph at its start vertex. -/
private lemma toSubgraph_eq_singletonSubgraph_of_isPath_of_eq {V : Type*} {G_sk : SimpleGraph V}
    {u v : V} {w : G_sk.Walk u v} (hp : w.IsPath) (huv : u = v) :
    w.toSubgraph = G_sk.singletonSubgraph u := by
  have hnil : w.Nil := (SimpleGraph.Walk.IsPath.nil_iff_eq hp).mpr huv
  cases w with
  | nil => rfl
  | cons _ _ => cases hnil

/-- Two walks with disjoint supports have distinct `toSubgraph`s. -/
private lemma toSubgraph_ne_of_disjoint_support {V : Type*} {G_sk : SimpleGraph V}
    {u₁ v₁ u₂ v₂ : V} {w₁ : G_sk.Walk u₁ v₁} {w₂ : G_sk.Walk u₂ v₂}
    (hdisj : Disjoint {x | x ∈ w₁.support} {x | x ∈ w₂.support}) :
    w₁.toSubgraph ≠ w₂.toSubgraph := by
  intro heq
  have h₁ : u₁ ∈ {x | x ∈ w₁.support} := w₁.start_mem_support
  have h₂ : u₁ ∈ {x | x ∈ w₂.support} := by
    rw [← SimpleGraph.Walk.verts_toSubgraph, ← heq, SimpleGraph.Walk.verts_toSubgraph]
    exact h₁
  exact Set.disjoint_left.mp hdisj h₁ h₂

/-- **Graph Minors XXI, (6.1)(iii)** (page 22 of the preprint):
"(iii) *If* $|\mu(a) \cup \mu(b')| = |\mu(a') \cup \mu(b)| = k$ *say, then*
$\{P_1, \dots, P_q, P_1', \dots, P_q'\}$ *has cardinality* $k$, *and its members are* $k$
*mutually vertex-disjoint paths of* $\mu(I) \cup \mu(I')$ *between* $V(\mu(a) \cup \mu(b'))$
*and* $V(\mu(b) \cup \mu(a'))$."

As in `theorem_6_1_i`, the binders `hJ_sub : J ⊆ F_star j`, `hJ_ends : SupportHasEnds Γ J b b'`,
`hIJ_inter : I ∩ J = {b}`, and `hI'J : I' ⊆ J` state that $a, b, a', b'$ are in order along
$F_j^*$ (see `exists_support_J_iff_areInOrderInSupport`). -/
theorem theorem_6_1_iii
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {a b a' b' : S} {I I' J : Set S} {k : ℕ}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' a' b')
    (hJ_sub : J ⊆ F_star j) (hJ_ends : SupportHasEnds Γ J b b')
    (hIJ_inter : I ∩ J = {b}) (hI'J : I' ⊆ J)
    {uP vP uP' vP' : Fin (q j) → α}
    (P : ∀ i : Fin (q j), (supportGraph G Γ μ I).skeleton.Walk (uP i) (vP i))
    (P' : ∀ i : Fin (q j), (supportGraph G Γ μ I').skeleton.Walk (uP' i) (vP' i))
    (huP : ∀ i, uP i ∈ (μ (.vertex a)).vertexSet)
    (hvP : ∀ i, vP i ∈ (μ (.vertex b)).vertexSet)
    (hP_path : ∀ i, (P i).IsPath)
    (hP_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support})
    (huP' : ∀ i, uP' i ∈ (μ (.vertex a')).vertexSet)
    (hvP' : ∀ i, vP' i ∈ (μ (.vertex b')).vertexSet)
    (hP'_path : ∀ i, (P' i).IsPath)
    (hP'_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P' i₁).support} {x | x ∈ (P' i₂).support})
    (hk₁ : ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet).ncard = k)
    (hk₂ : ((μ (.vertex a')).vertexSet ∪ (μ (.vertex b)).vertexSet).ncard = k) :
    let P_set : Set (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Subgraph :=
      Set.range (fun i =>
        ((P i).mapLe (skeleton_le_union_left (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph) ∪
      Set.range (fun i =>
        ((P' i).mapLe (skeleton_le_union_right (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph)
    P_set.ncard = k ∧
    (∀ Q₁ ∈ P_set, ∀ Q₂ ∈ P_set, Q₁ ≠ Q₂ → Disjoint Q₁.verts Q₂.verts) ∧
    (∀ Q ∈ P_set, ∃ (u v : α)
      (w : (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Walk u v),
      w.IsPath ∧
      u ∈ (μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet ∧
      v ∈ (μ (.vertex b)).vertexSet ∪ (μ (.vertex a')).vertexSet ∧
      w.toSubgraph = Q) := by
  have hends_I := ends_mem_of_supportHasEnds hI_ends
  have hends_I' := ends_mem_of_supportHasEnds hI'_ends
  have ha_Fj : a ∈ Γ.V ∩ F_star j := ⟨hends_I.2.2.1.1, hI_sub hends_I.1⟩
  have hb_Fj : b ∈ Γ.V ∩ F_star j := ⟨hends_I.2.2.2.1.1, hI_sub hends_I.2.1⟩
  have ha'_Fj : a' ∈ Γ.V ∩ F_star j := ⟨hends_I'.2.2.1.1, hI'_sub hends_I'.1⟩
  have hb'_Fj : b' ∈ Γ.V ∩ F_star j := ⟨hends_I'.2.2.2.1.1, hI'_sub hends_I'.2.1⟩
  have ha_card : (μ (.vertex a)).vertexSet.ncard = q j := (h_pres.μ_vertex_sub j a ha_Fj).2.2.1
  have hb_card : (μ (.vertex b)).vertexSet.ncard = q j := (h_pres.μ_vertex_sub j b hb_Fj).2.2.1
  have ha'_card : (μ (.vertex a')).vertexSet.ncard = q j := (h_pres.μ_vertex_sub j a' ha'_Fj).2.2.1
  have hb'_card : (μ (.vertex b')).vertexSet.ncard = q j := (h_pres.μ_vertex_sub j b' hb'_Fj).2.2.1
  have hμa_G : μ (.vertex a) ≤ G := (h_pres.μ_vertex_sub j a ha_Fj).1.trans (h_pres.v1_sub j)
  have hμb'_G : μ (.vertex b') ≤ G := (h_pres.μ_vertex_sub j b' hb'_Fj).1.trans (h_pres.v1_sub j)
  -- Key inclusion: `(μ a) ∩ (μ b') ⊆ (μ b) ∩ (μ a')`
  have hinter_sub : (μ (.vertex a)).vertexSet ∩ (μ (.vertex b')).vertexSet ⊆
      (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet := by
    have hsub_a : (μ (.vertex a)).vertexSet ⊆ (supportGraph G Γ μ I).vertexSet :=
      vertex_mu_subset_supportGraph ⟨ha_Fj.1, hends_I.1⟩ hμa_G
    have hsub_b' : (μ (.vertex b')).vertexSet ⊆ (supportGraph G Γ μ I').vertexSet :=
      vertex_mu_subset_supportGraph ⟨hb'_Fj.1, hends_I'.2.1⟩ hμb'_G
    exact (inter_subset_inter hsub_a hsub_b').trans
      (supportGraph_inter_subset_of_in_order h_pres j hI_sub hI_ends hI'_sub hI'_ends
        hJ_sub hJ_ends hIJ_inter hI'J)
  -- Equal union cardinalities force `(μ a) ∩ (μ b') = (μ b) ∩ (μ a')`
  have h_ie₁ := ncard_union_add_ncard_inter (μ (.vertex a)).vertexSet (μ (.vertex b')).vertexSet
    (μ (.vertex a)).vertexSet_finite (μ (.vertex b')).vertexSet_finite
  have h_ie₂ := ncard_union_add_ncard_inter (μ (.vertex a')).vertexSet (μ (.vertex b)).vertexSet
    (μ (.vertex a')).vertexSet_finite (μ (.vertex b)).vertexSet_finite
  rw [hk₁, ha_card, hb'_card] at h_ie₁
  rw [hk₂, ha'_card, hb_card, inter_comm] at h_ie₂
  have hinter_eq : (μ (.vertex a)).vertexSet ∩ (μ (.vertex b')).vertexSet =
      (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet :=
    eq_of_subset_of_ncard_le hinter_sub (by omega)
      ((μ (.vertex b)).vertexSet_finite.inter_of_left _)
  -- Whenever `uP' i' ∉ (μ (.vertex b)).vertexSet`, `(P' i').support` is disjoint from `(P i).support` for all `i`.
  have hdisj_extra : ∀ (i i' : Fin (q j)),
      uP' i' ∉ (μ (.vertex b)).vertexSet →
      Disjoint {x | x ∈ (P i).support} {x | x ∈ (P' i').support} := by
    intro i i' hnot_b
    rw [Set.disjoint_left]
    intro v hv_P hv_P'
    have h_i := theorem_6_1_i h_pres j hI_sub hI_ends hI'_sub hI'_ends
      hJ_sub hJ_ends hIJ_inter hI'J P P' huP hvP hP_disj huP' hvP' hP'_disj i i' hv_P hv_P'
    exact hnot_b (h_i.2.2 ▸ h_i.1.1)
  obtain ⟨huP_inj, huP_range, huP_start⟩ :=
    start_eq_of_mem_support_of_disjoint_walks P (μ (.vertex a)).vertexSet_finite ha_card huP hP_disj
  obtain ⟨hvP_inj, hvP_range, _⟩ :=
    end_eq_of_mem_support_of_disjoint_walks P (μ (.vertex b)).vertexSet_finite hb_card hvP hP_disj
  obtain ⟨huP'_inj, huP'_range, _⟩ :=
    start_eq_of_mem_support_of_disjoint_walks P' (μ (.vertex a')).vertexSet_finite ha'_card huP' hP'_disj
  obtain ⟨hvP'_inj, hvP'_range, hvP'_end⟩ :=
    end_eq_of_mem_support_of_disjoint_walks P' (μ (.vertex b')).vertexSet_finite hb'_card hvP' hP'_disj
  let S_extra : Finset (Fin (q j)) :=
    Finset.univ.filter (fun i' => uP' i' ∉ (μ (.vertex b)).vertexSet)
  have hS_extra_image : uP' '' (S_extra : Set (Fin (q j))) =
      (μ (.vertex a')).vertexSet \ (μ (.vertex b)).vertexSet := by
    ext v
    simp only [S_extra, Finset.coe_filter, Finset.mem_univ, true_and, mem_image, mem_ofPred_eq,
      mem_sdiff]
    constructor
    · rintro ⟨i', hnot_b, rfl⟩
      exact ⟨huP' i', hnot_b⟩
    · rintro ⟨hv_a', hnot_b⟩
      rw [← huP'_range] at hv_a'
      rcases hv_a' with ⟨i', rfl⟩
      exact ⟨i', hnot_b, rfl⟩
  have hcard_extra : S_extra.card + q j = k := by
    have h1 : (uP' '' (S_extra : Set (Fin (q j)))).ncard = S_extra.card := by
      rw [(huP'_inj.injOn).ncard_image, ncard_coe_finset]
    have h2 : ((μ (.vertex a')).vertexSet \ (μ (.vertex b)).vertexSet) ∪ (μ (.vertex b)).vertexSet =
        (μ (.vertex a')).vertexSet ∪ (μ (.vertex b)).vertexSet := sdiff_union_self
    have h3 := ncard_union_eq disjoint_sdiff_left
      (μ (.vertex a')).vertexSet_finite.sdiff (μ (.vertex b)).vertexSet_finite
    rw [h2, hk₂, ← hS_extra_image, h1, hb_card] at h3
    omega
  have hle₁ : (supportGraph G Γ μ I).skeleton ≤
      (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton :=
    skeleton_le_union_left _ _
  have hle₂ : (supportGraph G Γ μ I').skeleton ≤
      (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton :=
    skeleton_le_union_right _ _
  let K := (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton
  let f₁ : Fin (q j) → K.Subgraph := fun i => ((P i).mapLe hle₁).toSubgraph
  let f₂ : Fin (q j) → K.Subgraph := fun i => ((P' i).mapLe hle₂).toSubgraph
  have hf₁_verts : ∀ i, (f₁ i).verts = {x | x ∈ (P i).support} := by
    intro i; simp [f₁]
  have hf₂_verts : ∀ i, (f₂ i).verts = {x | x ∈ (P' i).support} := by
    intro i; simp [f₂]
  have hf₁_inj : Function.Injective f₁ := by
    intro i₁ i₂ h_eq
    by_contra hne
    refine toSubgraph_ne_of_disjoint_support ?_ h_eq
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hP_disj i₁ i₂ hne
  have hf₂_inj : Function.Injective f₂ := by
    intro i₁ i₂ h_eq
    by_contra hne
    refine toSubgraph_ne_of_disjoint_support ?_ h_eq
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hP'_disj i₁ i₂ hne
  -- Whenever `uP' i' ∈ (μ (.vertex b)).vertexSet`, `f₂ i' ∈ Set.range f₁`.
  have hf₂_in_range_f₁_of_mem_b : ∀ i' : Fin (q j),
      uP' i' ∈ (μ (.vertex b)).vertexSet → f₂ i' ∈ Set.range f₁ := by
    intro i' hmem_b
    have hmem_range : uP' i' ∈ Set.range vP := hvP_range.symm ▸ hmem_b
    rcases hmem_range with ⟨i, hi_eq⟩
    have hmem_inter : uP' i' ∈ (μ (.vertex a)).vertexSet ∩ (μ (.vertex b')).vertexSet := by
      rw [hinter_eq]
      exact ⟨hmem_b, huP' i'⟩
    have huP_eq : uP' i' = uP i :=
      huP_start i hmem_inter.1 (hi_eq ▸ (P i).end_mem_support)
    have hvP'_eq : uP' i' = vP' i' :=
      hvP'_end i' hmem_inter.2 (P' i').start_mem_support
    have hf₁_eq : f₁ i = K.singletonSubgraph (uP i) :=
      toSubgraph_eq_singletonSubgraph_of_isPath_of_eq ((hP_path i).mapLe hle₁)
        (huP_eq.symm.trans hi_eq.symm)
    have hf₂_eq : f₂ i' = K.singletonSubgraph (uP' i') :=
      toSubgraph_eq_singletonSubgraph_of_isPath_of_eq ((hP'_path i').mapLe hle₂) hvP'_eq
    exact ⟨i, by rw [hf₁_eq, hf₂_eq, huP_eq]⟩
  have hP_set_eq : Set.range f₁ ∪ Set.range f₂ =
      Set.range f₁ ∪ f₂ '' (S_extra : Set (Fin (q j))) := by
    ext Q
    simp only [mem_union, mem_range, mem_image, S_extra, Finset.coe_filter, Finset.mem_univ,
      true_and, mem_ofPred_eq]
    constructor
    · rintro (⟨i, rfl⟩ | ⟨i', rfl⟩)
      · exact Or.inl ⟨i, rfl⟩
      · by_cases hmem_b : uP' i' ∈ (μ (.vertex b)).vertexSet
        · exact Or.inl (hf₂_in_range_f₁_of_mem_b i' hmem_b)
        · exact Or.inr ⟨i', hmem_b, rfl⟩
    · rintro (⟨i, rfl⟩ | ⟨i', _, rfl⟩)
      · exact Or.inl ⟨i, rfl⟩
      · exact Or.inr ⟨i', rfl⟩
  have hdisj_f₁_f₂ : Disjoint (Set.range f₁) (f₂ '' (S_extra : Set (Fin (q j)))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨i, rfl⟩ ⟨i', hi'_extra, h_eq⟩
    simp only [S_extra, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hi'_extra
    refine toSubgraph_ne_of_disjoint_support ?_ h_eq.symm
    simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hdisj_extra i i' hi'_extra
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · -- Cardinality of `P_set` is `k`
    change (Set.range f₁ ∪ Set.range f₂).ncard = k
    rw [hP_set_eq, ncard_union_eq hdisj_f₁_f₂ (Set.toFinite _) (Set.toFinite _)]
    have hcard₁ : (Set.range f₁).ncard = q j := by
      rw [← image_univ, (hf₁_inj.injOn).ncard_image, ncard_univ, Nat.card_fin]
    have hcard₂ : (f₂ '' (S_extra : Set (Fin (q j)))).ncard = S_extra.card := by
      rw [(hf₂_inj.injOn).ncard_image, ncard_coe_finset]
    omega
  · -- Members of `P_set` are mutually vertex-disjoint
    intro Q₁ hQ₁ Q₂ hQ₂ hne
    change Q₁ ∈ Set.range f₁ ∪ Set.range f₂ at hQ₁
    change Q₂ ∈ Set.range f₁ ∪ Set.range f₂ at hQ₂
    rw [hP_set_eq] at hQ₁ hQ₂
    rcases hQ₁ with ⟨i₁, rfl⟩ | ⟨i₁', hi₁', rfl⟩ <;>
      rcases hQ₂ with ⟨i₂, rfl⟩ | ⟨i₂', hi₂', rfl⟩
    · have hij : i₁ ≠ i₂ := fun h => hne (congrArg f₁ h)
      rw [hf₁_verts, hf₁_verts]
      exact hP_disj i₁ i₂ hij
    · simp only [S_extra, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hi₂'
      rw [hf₁_verts, hf₂_verts]
      exact hdisj_extra i₁ i₂' hi₂'
    · simp only [S_extra, Finset.coe_filter, Finset.mem_univ, true_and, mem_ofPred_eq] at hi₁'
      rw [hf₂_verts, hf₁_verts]
      exact (hdisj_extra i₂ i₁' hi₁').symm
    · have hij : i₁' ≠ i₂' := fun h => hne (congrArg f₂ h)
      rw [hf₂_verts, hf₂_verts]
      exact hP'_disj i₁' i₂' hij
  · -- Each member of `𝒫` is a path of `μ(I) ∪ μ(I')` between `V(μ(a) ∪ μ(b'))` and `V(μ(b) ∪ μ(a'))`
    rintro Q (⟨i, rfl⟩ | ⟨i', rfl⟩)
    · exact ⟨uP i, vP i, (P i).mapLe hle₁, (hP_path i).mapLe hle₁,
        Or.inl (huP i), Or.inl (hvP i), rfl⟩
    · exact ⟨vP' i', uP' i', ((P' i').mapLe hle₂).reverse, ((hP'_path i').mapLe hle₂).reverse,
        Or.inr (hvP' i'), Or.inr (huP' i'), SimpleGraph.Walk.toSubgraph_reverse _⟩

/-- Existential (`HasDisjointPaths`) corollary of `theorem_6_1_iii`. -/
theorem theorem_6_1_iii_exists
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {a b a' b' : S} {I I' J : Set S} {k : ℕ}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' a' b')
    (hJ_sub : J ⊆ F_star j) (hJ_ends : SupportHasEnds Γ J b b')
    (hIJ_inter : I ∩ J = {b}) (hI'J : I' ⊆ J)
    (hk₁ : ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet).ncard = k)
    (hk₂ : ((μ (.vertex a')).vertexSet ∪ (μ (.vertex b)).vertexSet).ncard = k)
    (hP : HasDisjointPaths (supportGraph G Γ μ I).skeleton
      (μ (.vertex a)).vertexSet (μ (.vertex b)).vertexSet (q j))
    (hP' : HasDisjointPaths (supportGraph G Γ μ I').skeleton
      (μ (.vertex a')).vertexSet (μ (.vertex b')).vertexSet (q j)) :
    HasDisjointPaths (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton
      ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet)
      ((μ (.vertex b)).vertexSet ∪ (μ (.vertex a')).vertexSet) k := by
  rw [hasDisjointPaths_iff_walks] at hP hP' ⊢
  rcases hP with ⟨uP, vP, P, huP, hvP, hP_path, hP_disj⟩
  rcases hP' with ⟨uP', vP', P', huP', hvP', hP'_path, hP'_disj⟩
  have h_iii := theorem_6_1_iii h_pres j hI_sub hI_ends hI'_sub hI'_ends hJ_sub hJ_ends
    hIJ_inter hI'J P P' huP hvP hP_path hP_disj huP' hvP' hP'_path hP'_disj hk₁ hk₂
  dsimp only at h_iii
  rcases h_iii with ⟨hcard_P, hdisj_P, hpath_P⟩
  set P_set : Set (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Subgraph :=
    Set.range (fun i =>
      ((P i).mapLe (skeleton_le_union_left (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph) ∪
    Set.range (fun i =>
      ((P' i).mapLe (skeleton_le_union_right (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph)
  have hP_fin : P_set.Finite := (Set.toFinite _).union (Set.toFinite _)
  let emb :=
    (hP_fin.toFinset.equivFinOfCardEq (by
      rw [← ncard_eq_toFinset_card _ hP_fin, hcard_P])).symm
  have hemb_mem : ∀ idx : Fin k, (emb idx : (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Subgraph) ∈ P_set :=
    fun idx => hP_fin.mem_toFinset.mp (emb idx).2
  choose u_all v_all P_all hP_all_path hu_all hv_all hP_all_sub using
    fun idx : Fin k => hpath_P (emb idx).1 (hemb_mem idx)
  refine ⟨u_all, v_all, P_all, hu_all, hv_all, hP_all_path, ?_⟩
  intro idx₁ idx₂ hne
  have hQ_ne : (emb idx₁).1 ≠ (emb idx₂).1 :=
    fun h => hne (emb.injective (Subtype.ext h))
  have hdisj := hdisj_P (emb idx₁).1 (hemb_mem idx₁) (emb idx₂).1 (hemb_mem idx₂) hQ_ne
  rw [← hP_all_sub idx₁, ← hP_all_sub idx₂,
    SimpleGraph.Walk.verts_toSubgraph, SimpleGraph.Walk.verts_toSubgraph] at hdisj
  exact hdisj

/-- **Graph Minors XXI, (6.1)** (page 22 of the preprint):
"**6.1** *Let* $\Gamma, F_1^*, \dots, F_r^*, H_1, \dots, H_r, \mu$ *be a presentation of* $G$ *in*
$\Sigma$. *Let* $a, b, a', b' \in F_1^* \cap V(\Gamma)$ *be in order and let* $I, I' \subseteq F_1^*$
*be the supports with ends* $a, b$ *and* $a', b'$ *respectively. Let* $|\mu(a)| = q$; *let*
$P_1, \dots, P_q$ *be mutually vertex-disjoint paths of* $\mu(I)$ *between* $V(\mu(a))$ *and*
$V(\mu(b))$; *and let* $P_1', \dots, P_q'$ *be mutually vertex-disjoint paths of* $\mu(I')$ *between*
$V(\mu(a'))$ *and* $V(\mu(b'))$.
(i) *For* $1 \le i, i' \le q$, *if* $v \in V(P_i \cap P_{i'}')$, *then*
$v \in V(\mu(b) \cap \mu(a'))$ *and* $v$ *is an end of* $P_i$ *and of* $P_{i'}'$.
(ii) *If* $a' = b$, *then* $P_1, \dots, P_q$ *can be renumbered so that*
$P_1 \cup P_1', \dots, P_q \cup P_q'$ *are mutually vertex-disjoint paths of* $\mu(I \cup I')$
*between* $V(\mu(a))$ *and* $V(\mu(b'))$.
(iii) *If* $|\mu(a) \cup \mu(b')| = |\mu(a') \cup \mu(b)| = k$ *say, then*
$\{P_1, \dots, P_q, P_1', \dots, P_q'\}$ *has cardinality* $k$, *and its members are* $k$
*mutually vertex-disjoint paths of* $\mu(I) \cup \mu(I')$ *between* $V(\mu(a) \cup \mu(b'))$
*and* $V(\mu(b) \cup \mu(a'))$."

As in `theorem_6_1_i`, the binders `hJ_sub : J ⊆ F_star j`, `hJ_ends : SupportHasEnds Γ J b b'`,
`hIJ_inter : I ∩ J = {b}`, and `hI'J : I' ⊆ J` state that $a, b, a', b'$ are in order along
$F_j^*$ (see `exists_support_J_iff_areInOrderInSupport`). -/
theorem theorem_6_1_proof
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {a b a' b' : S} {I I' J : Set S}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b)
    (hI'_sub : I' ⊆ F_star j) (hI'_ends : SupportHasEnds Γ I' a' b')
    (hJ_sub : J ⊆ F_star j) (hJ_ends : SupportHasEnds Γ J b b')
    (hIJ_inter : I ∩ J = {b}) (hI'J : I' ⊆ J)
    {uP vP uP' vP' : Fin (q j) → α}
    (P : ∀ i : Fin (q j), (supportGraph G Γ μ I).skeleton.Walk (uP i) (vP i))
    (P' : ∀ i : Fin (q j), (supportGraph G Γ μ I').skeleton.Walk (uP' i) (vP' i))
    (huP : ∀ i, uP i ∈ (μ (.vertex a)).vertexSet)
    (hvP : ∀ i, vP i ∈ (μ (.vertex b)).vertexSet)
    (hP_path : ∀ i, (P i).IsPath)
    (hP_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P i₁).support} {x | x ∈ (P i₂).support})
    (huP' : ∀ i, uP' i ∈ (μ (.vertex a')).vertexSet)
    (hvP' : ∀ i, vP' i ∈ (μ (.vertex b')).vertexSet)
    (hP'_path : ∀ i, (P' i).IsPath)
    (hP'_disj : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint {x | x ∈ (P' i₁).support} {x | x ∈ (P' i₂).support}) :
    ((∀ (i i' : Fin (q j)) {v : α},
        v ∈ (P i).support → v ∈ (P' i').support →
        v ∈ (μ (.vertex b)).vertexSet ∩ (μ (.vertex a')).vertexSet ∧
        v = vP i ∧ v = uP' i') ∧
     (a' = b →
        ∃ (σ : Equiv.Perm (Fin (q j))) (hσ : ∀ i : Fin (q j), vP (σ i) = uP' i),
          let Q : ∀ i : Fin (q j),
              (supportGraph G Γ μ (I ∪ I')).skeleton.Walk (uP (σ i)) (vP' i) :=
            fun i =>
              ((P (σ i)).mapLe (supportGraph_skeleton_mono subset_union_left)).append
                (((P' i).copy (hσ i).symm rfl).mapLe (supportGraph_skeleton_mono subset_union_right))
          (∀ i : Fin (q j), uP (σ i) ∈ (μ (.vertex a)).vertexSet) ∧
          (∀ i : Fin (q j), vP' i ∈ (μ (.vertex b')).vertexSet) ∧
          (∀ i : Fin (q j), (Q i).IsPath) ∧
          (∀ i₁ i₂ : Fin (q j), i₁ ≠ i₂ →
            Disjoint {x | x ∈ (Q i₁).support} {x | x ∈ (Q i₂).support})) ∧
     (∀ k : ℕ,
        ((μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet).ncard = k →
        ((μ (.vertex a')).vertexSet ∪ (μ (.vertex b)).vertexSet).ncard = k →
        let P_set : Set (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Subgraph :=
          Set.range (fun i =>
            ((P i).mapLe (skeleton_le_union_left (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph) ∪
          Set.range (fun i =>
            ((P' i).mapLe (skeleton_le_union_right (supportGraph G Γ μ I) (supportGraph G Γ μ I'))).toSubgraph)
        P_set.ncard = k ∧
        (∀ Q₁ ∈ P_set, ∀ Q₂ ∈ P_set, Q₁ ≠ Q₂ → Disjoint Q₁.verts Q₂.verts) ∧
        (∀ Q ∈ P_set, ∃ (u v : α)
          (w : (supportGraph G Γ μ I ∪ supportGraph G Γ μ I').skeleton.Walk u v),
          w.IsPath ∧
          u ∈ (μ (.vertex a)).vertexSet ∪ (μ (.vertex b')).vertexSet ∧
          v ∈ (μ (.vertex b)).vertexSet ∪ (μ (.vertex a')).vertexSet ∧
          w.toSubgraph = Q))) :=
  ⟨fun i i' _ hv_P hv_P' =>
    theorem_6_1_i h_pres j hI_sub hI_ends hI'_sub hI'_ends hJ_sub hJ_ends hIJ_inter hI'J
      P P' huP hvP hP_disj huP' hvP' hP'_disj i i' hv_P hv_P',
   fun ha'b =>
    theorem_6_1_ii h_pres j hI_sub hI_ends hI'_sub hI'_ends hJ_sub hJ_ends hIJ_inter hI'J
      P P' huP hvP hP_path hP_disj huP' hvP' hP'_path hP'_disj ha'b,
   fun _ hk₁ hk₂ =>
    theorem_6_1_iii h_pres j hI_sub hI_ends hI'_sub hI'_ends hJ_sub hJ_ends hIJ_inter hI'J
      P P' huP hvP hP_path hP_disj huP' hvP' hP'_path hP'_disj hk₁ hk₂⟩

/-! ## 4. Graph Minors XXI, `(6.2)` (`theorem_6_2_proof`) -/

/-- Reversing `k` mutually vertex-disjoint paths swaps the start and end vertex sets. -/
lemma hasDisjointPaths_symm {V : Type*} {G_sk : SimpleGraph V} {Z₁ Z₂ : Set V} {k : ℕ}
    (h : HasDisjointPaths G_sk Z₁ Z₂ k) :
    HasDisjointPaths G_sk Z₂ Z₁ k := by
  rw [hasDisjointPaths_iff_walks] at h ⊢
  rcases h with ⟨u, v, p, hu, hv, hp, hdisj⟩
  refine ⟨v, u, fun i => (p i).reverse, hv, hu, fun i => (hp i).reverse, ?_⟩
  intro i₁ i₂ hne
  simpa [SimpleGraph.Walk.support_reverse] using hdisj i₁ i₂ hne

/-- **Graph Minors XXI, (6.2)** (page 23 of the preprint):
"Let $\Gamma, F_1^*, \ldots, F_r^*, H_1, \ldots, H_r, \mu$ be a presentation of a graph $G$ in some
surface $\Sigma$. Let $I \subseteq F_1^*$ be a support with ends $a, b$. Then there are
$|V(\mu(a))|$ mutually vertex-disjoint paths of $\mu(I)$ between $V(\mu(a))$ and $V(\mu(b))$." -/
theorem theorem_6_2_proof
    {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
    {ιV : S → α} {ιE : Set S → β}
    {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
    {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ}
    (h_pres : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (j : Fin r) {I : Set S} {a b : S}
    (hI_sub : I ⊆ F_star j) (hI_ends : SupportHasEnds Γ I a b) :
    HasDisjointPaths (supportGraph G Γ μ I).skeleton
      (μ (.vertex a)).vertexSet (μ (.vertex b)).vertexSet (q j) := by
  have hS := h_pres.is_surface
  have hge2 := h_pres.cuff_vertices_ge_two
  rcases h_pres.supports_isSupport j with ⟨endA, endB, hFj_ends⟩
  obtain ⟨C, hC, hFjC⟩ := exists_cuff_of_supportHasEnds hFj_ends
  let f := cuffHomeo hS hC
  have hends_Fj := ends_mem_of_supportHasEnds hFj_ends
  obtain ⟨t₀, ht₀_Ico, t₁, ⟨hle, hlt⟩, h_ab_Fj, hFj_eq, _⟩ :=
    support_eq_cuffPoint_Icc hS hC f hFj_ends hFjC
  have ht₀_mem : cuffPoint f t₀ ∈ Γ.V ∩ C := by
    refine ⟨?_, cuffPoint_mem f t₀⟩
    rcases h_ab_Fj with ⟨h1, _⟩ | ⟨h1, _⟩ <;> rw [h1]
    · exact hends_Fj.2.2.1.1
    · exact hends_Fj.2.2.2.1.1
  have ht₁V : cuffPoint f t₁ ∈ Γ.V := by
    rcases h_ab_Fj with ⟨_, h2⟩ | ⟨_, h2⟩ <;> rw [h2]
    · exact hends_Fj.2.2.2.1.1
    · exact hends_Fj.2.2.1.1
  -- Prove by strong induction on `n = (cuffPoint f '' Icc τa τb ∩ Γ.V).ncard` for all `t₀ ≤ τa ≤ τb ≤ t₁`.
  have h_ind : ∀ (n : ℕ) (τa τb : ℝ),
      t₀ ≤ τa → τa ≤ τb → τb ≤ t₁ →
      cuffPoint f τa ∈ Γ.V → cuffPoint f τb ∈ Γ.V →
      ((cuffPoint f '' Icc τa τb) ∩ Γ.V).ncard = n →
      HasDisjointPaths (supportGraph G Γ μ (cuffPoint f '' Icc τa τb)).skeleton
        (μ (.vertex (cuffPoint f τa))).vertexSet
        (μ (.vertex (cuffPoint f τb))).vertexSet (q j) := by
    intro n
    induction' n using Nat.strong_induction_on with n ih
    intro τa τb hα_ge hαβ hβ_le hαV hβV hcard_n
    rcases eq_or_lt_of_le hαβ with rfl | hα_lt_β
    · -- Base case: `τa = τb`
      have hα_Fj : cuffPoint f τa ∈ Γ.V ∩ F_star j := by
        refine ⟨hαV, ?_⟩
        rw [hFj_eq]; exact ⟨τa, ⟨hα_ge, hβ_le⟩, rfl⟩
      have hcard_μ : (μ (.vertex (cuffPoint f τa))).vertexSet.ncard = q j :=
        (h_pres.μ_vertex_sub j (cuffPoint f τa) hα_Fj).2.2.1
      have hfin_μ : (μ (.vertex (cuffPoint f τa))).vertexSet.Finite :=
        (μ (.vertex (cuffPoint f τa))).vertexSet_finite
      let emb := (hfin_μ.toFinset.equivFinOfCardEq (by
        rw [← ncard_eq_toFinset_card _ hfin_μ, hcard_μ])).symm
      have hemb_mem : ∀ i : Fin (q j), (emb i : α) ∈ (μ (.vertex (cuffPoint f τa))).vertexSet :=
        fun i => hfin_μ.mem_toFinset.mp (emb i).2
      rw [hasDisjointPaths_iff_walks]
      refine ⟨fun i => (emb i).1, fun i => (emb i).1, fun _ => SimpleGraph.Walk.nil,
        hemb_mem, hemb_mem, fun _ => SimpleGraph.Walk.IsPath.nil, ?_⟩
      intro i₁ i₂ hne
      rw [Set.disjoint_left]
      intro z hz₁ hz₂
      simp only [mem_ofPred_eq, SimpleGraph.Walk.support_nil, List.mem_singleton] at hz₁ hz₂
      exact hne (emb.injective (Subtype.ext (hz₁.symm.trans hz₂)))
    · -- Step case: `τa < τb`. Find the space `s` starting at `τa`.
      obtain ⟨s, hs, γ, hαγ, hγ_le_t₁, hs_Fj, hends_s, hs_eq⟩ :=
        exists_space_starting_at_angle hS hge2 hC f ht₀_mem hle hlt hFj_eq
          hα_ge (hα_lt_β.trans_le hβ_le) hαV ht₁V
      have hγ_le_β : γ ≤ τb := by
        by_contra hgt
        push Not at hgt
        have hβ_in_s : cuffPoint f τb ∈ s := by
          rw [hs_eq]; exact ⟨τb, ⟨hα_lt_β, hgt⟩, rfl⟩
        exact (subset_bd_diff_of_mem_drawingSpaces hs hβ_in_s).2 hβV
      have hγV : cuffPoint f γ ∈ Γ.V := hends_s.2.2.1.1
      -- By (V3), there are `q j` disjoint paths in `μ (.space s)` (and hence in `supportGraph (Icc τa γ)`).
      have hv3 := (h_pres.v3_space j s hs _ _ hs_Fj hends_s).2.2.2
      have hs_sub_I₁ : s ⊆ cuffPoint f '' Icc τa γ := by
        rw [hs_eq]; exact image_mono Ioo_subset_Icc_self
      have hμs_G : μ (.space s) ≤ G :=
        (h_pres.μ_space_sub j s hs hs_Fj).trans (h_pres.v1_sub j)
      have h_paths_I₁ : HasDisjointPaths (supportGraph G Γ μ (cuffPoint f '' Icc τa γ)).skeleton
          (μ (.vertex (cuffPoint f τa))).vertexSet
          (μ (.vertex (cuffPoint f γ))).vertexSet (q j) := by
        rw [hasDisjointPaths_iff_walks] at hv3 ⊢
        rcases hv3 with ⟨u₁, v₁, p₁, hu₁, hv₁, hp₁, hdisj₁⟩
        have hle_s := space_skeleton_le_supportGraph_skeleton hs hs_sub_I₁ hμs_G
        refine ⟨u₁, v₁, fun i => (p₁ i).mapLe hle_s, hu₁, hv₁, ?_, ?_⟩
        · intro i
          exact (hp₁ i).mapLe hle_s
        · intro i₁ i₂ hne
          simpa [SimpleGraph.Walk.support_mapLe_eq_support] using hdisj₁ i₁ i₂ hne
      rcases eq_or_lt_of_le hγ_le_β with rfl | hγ_lt_β
      · exact h_paths_I₁
      · -- Apply induction hypothesis to `I' = cuffPoint f '' Icc γ τb`.
        have hsub_strict : (cuffPoint f '' Icc γ τb) ∩ Γ.V ⊂ (cuffPoint f '' Icc τa τb) ∩ Γ.V := by
          refine ⟨inter_subset_inter_left _ (image_mono (Icc_subset_Icc_left hαγ.le)), ?_⟩
          intro hsub_rev
          have hα_in : cuffPoint f τa ∈ (cuffPoint f '' Icc τa τb) ∩ Γ.V :=
            ⟨⟨τa, ⟨le_rfl, hα_lt_β.le⟩, rfl⟩, hαV⟩
          rcases (hsub_rev hα_in).1 with ⟨t, ⟨ht1, ht2⟩, ht_eq⟩
          have ht_eq_α : t = τa :=
            cuffPoint_injOn_Ico f t₀ ⟨(hα_ge.trans hαγ.le).trans ht1, (ht2.trans hβ_le).trans_lt hlt⟩
              ⟨hα_ge, (hα_lt_β.le.trans hβ_le).trans_lt hlt⟩ ht_eq
          linarith
        have hcard_lt : ((cuffPoint f '' Icc γ τb) ∩ Γ.V).ncard < n := by
          rw [← hcard_n]
          exact ncard_lt_ncard hsub_strict (Γ.finite_V.subset inter_subset_right)
        have h_paths_I' := ih _ hcard_lt γ τb (hα_ge.trans hαγ.le) hγ_lt_β.le hβ_le hγV hβV rfl
        -- Combine `I₁ = Icc τa γ` and `I' = Icc γ τb` using `(6.1)(ii)`.
        have hI₁_sub : cuffPoint f '' Icc τa γ ⊆ F_star j := by
          rw [hFj_eq]; exact image_mono (Icc_subset_Icc hα_ge (hγ_le_β.trans hβ_le))
        have hI'_sub : cuffPoint f '' Icc γ τb ⊆ F_star j := by
          rw [hFj_eq]; exact image_mono (Icc_subset_Icc (hα_ge.trans hαγ.le) hβ_le)
        have hI₁_ends := supportHasEnds_cuffPoint_Icc hS hC f hα_ge hαγ.le (hγ_le_β.trans hβ_le) hlt hαV hγV
        have hI'_ends := supportHasEnds_cuffPoint_Icc hS hC f (hα_ge.trans hαγ.le) hγ_lt_β.le hβ_le hlt hγV hβV
        obtain ⟨hunion, hinter⟩ := cuffPoint_Icc_split f hα_ge hαγ.le hγ_lt_β.le hβ_le hlt
        have h_comb := theorem_6_1_ii_exists h_pres j hI₁_sub hI₁_ends hI'_sub hI'_ends hinter h_paths_I₁ h_paths_I'
        rwa [hunion] at h_comb
  obtain ⟨τa, τb, hα_ge, hαβ, hβ_le, hI_ab, hI_eq⟩ :=
    subsupport_eq_cuffPoint_Icc hS hC f hle hlt hFj_eq hI_sub hI_ends
  have hends_I := ends_mem_of_supportHasEnds hI_ends
  rcases hI_ab with ⟨hα_a, hβ_b⟩ | ⟨hα_b, hβ_a⟩
  · rw [hI_eq, ← hα_a, ← hβ_b]
    exact h_ind _ τa τb hα_ge hαβ hβ_le (hα_a.symm ▸ hends_I.2.2.1.1) (hβ_b.symm ▸ hends_I.2.2.2.1.1) rfl
  · rw [hI_eq, ← hα_b, ← hβ_a]
    exact hasDisjointPaths_symm
      (h_ind _ τa τb hα_ge hαβ hβ_le (hα_b.symm ▸ hends_I.2.2.2.1.1) (hβ_a.symm ▸ hends_I.2.2.1.1) rfl)

end Section6

end GraphMinor.GM21
