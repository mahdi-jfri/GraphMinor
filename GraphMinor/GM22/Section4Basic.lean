module

public import GraphMinor.GM22.Section2
public import GraphMinor.GM22.Section3
public import GraphMinor.GM11.RadialBasics
public import GraphMinor.GM11.RadialChord
public import GraphMinor.GM11.PaintingCells
public import GraphMinor.Surface.ArcTools
public import GraphMinor.Surface.CutLift

/-!
# Graph Minors XXII, Section 4 (Part 1): Proof of 4.1

This file formalizes the first part of Section 4 of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 537–538), proving **4.1** (`theorem_4_1`).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Metric Graph GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM11

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

local notation "𝕀" => unitInterval

/-! ## 1. Basic Properties of `insulatedSet`, `IsVariant`, and `graphUnion` -/

/-- For a closed subset `A` of a surface `S`, `A \ subBd A` equals `interior A`. -/
theorem sdiff_subBd_eq_interior {A : Set S} (hA : IsClosed A) (hbd : subBd A = frontier A) :
    A \ subBd A = interior A := by
  rw [hbd, frontier]
  ext z
  simp only [mem_sdiff, hA.closure_eq]
  exact ⟨fun ⟨hzA, h⟩ => by_contra fun hni => h ⟨hzA, hni⟩,
    fun hz => ⟨interior_subset hz, fun ⟨_, hni⟩ => hni hz⟩⟩

/-- The set `insulatedSet D Y h` of `h`-insulated points is open in `S`.
Graph Minors XXII, Section 4, proof of 4.1 (page 537):
"Now $T$ is open, for it is the union of the interiors of finitely many closed discs". -/
theorem isOpen_insulatedSet [T2Space S] (D : Drawing S) (Y : Set S) (h : ℕ) :
    IsOpen (insulatedSet D Y h) := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  rcases Nat.eq_zero_or_pos h with rfl | hpos
  · have huniv : insulatedSet D Y 0 = univ := by
      ext y
      simp [insulatedSet, IsInsulated]
    rw [huniv]
    exact Filter.univ_mem
  · rcases hx with ⟨Δ, hΔ_disc, hΔ_nest, hΔ_ends⟩
    obtain ⟨hx_in, hdisj⟩ := hΔ_ends hpos
    let idx : Fin h := ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩
    have hcl : IsClosed (Δ idx) := (hΔ_disc idx).1.isCompact.isClosed
    have h_eq : Δ idx \ subBd (Δ idx) = interior (Δ idx) := by
      rw [subBd_eq_frontier, frontier]
      ext z
      simp only [mem_sdiff, hcl.closure_eq]
      exact ⟨fun ⟨hzA, h⟩ => by_contra fun hni => h ⟨hzA, hni⟩,
        fun hz => ⟨interior_subset hz, fun ⟨_, hni⟩ => hni hz⟩⟩
    have hopen : IsOpen (Δ idx \ subBd (Δ idx)) := h_eq ▸ isOpen_interior
    refine Filter.mem_of_superset (hopen.mem_nhds hx_in) fun y hy => ?_
    exact ⟨Δ, hΔ_disc, hΔ_nest, fun _ => ⟨hy, hdisj⟩⟩

/-- For `h ≥ 1`, `Y` is disjoint from `insulatedSet D Y h`. -/
theorem disjoint_insulatedSet (D : Drawing S) (Y : Set S) {h : ℕ} (hh : 1 ≤ h) :
    Disjoint Y (insulatedSet D Y h) := by
  rw [disjoint_left]
  intro y hyY ⟨Δ, _, hΔ_nest, hΔ_ends⟩
  have hpos : 0 < h := hh
  obtain ⟨hy_in, hdisj⟩ := hΔ_ends hpos
  have hsub : Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩ ⊆ Δ ⟨0, hpos⟩ :=
    insulated_disc_anti hΔ_nest (Nat.zero_le _)
  exact disjoint_left.mp hdisj hyY (hsub hy_in.1)

/-- Monotonicity of `IsInsulated` when `D₁.U ⊆ D₂.U` and `Y₂ ⊆ Y₁`. -/
theorem IsInsulated.mono {D₁ D₂ : Drawing S} {Y₁ Y₂ : Set S} {h : ℕ} {x : S}
    (hins : IsInsulated D₁ Y₁ h x) (hU : D₁.U ⊆ D₂.U) (hY : Y₂ ⊆ Y₁) :
    IsInsulated D₂ Y₂ h x := by
  rcases hins with ⟨Δ, hΔ_disc, hΔ_nest, hΔ_ends⟩
  refine ⟨Δ, fun i => ⟨(hΔ_disc i).1, (hΔ_disc i).2.1, (hΔ_disc i).2.2.trans hU⟩,
    hΔ_nest, fun hpos => ?_⟩
  obtain ⟨hx_in, hdisj⟩ := hΔ_ends hpos
  exact ⟨hx_in, hdisj.mono_left hY⟩

theorem insulatedSet_mono {D₁ D₂ : Drawing S} {Y₁ Y₂ : Set S} {h : ℕ}
    (hU : D₁.U ⊆ D₂.U) (hY : Y₂ ⊆ Y₁) :
    insulatedSet D₁ Y₁ h ⊆ insulatedSet D₂ Y₂ h :=
  fun _ hx => hx.mono hU hY

/-- In any drawing `D`, for `e ∈ D.E`, `closure e ∩ D.V = closure e \ e`. -/
theorem _root_.GraphMinor.Surface.Drawing.closure_inter_V_eq_sdiff (D : Drawing S) {e : Set S}
    (he : e ∈ D.E) :
    closure e ∩ D.V = closure e \ e := by
  ext x
  have h := Set.ext_iff.mp (D.closure_diff_V he) x
  simp only [mem_inter_iff, mem_sdiff] at h ⊢
  tauto

/-- In any drawing `D`, `D.toGraph.IsLink e x y` depends only on `e ∈ D.E` and the set `e`. -/
theorem _root_.GraphMinor.Surface.Drawing.toGraph_isLink_iff_closure_sdiff (D : Drawing S)
    {e : Set S} {x y : S} :
    D.toGraph.IsLink e x y ↔ e ∈ D.E ∧ closure e \ e = {x, y} := by
  constructor
  · rintro ⟨he, _, _, hcap⟩
    rw [D.closure_inter_V_eq_sdiff he] at hcap
    exact ⟨he, hcap⟩
  · rintro ⟨he, hsdiff⟩
    have hcap : closure e ∩ D.V = {x, y} := by
      rw [D.closure_inter_V_eq_sdiff he, hsdiff]
    have hx : x ∈ D.V := (hcap.symm.subset (Or.inl rfl)).2
    have hy : y ∈ D.V := (hcap.symm.subset (Or.inr rfl)).2
    exact ⟨he, hx, hy, hcap⟩

/-- Two drawings share the same link relation on any common edge `e ∈ D₁.E ∩ D₂.E`. -/
theorem _root_.GraphMinor.Surface.Drawing.toGraph_isLink_eq_of_mem {D₁ D₂ : Drawing S} {e : Set S}
    (he₁ : e ∈ D₁.E) (he₂ : e ∈ D₂.E) (x y : S) :
    D₁.toGraph.IsLink e x y ↔ D₂.toGraph.IsLink e x y := by
  rw [D₁.toGraph_isLink_iff_closure_sdiff, D₂.toGraph_isLink_iff_closure_sdiff]
  exact ⟨fun ⟨_, h⟩ => ⟨he₂, h⟩, fun ⟨_, h⟩ => ⟨he₁, h⟩⟩

/-- Any two drawings embedded via the same `(ιV, ιE)` are compatible graphs. -/
theorem _root_.GraphMinor.Surface.Drawing.compatible_toEmbeddedGraph (D₁ D₂ : Drawing S)
    (ιV : S ↪ α) (ιE : Set S ↪ β) :
    (D₁.toEmbeddedGraph ιV ιE).Compatible (D₂.toEmbeddedGraph ιV ιE) := by
  rintro e ⟨e₁, he₁, rfl⟩ ⟨e₂, he₂, he_eq⟩ x y
  obtain rfl : e₁ = e₂ := ιE.injective he_eq.symm
  simp only [toEmbeddedGraph_eq_mapEmbed]
  constructor
  · rintro ⟨f, u, v, hl, hf, rfl, rfl⟩
    obtain rfl : f = e₁ := ιE.injective hf
    exact ⟨f, u, v, (D₁.toGraph_isLink_eq_of_mem he₁ he₂ u v).mp hl, rfl, rfl, rfl⟩
  · rintro ⟨f, u, v, hl, hf, rfl, rfl⟩
    obtain rfl : f = e₁ := ιE.injective hf
    exact ⟨f, u, v, (D₁.toGraph_isLink_eq_of_mem he₁ he₂ u v).mpr hl, rfl, rfl, rfl⟩

@[simp]
theorem vertexSet_graphUnion (G₁ G₂ : Graph α β) :
    V(graphUnion G₁ G₂) = V(G₁) ∪ V(G₂) := rfl

@[simp]
theorem edgeSet_graphUnion (G₁ G₂ : Graph α β) :
    E(graphUnion G₁ G₂) = E(G₁) ∪ E(G₂) := rfl

theorem isLink_graphUnion_of_compatible {G₁ G₂ : Graph α β} (hcomp : G₁.Compatible G₂)
    {e : β} {x y : α} :
    (graphUnion G₁ G₂).IsLink e x y ↔ G₁.IsLink e x y ∨ G₂.IsLink e x y := by
  change (G₁.IsLink e x y ∨ (e ∉ E(G₁) ∧ G₂.IsLink e x y)) ↔ _
  constructor
  · rintro (h₁ | ⟨_, h₂⟩)
    · exact Or.inl h₁
    · exact Or.inr h₂
  · rintro (h₁ | h₂)
    · exact Or.inl h₁
    · by_cases he₁ : e ∈ E(G₁)
      · exact Or.inl ((hcomp he₁ h₂.edge_mem x y).mpr h₂)
      · exact Or.inr ⟨he₁, h₂⟩

theorem le_graphUnion_left (G₁ G₂ : Graph α β) : G₁ ≤ graphUnion G₁ G₂ :=
  ⟨subset_union_left, fun _ _ _ h => Or.inl h⟩

theorem le_graphUnion_right {G₁ G₂ : Graph α β} (hcomp : G₁.Compatible G₂) :
    G₂ ≤ graphUnion G₁ G₂ :=
  ⟨subset_union_right, fun _ _ _ h => (isLink_graphUnion_of_compatible hcomp).mpr (Or.inr h)⟩

theorem eq_graphUnion_of_le {G G₁ G₂ : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G)
    (hV : V(G) = V(G₁) ∪ V(G₂)) (hE : E(G) = E(G₁) ∪ E(G₂)) :
    G = graphUnion G₁ G₂ := by
  have hcomp : G₁.Compatible G₂ := Compatible.of_le_le h₁ h₂
  refine Graph.ext hV fun e x y => ?_
  rw [isLink_graphUnion_of_compatible hcomp]
  constructor
  · intro hl
    have he : e ∈ E(G₁) ∪ E(G₂) := hE ▸ hl.edge_mem
    rcases he with he₁ | he₂
    · exact Or.inl ((h₁.isLink_iff he₁).mpr hl)
    · exact Or.inr ((h₂.isLink_iff he₂).mpr hl)
  · rintro (hl₁ | hl₂)
    · exact h₁.isLink_mono hl₁
    · exact h₂.isLink_mono hl₂

theorem IsVariant.refl (D : Drawing S) (T : Set S) : IsVariant D D T where
  V_diff_eq := rfl
  edge_subset_of_mem_diff_left _ h := (h.2 h.1).elim
  edge_subset_of_mem_diff_right _ h := (h.2 h.1).elim

theorem IsVariant.symm {D₁ D₂ : Drawing S} {T : Set S} (h : IsVariant D₁ D₂ T) :
    IsVariant D₂ D₁ T where
  V_diff_eq := h.V_diff_eq.symm
  edge_subset_of_mem_diff_left := h.edge_subset_of_mem_diff_right
  edge_subset_of_mem_diff_right := h.edge_subset_of_mem_diff_left

theorem IsVariant.trans {D₁ D₂ D₃ : Drawing S} {T : Set S}
    (h₁₂ : IsVariant D₁ D₂ T) (h₂₃ : IsVariant D₂ D₃ T) :
    IsVariant D₁ D₃ T where
  V_diff_eq := h₁₂.V_diff_eq.trans h₂₃.V_diff_eq
  edge_subset_of_mem_diff_left e he := by
    by_cases he₂ : e ∈ D₂.E
    · exact h₂₃.edge_subset_of_mem_diff_left e ⟨he₂, he.2⟩
    · exact h₁₂.edge_subset_of_mem_diff_left e ⟨he.1, he₂⟩
  edge_subset_of_mem_diff_right e he := by
    by_cases he₂ : e ∈ D₂.E
    · exact h₁₂.edge_subset_of_mem_diff_right e ⟨he₂, he.2⟩
    · exact h₂₃.edge_subset_of_mem_diff_right e ⟨he.1, he₂⟩

/-! ## 2. The Pullback Relation `PullbackTo` and Single-Vertex Deletion Steps -/

section Pullback

variable [T2Space S]

omit [T2Space S] in
/-- When `ιV ⁻¹' V(K) ⊆ D.V`, `ιE ⁻¹' E(K) ⊆ D.E`, `(D.toEmbeddedGraph ιV ιE).Compatible K`,
and `T = insulatedSet D (ιV ⁻¹' V(K)) h` with `h ≥ 1`, any `T`-variant `D₁` of `D` preserves the
vertex and edge intersection with `K` and remains compatible with `K`. -/
theorem IsVariant.disjoint_T_preimage_VK (D : Drawing S) (K : Graph α β) (ιV : S ↪ α)
    {h : ℕ} (hh : 1 ≤ h) :
    Disjoint (insulatedSet D (ιV ⁻¹' V(K)) h) (ιV ⁻¹' V(K)) :=
  (disjoint_insulatedSet D (ιV ⁻¹' V(K)) hh).symm

omit [T2Space S] in
theorem IsVariant.preimage_VK_subset {D D₁ : Drawing S} {K : Graph α β} {ιV : S ↪ α}
    {h : ℕ} (hh : 1 ≤ h) (hVK : ιV ⁻¹' V(K) ⊆ D.V)
    (hVar : IsVariant D D₁ (insulatedSet D (ιV ⁻¹' V(K)) h)) :
    ιV ⁻¹' V(K) ⊆ D₁.V := by
  intro v hv
  have hv_not_T : v ∉ insulatedSet D (ιV ⁻¹' V(K)) h :=
    disjoint_right.mp (IsVariant.disjoint_T_preimage_VK D K ιV hh) hv
  have hv_diff : v ∈ D.V \ insulatedSet D (ιV ⁻¹' V(K)) h := ⟨hVK hv, hv_not_T⟩
  rw [hVar.V_diff_eq] at hv_diff
  exact hv_diff.1

omit [T2Space S] in
theorem IsVariant.inter_VK_eq {D D₁ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    {h : ℕ} (hh : 1 ≤ h) (hVK : ιV ⁻¹' V(K) ⊆ D.V)
    (hVar : IsVariant D D₁ (insulatedSet D (ιV ⁻¹' V(K)) h)) :
    V(D₁.toEmbeddedGraph ιV ιE) ∩ V(K) = V(D.toEmbeddedGraph ιV ιE) ∩ V(K) := by
  have h₁ : ιV ⁻¹' V(K) ⊆ D₁.V := hVar.preimage_VK_subset hh hVK
  ext x
  simp only [Drawing.toEmbeddedGraph, mem_inter_iff, mem_image]
  constructor
  · rintro ⟨⟨v, _, rfl⟩, hxK⟩
    exact ⟨⟨v, hVK hxK, rfl⟩, hxK⟩
  · rintro ⟨⟨v, _, rfl⟩, hxK⟩
    exact ⟨⟨v, h₁ hxK, rfl⟩, hxK⟩

omit [T2Space S] in
theorem IsVariant.not_closure_subset_T_of_mem_preimage_EK {D : Drawing S} {K : Graph α β}
    {ιV : S ↪ α} {ιE : Set S ↪ β} {h : ℕ} (hh : 1 ≤ h)
    (hEK : ιE ⁻¹' E(K) ⊆ D.E) (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    {e : Set S} (heK : e ∈ ιE ⁻¹' E(K)) :
    ¬ closure e ⊆ insulatedSet D (ιV ⁻¹' V(K)) h := by
  have heD : e ∈ D.E := hEK heK
  obtain ⟨u, v, hlink⟩ := D.toGraph.exists_isLink_of_mem_edgeSet heD
  have hlink_emb : (D.toEmbeddedGraph ιV ιE).IsLink (ιE e) (ιV u) (ιV v) := by
    rw [toEmbeddedGraph_eq_mapEmbed, isLink_mapEmbed_iff]
    exact hlink
  have hlinkK : K.IsLink (ιE e) (ιV u) (ιV v) :=
    (hComp (mem_image_of_mem ιE heD) heK (ιV u) (ιV v)).mp hlink_emb
  have huK : u ∈ ιV ⁻¹' V(K) := hlinkK.left_mem
  have hu_cl : u ∈ closure e := by
    have : u ∈ closure e ∩ D.V := by rw [hlink.2.2.2]; exact mem_insert u {v}
    exact this.1
  intro hsub
  exact disjoint_left.mp (disjoint_insulatedSet D (ιV ⁻¹' V(K)) hh) huK (hsub hu_cl)

omit [T2Space S] in
theorem IsVariant.preimage_EK_subset {D D₁ : Drawing S} {K : Graph α β}
    {ιV : S ↪ α} {ιE : Set S ↪ β} {h : ℕ} (hh : 1 ≤ h)
    (hEK : ιE ⁻¹' E(K) ⊆ D.E) (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hVar : IsVariant D D₁ (insulatedSet D (ιV ⁻¹' V(K)) h)) :
    ιE ⁻¹' E(K) ⊆ D₁.E := by
  intro e heK
  by_contra he₁
  exact IsVariant.not_closure_subset_T_of_mem_preimage_EK hh hEK hComp heK
    (hVar.edge_subset_of_mem_diff_left e ⟨hEK heK, he₁⟩)

omit [T2Space S] in
theorem IsVariant.compatible_K {D D₁ : Drawing S} {K : Graph α β}
    {ιV : S ↪ α} {ιE : Set S ↪ β} {h : ℕ} (_hh : 1 ≤ h)
    (hEK : ιE ⁻¹' E(K) ⊆ D.E) (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (_hVar : IsVariant D D₁ (insulatedSet D (ιV ⁻¹' V(K)) h)) :
    (D₁.toEmbeddedGraph ιV ιE).Compatible K := by
  rintro b ⟨e, he₁, rfl⟩ hbK x y
  have heD : e ∈ D.E := hEK hbK
  have hcomp_D₁_D := Drawing.compatible_toEmbeddedGraph D₁ D ιV ιE
  exact (hcomp_D₁_D ⟨e, he₁, rfl⟩ ⟨e, heD, rfl⟩ x y).trans
    (hComp ⟨e, heD, rfl⟩ hbK x y)

omit [T2Space S] in
/-- If `D₁, D₂` are `T`-variants of `D` and `v₀ ∈ D₂.V ∩ T` satisfies `D₂.V \ {v₀} ⊆ D₁.V` and
`∀ e ∈ D₂.E, v₀ ∉ closure e → e ∈ D₁.E`, then deleting `ιV v₀` from
`graphUnion (D₂.toEmbeddedGraph ιV ιE) K` yields a subgraph of
`graphUnion (D₁.toEmbeddedGraph ιV ιE) K`. -/
theorem deleteVerts_graphUnion_le_of_step {D D₁ D₂ : Drawing S} {K : Graph α β}
    {ιV : S ↪ α} {ιE : Set S ↪ β} {h : ℕ} (hh : 1 ≤ h)
    (hEK : ιE ⁻¹' E(K) ⊆ D.E) (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hVar₁ : IsVariant D D₁ (insulatedSet D (ιV ⁻¹' V(K)) h))
    (hVar₂ : IsVariant D D₂ (insulatedSet D (ιV ⁻¹' V(K)) h))
    {v₀ : S} (hv₀ : v₀ ∈ D₂.V)
    (hV_sub : D₂.V \ {v₀} ⊆ D₁.V)
    (hE_sub : ∀ e ∈ D₂.E, v₀ ∉ closure e → e ∈ D₁.E) :
    (graphUnion (D₂.toEmbeddedGraph ιV ιE) K).deleteVerts {ιV v₀} ≤
      graphUnion (D₁.toEmbeddedGraph ιV ιE) K := by
  have hComp₁ := hVar₁.compatible_K hh hEK hComp
  have hComp₂ := hVar₂.compatible_K hh hEK hComp
  refine ⟨?_, ?_⟩
  · intro x hx
    rw [vertexSet_deleteVerts, vertexSet_graphUnion] at hx
    rcases hx with ⟨⟨v, hv₂, rfl⟩ | hxK, hx_ne⟩
    · have hv_ne : v ≠ v₀ := fun h => hx_ne (congrArg ιV h)
      exact Or.inl ⟨v, hV_sub ⟨hv₂, hv_ne⟩, rfl⟩
    · exact Or.inr hxK
  · intro b x y hl
    rw [deleteVerts_isLink, isLink_graphUnion_of_compatible hComp₂] at hl
    rw [isLink_graphUnion_of_compatible hComp₁]
    rcases hl with ⟨hl₂ | hlK, hx_ne, hy_ne⟩
    · left
      rw [toEmbeddedGraph_eq_mapEmbed] at hl₂ ⊢
      rcases hl₂ with ⟨e, x₀, y₀, hl_e, rfl, rfl, rfl⟩
      have hx₀_ne : x₀ ≠ v₀ := fun h => hx_ne (congrArg ιV h)
      have hy₀_ne : y₀ ≠ v₀ := fun h => hy_ne (congrArg ιV h)
      have hv₀_not_cl : v₀ ∉ closure e := by
        intro hv₀_cl
        have hv₀_cap : v₀ ∈ closure e ∩ D₂.V := ⟨hv₀_cl, hv₀⟩
        rw [hl_e.2.2.2] at hv₀_cap
        rcases hv₀_cap with rfl | rfl
        · exact hx₀_ne rfl
        · exact hy₀_ne rfl
      have he₁ : e ∈ D₁.E := hE_sub e hl_e.1 hv₀_not_cl
      have hl_e₁ : D₁.toGraph.IsLink e x₀ y₀ :=
        (D₁.toGraph_isLink_eq_of_mem he₁ hl_e.1 x₀ y₀).mpr hl_e
      exact (isLink_mapEmbed_iff ιV ιE D₁.toGraph).mpr hl_e₁
    · exact Or.inr hlK

/-- The pullback relation `PullbackTo h p D K ιV ιE D₁`: `D₁` is a `T`-variant of `D` with
`D.U ⊆ D₁.U`, and every subgraph `L₁ ≤ graphUnion (D₁.toEmbeddedGraph ιV ιE) K` pulls back to a
subgraph `L ≤ graphUnion (D.toEmbeddedGraph ιV ιE) K` with the same effect on `Z` and
`subgraphInter _ L K ≤ L₁`. -/
structure PullbackTo (h p : ℕ) (D : Drawing S) (K : Graph α β)
    (ιV : S ↪ α) (ιE : Set S ↪ β) (D₁ : Drawing S) : Prop where
  isVariant : IsVariant D D₁ (insulatedSet D (ιV ⁻¹' V(K)) h)
  U_subset : D.U ⊆ D₁.U
  pullback : ∀ Z ⊆ V(K), Z.ncard ≤ p →
    ∀ L₁ ≤ graphUnion (D₁.toEmbeddedGraph ιV ιE) K,
    ∃ L ≤ graphUnion (D.toEmbeddedGraph ιV ιE) K,
      HasSameEffectOn L L₁ Z ∧
      subgraphInter (graphUnion (D.toEmbeddedGraph ιV ιE) K) L K ≤ L₁

omit [T2Space S] in
theorem PullbackTo.refl (h p : ℕ) (D : Drawing S) (K : Graph α β)
    (ιV : S ↪ α) (ιE : Set S ↪ β) (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K) :
    PullbackTo h p D K ιV ιE D where
  isVariant := IsVariant.refl D _
  U_subset := Subset.rfl
  pullback _ _ _ L₁ hL₁ :=
    ⟨L₁, hL₁, rfl,
      subgraphInter_le_left hL₁ (le_graphUnion_right hComp)⟩

omit [T2Space S] in
/-- Single-step extension of `PullbackTo`: if `D₁` satisfies `PullbackTo` and `D₂` is a `T`-variant
of `D` with `D₁.U ⊆ D₂.U` and a vertex `v₀ ∈ D₂.V ∩ T` such that `D₂.V \ {v₀} ⊆ D₁.V` and
`∀ e ∈ D₂.E, v₀ ∉ closure e → e ∈ D₁.E`, then `D₂` satisfies `PullbackTo`. -/
theorem PullbackTo.step [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D₁ D₂ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (_hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB₁ : PullbackTo h p D K ιV ιE D₁)
    (hVar₂ : IsVariant D D₂ (insulatedSet D (ιV ⁻¹' V(K)) h))
    (hU₁₂ : D₁.U ⊆ D₂.U)
    {v₀ : S} (hv₀ : v₀ ∈ D₂.V) (hv₀T : v₀ ∈ insulatedSet D (ιV ⁻¹' V(K)) h)
    (hV_sub : D₂.V \ {v₀} ⊆ D₁.V)
    (hE_sub : ∀ e ∈ D₂.E, v₀ ∉ closure e → e ∈ D₁.E) :
    PullbackTo h p D K ιV ιE D₂ where
  isVariant := hVar₂
  U_subset := hPB₁.U_subset.trans hU₁₂
  pullback Z hZK hZp L₂ hL₂ := by
    let Γ₂ := D₂.toEmbeddedGraph ιV ιE
    let G₂ := graphUnion Γ₂ K
    let Γ₁ := D₁.toEmbeddedGraph ιV ιE
    let G₁ := graphUnion Γ₁ K
    have hComp₂ := hVar₂.compatible_K hh hEK hComp
    have hComp₁ := hPB₁.isVariant.compatible_K hh hEK hComp
    have hVG₂ : V(G₂).Finite := (D₂.finite_V.image ιV).union hVK_fin
    have hEG₂ : E(G₂).Finite := (D₂.finite_edges.image ιE).union hEK_fin
    have hIns₂ : IsInsulated D₂ (ιV ⁻¹' (V(Γ₂) ∩ V(K))) h v₀ := by
      refine hv₀T.mono (hPB₁.U_subset.trans hU₁₂) ?_
      intro x hx
      exact hx.2
    obtain ⟨L', hL'_del, hSame', hInter'⟩ := h31 G₂ Γ₂ K L₂ hVG₂ hEG₂
      (le_graphUnion_left Γ₂ K) (le_graphUnion_right hComp₂) rfl rfl
      D₂ ιV ιE rfl v₀ hv₀ hIns₂ Z hZK hZp hL₂
    have hdel_le : G₂.deleteVerts {ιV v₀} ≤ G₁ :=
      deleteVerts_graphUnion_le_of_step hh hEK hComp hPB₁.isVariant hVar₂ hv₀ hV_sub hE_sub
    have hL'₁ : L' ≤ G₁ := hL'_del.trans hdel_le
    obtain ⟨L, hLG, hSame, hInter⟩ := hPB₁.pullback Z hZK hZp L' hL'₁
    refine ⟨L, hLG, hSame.trans hSame', ?_⟩
    have hInter_K : subgraphInter (graphUnion (D.toEmbeddedGraph ιV ιE) K) L K ≤ K :=
      subgraphInter_le_right hLG (le_graphUnion_right hComp)
    refine (?_ : subgraphInter (graphUnion (D.toEmbeddedGraph ιV ιE) K) L K ≤
      subgraphInter G₂ L' K).trans hInter'
    refine ⟨subset_inter hInter.vertexSet_mono hInter_K.vertexSet_mono, fun e x y hl => ?_⟩
    change ((G₂.induce (V(L') ∩ V(K))).restrict (E(L') ∩ E(K))).IsLink e x y
    rw [restrict_isLink, induce_isLink]
    have hlL' := hInter.isLink_mono hl
    have hlK := hInter_K.isLink_mono hl
    exact ⟨⟨hlL'.edge_mem, hlK.edge_mem⟩,
      (le_graphUnion_right hComp₂).isLink_mono hlK,
      ⟨hlL'.left_mem, hlK.left_mem⟩, ⟨hlL'.right_mem, hlK.right_mem⟩⟩

/-! ## 3. Elementary Drawing Modifications in `T`: Subdividing Edges, Adding Points, Adding Chords -/

theorem deleteEdge_V (D₁ : Drawing S) (e : Set S) :
    (D₁.deleteEdge e).V = D₁.V := by
  change D₁.spanV D₁.V (D₁.E \ {e}) = D₁.V
  exact Subset.antisymm (D₁.spanV_subset _ _) fun x hx => Or.inl ⟨hx, hx⟩

theorem deleteEdge_E (D₁ : Drawing S) (e : Set S) :
    (D₁.deleteEdge e).E = D₁.E \ {e} := by
  rw [Drawing.deleteEdge, D₁.span_E]
  exact inter_eq_left.mpr sdiff_subset

theorem deleteEdge_U_union_closure (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E) :
    (D₁.deleteEdge e).U ∪ closure e = D₁.U := by
  change (D₁.spanV D₁.V (D₁.E \ {e}) ∪ ⋃ f ∈ (D₁.E \ {e}) ∩ D₁.E, closure f) ∪ closure e = D₁.U
  rw [show D₁.spanV D₁.V (D₁.E \ {e}) = D₁.V from deleteEdge_V D₁ e,
    inter_eq_left.mpr sdiff_subset]
  conv_rhs => rw [D₁.U_eq]
  ext x
  simp only [mem_union, mem_iUnion, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ((hxV | ⟨f, ⟨hf, _⟩, hxf⟩) | hxe)
    · exact Or.inl hxV
    · exact Or.inr ⟨f, hf, hxf⟩
    · exact Or.inr ⟨e, he, hxe⟩
  · rintro (hxV | ⟨f, hf, hxf⟩)
    · exact Or.inl (Or.inl hxV)
    · by_cases hfe : f = e
      · subst hfe
        exact Or.inr hxf
      · exact Or.inl (Or.inr ⟨f, ⟨hf, hfe⟩, hxf⟩)

theorem deleteEdge_U_inter_closure (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E) :
    (D₁.deleteEdge e).U ∩ closure e ⊆ closure e ∩ D₁.V := by
  change (D₁.spanV D₁.V (D₁.E \ {e}) ∪ ⋃ f ∈ (D₁.E \ {e}) ∩ D₁.E, closure f) ∩ closure e ⊆
    closure e ∩ D₁.V
  rw [show D₁.spanV D₁.V (D₁.E \ {e}) = D₁.V from deleteEdge_V D₁ e,
    inter_eq_left.mpr sdiff_subset]
  rintro x ⟨hxV | hxE, hxe⟩
  · exact ⟨hxe, hxV⟩
  · obtain ⟨f, ⟨hf, hfe⟩, hxf⟩ := mem_iUnion₂.mp hxE
    exact ⟨hxe, closure_inter_subset_V hf he hfe ⟨hxf, hxe⟩⟩

/-- Splitting an edge `e ∈ D₁.E` at an interior point `v₀ ∈ e` into two line segments `L₁, L₂`
with `L₁ ∪ L₂ = closure e` and `L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}`. -/
noncomputable def subdivEdgeSplit (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) : Drawing S :=
  have hI' : (lineDrawing hL₁ huv₀).U ∩ (lineDrawing hL₂ hv₀v).U ⊆
      (lineDrawing hL₁ huv₀).V ∩ (lineDrawing hL₂ hv₀v).V := hI
  let D_L : Drawing S := (lineDrawing hL₁ huv₀).glue (lineDrawing hL₂ hv₀v) hI'
  have hmeet : (D₁.deleteEdge e).U ∩ D_L.U ⊆ (D₁.deleteEdge e).V ∩ D_L.V := by
    change (D₁.deleteEdge e).U ∩ (L₁ ∪ L₂) ⊆ (D₁.deleteEdge e).V ∩ ({u, v₀} ∪ {v₀, v})
    rw [hU, deleteEdge_V]
    intro x hx
    have hx_cap := deleteEdge_U_inter_closure D₁ he hx
    rw [hcap] at hx_cap
    refine ⟨(hcap ▸ hx_cap).2, ?_⟩
    rcases hx_cap with rfl | rfl
    · exact Or.inl (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  (D₁.deleteEdge e).glue D_L hmeet

theorem subdivEdgeSplit_U (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI).U = D₁.U := by
  change (D₁.deleteEdge e).U ∪ (L₁ ∪ L₂) = D₁.U
  rw [hU, deleteEdge_U_union_closure D₁ he]

theorem subdivEdgeSplit_V (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI).V = insert v₀ D₁.V := by
  change (D₁.deleteEdge e).V ∪ ({u, v₀} ∪ {v₀, v}) = insert v₀ D₁.V
  rw [deleteEdge_V]
  have huV : u ∈ D₁.V := (hcap.symm.subset (Or.inl rfl)).2
  have hvV : v ∈ D₁.V := (hcap.symm.subset (Or.inr rfl)).2
  ext x
  simp only [mem_union, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (hx | (rfl | rfl) | (rfl | rfl))
    · exact Or.inr hx
    · exact Or.inr huV
    · exact Or.inl rfl
    · exact Or.inl rfl
    · exact Or.inr hvV
  · rintro (rfl | hx)
    · exact Or.inr (Or.inl (Or.inr rfl))
    · exact Or.inl hx

theorem subdivEdgeSplit_E (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI).E =
      (D₁.E \ {e}) ∪ {L₁ \ {u, v₀}, L₂ \ {v₀, v}} := by
  have hI' : (lineDrawing hL₁ huv₀).U ∩ (lineDrawing hL₂ hv₀v).U ⊆
      (lineDrawing hL₁ huv₀).V ∩ (lineDrawing hL₂ hv₀v).V := hI
  dsimp only [subdivEdgeSplit]
  rw [Drawing.glue_E, Drawing.glue_E (h := hI'), deleteEdge_E, lineDrawing_E, lineDrawing_E]
  ext f
  simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff]

theorem subdivEdgeSplit_isVariant {D D₁ : Drawing S} {T : Set S}
    (hVar : IsVariant D D₁ T) {e : Set S} (he : e ∈ D₁.E) (heT : closure e ⊆ T)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    IsVariant D (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI) T := by
  let D₂ := subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI
  have hv₀_mem : v₀ ∈ L₁ := hL₁.right_mem
  have hv₀T : v₀ ∈ T := heT (hU ▸ Or.inl hv₀_mem)
  refine hVar.trans ⟨?_, ?_, ?_⟩
  · rw [subdivEdgeSplit_V]
    ext x
    simp only [mem_sdiff, mem_insert_iff]
    exact ⟨fun ⟨hx, hxT⟩ => ⟨Or.inr hx, hxT⟩,
      fun ⟨hx, hxT⟩ => ⟨hx.resolve_left fun h => by subst h; exact hxT hv₀T, hxT⟩⟩
  · intro f hf
    rw [subdivEdgeSplit_E] at hf
    by_cases hfe : f = e
    · subst hfe
      exact heT
    · exact (hf.2 (Or.inl ⟨hf.1, hfe⟩)).elim
  · intro f hf
    have hfE := hf.1
    rw [subdivEdgeSplit_E] at hfE
    rcases hfE with ⟨hf₁, _⟩ | rfl | rfl
    · exact (hf.2 hf₁).elim
    · rw [closure_sdiff_pair hL₁]
      exact (subset_union_left.trans hU.le).trans heT
    · rw [closure_sdiff_pair hL₂]
      exact (subset_union_right.trans hU.le).trans heT

theorem subdivEdgeSplit_pullbackTo [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D₁ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB₁ : PullbackTo h p D K ιV ιE D₁)
    {e : Set S} (he : e ∈ D₁.E)
    (heT : closure e ⊆ insulatedSet D (ιV ⁻¹' V(K)) h)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    PullbackTo h p D K ιV ιE (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI) := by
  let D₂ := subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI
  have hVar₂ := subdivEdgeSplit_isVariant hPB₁.isVariant he heT hcap huv₀ hv₀v hL₁ hL₂ hU hI
  have hv₀T : v₀ ∈ insulatedSet D (ιV ⁻¹' V(K)) h := heT (hU ▸ Or.inl hL₁.right_mem)
  have hv₀V₂ : v₀ ∈ D₂.V := by
    rw [subdivEdgeSplit_V]
    exact mem_insert v₀ D₁.V
  refine hPB₁.step hh h31 hVK_fin hEK_fin hVK hEK hComp hVar₂
    (subdivEdgeSplit_U D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI).symm.le hv₀V₂ hv₀T ?_ ?_
  · rw [subdivEdgeSplit_V]
    rintro x ⟨rfl | hx, hne⟩
    · exact (hne rfl).elim
    · exact hx
  · intro f hf hv₀_not
    rw [subdivEdgeSplit_E] at hf
    rcases hf with ⟨hf₁, _⟩ | rfl | rfl
    · exact hf₁
    · rw [closure_sdiff_pair hL₁] at hv₀_not
      exact (hv₀_not hL₁.right_mem).elim
    · rw [closure_sdiff_pair hL₂] at hv₀_not
      exact (hv₀_not hL₂.left_mem).elim

/-- Subdividing any edge `e ∈ D₁.E` with `closure e ⊆ T` at a point `v₀ ∈ e` yields a drawing `D₂`
satisfying `PullbackTo` in which `e` is replaced by two line edges `e₁, e₂` with
`closure e₁ ∪ closure e₂ = closure e`. -/
theorem PullbackTo.subdivEdge [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D₁ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB₁ : PullbackTo h p D K ιV ιE D₁)
    {e : Set S} (he : e ∈ D₁.E)
    (heT : closure e ⊆ insulatedSet D (ιV ⁻¹' V(K)) h)
    {v₀ : S} (hv₀ : v₀ ∈ e) :
    ∃ (D₂ : Drawing S) (e₁ e₂ : Set S),
      PullbackTo h p D K ιV ιE D₂ ∧
      D₂.U = D₁.U ∧
      D₂.V = insert v₀ D₁.V ∧
      D₂.E = (D₁.E \ {e}) ∪ {e₁, e₂} ∧
      e₁ ∈ D₂.E ∧ e₂ ∈ D₂.E ∧
      closure e₁ ∪ closure e₂ = closure e ∧
      (∃ u, u ≠ v₀ ∧ closure e₁ ∩ D₂.V = {u, v₀} ∧ IsLineWithEnds (closure e₁) u v₀) ∧
      (∃ v, v₀ ≠ v ∧ closure e₂ ∩ D₂.V = {v₀, v} ∧ IsLineWithEnds (closure e₂) v₀ v) := by
  have hv₀_not_V : v₀ ∉ D₁.V := (he.2.1 hv₀).2
  have hv₀_cl : v₀ ∈ closure e := subset_closure hv₀
  rcases D₁.edge_cond e he with ⟨u, v, _, hcap, hL⟩ | ⟨u, hcap, hF⟩
  · have huV : u ∈ D₁.V := (hcap.symm.subset (Or.inl rfl)).2
    have hvV : v ∈ D₁.V := (hcap.symm.subset (Or.inr rfl)).2
    have huv₀ : u ≠ v₀ := fun h => hv₀_not_V (h ▸ huV)
    have hv₀v : v₀ ≠ v := fun h => hv₀_not_V (h ▸ hvV)
    obtain ⟨L₁, L₂, hL₁, hL₂, hU, hI₀⟩ := hL.split hv₀_cl huv₀.symm hv₀v
    have hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v} := by
      rw [hI₀]
      rintro x rfl
      exact ⟨Or.inr rfl, Or.inl rfl⟩
    let D₂ := subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI
    have hPB₂ := subdivEdgeSplit_pullbackTo hh h31 hVK_fin hEK_fin hVK hEK hComp hPB₁
      he heT hcap huv₀ hv₀v hL₁ hL₂ hU hI
    have hE₂ := subdivEdgeSplit_E D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI
    have he₁_mem : L₁ \ {u, v₀} ∈ D₂.E := hE₂.symm ▸ Or.inr (Or.inl rfl)
    have he₂_mem : L₂ \ {v₀, v} ∈ D₂.E := hE₂.symm ▸ Or.inr (Or.inr rfl)
    have hcl₁ : closure (L₁ \ {u, v₀}) = L₁ := closure_sdiff_pair hL₁
    have hcl₂ : closure (L₂ \ {v₀, v}) = L₂ := closure_sdiff_pair hL₂
    refine ⟨D₂, L₁ \ {u, v₀}, L₂ \ {v₀, v}, hPB₂,
      subdivEdgeSplit_U D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI,
      subdivEdgeSplit_V D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI,
      hE₂, he₁_mem, he₂_mem, by rw [hcl₁, hcl₂, hU], ?_, ?_⟩
    · refine ⟨u, huv₀, ?_, hcl₁.symm ▸ hL₁⟩
      rw [D₂.closure_inter_V_eq_sdiff he₁_mem, hcl₁]
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_and, not_not]
      exact ⟨fun ⟨_, h⟩ => h ‹_›,
        by rintro (rfl | rfl) <;> [exact ⟨hL₁.left_mem, fun _ => Or.inl rfl⟩;
          exact ⟨hL₁.right_mem, fun _ => Or.inr rfl⟩]⟩
    · refine ⟨v, hv₀v, ?_, hcl₂.symm ▸ hL₂⟩
      rw [D₂.closure_inter_V_eq_sdiff he₂_mem, hcl₂]
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_and, not_not]
      exact ⟨fun ⟨_, h⟩ => h ‹_›,
        by rintro (rfl | rfl) <;> [exact ⟨hL₂.left_mem, fun _ => Or.inl rfl⟩;
          exact ⟨hL₂.right_mem, fun _ => Or.inr rfl⟩]⟩
  · have hu_cl : u ∈ closure e := (hcap.symm.subset rfl).1
    have huV : u ∈ D₁.V := (hcap.symm.subset rfl).2
    have huv₀ : u ≠ v₀ := fun h => hv₀_not_V (h ▸ huV)
    have hcap' : closure e ∩ D₁.V = {u, u} := by rw [pair_eq_singleton, hcap]
    obtain ⟨L₁, L₂, hL₁, hL₂', hU, hI₀⟩ := hF.lines hu_cl hv₀_cl huv₀
    have hL₂ : IsLineWithEnds L₂ v₀ u := hL₂'.symm
    have hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, u} := by
      rw [hI₀, pair_comm v₀ u, inter_self]
    let D₂ := subdivEdgeSplit D₁ he hcap' huv₀ huv₀.symm hL₁ hL₂ hU hI
    have hPB₂ := subdivEdgeSplit_pullbackTo hh h31 hVK_fin hEK_fin hVK hEK hComp hPB₁
      he heT hcap' huv₀ huv₀.symm hL₁ hL₂ hU hI
    have hE₂ := subdivEdgeSplit_E D₁ he hcap' huv₀ huv₀.symm hL₁ hL₂ hU hI
    have he₁_mem : L₁ \ {u, v₀} ∈ D₂.E := hE₂.symm ▸ Or.inr (Or.inl rfl)
    have he₂_mem : L₂ \ {v₀, u} ∈ D₂.E := hE₂.symm ▸ Or.inr (Or.inr rfl)
    have hcl₁ : closure (L₁ \ {u, v₀}) = L₁ := closure_sdiff_pair hL₁
    have hcl₂ : closure (L₂ \ {v₀, u}) = L₂ := closure_sdiff_pair hL₂
    refine ⟨D₂, L₁ \ {u, v₀}, L₂ \ {v₀, u}, hPB₂,
      subdivEdgeSplit_U D₁ he hcap' huv₀ huv₀.symm hL₁ hL₂ hU hI,
      subdivEdgeSplit_V D₁ he hcap' huv₀ huv₀.symm hL₁ hL₂ hU hI,
      hE₂, he₁_mem, he₂_mem, by rw [hcl₁, hcl₂, hU], ?_, ?_⟩
    · refine ⟨u, huv₀, ?_, hcl₁.symm ▸ hL₁⟩
      rw [D₂.closure_inter_V_eq_sdiff he₁_mem, hcl₁]
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_and, not_not]
      exact ⟨fun ⟨_, h⟩ => h ‹_›,
        by rintro (rfl | rfl) <;> [exact ⟨hL₁.left_mem, fun _ => Or.inl rfl⟩;
          exact ⟨hL₁.right_mem, fun _ => Or.inr rfl⟩]⟩
    · refine ⟨u, huv₀.symm, ?_, hcl₂.symm ▸ hL₂⟩
      rw [D₂.closure_inter_V_eq_sdiff he₂_mem, hcl₂]
      ext x
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_and, not_not]
      exact ⟨fun ⟨_, h⟩ => h ‹_›,
        by rintro (rfl | rfl) <;> [exact ⟨hL₂.left_mem, fun _ => Or.inl rfl⟩;
          exact ⟨hL₂.right_mem, fun _ => Or.inr rfl⟩]⟩

/-- Adding a point `v₀ ∈ T` to `D₁` (either as an isolated vertex if `v₀ ∉ D₁.U`, by subdividing the
edge `e ∈ D₁.E` containing `v₀` if `v₀ ∈ D₁.U \ D₁.V`, or keeping `D₁` if `v₀ ∈ D₁.V`) preserves
`PullbackTo`. -/
theorem PullbackTo.addPoint [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D₁ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB₁ : PullbackTo h p D K ιV ιE D₁)
    {v₀ : S} (hv₀T : v₀ ∈ insulatedSet D (ιV ⁻¹' V(K)) h)
    (h_edge_T : ∀ e ∈ D₁.E, v₀ ∈ e → closure e ⊆ insulatedSet D (ιV ⁻¹' V(K)) h) :
    ∃ D₂ : Drawing S,
      PullbackTo h p D K ιV ιE D₂ ∧
      D₂.U = insert v₀ D₁.U ∧
      D₂.V = insert v₀ D₁.V ∧
      (∀ e ∈ D₁.E, v₀ ∉ e → e ∈ D₂.E) ∧
      (∀ f ∈ D₂.E \ D₁.E, ∃ e ∈ D₁.E, v₀ ∈ e ∧ closure f ⊆ closure e) := by
  by_cases hv₀V : v₀ ∈ D₁.V
  · refine ⟨D₁, hPB₁, (insert_eq_of_mem (D₁.V_subset_U hv₀V)).symm,
      (insert_eq_of_mem hv₀V).symm, fun e he _ => he, fun _ hf => (hf.2 hf.1).elim⟩
  · by_cases hv₀U : v₀ ∈ D₁.U
    · obtain ⟨e, he, hv₀e⟩ := D₁.exists_edge_of_mem hv₀U hv₀V
      obtain ⟨D₂, e₁, e₂, hPB₂, hU₂, hV₂, hE₂, _, _, hcl₁₂, _, _⟩ :=
        hPB₁.subdivEdge hh h31 hVK_fin hEK_fin hVK hEK hComp he (h_edge_T e he hv₀e) hv₀e
      refine ⟨D₂, hPB₂, hU₂.trans (insert_eq_of_mem hv₀U).symm, hV₂, ?_, ?_⟩
      · intro f hf hv₀f
        have hfe : f ≠ e := fun h => hv₀f (h ▸ hv₀e)
        rw [hE₂]
        exact Or.inl ⟨hf, hfe⟩
      · intro f hf
        have hfE := hf.1
        rw [hE₂] at hfE
        rcases hfE with ⟨hf₁, _⟩ | rfl | rfl
        · exact (hf.2 hf₁).elim
        · exact ⟨e, he, hv₀e, subset_union_left.trans hcl₁₂.le⟩
        · exact ⟨e, he, hv₀e, subset_union_right.trans hcl₁₂.le⟩
    · have hmeet : D₁.U ∩ (pointsDrawing (finite_singleton v₀)).U ⊆
          D₁.V ∩ (pointsDrawing (finite_singleton v₀)).V := by
        rintro x ⟨hxU, rfl⟩
        exact (hv₀U hxU).elim
      let D₂ := D₁.glue (pointsDrawing (finite_singleton v₀)) hmeet
      have hU₂ : D₂.U = insert v₀ D₁.U := union_singleton
      have hV₂ : D₂.V = insert v₀ D₁.V := union_singleton
      have hE₂ : D₂.E = D₁.E := by
        change (D₁.glue (pointsDrawing (finite_singleton v₀)) hmeet).E = D₁.E
        rw [Drawing.glue_E, pointsDrawing_E, union_empty]
      have hVar₂ : IsVariant D D₂ (insulatedSet D (ιV ⁻¹' V(K)) h) := by
        refine hPB₁.isVariant.trans ⟨?_, ?_, ?_⟩
        · rw [hV₂]
          ext x
          simp only [mem_sdiff, mem_insert_iff]
          exact ⟨fun ⟨hx, hxT⟩ => ⟨Or.inr hx, hxT⟩,
            fun ⟨hx, hxT⟩ => ⟨hx.resolve_left fun h => by subst h; exact hxT hv₀T, hxT⟩⟩
        · intro f hf
          rw [hE₂] at hf
          exact (hf.2 hf.1).elim
        · intro f hf
          rw [hE₂] at hf
          exact (hf.2 hf.1).elim
      have hPB₂ : PullbackTo h p D K ιV ιE D₂ := by
        refine hPB₁.step hh h31 hVK_fin hEK_fin hVK hEK hComp hVar₂
          (hU₂.symm ▸ subset_insert v₀ D₁.U) (hV₂.symm ▸ mem_insert v₀ D₁.V) hv₀T ?_ ?_
        · rw [hV₂]
          rintro x ⟨rfl | hx, hne⟩
          · exact (hne rfl).elim
          · exact hx
        · intro f hf _
          rwa [hE₂] at hf
      refine ⟨D₂, hPB₂, hU₂, hV₂, fun e he _ => hE₂.symm ▸ he, fun f hf => ?_⟩
      rw [hE₂] at hf
      exact (hf.2 hf.1).elim

/-- Adding a chord line `J ⊆ T` between two distinct vertices `x, y ∈ D₁.V` with `J ∩ D₁.U = {x, y}`
preserves `PullbackTo`. -/
theorem PullbackTo.addChord [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D₁ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB₁ : PullbackTo h p D K ιV ιE D₁)
    {x y : S} (hxy : x ≠ y) (hxV : x ∈ D₁.V) (hyV : y ∈ D₁.V)
    {J : Set S} (hJ : IsLineWithEnds J x y)
    (hJT : J ⊆ insulatedSet D (ιV ⁻¹' V(K)) h)
    (hJU : J ∩ D₁.U = {x, y}) :
    ∃ D₂ : Drawing S,
      PullbackTo h p D K ιV ιE D₂ ∧
      D₂.U = D₁.U ∪ J ∧
      D₂.V = D₁.V ∧
      D₂.E = D₁.E ∪ {J \ {x, y}} ∧
      J \ {x, y} ∈ D₂.E ∧
      closure (J \ {x, y}) = J := by
  have hV_sub : ({x, y} : Set S) ⊆ D₁.V := by
    rintro z (rfl | rfl) <;> assumption
  have hmeet : D₁.U ∩ (lineDrawing hJ hxy).U ⊆ D₁.V ∩ (lineDrawing hJ hxy).V := by
    change D₁.U ∩ J ⊆ D₁.V ∩ {x, y}
    rw [inter_comm, hJU]
    exact subset_inter hV_sub Subset.rfl
  let D₂ := D₁.glue (lineDrawing hJ hxy) hmeet
  have hU₂ : D₂.U = D₁.U ∪ J := rfl
  have hV₂ : D₂.V = D₁.V := union_eq_left.mpr hV_sub
  have hE₂ : D₂.E = D₁.E ∪ {J \ {x, y}} := by
    change (D₁.glue (lineDrawing hJ hxy) hmeet).E = _
    rw [Drawing.glue_E, lineDrawing_E]
  have hclJ : closure (J \ {x, y}) = J := closure_sdiff_pair hJ
  have hVar₂ : IsVariant D D₂ (insulatedSet D (ιV ⁻¹' V(K)) h) := by
    refine hPB₁.isVariant.trans ⟨by rw [hV₂], ?_, ?_⟩
    · intro f hf
      rw [hE₂] at hf
      exact (hf.2 (Or.inl hf.1)).elim
    · intro f hf
      have hfE := hf.1
      rw [hE₂] at hfE
      rcases hfE with hf₁ | rfl
      · exact (hf.2 hf₁).elim
      · rw [hclJ]
        exact hJT
  have hxT : x ∈ insulatedSet D (ιV ⁻¹' V(K)) h := hJT hJ.left_mem
  have hPB₂ : PullbackTo h p D K ιV ιE D₂ := by
    refine hPB₁.step hh h31 hVK_fin hEK_fin hVK hEK hComp hVar₂
      subset_union_left (hV₂.symm ▸ hxV) hxT (by rw [hV₂]; exact sdiff_subset) ?_
    intro f hf hx_not
    rw [hE₂] at hf
    rcases hf with hf₁ | rfl
    · exact hf₁
    · rw [hclJ] at hx_not
      exact (hx_not hJ.left_mem).elim
  exact ⟨D₂, hPB₂, hU₂, hV₂, hE₂, hE₂.symm ▸ Or.inr rfl, hclJ⟩

/-! ## 4. Arc Splitting, Walk Lifting, and Phase 1 Subdivision -/

theorem isLineWithEnds_extI_Icc {a : 𝕀 → S} (ha : IsArcMap a) {s r : ℝ}
    (hs : 0 ≤ s) (hsr : s < r) (hr : r ≤ 1) :
    IsLineWithEnds (extI a '' Icc s r) (extI a s) (extI a r) := by
  have h1 := (isArcMap_pieceA ha hs hsr hr).isLineWithEnds
  rwa [range_pieceA a hs hsr.le hr, pieceA_zero, pieceA_one] at h1

omit [TopologicalSpace S] [T2Space S] in
theorem extI_Icc_union {a : 𝕀 → S} {s c r : ℝ} (hsc : s ≤ c) (hcr : c ≤ r) :
    (extI a '' Icc s c) ∪ (extI a '' Icc c r) = extI a '' Icc s r := by
  rw [← image_union, Icc_union_Icc_eq_Icc hsc hcr]

omit [T2Space S] in
theorem extI_Icc_inter {a : 𝕀 → S} (ha : IsArcMap a) {s c r : ℝ}
    (hs : 0 ≤ s) (hsc : s ≤ c) (hcr : c ≤ r) (hr : r ≤ 1) :
    (extI a '' Icc s c) ∩ (extI a '' Icc c r) = {extI a c} := by
  ext y
  constructor
  · rintro ⟨⟨p, hp, rfl⟩, ⟨q, hq, hpq⟩⟩
    have heq : q = p := extI_injOn ha.2 ⟨hs.trans (hsc.trans hq.1), hq.2.trans hr⟩
      ⟨hs.trans hp.1, hp.2.trans (hcr.trans hr)⟩ hpq
    obtain rfl : p = c := le_antisymm hp.2 (heq ▸ hq.1)
    rfl
  · rintro rfl
    exact ⟨⟨c, ⟨hsc, le_rfl⟩, rfl⟩, ⟨c, ⟨le_rfl, hcr⟩, rfl⟩⟩

omit [T2Space S] in
theorem extI_ne_of_ne {a : 𝕀 → S} (ha : IsArcMap a) {s r : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hr : r ∈ Icc (0 : ℝ) 1) (hne : s ≠ r) :
    extI a s ≠ extI a r :=
  fun h => hne (extI_injOn ha.2 hs hr h)

/-- An edge `e ∈ D₁.E` is a line edge of `D₁` if its closure has two distinct endpoints in `D₁.V`
and is a line between them. -/
def IsLineEdge (D₁ : Drawing S) (e : Set S) : Prop :=
  ∃ u v : S, u ≠ v ∧ closure e ∩ D₁.V = {u, v} ∧ IsLineWithEnds (closure e) u v

omit [T2Space S] in
theorem IsLineEdge.iff_of_mem {D₁ D₂ : Drawing S} {e : Set S}
    (he₁ : e ∈ D₁.E) (he₂ : e ∈ D₂.E) :
    IsLineEdge D₁ e ↔ IsLineEdge D₂ e := by
  unfold IsLineEdge
  rw [D₁.closure_inter_V_eq_sdiff he₁, D₂.closure_inter_V_eq_sdiff he₂]

theorem isLineEdge_of_sdiff_pair {D₁ : Drawing S} {L : Set S} {u v : S}
    (huv : u ≠ v) (hL : IsLineWithEnds L u v) (he : L \ {u, v} ∈ D₁.E) :
    IsLineEdge D₁ (L \ {u, v}) := by
  have hcl : closure (L \ {u, v}) = L := closure_sdiff_pair hL
  refine ⟨u, v, huv, ?_, hcl.symm ▸ hL⟩
  rw [D₁.closure_inter_V_eq_sdiff he, hcl]
  ext x
  simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_and, not_not]
  exact ⟨fun ⟨hxL, h⟩ => h hxL,
    fun h => ⟨by rcases h with rfl | rfl; exacts [hL.left_mem, hL.right_mem], fun _ => h⟩⟩

theorem isLink_of_sdiff_pair {D₁ : Drawing S} {L : Set S} {u v : S}
    (_huv : u ≠ v) (hL : IsLineWithEnds L u v) (he : L \ {u, v} ∈ D₁.E) :
    D₁.toGraph.IsLink (L \ {u, v}) u v := by
  rw [D₁.toGraph_isLink_iff_closure_sdiff]
  refine ⟨he, ?_⟩
  rw [closure_sdiff_pair hL]
  ext x
  simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff, not_and, not_not]
  exact ⟨fun ⟨hxL, h⟩ => h hxL,
    fun h => ⟨by rcases h with rfl | rfl; exacts [hL.left_mem, hL.right_mem], fun _ => h⟩⟩

theorem subdivEdgeSplit_isLink_left (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI).toGraph.IsLink (L₁ \ {u, v₀}) u v₀ := by
  refine isLink_of_sdiff_pair huv₀ hL₁ ?_
  rw [subdivEdgeSplit_E]
  exact Or.inr (Or.inl rfl)

theorem subdivEdgeSplit_isLink_right (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v}) :
    (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI).toGraph.IsLink (L₂ \ {v₀, v}) v₀ v := by
  refine isLink_of_sdiff_pair hv₀v hL₂ ?_
  rw [subdivEdgeSplit_E]
  exact Or.inr (Or.inr rfl)

theorem subdivEdgeSplit_walk (D₁ : Drawing S) {e : Set S} (he : e ∈ D₁.E)
    {u v v₀ : S} (hcap : closure e ∩ D₁.V = {u, v})
    (huv₀ : u ≠ v₀) (hv₀v : v₀ ≠ v)
    {L₁ L₂ : Set S} (hL₁ : IsLineWithEnds L₁ u v₀) (hL₂ : IsLineWithEnds L₂ v₀ v)
    (hU : L₁ ∪ L₂ = closure e) (hI : L₁ ∩ L₂ ⊆ {u, v₀} ∩ {v₀, v})
    {a b : S} (W : GraphWalk D₁.toGraph a b) :
    Nonempty (GraphWalk (subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI).toGraph a b) := by
  let D₂ := subdivEdgeSplit D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI
  have hl₁ : D₂.toGraph.IsLink (L₁ \ {u, v₀}) u v₀ :=
    subdivEdgeSplit_isLink_left D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI
  have hl₂ : D₂.toGraph.IsLink (L₂ \ {v₀, v}) v₀ v :=
    subdivEdgeSplit_isLink_right D₁ he hcap huv₀ hv₀v hL₁ hL₂ hU hI
  induction W with
  | @nil x hv =>
    have hv₂ : x ∈ D₂.V := by
      rw [subdivEdgeSplit_V]
      exact Or.inr hv
    exact ⟨.nil hv₂⟩
  | @cons x y z f hl rest ih =>
    obtain ⟨W_rest⟩ := ih
    by_cases hfe : f = e
    · subst hfe
      have hxy_eq : ({x, y} : Set S) = {u, v} := by
        rw [← hl.2.2.2, hcap]
      have hx_uv : x = u ∨ x = v := by
        have : x ∈ ({x, y} : Set S) := Or.inl rfl
        rwa [hxy_eq] at this
      have hy_uv : y = u ∨ y = v := by
        have : y ∈ ({x, y} : Set S) := Or.inr rfl
        rwa [hxy_eq] at this
      have h_step : Nonempty (GraphWalk D₂.toGraph x y) := by
        rcases hx_uv with rfl | rfl <;> rcases hy_uv with rfl | rfl
        · exact ⟨.nil hl₁.left_mem⟩
        · exact ⟨.cons hl₁ (.cons hl₂ (.nil hl₂.right_mem))⟩
        · exact ⟨.cons hl₂.symm (.cons hl₁.symm (.nil hl₁.left_mem))⟩
        · exact ⟨.nil hl₂.right_mem⟩
      obtain ⟨W_xy⟩ := h_step
      exact ⟨W_xy.append W_rest⟩
    · have hf₂ : f ∈ D₂.E := by
        rw [subdivEdgeSplit_E]
        exact Or.inl ⟨hl.1, hfe⟩
      have hl_f₂ : D₂.toGraph.IsLink f x y :=
        (D₁.toGraph_isLink_eq_of_mem hl.1 hf₂ x y).mp hl
      exact ⟨.cons hl_f₂ W_rest⟩

/-- Phase 1, Step 1: Adding a finite set `F ⊆ T` of points that miss all edges in `D.E ∩ D'.E`
preserves `PullbackTo`, `D.E ∩ D'.E ⊆ D₁.E`, and `∀ f ∈ D₁.E \ (D.E ∩ D'.E), closure f ⊆ T`. -/
theorem exists_pullback_add_vertices [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
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
    (hVar' : IsVariant D D' (insulatedSet D (ιV ⁻¹' V(K)) h)) :
    ∃ D₁ : Drawing S,
      PullbackTo h p D K ιV ιE D₁ ∧
      D.V ⊆ D₁.V ∧
      D'.V ⊆ D₁.V ∧
      D.E ∩ D'.E ⊆ D₁.E ∧
      ∀ f ∈ D₁.E \ (D.E ∩ D'.E), closure f ⊆ insulatedSet D (ιV ⁻¹' V(K)) h := by
  let T := insulatedSet D (ιV ⁻¹' V(K)) h
  have hF_fin : (D'.V \ D.V).Finite := D'.finite_V.subset sdiff_subset
  suffices ∀ F : Set S, F.Finite → F ⊆ D'.V \ D.V →
      ∃ D₁ : Drawing S,
        PullbackTo h p D K ιV ιE D₁ ∧
        D.V ⊆ D₁.V ∧
        F ⊆ D₁.V ∧
        D.E ∩ D'.E ⊆ D₁.E ∧
        ∀ f ∈ D₁.E \ (D.E ∩ D'.E), closure f ⊆ T by
    obtain ⟨D₁, hPB₁, hDV, hFV, hEE, hcl⟩ := this (D'.V \ D.V) hF_fin Subset.rfl
    refine ⟨D₁, hPB₁, hDV, ?_, hEE, hcl⟩
    intro x hx
    by_cases hxD : x ∈ D.V
    · exact hDV hxD
    · exact hFV ⟨hx, hxD⟩
  intro F hF
  refine Set.Finite.induction_on F hF ?_ ?_
  · intro _
    refine ⟨D, PullbackTo.refl h p D K ιV ιE hComp, Subset.rfl, empty_subset _, inter_subset_left, ?_⟩
    rintro f ⟨hfD, hf_not⟩
    have hf_not' : f ∉ D'.E := fun hf' => hf_not ⟨hfD, hf'⟩
    exact hVar'.edge_subset_of_mem_diff_left f ⟨hfD, hf_not'⟩
  · rintro v₀ F hv₀_not hF_fin ih hF_sub
    have hv₀_mem : v₀ ∈ D'.V \ D.V := hF_sub (mem_insert v₀ F)
    have hF_sub' : F ⊆ D'.V \ D.V := (subset_insert v₀ F).trans hF_sub
    obtain ⟨D_cur, hPB_cur, hDV_cur, hFV_cur, hEE_cur, hcl_cur⟩ := ih hF_sub'
    have hv₀T : v₀ ∈ T := by
      by_contra hv₀_not_T
      have : v₀ ∈ D'.V \ T := ⟨hv₀_mem.1, hv₀_not_T⟩
      rw [← hVar'.V_diff_eq] at this
      exact hv₀_mem.2 this.1
    have hv₀_edge_T : ∀ e ∈ D_cur.E, v₀ ∈ e → closure e ⊆ T := by
      intro e he hv₀e
      by_cases he_inter : e ∈ D.E ∩ D'.E
      · exfalso
        exact (he_inter.2.2.1 hv₀e).2 hv₀_mem.1
      · exact hcl_cur e ⟨he, he_inter⟩
    obtain ⟨D_next, hPB_next, _, hV_next, hE_keep, hE_new⟩ :=
      hPB_cur.addPoint hh h31 hVK_fin hEK_fin hVK hEK hComp hv₀T hv₀_edge_T
    refine ⟨D_next, hPB_next, hDV_cur.trans (hV_next.symm ▸ subset_insert v₀ D_cur.V), ?_, ?_, ?_⟩
    · rw [hV_next]
      exact insert_subset_insert hFV_cur
    · intro e he
      have hv₀_not_e : v₀ ∉ e := fun hv₀e =>
        (he.2.2.1 hv₀e).2 hv₀_mem.1
      exact hE_keep e (hEE_cur he) hv₀_not_e
    · rintro f ⟨hf_next, hf_not_inter⟩
      by_cases hf_cur : f ∈ D_cur.E
      · exact hcl_cur f ⟨hf_cur, hf_not_inter⟩
      · obtain ⟨e, he_cur, hv₀e, hsub_cl⟩ := hE_new f ⟨hf_next, hf_cur⟩
        exact hsub_cl.trans (hv₀_edge_T e he_cur hv₀e)

/-- Phase 1, Step 2: Subdividing all loop edges in `D₁.E \ (D.E ∩ D'.E)` so that every edge in
`D₂.E \ (D.E ∩ D'.E)` is a line edge. -/
theorem exists_pullback_subdiv_loops [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D' D₁ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB₁ : PullbackTo h p D K ιV ιE D₁)
    (hDV₁ : D.V ⊆ D₁.V) (hD'V₁ : D'.V ⊆ D₁.V)
    (hEE₁ : D.E ∩ D'.E ⊆ D₁.E)
    (hcl₁ : ∀ f ∈ D₁.E \ (D.E ∩ D'.E), closure f ⊆ insulatedSet D (ιV ⁻¹' V(K)) h) :
    ∃ D₂ : Drawing S,
      PullbackTo h p D K ιV ιE D₂ ∧
      D.V ⊆ D₂.V ∧
      D'.V ⊆ D₂.V ∧
      D.E ∩ D'.E ⊆ D₂.E ∧
      ∀ f ∈ D₂.E \ (D.E ∩ D'.E),
        closure f ⊆ insulatedSet D (ιV ⁻¹' V(K)) h ∧ IsLineEdge D₂ f := by
  let T := insulatedSet D (ιV ⁻¹' V(K)) h
  suffices ∀ n : ℕ, ∀ D_cur : Drawing S,
      PullbackTo h p D K ιV ιE D_cur →
      D.V ⊆ D_cur.V →
      D'.V ⊆ D_cur.V →
      D.E ∩ D'.E ⊆ D_cur.E →
      (∀ f ∈ D_cur.E \ (D.E ∩ D'.E), closure f ⊆ T) →
      {f ∈ D_cur.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_cur f}.ncard = n →
      ∃ D₂ : Drawing S,
        PullbackTo h p D K ιV ιE D₂ ∧
        D.V ⊆ D₂.V ∧
        D'.V ⊆ D₂.V ∧
        D.E ∩ D'.E ⊆ D₂.E ∧
        ∀ f ∈ D₂.E \ (D.E ∩ D'.E), closure f ⊆ T ∧ IsLineEdge D₂ f by
    exact this _ D₁ hPB₁ hDV₁ hD'V₁ hEE₁ hcl₁ rfl
  intro n
  induction n with
  | zero =>
    intro D_cur hPB_cur hDV_cur hD'V_cur hEE_cur hcl_cur hncard
    have hfin : {f ∈ D_cur.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_cur f}.Finite :=
      D_cur.finite_edges.subset fun _ h => h.1.1
    have hempty : {f ∈ D_cur.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_cur f} = ∅ :=
      (ncard_eq_zero (s := _) hfin).mp hncard
    refine ⟨D_cur, hPB_cur, hDV_cur, hD'V_cur, hEE_cur, fun f hf => ⟨hcl_cur f hf, ?_⟩⟩
    by_contra hnot
    have : f ∈ ({f ∈ D_cur.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_cur f} : Set (Set S)) := ⟨hf, hnot⟩
    rw [hempty] at this
    exact this
  | succ m ih =>
    intro D_cur hPB_cur hDV_cur hD'V_cur hEE_cur hcl_cur hncard
    have hne : {f ∈ D_cur.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_cur f}.Nonempty :=
      nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨e, ⟨he_cur, he_not_inter⟩, he_not_line⟩ := hne
    have heT : closure e ⊆ T := hcl_cur e ⟨he_cur, he_not_inter⟩
    obtain ⟨v₀, hv₀e⟩ : e.Nonempty := he_cur.1
    obtain ⟨D_next, e₁, e₂, hPB_next, _, hV_next, hE_next, _, _, hU, hline₁, hline₂⟩ :=
      hPB_cur.subdivEdge hh h31 hVK_fin hEK_fin hVK hEK hComp he_cur heT hv₀e
    have hV_sub : D_cur.V ⊆ D_next.V := hV_next.symm ▸ subset_insert v₀ D_cur.V
    have he₁_line : IsLineEdge D_next e₁ := by
      rcases hline₁ with ⟨u, huv₀, hcap₁, hL₁⟩
      exact ⟨u, v₀, huv₀, hcap₁, hL₁⟩
    have he₂_line : IsLineEdge D_next e₂ := by
      rcases hline₂ with ⟨v, hv₀v, hcap₂, hL₂⟩
      exact ⟨v₀, v, hv₀v, hcap₂, hL₂⟩
    have hEE_next : D.E ∩ D'.E ⊆ D_next.E := by
      intro f hf
      rw [hE_next]
      exact Or.inl ⟨hEE_cur hf, fun hfe => he_not_inter (hfe ▸ hf)⟩
    have hcl_next : ∀ f ∈ D_next.E \ (D.E ∩ D'.E), closure f ⊆ T := by
      rintro f ⟨hf_next, hf_not⟩
      rw [hE_next] at hf_next
      rcases hf_next with ⟨hf_cur, _⟩ | (rfl | rfl)
      · exact hcl_cur f ⟨hf_cur, hf_not⟩
      · exact (subset_union_left.trans hU.le).trans heT
      · exact (subset_union_right.trans hU.le).trans heT
    have h_nonline_eq :
        {f ∈ D_next.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_next f} =
          {f ∈ D_cur.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_cur f} \ {e} := by
      ext f
      simp only [mem_ofPred_eq, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨⟨hf_next, hf_not⟩, hf_nl⟩
        have hf_next' := hf_next
        rw [hE_next] at hf_next'
        rcases hf_next' with ⟨hf_cur, hfe⟩ | (rfl | rfl)
        · refine ⟨⟨⟨hf_cur, hf_not⟩, ?_⟩, hfe⟩
          rwa [IsLineEdge.iff_of_mem hf_cur hf_next]
        · exact (hf_nl he₁_line).elim
        · exact (hf_nl he₂_line).elim
      · rintro ⟨⟨⟨hf_cur, hf_not⟩, hf_nl⟩, hfe⟩
        have hf_next : f ∈ D_next.E := by
          rw [hE_next]
          exact Or.inl ⟨hf_cur, hfe⟩
        refine ⟨⟨hf_next, hf_not⟩, ?_⟩
        rwa [← IsLineEdge.iff_of_mem hf_cur hf_next]
    have he_mem_nl : e ∈ {f ∈ D_cur.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_cur f} :=
      ⟨⟨he_cur, he_not_inter⟩, he_not_line⟩
    have hncard_next : {f ∈ D_next.E \ (D.E ∩ D'.E) | ¬ IsLineEdge D_next f}.ncard = m := by
      rw [h_nonline_eq, ncard_sdiff_singleton_of_mem he_mem_nl,
        hncard, Nat.add_sub_cancel]
    exact ih D_next hPB_next (hDV_cur.trans hV_sub) (hD'V_cur.trans hV_sub)
      hEE_next hcl_next hncard_next

/-- Subdividing an arc segment `(extI a '' Icc 0 b) \ {extI a 0, extI a b}` of parameter length
`b ≤ (n + 1) * (δ / 2)` into sub-edges of parameter length at most `δ / 2`. -/
theorem exists_subdiv_arc_mesh [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    {a : 𝕀 → S} (ha : IsArcMap a) {δ : ℝ} (hδ : 0 < δ) :
    ∀ (n : ℕ) {b : ℝ}, 0 < b → b ≤ 1 → b ≤ (n + 1 : ℝ) * (δ / 2) →
      ∀ (D_cur : Drawing S),
        PullbackTo h p D K ιV ιE D_cur →
        let e_b := (extI a '' Icc 0 b) \ {extI a 0, extI a b}
        e_b ∈ D_cur.E →
        closure e_b ⊆ insulatedSet D (ιV ⁻¹' V(K)) h →
        ∃ D_next : Drawing S,
          PullbackTo h p D K ιV ιE D_next ∧
          D_next.U = D_cur.U ∧
          D_cur.V ⊆ D_next.V ∧
          D_cur.E \ {e_b} ⊆ D_next.E ∧
          ∀ f ∈ D_next.E \ (D_cur.E \ {e_b}),
            IsLineEdge D_next f ∧
            ∃ s₁ s₂ : ℝ, 0 ≤ s₁ ∧ s₁ < s₂ ∧ s₂ ≤ b ∧ s₂ - s₁ ≤ δ / 2 ∧
              closure f = extI a '' Icc s₁ s₂ := by
  intro n
  induction n with
  | zero =>
    intro b hb0 hb1 hb_le D_cur hPB_cur e_b he_b he_b_T
    have hb_delta : b ≤ δ / 2 := by simpa using hb_le
    have hL_b : IsLineWithEnds (extI a '' Icc 0 b) (extI a 0) (extI a b) :=
      isLineWithEnds_extI_Icc ha le_rfl hb0 hb1
    have hne_0b : extI a 0 ≠ extI a b :=
      extI_ne_of_ne ha ⟨le_rfl, zero_le_one⟩ ⟨hb0.le, hb1⟩ hb0.ne
    have hcl_eb : closure e_b = extI a '' Icc 0 b := closure_sdiff_pair hL_b
    refine ⟨D_cur, hPB_cur, rfl, Subset.rfl, sdiff_subset, ?_⟩
    rintro f ⟨hf_cur, hf_not⟩
    have hfe : f = e_b := by_contra fun hne => hf_not ⟨hf_cur, hne⟩
    subst hfe
    exact ⟨isLineEdge_of_sdiff_pair hne_0b hL_b he_b,
      0, b, le_rfl, hb0, le_rfl, by linarith, hcl_eb⟩
  | succ m ih =>
    intro b hb0 hb1 hb_le D_cur hPB_cur e_b he_b he_b_T
    by_cases hb_m : b ≤ (m + 1 : ℝ) * (δ / 2)
    · exact ih hb0 hb1 hb_m D_cur hPB_cur he_b he_b_T
    · have hb_m' : (m + 1 : ℝ) * (δ / 2) < b := lt_of_not_ge hb_m
      let c : ℝ := (m + 1 : ℝ) * (δ / 2)
      have hc0 : 0 < c := mul_pos (Nat.cast_add_one_pos m) (half_pos hδ)
      have hcb : c < b := hb_m'
      have hc1 : c ≤ 1 := hcb.le.trans hb1
      have hbc_delta : b - c ≤ δ / 2 := by
        dsimp only [c]
        push_cast at hb_le
        linarith
      have hL_b : IsLineWithEnds (extI a '' Icc 0 b) (extI a 0) (extI a b) :=
        isLineWithEnds_extI_Icc ha le_rfl hb0 hb1
      have hcl_eb : closure e_b = extI a '' Icc 0 b := closure_sdiff_pair hL_b
      have hne_0b : extI a 0 ≠ extI a b :=
        extI_ne_of_ne ha ⟨le_rfl, zero_le_one⟩ ⟨hb0.le, hb1⟩ hb0.ne
      have hlink_eb : D_cur.toGraph.IsLink e_b (extI a 0) (extI a b) :=
        isLink_of_sdiff_pair hne_0b hL_b he_b
      have hcap_eb : closure e_b ∩ D_cur.V = {extI a 0, extI a b} := hlink_eb.2.2.2
      have huv₀ : extI a 0 ≠ extI a c :=
        extI_ne_of_ne ha ⟨le_rfl, zero_le_one⟩ ⟨hc0.le, hc1⟩ hc0.ne
      have hv₀v : extI a c ≠ extI a b :=
        extI_ne_of_ne ha ⟨hc0.le, hc1⟩ ⟨hb0.le, hb1⟩ hcb.ne
      let L₁ := extI a '' Icc 0 c
      let L₂ := extI a '' Icc c b
      have hL₁ : IsLineWithEnds L₁ (extI a 0) (extI a c) :=
        isLineWithEnds_extI_Icc ha le_rfl hc0 hc1
      have hL₂ : IsLineWithEnds L₂ (extI a c) (extI a b) :=
        isLineWithEnds_extI_Icc ha hc0.le hcb hb1
      have hU : L₁ ∪ L₂ = closure e_b := by
        rw [hcl_eb]
        exact extI_Icc_union hc0.le hcb.le
      have hI : L₁ ∩ L₂ ⊆ {extI a 0, extI a c} ∩ {extI a c, extI a b} := by
        rw [extI_Icc_inter ha le_rfl hc0.le hcb.le hb1]
        rintro x rfl
        exact ⟨Or.inr rfl, Or.inl rfl⟩
      let D_mid := subdivEdgeSplit D_cur he_b hcap_eb huv₀ hv₀v hL₁ hL₂ hU hI
      have hPB_mid : PullbackTo h p D K ιV ιE D_mid :=
        subdivEdgeSplit_pullbackTo hh h31 hVK_fin hEK_fin hVK hEK hComp hPB_cur
          he_b he_b_T hcap_eb huv₀ hv₀v hL₁ hL₂ hU hI
      have hU_mid : D_mid.U = D_cur.U :=
        subdivEdgeSplit_U D_cur he_b hcap_eb huv₀ hv₀v hL₁ hL₂ hU hI
      have hV_mid : D_cur.V ⊆ D_mid.V := by
        change D_cur.V ⊆ (subdivEdgeSplit D_cur he_b hcap_eb huv₀ hv₀v hL₁ hL₂ hU hI).V
        rw [subdivEdgeSplit_V]
        exact subset_insert (extI a c) D_cur.V
      have hE_mid : D_mid.E = (D_cur.E \ {e_b}) ∪ {L₁ \ {extI a 0, extI a c}, L₂ \ {extI a c, extI a b}} :=
        subdivEdgeSplit_E D_cur he_b hcap_eb huv₀ hv₀v hL₁ hL₂ hU hI
      let e_c := L₁ \ {extI a 0, extI a c}
      let f₂ := L₂ \ {extI a c, extI a b}
      have he_c_mid : e_c ∈ D_mid.E := by
        rw [hE_mid]
        exact Or.inr (Or.inl rfl)
      have hf₂_mid : f₂ ∈ D_mid.E := by
        rw [hE_mid]
        exact Or.inr (Or.inr rfl)
      have hcl_ec : closure e_c = L₁ := closure_sdiff_pair hL₁
      have hcl_f₂ : closure f₂ = L₂ := closure_sdiff_pair hL₂
      have he_c_T : closure e_c ⊆ insulatedSet D (ιV ⁻¹' V(K)) h := by
        rw [hcl_ec]
        exact (subset_union_left.trans hU.le).trans he_b_T
      have hf₂_ne_ec : f₂ ≠ e_c := by
        intro heq
        have hcl_eq : L₂ = L₁ := by rw [← hcl_f₂, heq, hcl_ec]
        have hb_mem : extI a b ∈ L₁ ∩ L₂ := by
          rw [← hcl_eq]
          exact ⟨hL₂.right_mem, hL₂.right_mem⟩
        rw [extI_Icc_inter ha le_rfl hc0.le hcb.le hb1] at hb_mem
        exact hv₀v.symm hb_mem
      obtain ⟨D_next, hPB_next, hU_next, hV_next, hE_keep, hE_new⟩ :=
        ih hc0 hc1 le_rfl D_mid hPB_mid he_c_mid he_c_T
      refine ⟨D_next, hPB_next, hU_next.trans hU_mid, hV_mid.trans hV_next, ?_, ?_⟩
      · intro f hf
        apply hE_keep
        refine ⟨?_, ?_⟩
        · rw [hE_mid]
          exact Or.inl hf
        · intro hfe_c
          subst hfe_c
          have hcl_sub : L₁ ⊆ closure e_b := subset_union_left.trans hU.le
          have h_inter : L₁ ⊆ D_cur.V := by
            intro x hx
            exact closure_inter_subset_V hf.1 he_b hf.2 ⟨hcl_ec.symm ▸ hx, hcl_sub hx⟩
          have hx_in : extI a (c / 2) ∈ e_c := by
            refine ⟨⟨c / 2, ⟨by linarith, by linarith⟩, rfl⟩, ?_⟩
            rintro (h0 | hc_eq)
            · exact extI_ne_of_ne ha ⟨by linarith, by linarith⟩ ⟨le_rfl, zero_le_one⟩ (by linarith) h0
            · exact extI_ne_of_ne ha ⟨by linarith, by linarith⟩ ⟨hc0.le, hc1⟩ (by linarith) hc_eq
          exact (hf.1.2.1 hx_in).2 (h_inter hx_in.1)
      · rintro f ⟨hf_next, hf_not_keep⟩
        by_cases hf_mid : f ∈ D_mid.E \ {e_c}
        · have hf_mid' := hf_mid.1
          rw [hE_mid] at hf_mid'
          rcases hf_mid' with hf_keep | (rfl | rfl)
          · exact (hf_not_keep hf_keep).elim
          · exact (hf_mid.2 rfl).elim
          · refine ⟨isLineEdge_of_sdiff_pair hv₀v hL₂ hf_next,
              c, b, hc0.le, hcb, le_rfl, hbc_delta, hcl_f₂⟩
        · obtain ⟨h_line, s₁, s₂, hs₁, hs₁₂, hs₂c, h_len, hcl_f⟩ := hE_new f ⟨hf_next, hf_mid⟩
          exact ⟨h_line, s₁, s₂, hs₁, hs₁₂, hs₂c.trans hcb.le, h_len, hcl_f⟩

/-- Subdividing a single line edge `e ∈ D_cur.E` finely enough with respect to families of closed sets
`W, B : Fin k → Set S` satisfying `Disjoint (W i) (B i)` and `∀ i ≠ j, W j ⊆ B i`. -/
theorem exists_subdiv_single_edge_fine [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D_cur : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB_cur : PullbackTo h p D K ιV ιE D_cur)
    {e : Set S} (he : e ∈ D_cur.E)
    (heT : closure e ⊆ insulatedSet D (ιV ⁻¹' V(K)) h)
    (he_line : IsLineEdge D_cur e)
    {k : ℕ} (W B : Fin k → Set S)
    (hW_cl : ∀ i, IsClosed (W i)) (hB_cl : ∀ i, IsClosed (B i))
    (hWB_disj : ∀ i, Disjoint (W i) (B i))
    (hW_sub_B : ∀ i j, i ≠ j → W j ⊆ B i) :
    ∃ D_next : Drawing S,
      PullbackTo h p D K ιV ιE D_next ∧
      D_next.U = D_cur.U ∧
      D_cur.V ⊆ D_next.V ∧
      D_cur.E \ {e} ⊆ D_next.E ∧
      ∀ f ∈ D_next.E \ (D_cur.E \ {e}),
        closure f ⊆ closure e ∧
        IsLineEdge D_next f ∧
        (∀ i : Fin k, (closure f ∩ W i).Nonempty → Disjoint (closure f) (B i)) ∧
        (∀ f' ∈ D_next.E \ (D_cur.E \ {e}), ∀ i j : Fin k, i ≠ j →
          (closure f ∩ W i).Nonempty → (closure f' ∩ W j).Nonempty →
          Disjoint (closure f) (closure f')) := by
  rcases he_line with ⟨u, v, _, hcap, hL⟩
  obtain ⟨a, ha, hrange, ha0, ha1⟩ := hL.exists_arc
  have hIcc_eq : extI a '' Icc (0 : ℝ) 1 = closure e := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, (extI_of_mem a ht).symm⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, extI_coe a t⟩
  have he_eq : (extI a '' Icc (0 : ℝ) 1) \ {extI a 0, extI a 1} = e := by
    have h0 : extI a 0 = u := (extI_of_mem a ⟨le_rfl, zero_le_one⟩).trans ha0
    have h1 : extI a 1 = v := (extI_of_mem a ⟨zero_le_one, le_rfl⟩).trans ha1
    rw [hIcc_eq, h0, h1, ← hcap, D_cur.closure_inter_V_eq_sdiff he]
    ext x
    simp only [mem_sdiff, not_and, not_not]
    exact ⟨fun ⟨hx, h⟩ => h hx, fun hx => ⟨subset_closure hx, fun _ => hx⟩⟩
  let K_all : Set (ℝ × ℝ) :=
    ⋃ i : Fin k, (Icc (0 : ℝ) 1 ∩ (extI a) ⁻¹' (W i)) ×ˢ (Icc (0 : ℝ) 1 ∩ (extI a) ⁻¹' (B i))
  have hK_comp : IsCompact K_all := by
    refine isCompact_iUnion fun i => IsCompact.prod ?_ ?_
    · exact isCompact_Icc.inter_right ((hW_cl i).preimage (continuous_extI ha.1))
    · exact isCompact_Icc.inter_right ((hB_cl i).preimage (continuous_extI ha.1))
  obtain ⟨δ, hδ, hδ_le⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ K_all, δ ≤ |p.1 - p.2| := by
    by_cases hKne : K_all.Nonempty
    · obtain ⟨p₀, hp₀K, hp₀_min⟩ :=
        hK_comp.exists_isMinOn hKne (continuous_fst.sub continuous_snd).abs.continuousOn
      obtain ⟨i₀, ⟨_, hp₀W⟩, ⟨_, hp₀B⟩⟩ := mem_iUnion.mp hp₀K
      have hne : p₀.1 ≠ p₀.2 := fun heq =>
        disjoint_left.mp (hWB_disj i₀) hp₀W (heq ▸ hp₀B)
      exact ⟨|p₀.1 - p₀.2|, abs_sub_pos.mpr hne, fun p hp => hp₀_min hp⟩
    · exact ⟨1, zero_lt_one, fun p hp => (hKne ⟨p, hp⟩).elim⟩
  have hδ2 : 0 < δ / 2 := half_pos hδ
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ((δ / 2) / 2))
  have hn_le : (1 : ℝ) ≤ (n + 1 : ℝ) * ((δ / 2) / 2) := by
    have hpos : 0 < (δ / 2) / 2 := half_pos hδ2
    have h1 : 1 < (n : ℝ) * ((δ / 2) / 2) := (div_lt_iff₀ hpos).mp hn
    linarith
  have he_mem' : (extI a '' Icc 0 1) \ {extI a 0, extI a 1} ∈ D_cur.E := he_eq.symm ▸ he
  have he_T' : closure ((extI a '' Icc 0 1) \ {extI a 0, extI a 1}) ⊆
      insulatedSet D (ιV ⁻¹' V(K)) h := he_eq.symm ▸ heT
  obtain ⟨D_next, hPB_next, hU_next, hV_next, hE_keep, hE_new⟩ :=
    exists_subdiv_arc_mesh hh h31 hVK_fin hEK_fin hVK hEK hComp ha hδ2 n
      zero_lt_one le_rfl hn_le D_cur hPB_cur he_mem' he_T'
  rw [he_eq] at hE_keep hE_new
  refine ⟨D_next, hPB_next, hU_next, hV_next, hE_keep, ?_⟩
  intro f hf
  obtain ⟨hf_line, s₁, s₂, hs₁, hs₁₂, hs₂1, h_len, hcl_f⟩ := hE_new f hf
  refine ⟨?_, hf_line, ?_, ?_⟩
  · rw [hcl_f, ← hIcc_eq]
    exact image_mono (Icc_subset_Icc hs₁ hs₂1)
  · intro i ⟨x, hxf, hxW⟩
    rw [disjoint_left]
    intro y hyf hyB
    rw [hcl_f] at hxf hyf
    rcases hxf with ⟨p_t, hp_t, rfl⟩
    rcases hyf with ⟨q_t, hq_t, rfl⟩
    have hp_Icc : p_t ∈ Icc (0 : ℝ) 1 := ⟨hs₁.trans hp_t.1, hp_t.2.trans hs₂1⟩
    have hq_Icc : q_t ∈ Icc (0 : ℝ) 1 := ⟨hs₁.trans hq_t.1, hq_t.2.trans hs₂1⟩
    have hpq_K : (p_t, q_t) ∈ K_all :=
      mem_iUnion.mpr ⟨i, ⟨hp_Icc, hxW⟩, ⟨hq_Icc, hyB⟩⟩
    have h_low : δ ≤ |p_t - q_t| := hδ_le (p_t, q_t) hpq_K
    have h_up : |p_t - q_t| ≤ (δ / 2) / 2 :=
      abs_sub_le_iff.mpr ⟨by linarith [hp_t.1, hp_t.2, hq_t.1, hq_t.2],
        by linarith [hp_t.1, hp_t.2, hq_t.1, hq_t.2]⟩
    linarith
  · intro f' hf' i j hij ⟨x, hxf, hxW⟩ ⟨y, hyf', hyW⟩
    obtain ⟨_, t₁, t₂, ht₁, ht₁₂, ht₂1, h_len', hcl_f'⟩ := hE_new f' hf'
    rw [disjoint_left]
    intro z hzf hzf'
    rw [hcl_f] at hxf hzf
    rw [hcl_f'] at hyf' hzf'
    rcases hxf with ⟨p_t, hp_t, rfl⟩
    rcases hyf' with ⟨q_t, hq_t, rfl⟩
    rcases hzf with ⟨r₁, hr₁, rfl⟩
    rcases hzf' with ⟨r₂, hr₂, hr_eq⟩
    have hp_Icc : p_t ∈ Icc (0 : ℝ) 1 := ⟨hs₁.trans hp_t.1, hp_t.2.trans hs₂1⟩
    have hq_Icc : q_t ∈ Icc (0 : ℝ) 1 := ⟨ht₁.trans hq_t.1, hq_t.2.trans ht₂1⟩
    have hr₁_Icc : r₁ ∈ Icc (0 : ℝ) 1 := ⟨hs₁.trans hr₁.1, hr₁.2.trans hs₂1⟩
    have hr₂_Icc : r₂ ∈ Icc (0 : ℝ) 1 := ⟨ht₁.trans hr₂.1, hr₂.2.trans ht₂1⟩
    have hr₁₂ : r₁ = r₂ := extI_injOn ha.2 hr₁_Icc hr₂_Icc hr_eq.symm
    have hpq_K : (p_t, q_t) ∈ K_all :=
      mem_iUnion.mpr ⟨i, ⟨hp_Icc, hxW⟩, ⟨hq_Icc, hW_sub_B i j hij hyW⟩⟩
    have h_low : δ ≤ |p_t - q_t| := hδ_le (p_t, q_t) hpq_K
    have h_up₁ : |p_t - r₁| ≤ (δ / 2) / 2 :=
      abs_sub_le_iff.mpr ⟨by linarith [hp_t.1, hp_t.2, hr₁.1, hr₁.2],
        by linarith [hp_t.1, hp_t.2, hr₁.1, hr₁.2]⟩
    have h_up₂ : |r₂ - q_t| ≤ (δ / 2) / 2 :=
      abs_sub_le_iff.mpr ⟨by linarith [hq_t.1, hq_t.2, hr₂.1, hr₂.2],
        by linarith [hq_t.1, hq_t.2, hr₂.1, hr₂.2]⟩
    have h_tri : |p_t - q_t| ≤ |p_t - r₁| + |r₂ - q_t| := by
      rw [hr₁₂]
      exact abs_sub_le p_t r₂ q_t
    linarith

/-- Phase 1, Step 3: Finely subdividing all edges in `D₂.E \ (D.E ∩ D'.E)` with respect to the
pairwise disjoint closed component sets `W : Fin k → Set S`. -/
theorem exists_pullback_fine_subdiv [DecidableEq α] {h p : ℕ} (hh : 1 ≤ h)
    (h31 : ∀ (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
      Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
      ∀ (D₂ : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D₂.toEmbeddedGraph ιV ιE →
      ∀ v₀ ∈ D₂.V, IsInsulated D₂ (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
      ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
      ∃ L' ≤ G.deleteVerts {ιV v₀},
        HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L)
    {D D' D₂ : Drawing S} {K : Graph α β} {ιV : S ↪ α} {ιE : Set S ↪ β}
    (hVK_fin : V(K).Finite) (hEK_fin : E(K).Finite)
    (hVK : ιV ⁻¹' V(K) ⊆ D.V) (hEK : ιE ⁻¹' E(K) ⊆ D.E)
    (hComp : (D.toEmbeddedGraph ιV ιE).Compatible K)
    (hPB₂ : PullbackTo h p D K ιV ιE D₂)
    (hEE₂ : D.E ∩ D'.E ⊆ D₂.E)
    (hcl₂ : ∀ f ∈ D₂.E \ (D.E ∩ D'.E),
      closure f ⊆ insulatedSet D (ιV ⁻¹' V(K)) h ∧ IsLineEdge D₂ f)
    {k : ℕ} (W : Fin k → Set S)
    (hW_cl : ∀ i, IsClosed (W i))
    (hW_disj : Pairwise (Disjoint on W)) :
    let B : Fin k → Set S := fun i => (D₂.V \ W i) ∪ ⋃ j ∈ ({i}ᶜ : Set (Fin k)), W j
    ∃ D₃ : Drawing S,
      PullbackTo h p D K ιV ιE D₃ ∧
      D₃.U = D₂.U ∧
      D₂.V ⊆ D₃.V ∧
      D.E ∩ D'.E ⊆ D₃.E ∧
      (∀ f ∈ D₃.E \ (D.E ∩ D'.E),
        closure f ⊆ insulatedSet D (ιV ⁻¹' V(K)) h ∧
        IsLineEdge D₃ f ∧
        ∀ i : Fin k, (closure f ∩ W i).Nonempty → Disjoint (closure f) (B i)) ∧
      (∀ f₁ ∈ D₃.E \ (D.E ∩ D'.E), ∀ f₂ ∈ D₃.E \ (D.E ∩ D'.E),
        ∀ i j : Fin k, i ≠ j →
          (closure f₁ ∩ W i).Nonempty → (closure f₂ ∩ W j).Nonempty →
          Disjoint (closure f₁) (closure f₂)) := by
  intro B
  let T := insulatedSet D (ιV ⁻¹' V(K)) h
  have hB_cl : ∀ i, IsClosed (B i) := by
    intro i
    refine IsClosed.union (D₂.finite_V.subset sdiff_subset).isClosed ?_
    exact (finite_univ.subset (subset_univ _)).isClosed_biUnion fun j _ => hW_cl j
  have hWB_disj : ∀ i, Disjoint (W i) (B i) := by
    intro i
    rw [disjoint_left]
    rintro x hxW (⟨_, hx_not⟩ | hx_union)
    · exact hx_not hxW
    · obtain ⟨j, hj, hxWj⟩ := mem_iUnion₂.mp hx_union
      exact disjoint_left.mp (hW_disj (Ne.symm hj)) hxW hxWj
  have hW_sub_B : ∀ i j, i ≠ j → W j ⊆ B i := by
    intro i j hij x hx
    exact Or.inr (mem_iUnion₂.mpr ⟨j, hij.symm, hx⟩)
  let E₀ := D₂.E \ (D.E ∩ D'.E)
  have hE₀_fin : E₀.Finite := D₂.finite_edges.subset sdiff_subset
  suffices ∀ F : Set (Set S), F.Finite → F ⊆ E₀ →
      ∃ D₃ : Drawing S,
        PullbackTo h p D K ιV ιE D₃ ∧
        D₃.U = D₂.U ∧
        D₂.V ⊆ D₃.V ∧
        D.E ∩ D'.E ⊆ D₃.E ∧
        E₀ \ F ⊆ D₃.E ∧
        (∀ f ∈ D₃.E \ (D.E ∩ D'.E),
          closure f ⊆ T ∧ IsLineEdge D₃ f ∧
          ∃ e₀ ∈ E₀, closure f ⊆ closure e₀ ∧ (e₀ ∈ E₀ \ F → f = e₀)) ∧
        (∀ f ∈ (D₃.E \ (D.E ∩ D'.E)) \ (E₀ \ F),
          ∀ i : Fin k, (closure f ∩ W i).Nonempty → Disjoint (closure f) (B i)) ∧
        (∀ f₁ ∈ (D₃.E \ (D.E ∩ D'.E)) \ (E₀ \ F),
          ∀ f₂ ∈ (D₃.E \ (D.E ∩ D'.E)) \ (E₀ \ F),
          ∀ i j : Fin k, i ≠ j →
            (closure f₁ ∩ W i).Nonempty → (closure f₂ ∩ W j).Nonempty →
            Disjoint (closure f₁) (closure f₂)) by
    obtain ⟨D₃, hPB₃, hU₃, hV₃, hEE₃, _, h_meta, h_fine, h_disj⟩ :=
      this E₀ hE₀_fin Subset.rfl
    rw [sdiff_self, sdiff_empty] at h_fine h_disj
    refine ⟨D₃, hPB₃, hU₃, hV₃, hEE₃, ?_, h_disj⟩
    intro f hf
    exact ⟨(h_meta f hf).1, (h_meta f hf).2.1, h_fine f hf⟩
  intro F hF
  refine Set.Finite.induction_on F hF ?_ ?_
  · intro _
    rw [sdiff_empty]
    refine ⟨D₂, hPB₂, rfl, Subset.rfl, hEE₂, sdiff_subset, ?_, ?_, ?_⟩
    · intro f hf
      exact ⟨(hcl₂ f hf).1, (hcl₂ f hf).2, f, hf, Subset.rfl, fun _ => rfl⟩
    · intro f hf
      exact (hf.2 hf.1).elim
    · intro f₁ hf₁
      exact (hf₁.2 hf₁.1).elim
  · rintro e F he_not_F hF_fin ih hF_sub
    have he_E₀ : e ∈ E₀ := hF_sub (mem_insert e F)
    have hF_sub' : F ⊆ E₀ := (subset_insert e F).trans hF_sub
    obtain ⟨D_cur, hPB_cur, hU_cur, hV_cur, hEE_cur, hrem_cur, h_meta, h_fine, h_disj⟩ :=
      ih hF_sub'
    have he_rem : e ∈ E₀ \ F := ⟨he_E₀, he_not_F⟩
    have he_cur : e ∈ D_cur.E := hrem_cur he_rem
    have he_diff : e ∈ D_cur.E \ (D.E ∩ D'.E) := ⟨he_cur, he_E₀.2⟩
    obtain ⟨heT, he_line, _⟩ := h_meta e he_diff
    obtain ⟨D_next, hPB_next, hU_next, hV_next, hE_keep, hE_new⟩ :=
      exists_subdiv_single_edge_fine hh h31 hVK_fin hEK_fin hVK hEK hComp hPB_cur
        he_cur heT he_line W B hW_cl hB_cl hWB_disj hW_sub_B
    refine ⟨D_next, hPB_next, hU_next.trans hU_cur, hV_cur.trans hV_next, ?_, ?_, ?_, ?_, ?_⟩
    · intro f hf
      exact hE_keep ⟨hEE_cur hf, fun hfe => he_E₀.2 (hfe ▸ hf)⟩
    · intro f hf
      exact hE_keep ⟨hrem_cur ⟨hf.1, fun hfF => hf.2 (Or.inr hfF)⟩,
        fun hfe => hf.2 (Or.inl hfe)⟩
    · intro f hf
      by_cases hf_keep : f ∈ D_cur.E \ {e}
      · have hf_cur_diff : f ∈ D_cur.E \ (D.E ∩ D'.E) := ⟨hf_keep.1, hf.2⟩
        obtain ⟨hfT, hf_line, e₀, he₀, hcl_sub, he₀_eq⟩ := h_meta f hf_cur_diff
        refine ⟨hfT, (IsLineEdge.iff_of_mem hf_keep.1 hf.1).mp hf_line,
          e₀, he₀, hcl_sub, fun he₀_rem => he₀_eq ⟨he₀_rem.1, fun hF' => he₀_rem.2 (Or.inr hF')⟩⟩
      · obtain ⟨hcl_sub, hf_line, _, _⟩ := hE_new f ⟨hf.1, hf_keep⟩
        refine ⟨hcl_sub.trans heT, hf_line, e, he_E₀, hcl_sub, fun h_abs => ?_⟩
        exact (h_abs.2 (Or.inl rfl)).elim
    · intro f hf i hne_W
      by_cases hf_keep : f ∈ D_cur.E \ {e}
      · refine h_fine f ⟨⟨hf_keep.1, hf.1.2⟩, ?_⟩ i hne_W
        rintro ⟨hf_E₀, hf_not_F⟩
        rcases eq_or_ne f e with rfl | hfe
        · exact hf_keep.2 rfl
        · exact hf.2 ⟨hf_E₀, fun h_ins => hf_not_F (h_ins.resolve_left hfe)⟩
      · exact (hE_new f ⟨hf.1.1, hf_keep⟩).2.2.1 i hne_W
    · intro f₁ hf₁ f₂ hf₂ i j hij hW₁ hW₂
      by_cases hk₁ : f₁ ∈ D_cur.E \ {e} <;> by_cases hk₂ : f₂ ∈ D_cur.E \ {e}
      · have hf₁' : f₁ ∈ (D_cur.E \ (D.E ∩ D'.E)) \ (E₀ \ F) := by
          refine ⟨⟨hk₁.1, hf₁.1.2⟩, fun h => ?_⟩
          exact hf₁.2 ⟨h.1, fun h_ins => h.2 (h_ins.resolve_left hk₁.2)⟩
        have hf₂' : f₂ ∈ (D_cur.E \ (D.E ∩ D'.E)) \ (E₀ \ F) := by
          refine ⟨⟨hk₂.1, hf₂.1.2⟩, fun h => ?_⟩
          exact hf₂.2 ⟨h.1, fun h_ins => h.2 (h_ins.resolve_left hk₂.2)⟩
        exact h_disj f₁ hf₁' f₂ hf₂' i j hij hW₁ hW₂
      · have hf₁' : f₁ ∈ (D_cur.E \ (D.E ∩ D'.E)) \ (E₀ \ F) := by
          refine ⟨⟨hk₁.1, hf₁.1.2⟩, fun h => ?_⟩
          exact hf₁.2 ⟨h.1, fun h_ins => h.2 (h_ins.resolve_left hk₁.2)⟩
        obtain ⟨_, _, e₁, he₁, hcl₁, he₁_eq⟩ := h_meta f₁ ⟨hk₁.1, hf₁.1.2⟩
        have he₁_ne_e : e₁ ≠ e := fun h_eq => hf₁'.2 (by subst h_eq; rw [he₁_eq he_rem]; exact he_rem)
        have hcl₂ : closure f₂ ⊆ closure e := (hE_new f₂ ⟨hf₂.1.1, hk₂⟩).1
        have hdisj₁ : Disjoint (closure f₁) (B i) := h_fine f₁ hf₁' i hW₁
        have hdisj₂ : Disjoint (closure f₂) (B j) := (hE_new f₂ ⟨hf₂.1.1, hk₂⟩).2.2.1 j hW₂
        rw [disjoint_left]
        intro z hz₁ hz₂
        have hzV₂ : z ∈ D₂.V :=
          closure_inter_subset_V he₁.1 he_E₀.1 he₁_ne_e ⟨hcl₁ hz₁, hcl₂ hz₂⟩
        have hzW_i : z ∈ W i := by_contra fun hn => disjoint_left.mp hdisj₁ hz₁ (Or.inl ⟨hzV₂, hn⟩)
        have hzW_j : z ∈ W j := by_contra fun hn => disjoint_left.mp hdisj₂ hz₂ (Or.inl ⟨hzV₂, hn⟩)
        exact disjoint_left.mp (hW_disj hij) hzW_i hzW_j
      · have hf₂' : f₂ ∈ (D_cur.E \ (D.E ∩ D'.E)) \ (E₀ \ F) := by
          refine ⟨⟨hk₂.1, hf₂.1.2⟩, fun h => ?_⟩
          exact hf₂.2 ⟨h.1, fun h_ins => h.2 (h_ins.resolve_left hk₂.2)⟩
        obtain ⟨_, _, e₂, he₂, hcl₂, he₂_eq⟩ := h_meta f₂ ⟨hk₂.1, hf₂.1.2⟩
        have he₂_ne_e : e₂ ≠ e := fun h_eq => hf₂'.2 (by subst h_eq; rw [he₂_eq he_rem]; exact he_rem)
        have hcl₁ : closure f₁ ⊆ closure e := (hE_new f₁ ⟨hf₁.1.1, hk₁⟩).1
        have hdisj₁ : Disjoint (closure f₁) (B i) := (hE_new f₁ ⟨hf₁.1.1, hk₁⟩).2.2.1 i hW₁
        have hdisj₂ : Disjoint (closure f₂) (B j) := h_fine f₂ hf₂' j hW₂
        rw [disjoint_left]
        intro z hz₁ hz₂
        have hzV₂ : z ∈ D₂.V :=
          closure_inter_subset_V he_E₀.1 he₂.1 he₂_ne_e.symm ⟨hcl₁ hz₁, hcl₂ hz₂⟩
        have hzW_i : z ∈ W i := by_contra fun hn => disjoint_left.mp hdisj₁ hz₁ (Or.inl ⟨hzV₂, hn⟩)
        have hzW_j : z ∈ W j := by_contra fun hn => disjoint_left.mp hdisj₂ hz₂ (Or.inl ⟨hzV₂, hn⟩)
        exact disjoint_left.mp (hW_disj hij) hzW_i hzW_j
      · exact (hE_new f₁ ⟨hf₁.1.1, hk₁⟩).2.2.2 f₂ ⟨hf₂.1.1, hk₂⟩ i j hij hW₁ hW₂

end Pullback

end GraphMinor.GM22
