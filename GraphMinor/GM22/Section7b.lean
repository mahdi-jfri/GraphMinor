module

public import GraphMinor.GM22.Section7
public import GraphMinor.GM22.Parallel
public import GraphMinor.GM22.Cited
import GraphMinor.GM22.ParallelProofs
import GraphMinor.GM11.CitedResults
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM12.Section79

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 7: Lemma 7.2 (page 547)

This file formalizes **7.2** (`theorem_7_2`) and its claims (`lemma_7_2_claim_1`,
`lemma_7_2_claim_2`) from Section 7 of:
N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (page 547).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Topology Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 Hypergraph

universe w u v u₁ v₁

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}

/-! ## 1. Helper Lemmas on `graphUnion`, `IsInsulated`, and `subsetTangleDist` -/

@[simp]
theorem vertexSet_graphUnion (G₁ G₂ : Graph α β) :
    V(graphUnion G₁ G₂) = V(G₁) ∪ V(G₂) :=
  rfl

@[simp]
theorem edgeSet_graphUnion (G₁ G₂ : Graph α β) :
    E(graphUnion G₁ G₂) = E(G₁) ∪ E(G₂) :=
  rfl

theorem le_graphUnion_left (G₁ G₂ : Graph α β) :
    G₁ ≤ graphUnion G₁ G₂ :=
  ⟨subset_union_left, fun _ _ _ h => Or.inl h⟩

theorem le_graphUnion_right {G₁ G₂ : Graph α β} (hComp : G₁.Compatible G₂) :
    G₂ ≤ graphUnion G₁ G₂ := by
  refine ⟨subset_union_right, fun e x y h => ?_⟩
  by_cases he₁ : e ∈ E(G₁)
  · exact Or.inl ((hComp he₁ h.edge_mem x y).mpr h)
  · exact Or.inr ⟨he₁, h⟩

theorem graphUnion_le {G₁ G₂ G : Graph α β} (h₁ : G₁ ≤ G) (h₂ : G₂ ≤ G) :
    graphUnion G₁ G₂ ≤ G := by
  refine ⟨union_subset h₁.vertexSet_mono h₂.vertexSet_mono, ?_⟩
  rintro e x y (h | ⟨_, h⟩)
  · exact h.mono h₁
  · exact h.mono h₂

theorem graphUnion_isLink {G₁ G₂ : Graph α β} (hComp : G₁.Compatible G₂) {e : β} {x y : α} :
    (graphUnion G₁ G₂).IsLink e x y ↔ G₁.IsLink e x y ∨ G₂.IsLink e x y := by
  constructor
  · rintro (h | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases he₁ : e ∈ E(G₁)
      · exact Or.inl ((hComp he₁ h.edge_mem x y).mpr h)
      · exact Or.inr ⟨he₁, h⟩

omit [T2Space S] in
/-- Monotonicity of `IsInsulated` in the target set $Y$: if $X \subseteq Y$ and $x$ is
$h$-insulated from $Y$ by $\Gamma$, then $x$ is $h$-insulated from $X$ by $\Gamma$. -/
theorem IsInsulated.anti {Γ : Drawing S} {X Y : Set S} {h : ℕ} {x : S}
    (hXY : X ⊆ Y) (hIns : IsInsulated Γ Y h x) :
    IsInsulated Γ X h x := by
  rcases hIns with ⟨Δ, hDisc, hNest, hBase⟩
  refine ⟨Δ, hDisc, hNest, fun hpos => ?_⟩
  obtain ⟨hx_in, hDisj⟩ := hBase hpos
  exact ⟨hx_in, hDisj.mono_left hXY⟩

/-- Symmetry of `subsetTangleDist` when $d$ is symmetric on $A(\Gamma)$. -/
theorem subsetTangleDist_comm {Γ : Drawing S} {ord : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))} {d : Set S → Set S → ℕ}
    (hM : HasTangleMetric Γ ord T d) (X Y : Set S) :
    subsetTangleDist Γ ord d X Y = subsetTangleDist Γ ord d Y X := by
  classical
  have hex_iff : (∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty) ↔
      (∃ b ∈ Γ.A, ∃ a ∈ Γ.A, (b ∩ Y).Nonempty ∧ (a ∩ X).Nonempty) :=
    ⟨fun ⟨a, ha, b, hb, haX, hbY⟩ => ⟨b, hb, a, ha, hbY, haX⟩,
      fun ⟨b, hb, a, ha, hbY, haX⟩ => ⟨a, ha, b, hb, haX, hbY⟩⟩
  have hset_eq : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty ∧ d a b = k} =
      {k : ℕ | ∃ b ∈ Γ.A, ∃ a ∈ Γ.A, (b ∩ Y).Nonempty ∧ (a ∩ X).Nonempty ∧ d b a = k} := by
    ext k
    simp only [mem_ofPred_eq]
    constructor
    · rintro ⟨a, ha, b, hb, haX, hbY, rfl⟩
      exact ⟨b, hb, a, ha, hbY, haX, HasTangleMetric.comm hM hb ha⟩
    · rintro ⟨b, hb, a, ha, hbY, haX, rfl⟩
      exact ⟨a, ha, b, hb, haX, hbY, HasTangleMetric.comm hM ha hb⟩
  unfold subsetTangleDist
  by_cases hex : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ X).Nonempty ∧ (b ∩ Y).Nonempty
  · have hex' := hex_iff.mp hex
    simp only [hex, hex', ↓reduceIte, hset_eq]
  · have hex' : ¬ ∃ b ∈ Γ.A, ∃ a ∈ Γ.A, (b ∩ Y).Nonempty ∧ (a ∩ X).Nonempty :=
      fun h => hex (hex_iff.mpr h)
    simp only [hex, hex', ↓reduceIte]

/-- For vertices $u, v \in V(\Gamma)$, `subsetTangleDist Γ ord d {u} {v} = d {u} {v}`. -/
theorem subsetTangleDist_singleton_singleton {Γ : Drawing S} {ord : ℕ} {d : Set S → Set S → ℕ}
    {u v : S} (hu : u ∈ Γ.V) (hv : v ∈ Γ.V) :
    subsetTangleDist Γ ord d {u} {v} = d {u} {v} := by
  classical
  have huA : ({u} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨u, hu, rfl⟩)
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hex : ∃ a ∈ Γ.A, ∃ b ∈ Γ.A, (a ∩ {u}).Nonempty ∧ (b ∩ {v}).Nonempty :=
    ⟨{u}, huA, {v}, hvA, ⟨u, rfl, rfl⟩, ⟨v, rfl, rfl⟩⟩
  have hset : {k : ℕ | ∃ a ∈ Γ.A, ∃ b ∈ Γ.A,
      (a ∩ {u}).Nonempty ∧ (b ∩ {v}).Nonempty ∧ d a b = k} = {d {u} {v}} := by
    ext k
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨a, ha, b, hb, ⟨x, hxa, rfl⟩, ⟨y, hyb, rfl⟩, rfl⟩
      have ha_eq : a = {x} := GM12.atom_eq_of_inter_nonempty ha huA ⟨x, hxa, rfl⟩
      have hb_eq : b = {y} := GM12.atom_eq_of_inter_nonempty hb hvA ⟨y, hyb, rfl⟩
      rw [ha_eq, hb_eq]
    · rintro rfl
      exact ⟨{u}, huA, {v}, hvA, ⟨u, rfl, rfl⟩, ⟨v, rfl, rfl⟩, rfl⟩
  simp only [subsetTangleDist, hex, ↓reduceIte, hset, csInf_singleton]

/-! ## 2. Models in `G.deleteVerts` and `SystemJ1ToJ6` Root Membership -/

/-- If a model $(\phi_V, \phi_E)$ of $R_H$ in $R_G$ has $\phi_V(v) \le G \setminus S_0$ for all
$v \in V(H)$, then $(\phi_V, \phi_E)$ is also a model of $R_H$ in $(G \setminus S_0, \omega)$. -/
theorem IsRootedDigraphModel.toDeleteVerts {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {S₀ : Set α}
    (hMod : IsRootedDigraphModel R_G R_H φV φE)
    (hroots : ∀ i : Fin q, R_G.roots i ∈ V(R_G.G.toGraph.deleteVerts S₀))
    (hφV_le : ∀ v ∈ V(R_H.G.toGraph), φV v ≤ R_G.G.toGraph.deleteVerts S₀) :
    IsRootedDigraphModel
      (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts S₀) Graph.deleteVerts_le R_G.roots hroots)
      R_H φV φE := by
  refine ⟨hφV_le, hMod.connected_of_mem, hMod.disjoint_V, hMod.root_mem, ?_,
    hMod.injOn_E, hMod.edge_not_mem_φV, hMod.head_mem, hMod.tail_mem⟩
  intro e he
  have hlink_G : R_G.G.toGraph.IsLink (φE e) (R_G.G.tail (φE e)) (R_G.G.head (φE e)) :=
    R_G.G.isLink_of_mem (φE e) (hMod.edge_mem e he)
  have ht_mem : R_G.G.tail (φE e) ∈ V(R_G.G.toGraph.deleteVerts S₀) :=
    (hφV_le (R_H.G.tail e) (R_H.G.isLink_of_mem e he).left_mem).vertexSet_mono
      (hMod.tail_mem e he)
  have hh_mem : R_G.G.head (φE e) ∈ V(R_G.G.toGraph.deleteVerts S₀) :=
    (hφV_le (R_H.G.head e) (R_H.G.isLink_of_mem e he).right_mem).vertexSet_mono
      (hMod.head_mem e he)
  rw [Graph.vertexSet_deleteVerts] at ht_mem hh_mem
  have hlink_del :
      (R_G.G.toGraph.deleteVerts S₀).IsLink (φE e) (R_G.G.tail (φE e)) (R_G.G.head (φE e)) := by
    rw [Graph.deleteVerts_isLink]
    exact ⟨hlink_G, ht_mem.2, hh_mem.2⟩
  exact hlink_del.edge_mem

/-- Under `(J1)`–`(J6)`, every root $w_i$ of $R_G$ belongs to $V(G \setminus \{v^*\})$. -/
theorem SystemJ1ToJ6.roots_mem_deleteVerts_v_star {q : ℕ}
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
    (i : Fin q) :
    R_G.roots i ∈ V(R_G.G.toGraph.deleteVerts {ιV v_star}) := by
  rw [Graph.vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff]
  refine ⟨R_G.roots_mem i, ?_⟩
  intro heq
  have hv_mem : ιV v_star ∈ V(R_G.G.toGraph.deleteVerts W) :=
    hJ.Γ_le.vertexSet_mono ⟨v_star, hJ.v_star_mem.1, rfl⟩
  rw [Graph.vertexSet_deleteVerts] at hv_mem
  apply hv_mem.2
  rw [hJ.W_eq, ← heq]
  exact ⟨i, rfl⟩

/-! ## 3. Claims (1) and (2) and Proof of 7.2 (page 547) -/

/-- **Graph Minors XXII, (7.2) Claim (1)** (page 547):
(1) "$v^*$ is $h$-insulated from $V(\Gamma \cap K')$ by $\Gamma$." -/
theorem lemma_7_2_claim_1 {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 𝒜' : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord h : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (h𝒜'_sub : 𝒜' ⊆ 𝒜)
    (hh1 : 1 ≤ h) (hθ : θ = 2 * h + 5)
    (hdist_𝒜' : ∀ A ∈ 𝒜', θ ≤ subsetTangleDist Γ ord d {v_star} (D A)) :
    let K' := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜')
    IsInsulated Γ {v ∈ Γ.V | ιV v ∈ V(K')} h v_star := by
  intro K'
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hJ.v_star_mem.1, rfl⟩)
  have hdist_pt : ∀ v ∈ Γ.V, ιV v ∈ V(K') → 2 * h + 5 ≤ d {v} {v_star} := by
    intro v hv hvK'
    have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
    rw [← hθ]
    rcases hvK' with hvK | hvU
    · have hd1 : θ ≤ subsetTangleDist Γ ord d {v} (Set.univ \ Δ) :=
        hJ.dist_Γ_inter_K v hv hvK
      have hv_star_diff : ({v_star} : Set S) ⊆ Set.univ \ Δ :=
        singleton_subset_iff.mpr ⟨trivial, hJ.v_star_mem.2⟩
      have hd2 : subsetTangleDist Γ ord d {v} (Set.univ \ Δ) ≤
          subsetTangleDist Γ ord d {v} {v_star} :=
        subsetTangleDist_anti (fun a ha b hb => HasTangleMetric.le_ord hJ.hasMetric ha hb)
          Subset.rfl hv_star_diff
      rw [subsetTangleDist_singleton_singleton hv hJ.v_star_mem.1] at hd2
      exact hd1.trans hd2
    · rw [vertexSet_subgraphSUnion, mem_iUnion₂] at hvU
      rcases hvU with ⟨A, hA', hvA_mem⟩
      have hA : A ∈ 𝒜 := h𝒜'_sub hA'
      have hv_inter : ιV v ∈ V((Γ.toEmbeddedGraph ιV ιE) ⊓ A) := ⟨⟨v, hv, rfl⟩, hvA_mem⟩
      rw [← hJ.Γ_inter_D A hA] at hv_inter
      rcases hv_inter with ⟨v', hv', hvv'⟩
      have hv_eq : v' = v := ιV.injective hvv'
      subst v'
      have hvD_mem : v ∈ D A := by
        rcases hv' with ⟨⟨_, hvD⟩, _⟩ | hvE
        · exact hvD
        · rw [mem_iUnion₂] at hvE
          rcases hvE with ⟨e, ⟨⟨_, heD⟩, _⟩, hve, _⟩
          exact (hJ.disc_D A hA).1.isClosed.closure_subset_iff.mpr heD hve
      have hd1 : θ ≤ subsetTangleDist Γ ord d {v_star} (D A) := hdist_𝒜' A hA'
      have hd2 : subsetTangleDist Γ ord d {v_star} (D A) ≤ d {v_star} {v} :=
        subsetTangleDist_le_of_mem hv_star_A hvA ⟨v_star, rfl, rfl⟩ ⟨v, rfl, hvD_mem⟩
      rw [HasTangleMetric.comm hJ.hasMetric hvA hv_star_A]
      exact hd1.trans hd2
  let Y := ⋃ y ∈ {y ∈ Γ.A | 2 * h + 5 ≤ d y {v_star}}, y
  have hord : 2 * h + 5 ≤ ord := hθ ▸ hJ.θ_le_ord
  have hIns_Y : IsInsulated Γ Y h v_star :=
    theorem_5_2_parallel.{w} h Γ ord T d v_star {v_star} Y hh1 hS hord hJ.hasMetric hv_star_A (mem_singleton v_star) rfl
  refine hIns_Y.anti ?_
  rintro v ⟨hv, hvK'⟩
  have hvA : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  exact mem_biUnion ⟨hvA, hdist_pt v hv hvK'⟩ (mem_singleton v)

/-- **Graph Minors XXII, (7.2) Claim (2)** (page 547):
(2) *There is a basis $Z$ for $\phi'$ with $Z \subseteq V(K')$.* -/
theorem lemma_7_2_claim_2 {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 𝒜' : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV φV' : αH → Graph α β} {φE φE' : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hAdequate : IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φV' φE') :
    let K' := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜')
    IsModelBasis R_G R_H φV' φE' V(K') := by
  intro K'
  have hP_le : ∀ A ∈ 𝒜', A ≤ R_G.G.toGraph :=
    fun A hA' => hJ.le_of_mem_𝒜 A (hAdequate.subset hA')
  have hK'_le : K' ≤ R_G.G.toGraph :=
    graphUnion_le hJ.sep_NK.1.2.1 (subgraphSUnion_le hP_le)
  have hEK' : E(K') = E(K) ∪ ⋃ A ∈ 𝒜', E(A) := by
    rw [edgeSet_graphUnion, edgeSet_subgraphSUnion hP_le]
  have hVK' : V(K') = V(K) ∪ ⋃ A ∈ 𝒜', V(A) := by
    rw [vertexSet_graphUnion, vertexSet_subgraphSUnion]
  refine ⟨hK'_le.vertexSet_mono, ?_, ?_, ?_, ?_⟩
  · intro i
    have hriW : R_G.roots i ∈ W := by
      rw [hJ.W_eq]
      exact ⟨i, rfl⟩
    exact Or.inl (hJ.sep_NK.2 hriW).2
  · intro e he
    have heK' : φE' e ∈ E(K') := by
      rw [hEK']
      exact hAdequate.φE_mem e he
    have hlink_G : R_G.G.toGraph.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      R_G.G.isLink_of_mem (φE' e) (hK'_le.edgeSet_mono heK')
    have hlink_K' : K'.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      (hK'_le.isLink_iff heK').mpr hlink_G
    exact hlink_K'.right_mem
  · intro e he
    have heK' : φE' e ∈ E(K') := by
      rw [hEK']
      exact hAdequate.φE_mem e he
    have hlink_G : R_G.G.toGraph.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      R_G.G.isLink_of_mem (φE' e) (hK'_le.edgeSet_mono heK')
    have hlink_K' : K'.IsLink (φE' e) (R_G.G.tail (φE' e)) (R_G.G.head (φE' e)) :=
      (hK'_le.isLink_iff heK').mpr hlink_G
    exact hlink_K'.left_mem
  · intro v hv
    rw [Set.inter_comm, hVK']
    exact hAdequate.φV_meets v hv

/-- Under `(J1)`–`(J6)` and `IsAdequateFor`, every branch set $\phi'(v)$ ($v \in V(H)$) is a
subgraph of $\Gamma \cup K'$, where $K' = K \cup \bigcup(A : A \in \mathcal{A}')$. -/
theorem IsAdequateFor.φV_le_Γ_union_K' {q : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {𝒜 𝒜' : Set (Graph α β)} {πLen : Graph α β → ℕ} {πS : ∀ A : Graph α β, Fin (πLen A) → S}
    {Γ : Drawing S} {orient : GM19.SurfaceOrientation S}
    {θ ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Set S → Set S} {d : Set S → Set S → ℕ}
    {D : Graph α β → Set S}
    {N K : Graph α β} {Δ : Set S} {v_star : S}
    {δ : ℕ} {R_H : RootedDigraph αH βH q}
    {φV φV' : αH → Graph α β} {φE φE' : βH → β}
    (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE)
    (hMod' : IsRootedDigraphModel R_G R_H φV' φE')
    (hAdequate : IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φV' φE')
    {v : αH} (hv : v ∈ V(R_H.G.toGraph)) :
    let K' := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜')
    φV' v ≤ graphUnion (Γ.toEmbeddedGraph ιV ιE) K' := by
  classical
  intro K'
  have hP_le : ∀ A ∈ 𝒜, A ≤ R_G.G.toGraph := hJ.le_of_mem_𝒜
  have hP'_le : ∀ A ∈ 𝒜', A ≤ R_G.G.toGraph :=
    fun A hA' => hJ.le_of_mem_𝒜 A (hAdequate.subset hA')
  have hΓ_G : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph :=
    hJ.Γ_le.trans Graph.deleteVerts_le
  have hK'_G : K' ≤ R_G.G.toGraph :=
    graphUnion_le hJ.sep_NK.1.2.1 (subgraphSUnion_le hP'_le)
  have hG₀_G : graphUnion (Γ.toEmbeddedGraph ιV ιE) K' ≤ R_G.G.toGraph :=
    graphUnion_le hΓ_G hK'_G
  have hφ_G : φV' v ≤ R_G.G.toGraph := hMod'.subgraph_of_mem v hv
  have hComp : (φV' v).Compatible (graphUnion (Γ.toEmbeddedGraph ιV ιE) K') :=
    Compatible.of_le_le hφ_G hG₀_G
  have hVG : V(R_G.G.toGraph) = V(N) ∪ V(K) := hJ.sep_NK.1.2.2.1.symm
  have hEG : E(R_G.G.toGraph) = E(N) ∪ E(K) := hJ.sep_NK.1.2.2.2.1.symm
  have hVN : V(N) = V(Γ.toEmbeddedGraph ιV ιE) ∪ W ∪ ⋃ A ∈ 𝒜, V(A) := by
    rw [hJ.N_eq, vertexSet_graphUnion, vertexSet_graphUnion, vertexSet_subgraphSUnion]
    rfl
  have hEN : E(N) = E(Γ.toEmbeddedGraph ιV ιE) ∪ ⋃ A ∈ 𝒜, E(A) := by
    rw [hJ.N_eq, edgeSet_graphUnion, edgeSet_graphUnion, Graph.edgeSet_noEdge, union_empty,
      edgeSet_subgraphSUnion hP_le]
  have hV_sub : V(φV' v) ⊆ V(graphUnion (Γ.toEmbeddedGraph ιV ιE) K') := by
    intro x hx
    have hxG : x ∈ V(R_G.G.toGraph) := hφ_G.vertexSet_mono hx
    rw [hVG, hVN] at hxG
    rcases hxG with ((hxΓ | hxW) | hxU) | hxK
    · exact Or.inl hxΓ
    · exact Or.inr (Or.inl (hJ.sep_NK.2 hxW).2)
    · rw [mem_iUnion₂] at hxU
      rcases hxU with ⟨A, hA, hxA⟩
      by_cases hA' : A ∈ 𝒜'
      · exact Or.inr (Or.inr (mem_iUnion₂.mpr ⟨A, hA', hxA⟩))
      · have hle_ΓW : A ⊓ φV' v ≤ graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β) := by
          by_contra hnot
          exact hA' (hAdequate.mem_of_not_le_Γ_union_NW v hv A hA hnot)
        have hx_inter : x ∈ V(A ⊓ φV' v) := ⟨hxA, hx⟩
        rcases hle_ΓW.vertexSet_mono hx_inter with hxΓ | hxW
        · exact Or.inl hxΓ
        · exact Or.inr (Or.inl (hJ.sep_NK.2 hxW).2)
    · exact Or.inr (Or.inl hxK)
  have hE_sub : E(φV' v) ⊆ E(graphUnion (Γ.toEmbeddedGraph ιV ιE) K') := by
    intro e he
    have heG : e ∈ E(R_G.G.toGraph) := hφ_G.edgeSet_mono he
    rw [hEG, hEN] at heG
    rcases heG with (heΓ | heU) | heK
    · exact Or.inl heΓ
    · rw [mem_iUnion₂] at heU
      rcases heU with ⟨A, hA, heA⟩
      by_cases hA' : A ∈ 𝒜'
      · refine Or.inr (Or.inr ?_)
        rw [edgeSet_subgraphSUnion hP'_le, mem_iUnion₂]
        exact ⟨A, hA', heA⟩
      · have hle_ΓW : A ⊓ φV' v ≤ graphUnion (Γ.toEmbeddedGraph ιV ιE) (Graph.noEdge W β) := by
          by_contra hnot
          exact hA' (hAdequate.mem_of_not_le_Γ_union_NW v hv A hA hnot)
        obtain ⟨x, y, hxy_φ⟩ := (φV' v).exists_isLink_of_mem_edgeSet he
        have hxy_G : R_G.G.toGraph.IsLink e x y := hxy_φ.mono hφ_G
        have hxy_A : A.IsLink e x y := ((hJ.le_of_mem_𝒜 A hA).isLink_iff heA).mpr hxy_G
        have hxy_inter : (A ⊓ φV' v).IsLink e x y := ⟨hxy_A, hxy_φ⟩
        rcases hle_ΓW.edgeSet_mono hxy_inter.edge_mem with heΓ | heW
        · exact Or.inl heΓ
        · simp at heW
    · exact Or.inr (Or.inl heK)
  refine ⟨hV_sub, fun e x y hlink => ?_⟩
  have he_mem : e ∈ E(graphUnion (Γ.toEmbeddedGraph ιV ιE) K') := hE_sub hlink.edge_mem
  exact (hComp hlink.edge_mem he_mem x y).mp hlink

/-- **Graph Minors XXII, (7.2)** (page 547):
"For all $q, \delta \ge 0$ there exists $\theta \ge 4$ with the following property. Let (J1)–(J6)
hold, and let $\mathcal{A}' \subseteq \mathcal{A}$ be adequate for some model $\phi'$ of
$(H, \chi)$ in $(G, \omega)$, where $d(v^*, D(A)) \ge \theta$ for all $A \in \mathcal{A}'$. Then
there is a model of $(H, \chi)$ in $(G \setminus \{v^*\}, \omega)$." -/
theorem theorem_7_2_proof
    (q δ : ℕ) :
    ∃ θ : ℕ, 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} {αH : Type u₁} {βH : Type v₁}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (𝒜 𝒜' : Set (Graph α β)) (πLen : Graph α β → ℕ) (πS : ∀ A : Graph α β, Fin (πLen A) → S)
        (Γ : Drawing S) (orient : GM19.SurfaceOrientation S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (ins : Set S → Set S) (d : Set S → Set S → ℕ)
        (D : Graph α β → Set S)
        (N K : Graph α β) (Δ : Set S) (v_star : S)
        (R_H : RootedDigraph αH βH q)
        (φV φV' : αH → Graph α β) (φE φE' : βH → β)
        (hJ : SystemJ1ToJ6 ιV ιE R_G W 𝒜 πLen πS Γ orient θ ord T ins d D N K Δ v_star δ R_H φV φE),
        IsRootedDigraphModel R_G R_H φV' φE' →
        IsAdequateFor ιV ιE W 𝒜 𝒜' Γ K R_H φV' φE' →
        (∀ A ∈ 𝒜', θ ≤ subsetTangleDist Γ ord d {v_star} (D A)) →
        HasRootedDigraphModel
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots hJ.roots_mem_deleteVerts_v_star)
          R_H := by
  classical
  let p := q + 3 * δ
  obtain ⟨h, hh1, h31_spec⟩ := theorem_3_1_parallel.{w, u, v} p
  let θ := 2 * h + 5
  refine ⟨θ, by omega, ?_⟩
  intro S _ _ α β αH βH ιV ιE R_G W 𝒜 𝒜' πLen πS Γ orient ord T ins d D N K Δ v_star R_H
    φV φV' φE φE' hJ hMod' hAdequate hdist_𝒜'
  obtain ⟨hS_closed, hConn⟩ := GM11.IsSphere.isClosedSurface hJ.isSphere
  have hS_surf : IsSurface S := IsClosedSurface.isSurface hS_closed
  let K' := graphUnion K (subgraphSUnion R_G.G.toGraph 𝒜')
  let G₀ := graphUnion (Γ.toEmbeddedGraph ιV ιE) K'
  have hP'_le : ∀ A ∈ 𝒜', A ≤ R_G.G.toGraph :=
    fun A hA' => hJ.le_of_mem_𝒜 A (hAdequate.subset hA')
  have hΓ_G : Γ.toEmbeddedGraph ιV ιE ≤ R_G.G.toGraph :=
    hJ.Γ_le.trans Graph.deleteVerts_le
  have hK'_G : K' ≤ R_G.G.toGraph :=
    graphUnion_le hJ.sep_NK.1.2.1 (subgraphSUnion_le hP'_le)
  have hG₀_G : G₀ ≤ R_G.G.toGraph := graphUnion_le hΓ_G hK'_G
  have hComp_Γ_K' : (Γ.toEmbeddedGraph ιV ιE).Compatible K' :=
    Compatible.of_le_le hΓ_G hK'_G
  -- Claim (1): `v_star` is `h`-insulated from `V(Γ ∩ K')` by `Γ`.
  have hIns : IsInsulated Γ {v ∈ Γ.V | ιV v ∈ V(K')} h v_star :=
    lemma_7_2_claim_1 hJ hAdequate.subset hh1 rfl hdist_𝒜'
  -- Claim (2): `V(K')` is a basis for `φ'`, so by 6.1 there is a basis `Z ⊆ V(K')` with `|Z| ≤ p`.
  have hBasis_K' : IsModelBasis R_G R_H φV' φE' V(K') :=
    lemma_7_2_claim_2 hJ hAdequate
  obtain ⟨Z, hZ_sub_K', hBasis_Z, hZ_card⟩ :=
    gm22_theorem_6_1 R_G R_H φV' φE' V(K') hJ.detail_H hMod' hBasis_K'
  -- Let `L = ⋃(φ'(v) : v ∈ V(H))`. By adequacy (i), `L ≤ G₀`.
  let L := subgraphSUnion R_G.G.toGraph (φV' '' V(R_H.G.toGraph))
  have hφ_le_G₀ : ∀ P ∈ φV' '' V(R_H.G.toGraph), P ≤ G₀ := by
    rintro _ ⟨v, hv, rfl⟩
    exact hAdequate.φV_le_Γ_union_K' hJ hMod' hv
  have hφ_le_G : ∀ P ∈ φV' '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph :=
    fun P hP => (hφ_le_G₀ P hP).trans hG₀_G
  have hL_le_G : L ≤ R_G.G.toGraph := subgraphSUnion_le hφ_le_G
  have hComp_L_G₀ : L.Compatible G₀ := Compatible.of_le_le hL_le_G hG₀_G
  have hL_le_G₀ : L ≤ G₀ := by
    refine ⟨?_, fun e x y hl => ?_⟩
    · rw [vertexSet_subgraphSUnion]
      exact iUnion₂_subset fun P hP => (hφ_le_G₀ P hP).vertexSet_mono
    · have he_sub : E(L) ⊆ E(G₀) := by
        rw [edgeSet_subgraphSUnion hφ_le_G]
        exact iUnion₂_subset fun P hP => (hφ_le_G₀ P hP).edgeSet_mono
      exact (hComp_L_G₀ hl.edge_mem (he_sub hl.edge_mem) x y).mp hl
  -- Apply 3.1 to `G₀ = Γ ∪ K'` with `K'`, `L`, `v_star`, and `Z`.
  obtain ⟨L', hL'_le_G₀_del, heff, hL'_inter_K'⟩ :=
    h31_spec ιV ιE G₀ K' L Γ v_star Z
      hS_surf
      (hJ.finite_V.subset hG₀_G.vertexSet_mono)
      (hJ.finite_E.subset hG₀_G.edgeSet_mono)
      (le_graphUnion_left _ _)
      (le_graphUnion_right hComp_Γ_K')
      rfl
      hJ.v_star_mem.1
      hIns
      hZ_sub_K'
      hZ_card
      hL_le_G₀
  have hL'_le_G_del : L' ≤ R_G.G.toGraph.deleteVerts {ιV v_star} := by
    refine ⟨?_, fun e x y hl => ?_⟩
    · refine hL'_le_G₀_del.vertexSet_mono.trans ?_
      rw [Graph.vertexSet_deleteVerts, Graph.vertexSet_deleteVerts]
      exact sdiff_le_sdiff_right hG₀_G.vertexSet_mono
    · have hl_G₀ := hl.mono hL'_le_G₀_del
      rw [Graph.deleteVerts_isLink] at hl_G₀ ⊢
      exact ⟨hl_G₀.1.mono hG₀_G, hl_G₀.2⟩
  have hL'_le_G : L' ≤ R_G.G.toGraph := hL'_le_G_del.trans Graph.deleteVerts_le
  -- Check `L' ≤ G \ φ'(E(H))` using `φ'(E(H)) ⊆ E(K')`, `φ'(E(H)) ∩ E(L) = ∅`, and `L' ⊓ K' ≤ L`.
  have hL'_le_delEdges : L' ≤ R_G.G.toGraph.deleteEdges (φE' '' E(R_H.G.toGraph)) := by
    refine ⟨by rw [Graph.vertexSet_deleteEdges]; exact hL'_le_G.vertexSet_mono, fun e x y hl => ?_⟩
    rw [Graph.deleteEdges_isLink]
    refine ⟨hl.mono hL'_le_G, ?_⟩
    rintro ⟨eH, heH, rfl⟩
    have hxy_G : R_G.G.toGraph.IsLink (φE' eH) x y := hl.mono hL'_le_G
    have heK' : φE' eH ∈ E(K') := by
      rw [edgeSet_graphUnion, edgeSet_subgraphSUnion hP'_le]
      exact hAdequate.φE_mem eH heH
    have hxy_K' : K'.IsLink (φE' eH) x y := (hK'_G.isLink_iff heK').mpr hxy_G
    have hxy_inter : (L' ⊓ K').IsLink (φE' eH) x y := ⟨hl, hxy_K'⟩
    have heL : φE' eH ∈ E(L) := hL'_inter_K'.edgeSet_mono hxy_inter.edge_mem
    rw [edgeSet_subgraphSUnion hφ_le_G, mem_iUnion₂] at heL
    rcases heL with ⟨_, ⟨v, hv, rfl⟩, he_φv⟩
    exact hMod'.edge_not_mem_φV eH heH v hv he_φv
  -- Apply 6.2 to obtain a model `(φ''V, φE')` of `R_H` in `R_G` with components in `L'`.
  obtain ⟨φ''V, hφ''V_comp, hMod''⟩ :=
    gm22_theorem_6_2 R_G R_H φV' φE' Z L L' hMod' hBasis_Z rfl hL'_le_delEdges heff
  refine ⟨φ''V, φE', hMod''.toDeleteVerts hJ.roots_mem_deleteVerts_v_star ?_⟩
  intro v hv
  exact (hφ''V_comp v hv).1.1.trans hL'_le_G_del

end GraphMinor.GM22
