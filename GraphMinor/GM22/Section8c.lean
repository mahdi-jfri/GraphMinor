module

public import GraphMinor.GM22.Section8c3
import GraphMinor.GM12.Section79

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 8 (Part c: Claim 13 and Theorem 8.3)

This file completes the formalization of Section 8 of Robertson and Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
Journal of Combinatorial Theory, Series B **102** (2012), 530–563 (pages 559–563),
by proving Claim (13) (`lemma_8_3_claim_13`) and Theorem (8.3) (`theorem_8_3`).
-/

@[expose] public section

namespace GraphMinor.GM22

open Classical Set Function Topology Metric Graph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM07 GraphMinor.GM09
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM19

universe w u v

variable {S : Type w} [TopologicalSpace S] [T2Space S]
variable {α : Type u} {β : Type v}

/-! ## 1. Helper Lemmas for Claim (13) and Theorem (8.3) -/

/-- Under `h83.hyp_ii`, the region `r₀ ∈ Γ.R` with `subBd r₀ = C₀.U` is also a region of the
subdrawing `C₀` (`r₀ ∈ C₀.R`). -/
theorem region_C₀_of_hypotheses83
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : GM19.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star) :
    r₀ ∈ C₀.R := by
  obtain ⟨hS, _⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  have : LocallyConnectedSpace S := GM11.IsClosedSurface.locallyConnectedSpace hS
  have hr₀ : r₀ ∈ Γ.R := h83.hyp_ii.2.2.1
  have hbd_r₀ : subBd r₀ = C₀.U := h83.hyp_ii.2.2.2
  have hC₀_sub_Γ : C₀.U ⊆ Γ.U := h83.hyp_ii.1.U_subset
  have hr₀_open : IsOpen r₀ := GM11.region_isOpen hr₀
  have hr₀_pre : IsPreconnected r₀ := GM11.region_isPreconnected hr₀
  obtain ⟨x, hxr₀⟩ := GM11.region_nonempty hr₀
  have hr₀_sub_compl : r₀ ⊆ Set.univ \ C₀.U := by
    intro y hy
    exact ⟨mem_univ y, fun hyC₀ => GM11.region_subset hr₀ hy (hC₀_sub_Γ hyC₀)⟩
  have hx_compl : x ∈ Set.univ \ C₀.U := hr₀_sub_compl hxr₀
  rw [GM11.mem_R_iff]
  refine ⟨x, hx_compl.2, Subset.antisymm ?_ ?_⟩
  · exact hr₀_pre.subset_connectedComponentIn hxr₀ hr₀_sub_compl
  · have hsub_union : connectedComponentIn (Set.univ \ C₀.U) x ⊆ r₀ ∪ (closure r₀)ᶜ := by
      intro y hy
      have hy_not_C₀ : y ∉ C₀.U := (connectedComponentIn_subset (Set.univ \ C₀.U) x hy).2
      by_cases hy_cl : y ∈ closure r₀
      · left
        by_contra hy_not_r₀
        have hy_bd : y ∈ subBd r₀ := by
          rw [GM11.subBd_eq_frontier, frontier, hr₀_open.interior_eq]
          exact ⟨hy_cl, hy_not_r₀⟩
        exact hy_not_C₀ (hbd_r₀ ▸ hy_bd)
      · exact Or.inr hy_cl
    exact isPreconnected_connectedComponentIn.subset_left_of_subset_union
      hr₀_open isClosed_closure.isOpen_compl
      (disjoint_compl_right.mono_left subset_closure)
      hsub_union
      ⟨x, mem_connectedComponentIn hx_compl, hxr₀⟩

/-- Under `Hypotheses83`, every root `R_G.roots i` belongs to `V(R_G.G.toGraph.deleteVerts {ιV v_star})`. -/
theorem Hypotheses83.roots_mem_deleteVerts_v_star
    {q δ h θ : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : GM19.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (i : Fin q) :
    R_G.roots i ∈ V(R_G.G.toGraph.deleteVerts {ιV v_star}) := by
  rw [Graph.vertexSet_deleteVerts, mem_sdiff, mem_singleton_iff]
  refine ⟨R_G.roots_mem i, fun heq => ?_⟩
  have hroot_W : R_G.roots i ∈ W := h83.ordering_W.2.2 ▸ ⟨i, rfl⟩
  have hv_star_del : ιV v_star ∈ V(R_G.G.toGraph.deleteVerts W) :=
    h83.Γ_le.vertexSet_mono ⟨v_star, h83.hyp_xiv.1.1, rfl⟩
  rw [Graph.vertexSet_deleteVerts] at hv_star_del
  exact hv_star_del.2 (heq ▸ hroot_W)

/-- Casting the left factor of `seqConcat` along an equality of lengths `n₁ = n₂`. -/
theorem seqConcat_cast_left {n₁ n₂ q : ℕ} (hn : n₁ = n₂)
    (f₁ : Fin n₁ → α) (f₂ : Fin n₂ → α) (ω : Fin q → α)
    (hf : ∀ i : Fin n₁, f₁ i = f₂ (Fin.cast hn i)) (k : Fin (n₁ + q)) :
    seqConcat f₁ ω k = seqConcat f₂ ω (Fin.cast (congrArg (· + q) hn) k) := by
  subst hn
  have hfeq : f₁ = f₂ := funext fun i => hf i
  subst hfeq
  rfl

/-- Transporting `HasSameDeltaFolio` between `subRootedDigraph`s along an equality of root lengths
and pointwise equal root sequences. -/
theorem hasSameDeltaFolio_subRootedDigraph_cast {q δ n₁ n₂ : ℕ}
    {G : Digraph α β} {A₁ A₂ : Graph α β}
    (hA₁ : A₁ ≤ G.toGraph) (hA₂ : A₂ ≤ G.toGraph)
    (hA₁' : A₁ ≤ G.toGraph) (hA₂' : A₂ ≤ G.toGraph)
    (hn : n₁ = n₂)
    (r₁ : Fin (n₁ + q) → α) (r₂ : Fin (n₁ + q) → α)
    (r₁' : Fin (n₂ + q) → α) (r₂' : Fin (n₂ + q) → α)
    (hr₁ : ∀ k : Fin (n₁ + q), r₁ k = r₁' (Fin.cast (congrArg (· + q) hn) k))
    (hr₂ : ∀ k : Fin (n₁ + q), r₂ k = r₂' (Fin.cast (congrArg (· + q) hn) k))
    (hm₁ : ∀ k, r₁ k ∈ V(A₁)) (hm₂ : ∀ k, r₂ k ∈ V(A₂))
    (hm₁' : ∀ k, r₁' k ∈ V(A₁)) (hm₂' : ∀ k, r₂' k ∈ V(A₂))
    (h : HasSameDeltaFolio (subRootedDigraph G A₁ hA₁' r₁' hm₁')
      (subRootedDigraph G A₂ hA₂' r₂' hm₂') δ) :
    HasSameDeltaFolio (subRootedDigraph G A₁ hA₁ r₁ hm₁)
      (subRootedDigraph G A₂ hA₂ r₂ hm₂) δ := by
  subst hn
  have heq₁ : r₁ = r₁' := funext fun k => hr₁ k
  have heq₂ : r₂ = r₂' := funext fun k => hr₂ k
  subst heq₁ heq₂
  intro αH βH R_H hDet
  exact h R_H hDet

/-- Any model of `R_H` in `(G \ X, ω)` is also a model of `R_H` in `(G, ω)`. -/
theorem hasRootedDigraphModel_of_subRootedDigraph
    {q : ℕ} {αH βH : Type*}
    (R_G : RootedDigraph α β q) (A : Graph α β) (hA : A ≤ R_G.G.toGraph)
    (hroots : ∀ i : Fin q, R_G.roots i ∈ V(A))
    (R_H : RootedDigraph αH βH q)
    (hMod : HasRootedDigraphModel (subRootedDigraph R_G.G A hA R_G.roots hroots) R_H) :
    HasRootedDigraphModel R_G R_H := by
  obtain ⟨φV, φE, hM⟩ := hMod
  refine ⟨φV, φE, ?_⟩
  exact
    { subgraph_of_mem := fun v hv => (hM.subgraph_of_mem v hv).trans hA
      connected_of_mem := hM.connected_of_mem
      disjoint_V := hM.disjoint_V
      root_mem := hM.root_mem
      edge_mem := fun e he => hA.edgeSet_mono (hM.edge_mem e he)
      injOn_E := hM.injOn_E
      edge_not_mem_φV := hM.edge_not_mem_φV
      head_mem := hM.head_mem
      tail_mem := hM.tail_mem }

/-! ## 2. Claim (13) of Theorem (8.3) (pages 562–563) -/

/-- **Claim (13) of Theorem (8.3)** (Graph Minors XXII, Section 8, pages 562–563):
"(13) For every $A \in \mathcal{A}'$ with $D(A) \cap \Delta = \emptyset$ and every $v \in V(\Gamma)$
with $v \notin \Delta$, there exists $A' \in \mathcal{A}'$ with $d(v, D(A')) \le \eta$ such that
$(A', \pi(A') + \omega)$ has the same $\delta$-folio as $(A, \pi(A) + \omega)$." -/
theorem lemma_8_3_claim_13
    {q δ h θ θ' : ℕ}
    {ιV : S ↪ α} {ιE : Set S ↪ β}
    {R_G : RootedDigraph α β q} {W : Set α}
    {Γ C₀ : GM19.Drawing S} {r₀ : Set S} {orient : GM19.SurfaceOrientation S}
    {PiSet : Set S}
    {ord : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    {J : Graph α β} {Z : Set α} {𝒜 : Set (Graph α β)}
    {πLen : Graph α β → ℕ} {πA : ∀ A : Graph α β, Fin (πLen A) → α}
    {vA : Graph α β → S} {D_disc : Set S} {v_star : S}
    (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
      πLen πA vA D_disc v_star)
    (hθ_bound : θ' + h + 7 ≤ θ)
    {D₀ : Graph α β → Set S}
    (hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D₀ A).Nonempty)
    {Δ : Set S}
    (hc9_near : ∀ x ∈ Γ.A, ¬ (x ⊆ Δ \ subBd Δ) → d {v_star} x ≤ θ' + 2)
    (hc10_dist : θ - θ' - 2 ≤ subsetTangleDist Γ ord d D_disc (Set.univ \ Δ))
    (hc10_sub : D_disc ⊆ Δ) :
    let 𝒜' := {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V}
    ∀ (A : Graph α β) (hA : A ∈ 𝒜'), Disjoint (D₀ A) Δ →
    ∀ v ∈ Γ.V, v ∉ Δ →
    ∃ (A' : Graph α β) (hA' : A' ∈ 𝒜'),
      subsetTangleDist Γ ord d {v} (D₀ A') ≤ h + 1 ∧
      ∃ hlen : πLen A' = πLen A,
        HasSameDeltaFolio
          (subRootedDigraph R_G.G A' ((h83.hyp_vi.2.2.1.2.1 A' hA'.1).trans h83.hyp_v.1)
            (seqConcat (πA A' ∘ Fin.cast hlen.symm) R_G.roots)
            (seqConcat_mem
              (fun j => ((h83.hyp_vii A' hA'.1).2.2.subset ⟨Fin.cast hlen.symm j, rfl⟩).2)
              (fun j => h83.hyp_vi.2.2.2 A' hA'.1 (h83.ordering_W.2.2.subset ⟨j, rfl⟩))))
          (subRootedDigraph R_G.G A ((h83.hyp_vi.2.2.1.2.1 A hA.1).trans h83.hyp_v.1)
            (seqConcat (πA A) R_G.roots)
            (seqConcat_mem
              (fun j => ((h83.hyp_vii A hA.1).2.2.subset ⟨j, rfl⟩).2)
              (fun j => h83.hyp_vi.2.2.2 A hA.1 (h83.ordering_W.2.2.subset ⟨j, rfl⟩))))
          δ := by
  intro 𝒜' A hA hdisj v hv hv_not_Δ
  obtain ⟨hS, hConn⟩ := GM11.IsSphere.isClosedSurface h83.hyp_i.1
  let : ConnectedSpace S := hConn
  have hM := h83.hyp_iv.2.1
  have hle_ord : ∀ a ∈ Γ.A, ∀ b ∈ Γ.A, d a b ≤ ord :=
    fun a ha b hb => HasTangleMetric.le_ord hM ha hb
  have hv_star_V : v_star ∈ Γ.V := h83.hyp_xiv.1.1
  have hv_star_A : ({v_star} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v_star, hv_star_V, rfl⟩)
  have hvA_V : vA A ∈ Γ.V := (h83.hyp_xi A hA.1).1
  have hvA_A : ({vA A} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨vA A, hvA_V, rfl⟩)
  -- Step 1: By Claim (6) and Claim (9), `d {v_star} {vA A} ≤ θ' + 3`, so `vA A ∈ univ \ D_disc`.
  obtain ⟨r, hr, hvA_r, p, hpr, hpD₀⟩ := hc6 A hA.1
  have hr_A : r ∈ Γ.A := Or.inr hr
  have hr_not_sub : ¬ (r ⊆ Δ \ subBd Δ) :=
    fun hsub => Set.disjoint_left.mp hdisj hpD₀ (hsub hpr).1
  have hd_vs_r : d {v_star} r ≤ θ' + 2 := hc9_near r hr_A hr_not_sub
  have hd_vA_r : d {vA A} r ≤ 1 := (dist_vertex_region_le_one_8_3 h83 hvA_V hr hvA_r).1
  have hd_r_vA : d r {vA A} ≤ 1 := (HasTangleMetric.comm hM hr_A hvA_A).trans_le hd_vA_r
  have hd_vs_vA : d {v_star} {vA A} ≤ θ' + 3 :=
    (HasTangleMetric.triangle hS hM hv_star_A hr_A hvA_A).trans (by omega)
  have hvA_not_D : vA A ∈ Set.univ \ D_disc := by
    refine ⟨mem_univ _, fun hvA_D => ?_⟩
    have hle : subsetTangleDist Γ ord d {v_star} D_disc ≤ d {v_star} {vA A} :=
      subsetTangleDist_le_of_mem hv_star_A hvA_A ⟨v_star, rfl, rfl⟩ ⟨vA A, rfl, hvA_D⟩
    have hge := h83.hyp_xiv.2
    omega
  -- Step 2: By Claim (10), `v ∈ Γ.V \ D_disc` and `d({v}, D_disc) ≥ θ - θ' - 2 > h`.
  have hv_not_D : v ∈ Γ.V \ D_disc := ⟨hv, fun hvD => hv_not_Δ (hc10_sub hvD)⟩
  have hv_A : ({v} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨v, hv, rfl⟩)
  have hd_v_D : θ - θ' - 2 ≤ subsetTangleDist Γ ord d {v} D_disc := by
    have hθ_ord := h83.hyp_iv.1
    refine le_subsetTangleDist_of_forall (by omega) fun a ha b hb hav hbD => ?_
    have ha_eq : a = {v} := GM12.atom_eq_of_inter_nonempty ha hv_A hav
    subst ha_eq
    have h1 : θ - θ' - 2 ≤ d b {v} :=
      hc10_dist.trans (subsetTangleDist_le_of_mem hb hv_A hbD ⟨v, rfl, mem_univ v, hv_not_Δ⟩)
    rwa [HasTangleMetric.comm hM hv_A hb]
  have hnot_le_h : ¬ subsetTangleDist Γ ord d {v} D_disc ≤ h := by omega
  -- Step 3: Apply hypothesis (xiii) to obtain `A' ∈ 𝒜`.
  obtain ⟨A', hA', hd_v_vA'_sub, hlen, hfolio⟩ :=
    (h83.hyp_xiii A hA.1 hvA_not_D v hv_not_D).resolve_left hnot_le_h
  have hvA'_V : vA A' ∈ Γ.V := (h83.hyp_xi A' hA').1
  have hvA'_A : ({vA A'} : Set S) ∈ Γ.A := Or.inl (Or.inl ⟨vA A', hvA'_V, rfl⟩)
  have hd_v_vA' : d {v} {vA A'} ≤ h := by
    rw [← subsetTangleDist_singletons_eq (Γ := Γ) (ord := ord) (d := d) hv hvA'_V]
    exact hd_v_vA'_sub
  -- Step 4: By Claim (6) for `A'`, `subsetTangleDist Γ ord d {v} (D₀ A') ≤ h + 1`.
  obtain ⟨r', hr', hvA'_r', q_pt, hqr', hqD₀'⟩ := hc6 A' hA'
  have hr'_A : r' ∈ Γ.A := Or.inr hr'
  have hd_vA'_r' : d {vA A'} r' ≤ 1 := (dist_vertex_region_le_one_8_3 h83 hvA'_V hr' hvA'_r').1
  have hd_v_D₀A' : subsetTangleDist Γ ord d {v} (D₀ A') ≤ h + 1 := by
    have h1 : subsetTangleDist Γ ord d {v} (D₀ A') ≤ d {v} r' :=
      subsetTangleDist_le_of_mem hv_A hr'_A ⟨v, rfl, rfl⟩ ⟨q_pt, hqr', hqD₀'⟩
    have h2 : d {v} r' ≤ d {v} {vA A'} + d {vA A'} r' :=
      HasTangleMetric.triangle hS hM hv_A hvA'_A hr'_A
    omega
  -- Step 5: Show `A' ∈ 𝒜'`, that is, `5 ≤ subsetTangleDist Γ ord d {vA A'} C₀.V`.
  have hC₀V_sub_D : C₀.V ⊆ D_disc := by
    intro x hx
    have hxU : x ∈ C₀.U := C₀.V_subset_U hx
    rw [← h83.hyp_ii.2.2.2, GM11.subBd_eq_frontier] at hxU
    have hx_cl : x ∈ closure r₀ := frontier_subset_closure hxU
    exact h83.hyp_xii.1.isClosed.closure_subset_iff.mpr h83.hyp_xii.2.2 hx_cl
  have hd_v_C₀ : θ - θ' - 2 ≤ subsetTangleDist Γ ord d {v} C₀.V :=
    hd_v_D.trans (subsetTangleDist_anti hle_ord Subset.rfl hC₀V_sub_D)
  have htri_C₀ :
      subsetTangleDist Γ ord d {v} C₀.V ≤
        d {v} {vA A'} + subsetTangleDist Γ ord d {vA A'} C₀.V :=
    subsetTangleDist_singleton_triangle hS hM hv hvA'_V C₀.V
  have hA'_mem : A' ∈ 𝒜' := ⟨hA', by omega⟩
  exact ⟨A', hA'_mem, hd_v_D₀A', hlen, hfolio⟩

/-! ## 3. Theorem (8.3) (pages 559–563) -/

/-- **Graph Minors XXII, (8.3)** (Section 8, pages 559–560):
"For all $q, \delta \ge 0$ and $h \ge 4$, there exists $\theta \ge h$ with the following property.
Let $G$ be a digraph, let $W \subseteq V(G)$ with $|W| = q$, and let $\omega$ be an ordering of $W$.
Let $\Gamma \subseteq G \setminus W$ satisfy the following. ... Then $(G \setminus \{v^*\}, \omega)$
has the same $\delta$-folio as $(G, \omega)$." -/
theorem theorem_8_3_proof  (q δ h : ℕ) :
    ∃ θ : ℕ, h ≤ θ ∧ 4 ≤ θ ∧
      ∀ {S : Type w} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v}
        (ιV : S ↪ α) (ιE : Set S ↪ β)
        (R_G : RootedDigraph α β q) (W : Set α)
        (Γ C₀ : GM19.Drawing S) (r₀ : Set S) (orient : GM19.SurfaceOrientation S)
        (PiSet : Set S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (J : Graph α β) (Z : Set α) (𝒜 : Set (Graph α β))
        (πLen : Graph α β → ℕ) (πA : ∀ A : Graph α β, Fin (πLen A) → α)
        (vA : Graph α β → S) (D_disc : Set S) (v_star : S)
        (h83 : Hypotheses83 q δ h θ ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜
          πLen πA vA D_disc v_star),
        HasSameDeltaFolio
          (subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
            R_G.roots h83.roots_mem_deleteVerts_v_star)
          R_G δ := by
  let η := h + 1
  obtain ⟨θ', hθ'4, hθ'_spec⟩ := theorem_8_2_proof.{w, u, v, 0, 0} q δ η
  let θ := 2 * θ' + h + 14
  refine ⟨θ, by omega, by omega, ?_⟩
  intro S _ _ α β ιV ιE R_G W Γ C₀ r₀ orient PiSet ord T d J Z 𝒜 πLen πA vA D_disc v_star h83
  have hθ_ord : θ ≤ ord := h83.hyp_iv.1
  have hord4 : 4 ≤ ord := by omega
  -- Step 1: Obtain `Δ₀` from `exists_disc_Δ₀_8_3`.
  have hr₀_C₀ : r₀ ∈ C₀.R := region_C₀_of_hypotheses83 h83
  have hΓ_disj_r₀ : Disjoint Γ.U r₀ :=
    Set.disjoint_left.mpr fun _ hxU hxr₀ => GM11.region_subset h83.hyp_ii.2.2.1 hxr₀ hxU
  have hPi_fin : PiSet.Finite := Set.finite_of_ncard_ne_zero (by rw [h83.hyp_iii.2]; omega)
  obtain ⟨Δ₀, hΔ₀, _, hΓ_Δ₀, hbd_Δ₀_Pi, hcompl_r₀, _, h_disc_compl, h_bd_compl,
      e_C_Δ₀, he_C_Δ₀⟩ :=
    exists_disc_Δ₀_8_3 h83.hyp_i.1 Γ C₀ r₀ PiSet h83.hyp_ii.2.1 hr₀_C₀ hΓ_disj_r₀
      hPi_fin h83.hyp_iii.1 h83.hyp_ii.1.1
  -- Step 2: Obtain `α_map` and `D₀` from Claim (3).
  obtain ⟨α_map, D₀, hα_Δ₀, _, hα_Pi, hα_ΓV, hα_ΓU, hinj, hD₀, hD₀_norm_bd,
      hα_bdA, hα_inA, hD₀_props, hD₀_inter, hD₀_bdΔ₀⟩ :=
    lemma_8_3_claim_3 h83 hord4 hΔ₀ hΓ_Δ₀ hbd_Δ₀_Pi e_C_Δ₀ he_C_Δ₀
  -- Step 3: Obtain `Δ` from Claim (9) and distance bounds from Claim (6) and Claim (10).
  obtain ⟨Δ, hΔ_disc, hΔ_bd, hv_star_not_Δ, _, hc9_dist, hc9_near⟩ :=
    lemma_8_3_claim_9 (θ' := θ') h83 (by omega) (by omega) hcompl_r₀
  obtain ⟨hc10_dist, hc10_sub⟩ := lemma_8_3_claim_10 h83 (by omega) hc9_near
  have hD₀_norm : ∀ A ∈ 𝒜, subBd (D₀ A) ∩ Γ.U ⊆ Γ.V := fun A hA => (hD₀_norm_bd A hA).1
  have hc6 : ∀ A ∈ 𝒜, ∃ r ∈ Γ.R, vA A ∈ subBd r ∧ (r ∩ D₀ A).Nonempty :=
    lemma_8_3_claim_6 h83 hord4 hΔ₀ hbd_Δ₀_Pi hα_ΓV hα_ΓU hinj hD₀ hD₀_norm hα_bdA hD₀_props
  -- Step 4: Obtain the augmented system `(ιV', 𝒜'', πLen'', πS'', D'', ins, N, K)` satisfying
  -- `(J1)`–`(J7)`.
  obtain ⟨ιV', 𝒜'', πLen'', πS'', D'', ins, N, K, hf_ΓV, h𝒜'_sub, hdisj_in_𝒜',
      h𝒜'_agree, hJ7_𝒜'', hSys⟩ :=
    exists_augmented_system_8_3 h83 hθ'4 (by omega) hΔ₀ hΓ_Δ₀ hbd_Δ₀_Pi hcompl_r₀
      h_disc_compl h_bd_compl hα_Δ₀ hα_Pi hα_ΓV hα_ΓU hinj hD₀ hD₀_norm_bd hα_bdA hα_inA
      hD₀_props hD₀_inter hD₀_bdΔ₀ hΔ_disc hΔ_bd hv_star_not_Δ hc9_near
  -- Step 5: Verify the homogeneity condition for `𝒜''` from Claim (13).
  have hHom_𝒜'' :
      ∀ B ∈ 𝒜'', Disjoint (D'' B) Δ → ∀ v ∈ Γ.V, v ∉ Δ →
        ∃ A' ∈ 𝒜'', subsetTangleDist Γ ord d {v} (D'' A') ≤ η ∧
          ∃ hlen : πLen'' A' = πLen'' B,
            ∀ (hB_le : B ≤ R_G.G.toGraph) (hA'_le : A' ≤ R_G.G.toGraph)
              (hπB : ∀ k : Fin (πLen'' B + q),
                seqConcat (ιV' ∘ πS'' B) R_G.roots k ∈ V(B))
              (hπA' : ∀ k : Fin (πLen'' B + q),
                seqConcat (fun k : Fin (πLen'' B) =>
                  ιV' (πS'' A' (Fin.cast hlen.symm k))) R_G.roots k ∈ V(A')),
              HasSameDeltaFolio
                (subRootedDigraph R_G.G A' hA'_le
                  (seqConcat (fun k : Fin (πLen'' B) =>
                    ιV' (πS'' A' (Fin.cast hlen.symm k))) R_G.roots) hπA')
                (subRootedDigraph R_G.G B hB_le
                  (seqConcat (ιV' ∘ πS'' B) R_G.roots) hπB) δ := by
    intro B hB hdisj v hv hv_not_Δ
    have hB' : B ∈ {A ∈ 𝒜 | 5 ≤ subsetTangleDist Γ ord d {vA A} C₀.V} :=
      hdisj_in_𝒜' B hB hdisj
    obtain ⟨hD''_B, hlen_B, hπ_B⟩ := h𝒜'_agree B hB'
    have hdisj₀ : Disjoint (D₀ B) Δ := hD''_B ▸ hdisj
    obtain ⟨A', hA', hd_v_A', hlen₀, hfolio₀⟩ :=
      lemma_8_3_claim_13 h83 (by omega) hc6 hc9_near hc10_dist hc10_sub B hB' hdisj₀ v hv hv_not_Δ
    obtain ⟨hD''_A', hlen_A', hπ_A'⟩ := h𝒜'_agree A' hA'
    have hlen'' : πLen'' A' = πLen'' B := hlen_A'.trans (hlen₀.trans hlen_B.symm)
    refine ⟨A', h𝒜'_sub hA', hD''_A'.symm ▸ hd_v_A', hlen'', ?_⟩
    intro hB_le hA'_le hπB hπA'
    refine hasSameDeltaFolio_subRootedDigraph_cast hA'_le hB_le
      ((h83.hyp_vi.2.2.1.2.1 A' hA'.1).trans h83.hyp_v.1)
      ((h83.hyp_vi.2.2.1.2.1 B hB'.1).trans h83.hyp_v.1)
      hlen_B _ _ _ _ ?_ ?_ hπA' hπB _ _ hfolio₀
    · intro k
      refine seqConcat_cast_left hlen_B
        (fun i : Fin (πLen'' B) => ιV' (πS'' A' (Fin.cast hlen''.symm i)))
        (πA A' ∘ Fin.cast hlen₀.symm) R_G.roots (fun i => ?_) k
      have hcast :
          Fin.cast hlen''.symm i =
            Fin.cast hlen_A'.symm (Fin.cast hlen₀.symm (Fin.cast hlen_B i)) := by
        ext; rfl
      rw [hcast]
      exact hπ_A' (Fin.cast hlen₀.symm (Fin.cast hlen_B i))
    · intro k
      refine seqConcat_cast_left hlen_B
        (ιV' ∘ πS'' B) (πA B) R_G.roots (fun i => ?_) k
      have hcast : Fin.cast hlen_B.symm (Fin.cast hlen_B i) = i := by
        ext; rfl
      have h1 := hπ_B (Fin.cast hlen_B i)
      rwa [hcast] at h1
  -- Step 6: Conclude `HasSameDeltaFolio` between `(G \ {v^*}, ω)` and `(G, ω)`.
  intro αH βH R_H hDet
  constructor
  · exact hasRootedDigraphModel_of_subRootedDigraph R_G
      (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
      h83.roots_mem_deleteVerts_v_star R_H
  · rintro ⟨φV, φE, hMod⟩
    let hJ := hSys R_H φV φE hDet hMod
    have hMod_del := hθ'_spec ιV' ιE R_G W 𝒜'' πLen'' πS'' Γ orient ord T ins d D'' N K Δ
      v_star R_H φV φE hJ hJ7_𝒜'' hHom_𝒜'' hc9_dist
    have hv_star_eq : ιV' v_star = ιV v_star := hf_ΓV v_star h83.hyp_xiv.1.1
    have hsub_eq :
        subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV' v_star}) Graph.deleteVerts_le
          R_G.roots hJ.roots_mem_deleteVerts_v_star =
        subRootedDigraph R_G.G (R_G.G.toGraph.deleteVerts {ιV v_star}) Graph.deleteVerts_le
          R_G.roots h83.roots_mem_deleteVerts_v_star := by
      simp only [hv_star_eq]
    rwa [← hsub_eq]

end GraphMinor.GM22
