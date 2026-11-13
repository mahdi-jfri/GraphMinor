module

public import GraphMinor.GM01.Defs
public import GraphMinor.Minor.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
import Mathlib.Data.Set.Finite.Basic

/-!
# Basic Lemmas for Graph Minors I, Section 2

This file provides the basic API for `toGraph`, minor models built from pairwise vertex-disjoint
connected subgraphs, invariance of `𝓕_θ` under subgraphs and minors, and the order and decomposition
of vertices along a `Path`.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph Graph Set Relation

variable {α γ : Type*}

/-! ### Basic properties of `toGraph` and `𝓕` -/

@[simp]
lemma vertexSet_toGraph (G : (⊤ : SimpleGraph α).Subgraph) : V(toGraph G) = G.verts := rfl

@[simp]
lemma edgeSet_toGraph (G : (⊤ : SimpleGraph α).Subgraph) : E(toGraph G) = G.edgeSet := rfl

@[simp]
lemma isLink_toGraph (G : (⊤ : SimpleGraph α).Subgraph) (e : Sym2 α) (x y : α) :
    (toGraph G).IsLink e x y ↔ e = s(x, y) ∧ G.Adj x y := Iff.rfl

lemma adj_toGraph (G : (⊤ : SimpleGraph α).Subgraph) (x y : α) :
    (toGraph G).Adj x y ↔ G.Adj x y := by
  constructor
  · rintro ⟨_, _, hadj⟩
    exact hadj
  · intro hadj
    exact ⟨s(x, y), rfl, hadj⟩

lemma inc_toGraph (G : (⊤ : SimpleGraph α).Subgraph) (e : Sym2 α) (x : α) :
    (toGraph G).Inc e x ↔ ∃ y, e = s(x, y) ∧ G.Adj x y := Iff.rfl

lemma not_isLoopAt_toGraph (G : (⊤ : SimpleGraph α).Subgraph) (e : Sym2 α) (x : α) :
    ¬ (toGraph G).IsLoopAt e x := by
  rintro ⟨_, hadj⟩
  exact G.loopless.irrefl x hadj

lemma toGraph_mono {G' G : (⊤ : SimpleGraph α).Subgraph} (h : G' ≤ G) :
    toGraph G' ≤ toGraph G :=
  ⟨h.1, fun _ _ _ ⟨he, hadj⟩ ↦ ⟨he, h.2 hadj⟩⟩

lemma finite_edgeSet_of_finite_verts {G : (⊤ : SimpleGraph α).Subgraph} (hG : G.verts.Finite) :
    G.edgeSet.Finite := by
  have hsub : G.edgeSet ⊆ (fun p : α × α ↦ s(p.1, p.2)) '' (G.verts ×ˢ G.verts) := by
    rintro ⟨x, y⟩ hxy
    exact ⟨(x, y), ⟨G.edge_vert hxy, G.edge_vert hxy.symm⟩, rfl⟩
  exact ((hG.prod hG).image _).subset hsub

lemma ofSimpleGraph_eq_toGraph (H : SimpleGraph γ) :
    Graph.ofSimpleGraph H = toGraph (SimpleGraph.toSubgraph H le_top) := by
  ext e x y
  · simp [toGraph, SimpleGraph.toSubgraph]
  · simp only [ofSimpleGraph_isLink, isLink_toGraph, toSubgraph_adj]
    exact ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, by rwa [h1, mem_edgeSet] at h2⟩,
      fun ⟨h1, h2⟩ ↦ ⟨h1, by rwa [h1, mem_edgeSet]⟩⟩

lemma graphConnected_toGraph_iff (K : (⊤ : SimpleGraph α).Subgraph) :
    GraphConnected (toGraph K) ↔ K.Connected := by
  rw [GraphConnected, Subgraph.connected_iff_forall_exists_walk_subgraph, vertexSet_toGraph]
  refine and_congr_right fun _ ↦ ⟨fun h u v hu hv ↦ ?_, fun h x hx y hy ↦ ?_⟩
  · have hrt : ∀ w ∈ K.verts, ReflTransGen (toGraph K).Adj u w →
        ∃ p : (⊤ : SimpleGraph α).Walk u w, p.toSubgraph ≤ K := by
      intro w _ hrt
      induction hrt with
      | refl =>
        refine ⟨.nil, ?_⟩
        simp [hu]
      | @tail a b _ hab ih =>
        obtain ⟨_, _, hadj⟩ := hab
        obtain ⟨p, hp⟩ := ih hadj.fst_mem
        have hadj' : (⊤ : SimpleGraph α).Adj a b := hadj.adj_sub
        refine ⟨p.append (.cons hadj' .nil), ?_⟩
        rw [Walk.toSubgraph_append, Walk.toSubgraph_cons_nil_eq_subgraphOfAdj]
        exact sup_le hp (subgraphOfAdj_le_of_adj K hadj)
    exact hrt v hv (h u hu v hv)
  · obtain ⟨p, hp⟩ := h hx hy
    have haux : ∀ {a b : α} (q : (⊤ : SimpleGraph α).Walk a b),
        q.toSubgraph ≤ K → ReflTransGen (toGraph K).Adj a b := by
      intro a b q hq
      induction q with
      | nil => exact .refl
      | @cons a c b _ q' ih =>
        rw [Walk.toSubgraph, sup_le_iff] at hq
        have hadjK : K.Adj a c := hq.1.2 (by simp)
        exact ReflTransGen.head ((adj_toGraph K a c).2 hadjK) (ih hq.2)
    exact haux p hp

/-- If `G' ≤ G`, then `toGraph G'` is isomorphic to a minor of `toGraph G`. -/
lemma isIsoMinor_toGraph_of_le {G' G : (⊤ : SimpleGraph α).Subgraph} (h : G' ≤ G) :
    IsIsoMinor (toGraph G') (toGraph G) := by
  obtain ⟨G₁, hle, C, hC, hIso⟩ := IsIsoMinor.refl (toGraph G')
  exact ⟨G₁, hle.trans (toGraph_mono h), C, hC, hIso⟩

lemma mem_𝓕_of_isIsoMinor {θ : ℕ} {G' : (⊤ : SimpleGraph γ).Subgraph}
    {G : (⊤ : SimpleGraph α).Subgraph} (hminor : IsIsoMinor (toGraph G') (toGraph G))
    (hG : G ∈ 𝓕 θ) : G' ∈ 𝓕 θ :=
  fun hgrid ↦ hG (hgrid.trans hminor)

lemma mem_𝓕_of_le {θ : ℕ} {G' G : (⊤ : SimpleGraph α).Subgraph} (hle : G' ≤ G) (hG : G ∈ 𝓕 θ) :
    G' ∈ 𝓕 θ :=
  mem_𝓕_of_isIsoMinor (isIsoMinor_toGraph_of_le hle) hG

/-! ### Minor models from connected subgraphs -/

/-- Building a minor model of `toGraph H` in `toGraph G` from pairwise vertex-disjoint connected
subgraphs `K u ≤ G` (`u ∈ H.verts`) with an edge of `G` between `K u` and `K v` whenever
`H.Adj u v`. -/
theorem isIsoMinor_toGraph_of_connected_subgraphs {H : (⊤ : SimpleGraph γ).Subgraph}
    {G : (⊤ : SimpleGraph α).Subgraph} (hH : H.verts.Finite) (hG : G.verts.Finite)
    (K : γ → (⊤ : SimpleGraph α).Subgraph)
    (hK_le : ∀ u ∈ H.verts, K u ≤ G)
    (hK_conn : ∀ u ∈ H.verts, (K u).Connected)
    (hK_disj : ∀ u ∈ H.verts, ∀ v ∈ H.verts, u ≠ v → Disjoint (K u).verts (K v).verts)
    (hK_adj : ∀ ⦃u v⦄, H.Adj u v → ∃ x ∈ (K u).verts, ∃ y ∈ (K v).verts, G.Adj x y) :
    IsIsoMinor (toGraph H) (toGraph G) := by
  classical
  rcases H.verts.eq_empty_or_nonempty with hH_empty | ⟨u₀, hu₀⟩
  · have hEH : H.edgeSet = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      rintro ⟨u, v⟩ huv
      have hu : u ∈ H.verts := H.edge_vert huv
      simp [hH_empty] at hu
    refine ⟨Graph.noEdge ∅ (Sym2 α), by simp, ∅, empty_subset _, ⟨?_⟩⟩
    refine
      { vertexEquiv :=
          { toFun := fun ⟨u, hu⟩ ↦ absurd hu (by simp [hH_empty])
            invFun := fun ⟨X, hX⟩ ↦ absurd hX (by simp [contract])
            left_inv := fun ⟨u, hu⟩ ↦ absurd hu (by simp [hH_empty])
            right_inv := fun ⟨X, hX⟩ ↦ absurd hX (by simp [contract]) }
        edgeEquiv :=
          { toFun := fun ⟨e, he⟩ ↦ absurd he (by simp [hEH])
            invFun := fun ⟨e, he⟩ ↦ absurd he (by simp [contract])
            left_inv := fun ⟨e, he⟩ ↦ absurd he (by simp [hEH])
            right_inv := fun ⟨e, he⟩ ↦ absurd he (by simp [contract]) }
        isLink_iff := fun ⟨e, he⟩ _ _ ↦ absurd he (by simp [hEH]) }
  · obtain ⟨x₀, _⟩ := (hK_conn u₀ hu₀).nonempty
    have hchoose : ∀ e : Sym2 γ, e ∈ H.edgeSet →
        ∃ x y : α, G.Adj x y ∧ ∀ u v, e = s(u, v) →
          (x ∈ (K u).verts ∧ y ∈ (K v).verts) ∨ (x ∈ (K v).verts ∧ y ∈ (K u).verts) := by
      rintro ⟨u, v⟩ huv
      have hadj : H.Adj u v := huv
      obtain ⟨x, hx, y, hy, hxy⟩ := hK_adj hadj
      refine ⟨x, y, hxy, fun u' v' heq ↦ ?_⟩
      rcases Sym2.eq_iff.1 heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hx, hy⟩
      · exact Or.inr ⟨hx, hy⟩
    let ηv : γ → Set α := fun u ↦ (K u).verts
    let ηe : Sym2 γ → Sym2 α := fun e ↦
      if he : e ∈ H.edgeSet then s((hchoose e he).choose, (hchoose e he).choose_spec.choose)
      else s(x₀, x₀)
    have hηe_spec : ∀ {e : Sym2 γ} (he : e ∈ H.edgeSet),
        ∃ x y : α, ηe e = s(x, y) ∧ G.Adj x y ∧ ∀ u v, e = s(u, v) →
          (x ∈ (K u).verts ∧ y ∈ (K v).verts) ∨ (x ∈ (K v).verts ∧ y ∈ (K u).verts) := by
      intro e he
      refine ⟨(hchoose e he).choose, (hchoose e he).choose_spec.choose, dite_eq_left he,
        (hchoose e he).choose_spec.choose_spec.1, (hchoose e he).choose_spec.choose_spec.2⟩
    apply isIsoMinor_of_isMinorModel (toGraph H) (toGraph G) hH
      (finite_edgeSet_of_finite_verts hH) hG (finite_edgeSet_of_finite_verts hG) ηv ηe
    refine
      { vertex_nonempty := fun u hu ↦ (hK_conn u hu).nonempty
        vertex_subset := fun u hu ↦ (hK_le u hu).1
        edge_mem := fun e he ↦ by
          obtain ⟨x, y, hηe, hxy, _⟩ := hηe_spec he
          rw [edgeSet_toGraph, hηe, Subgraph.mem_edgeSet]
          exact hxy
        vertex_disjoint := fun u₁ hu₁ u₂ hu₂ hne ↦ hK_disj u₁ hu₁ u₂ hu₂ hne
        edge_injOn := fun e₁ he₁ e₂ he₂ heq ↦ by
          induction e₁ with | h u₁ v₁ =>
          induction e₂ with | h u₂ v₂ =>
          have hadj₁ : H.Adj u₁ v₁ := he₁
          have hadj₂ : H.Adj u₂ v₂ := he₂
          obtain ⟨x₁, y₁, hη₁, _, hmem₁⟩ := hηe_spec he₁
          obtain ⟨x₂, y₂, hη₂, _, hmem₂⟩ := hηe_spec he₂
          have hpair : s(x₁, y₁) = s(x₂, y₂) := hη₁.symm.trans (heq.trans hη₂)
          have hm₁ := hmem₁ u₁ v₁ rfl
          have hm₂ := hmem₂ u₂ v₂ rfl
          have h_eq : ∀ {a : α} {w₁ w₂ : γ}, w₁ ∈ H.verts → w₂ ∈ H.verts →
              a ∈ (K w₁).verts → a ∈ (K w₂).verts → w₁ = w₂ := by
            intro a w₁ w₂ hw₁ hw₂ ha₁ ha₂
            by_contra hne
            exact (hK_disj w₁ hw₁ w₂ hw₂ hne).notMem_of_mem_left ha₁ ha₂
          have hu₁ : u₁ ∈ H.verts := hadj₁.fst_mem
          have hv₁ : v₁ ∈ H.verts := hadj₁.snd_mem
          have hu₂ : u₂ ∈ H.verts := hadj₂.fst_mem
          have hv₂ : v₂ ∈ H.verts := hadj₂.snd_mem
          rcases Sym2.eq_iff.1 hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
            rcases hm₁ with ⟨hx₁, hy₁⟩ | ⟨hx₁, hy₁⟩ <;>
            rcases hm₂ with ⟨hx₂, hy₂⟩ | ⟨hx₂, hy₂⟩
          · rw [h_eq hu₁ hu₂ hx₁ hx₂, h_eq hv₁ hv₂ hy₁ hy₂]
          · rw [h_eq hu₁ hv₂ hx₁ hx₂, h_eq hv₁ hu₂ hy₁ hy₂, Sym2.eq_swap]
          · rw [h_eq hv₁ hu₂ hx₁ hx₂, h_eq hu₁ hv₂ hy₁ hy₂, Sym2.eq_swap]
          · rw [h_eq hv₁ hv₂ hx₁ hx₂, h_eq hu₁ hu₂ hy₁ hy₂]
          · rw [h_eq hu₁ hv₂ hx₁ hy₂, h_eq hv₁ hu₂ hy₁ hx₂, Sym2.eq_swap]
          · rw [h_eq hu₁ hu₂ hx₁ hy₂, h_eq hv₁ hv₂ hy₁ hx₂]
          · rw [h_eq hv₁ hv₂ hx₁ hy₂, h_eq hu₁ hu₂ hy₁ hx₂]
          · rw [h_eq hv₁ hu₂ hx₁ hy₂, h_eq hu₁ hv₂ hy₁ hx₂, Sym2.eq_swap]
        inc_iff := fun w hw e he ↦ by
          induction e with | h u v =>
          have hadj : H.Adj u v := he
          have hu : u ∈ H.verts := hadj.fst_mem
          have hv : v ∈ H.verts := hadj.snd_mem
          obtain ⟨x, y, hη, hxy, hmem⟩ := hηe_spec he
          have hm := hmem u v rfl
          have h_eq : ∀ {a : α} {w₁ w₂ : γ}, w₁ ∈ H.verts → w₂ ∈ H.verts →
              a ∈ (K w₁).verts → a ∈ (K w₂).verts → w₁ = w₂ := by
            intro a w₁ w₂ hw₁ hw₂ ha₁ ha₂
            by_contra hne
            exact (hK_disj w₁ hw₁ w₂ hw₂ hne).notMem_of_mem_left ha₁ ha₂
          constructor
          · rintro ⟨w', heq_uv, _⟩
            have hwu : w = u ∨ w = v := by
              rcases Sym2.eq_iff.1 heq_uv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · exact Or.inl rfl
              · exact Or.inr rfl
            rcases hwu with rfl | rfl <;> rcases hm with ⟨hx, hy⟩ | ⟨hx, hy⟩
            · exact ⟨x, hx, y, hη, hxy⟩
            · exact ⟨y, hy, x, hη.trans (Sym2.eq_swap), hxy.symm⟩
            · exact ⟨y, hy, x, hη.trans (Sym2.eq_swap), hxy.symm⟩
            · exact ⟨x, hx, y, hη, hxy⟩
          · rintro ⟨a, ha, b, hab, _⟩
            have hpair : s(x, y) = s(a, b) := hη.symm.trans hab
            have hauv : a ∈ (K u).verts ∨ a ∈ (K v).verts := by
              rcases Sym2.eq_iff.1 hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
                rcases hm with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> tauto
            rcases hauv with hau | hav
            · have hwu : w = u := h_eq hw hu ha hau
              subst hwu
              exact ⟨v, rfl, hadj⟩
            · have hwv : w = v := h_eq hw hv ha hav
              subst hwv
              exact ⟨u, Sym2.eq_swap, hadj.symm⟩
        isLoopAt_iff := fun w hw e he ↦ by
          simp only [not_isLoopAt_toGraph, false_iff, not_forall]
          induction e with | h u v =>
          have hadj : H.Adj u v := he
          have huv_ne : u ≠ v := hadj.ne
          have hu : u ∈ H.verts := hadj.fst_mem
          have hv : v ∈ H.verts := hadj.snd_mem
          obtain ⟨x, y, hη, hxy, hmem⟩ := hηe_spec he
          rcases hmem u v rfl with ⟨hx, hy⟩ | ⟨hx, hy⟩
          · by_cases hwu : w = u
            · subst hwu
              exact ⟨y, ⟨x, hη.trans Sym2.eq_swap, hxy.symm⟩,
                (hK_disj w hw v hv huv_ne).notMem_of_mem_right hy⟩
            · exact ⟨x, ⟨y, hη, hxy⟩, (hK_disj w hw u hu hwu).notMem_of_mem_right hx⟩
          · by_cases hwu : w = u
            · subst hwu
              exact ⟨x, ⟨y, hη, hxy⟩, (hK_disj w hw v hv huv_ne).notMem_of_mem_right hx⟩
            · exact ⟨y, ⟨x, hη.trans Sym2.eq_swap, hxy.symm⟩,
                (hK_disj w hw u hu hwu).notMem_of_mem_right hy⟩
        connected := fun w hw ↦ by
          refine ⟨toGraph (K w), ?_, rfl, (graphConnected_toGraph_iff (K w)).2 (hK_conn w hw)⟩
          refine ⟨(hK_le w hw).1, fun e x y ⟨he, hadjK⟩ ↦ ⟨⟨he, (hK_le w hw).2 hadjK⟩, ?_⟩⟩
          rintro ⟨e', he', heq⟩
          induction e' with | h u v =>
          have hadj : H.Adj u v := he'
          have huv_ne : u ≠ v := hadj.ne
          have hu : u ∈ H.verts := hadj.fst_mem
          have hv : v ∈ H.verts := hadj.snd_mem
          obtain ⟨x', y', hη, _, hmem⟩ := hηe_spec he'
          have hpair : s(x', y') = s(x, y) := hη.symm.trans (heq.trans he)
          have hx_w : x ∈ (K w).verts := hadjK.fst_mem
          have hy_w : y ∈ (K w).verts := hadjK.snd_mem
          have hxy_uv : (x ∈ (K u).verts ∧ y ∈ (K v).verts) ∨
              (x ∈ (K v).verts ∧ y ∈ (K u).verts) := by
            rcases Sym2.eq_iff.1 hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              rcases hmem u v rfl with ⟨hx', hy'⟩ | ⟨hx', hy'⟩ <;> tauto
          have h_eq : ∀ {a : α} {w₁ w₂ : γ}, w₁ ∈ H.verts → w₂ ∈ H.verts →
              a ∈ (K w₁).verts → a ∈ (K w₂).verts → w₁ = w₂ := by
            intro a w₁ w₂ hw₁ hw₂ ha₁ ha₂
            by_contra hne
            exact (hK_disj w₁ hw₁ w₂ hw₂ hne).notMem_of_mem_left ha₁ ha₂
          rcases hxy_uv with ⟨hxu, hyv⟩ | ⟨hxv, hyu⟩
          · exact huv_ne ((h_eq hw hu hx_w hxu).symm.trans (h_eq hw hv hy_w hyv))
          · exact huv_ne ((h_eq hw hu hy_w hyu).symm.trans (h_eq hw hv hx_w hxv)) }

/-- Building a minor model of `Graph.ofSimpleGraph H` in `toGraph G` from pairwise vertex-disjoint
connected subgraphs `K u ≤ G` (`u : γ`) with an edge of `G` between `K u` and `K v` whenever
`H.Adj u v`. -/
theorem isIsoMinor_ofSimpleGraph_of_connected_subgraphs [Finite γ] (H : SimpleGraph γ)
    {G : (⊤ : SimpleGraph α).Subgraph} (hG : G.verts.Finite)
    (K : γ → (⊤ : SimpleGraph α).Subgraph)
    (hK_le : ∀ u, K u ≤ G)
    (hK_conn : ∀ u, (K u).Connected)
    (hK_disj : Pairwise fun u v ↦ Disjoint (K u).verts (K v).verts)
    (hK_adj : ∀ ⦃u v⦄, H.Adj u v → ∃ x ∈ (K u).verts, ∃ y ∈ (K v).verts, G.Adj x y) :
    IsIsoMinor (Graph.ofSimpleGraph H) (toGraph G) := by
  rw [ofSimpleGraph_eq_toGraph H]
  exact isIsoMinor_toGraph_of_connected_subgraphs finite_univ hG K (fun u _ ↦ hK_le u)
    (fun u _ ↦ hK_conn u) (fun u _ v _ hne ↦ hK_disj hne) hK_adj

/-! ### Paths, subpaths, and vertex order -/

namespace Path

variable (P : Path α) {u v w : α}

@[simp]
lemma mem_verts_iff : v ∈ P.verts ↔ v ∈ P.walk.support :=
  P.walk.mem_verts_toSubgraph

@[simp]
lemma first_mem_verts : P.first ∈ P.verts :=
  P.walk.start_mem_verts_toSubgraph

@[simp]
lemma last_mem_verts : P.last ∈ P.verts :=
  P.walk.end_mem_verts_toSubgraph

lemma verts_nonempty : P.verts.Nonempty :=
  ⟨P.first, P.first_mem_verts⟩

lemma verts_finite : P.verts.Finite := by
  rw [verts, toSubgraph, Walk.verts_toSubgraph]
  exact List.finite_toSet P.walk.support

lemma connected_toSubgraph : P.toSubgraph.Connected :=
  P.walk.toSubgraph_connected

lemma support_nodup : P.walk.support.Nodup :=
  P.isPath.support_nodup

lemma precedes_iff_idxOf [DecidableEq α] :
    P.Precedes u v ↔ u ∈ P.verts ∧ v ∈ P.verts ∧
      P.walk.support.idxOf u < P.walk.support.idxOf v := by
  constructor
  · rintro ⟨i, j, hi, hj, hij, rfl, rfl⟩
    have hu : P.walk.support[i] ∈ P.walk.support := List.getElem_mem hi
    have hv : P.walk.support[j] ∈ P.walk.support := List.getElem_mem hj
    rw [mem_verts_iff, mem_verts_iff]
    refine ⟨hu, hv, ?_⟩
    rw [P.support_nodup.idxOf_getElem i hi, P.support_nodup.idxOf_getElem j hj]
    exact hij
  · rintro ⟨hu, hv, hij⟩
    rw [mem_verts_iff] at hu hv
    have hi : P.walk.support.idxOf u < P.walk.support.length := List.idxOf_lt_length_of_mem hu
    have hj : P.walk.support.idxOf v < P.walk.support.length := List.idxOf_lt_length_of_mem hv
    exact ⟨P.walk.support.idxOf u, P.walk.support.idxOf v, hi, hj, hij,
      List.getElem_idxOf hi, List.getElem_idxOf hj⟩

lemma Precedes.fst_mem {P : Path α} (h : P.Precedes u v) : u ∈ P.verts := by
  classical
  exact ((P.precedes_iff_idxOf).1 h).1

lemma Precedes.snd_mem {P : Path α} (h : P.Precedes u v) : v ∈ P.verts := by
  classical
  exact ((P.precedes_iff_idxOf).1 h).2.1

lemma precedes_irrefl (u : α) : ¬ P.Precedes u u := by
  classical
  rw [P.precedes_iff_idxOf]
  intro h
  exact Nat.lt_irrefl _ h.2.2

lemma Precedes.ne {P : Path α} (h : P.Precedes u v) : u ≠ v := by
  rintro rfl
  exact P.precedes_irrefl u h

lemma Precedes.asymm {P : Path α} (h : P.Precedes u v) : ¬ P.Precedes v u := by
  classical
  rw [P.precedes_iff_idxOf] at h ⊢
  intro h'
  exact Nat.lt_asymm h.2.2 h'.2.2

lemma Precedes.trans {P : Path α} (h₁ : P.Precedes u v) (h₂ : P.Precedes v w) : P.Precedes u w := by
  classical
  rw [P.precedes_iff_idxOf] at h₁ h₂ ⊢
  exact ⟨h₁.1, h₂.2.1, Nat.lt_trans h₁.2.2 h₂.2.2⟩

lemma precedes_or_eq_or_precedes (hu : u ∈ P.verts) (hv : v ∈ P.verts) :
    P.Precedes u v ∨ u = v ∨ P.Precedes v u := by
  classical
  simp only [P.precedes_iff_idxOf, hu, hv, true_and]
  rcases lt_trichotomy (P.walk.support.idxOf u) (P.walk.support.idxOf v) with hlt | heq | hgt
  · exact Or.inl hlt
  · rw [mem_verts_iff] at hu
    exact Or.inr (Or.inl ((List.idxOf_inj hu).1 heq))
  · exact Or.inr (Or.inr hgt)

lemma not_precedes_first : ¬ P.Precedes u P.first := by
  classical
  rw [P.precedes_iff_idxOf]
  rintro ⟨_, _, hlt⟩
  have h0 : P.walk.support.idxOf P.first = 0 := by
    cases h : P.walk.support with
    | nil => exact absurd h (P.walk.support_ne_nil)
    | cons a l =>
      have ha : a = P.first := by
        have := P.walk.head_support
        simpa [h] using this
      subst ha
      simp
  omega

lemma first_precedes_of_ne (hv : v ∈ P.verts) (hne : v ≠ P.first) : P.Precedes P.first v := by
  rcases P.precedes_or_eq_or_precedes P.first_mem_verts hv with h | rfl | h
  · exact h
  · exact absurd rfl hne
  · exact absurd h P.not_precedes_first

lemma not_last_precedes : ¬ P.Precedes P.last v := by
  classical
  rintro ⟨i, j, hi, hj, hij, hlast, _⟩
  have hlen : P.walk.support.length = P.walk.length + 1 := P.walk.length_support
  have hget_last : P.walk.support[P.walk.length]'(by omega) = P.last := by
    rw [← P.walk.getVert_eq_support_getElem le_rfl, P.walk.getVert_length]
  have hi_eq : i = P.walk.length := by
    apply (P.support_nodup.getElem_inj_iff (i := i) (j := P.walk.length) (hi := hi)
      (hj := by omega)).1
    rw [hlast, hget_last]
  omega

lemma precedes_last_of_ne (hu : u ∈ P.verts) (hne : u ≠ P.last) : P.Precedes u P.last := by
  rcases P.precedes_or_eq_or_precedes hu P.last_mem_verts with h | rfl | h
  · exact h
  · exact absurd rfl hne
  · exact absurd h P.not_last_precedes

/-- If `Q.walk` is a subwalk of `P.walk`, then `Q.toSubgraph ≤ P.toSubgraph`. -/
lemma toSubgraph_le_of_isSubwalk {Q : Path α} (h : Q.walk.IsSubwalk P.walk) :
    Q.toSubgraph ≤ P.toSubgraph := by
  refine ⟨fun x hx ↦ ?_, fun x y hxy ↦ ?_⟩
  · exact P.mem_verts_iff.2 (h.support_subset (Q.mem_verts_iff.1 hx))
  · rw [toSubgraph, Walk.adj_toSubgraph_iff_mem_edges] at hxy ⊢
    exact h.edges_subset hxy

/-- If `Q.walk` is a subwalk of `P.walk`, then the order of vertices on `Q` is the restriction of
the order of vertices on `P`. -/
lemma precedes_iff_of_isSubwalk {Q : Path α} (h : Q.walk.IsSubwalk P.walk) :
    Q.Precedes u v ↔ u ∈ Q.verts ∧ v ∈ Q.verts ∧ P.Precedes u v := by
  obtain ⟨s, t, hst⟩ := Walk.isSubwalk_iff_support_isInfix.1 h
  have hlen : P.walk.support.length = s.length + Q.walk.support.length + t.length := by
    have := congrArg List.length hst
    simp only [List.length_append] at this
    omega
  have hget : ∀ (i : ℕ) (hi : i < Q.walk.support.length),
      P.walk.support[s.length + i]'(by omega) = Q.walk.support[i] := by
    intro i hi
    have h1 : (s ++ Q.walk.support ++ t)[s.length + i]'(by
        simp only [List.length_append]; omega) = Q.walk.support[i] := by
      rw [List.getElem_append_left (by simp only [List.length_append]; omega)]
      rw [List.getElem_append_right (Nat.le_add_right _ _)]
      simp
    simpa [hst] using h1
  constructor
  · rintro ⟨i, j, hi, hj, hij, rfl, rfl⟩
    have hu : Q.walk.support[i] ∈ Q.verts := Q.mem_verts_iff.2 (List.getElem_mem hi)
    have hv : Q.walk.support[j] ∈ Q.verts := Q.mem_verts_iff.2 (List.getElem_mem hj)
    refine ⟨hu, hv, s.length + i, s.length + j, by omega, by omega, by omega,
      hget i hi, hget j hj⟩
  · rintro ⟨hu, hv, i', j', hi', hj', hij', hu', hv'⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 (Q.mem_verts_iff.1 hu)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 (Q.mem_verts_iff.1 hv)
    have hi_eq : i' = s.length + i := by
      apply (P.support_nodup.getElem_inj_iff (hi := hi') (hj := by omega)).1
      rw [hu', hget i hi]
    have hj_eq : j' = s.length + j := by
      apply (P.support_nodup.getElem_inj_iff (hi := hj') (hj := by omega)).1
      rw [hv', hget j hj]
    exact ⟨i, j, hi, hj, by omega, rfl, rfl⟩

/-- The one-vertex path at `v`. -/
def singleton (v : α) : Path α where
  first := v
  last := v
  walk := .nil
  isPath := .nil

@[simp]
lemma singleton_first (v : α) : (singleton v).first = v := rfl

@[simp]
lemma singleton_last (v : α) : (singleton v).last = v := rfl

@[simp]
lemma singleton_verts (v : α) : (singleton v).verts = {v} := by
  simp [singleton, verts, toSubgraph]

/-- Given a walk `p : (⊤ : SimpleGraph α).Walk u v`, its bypass is a `Path α` from `u` to `v`
whose subgraph is contained in `p.toSubgraph`. -/
noncomputable def ofWalk {u v : α} (p : (⊤ : SimpleGraph α).Walk u v) : Path α := by
  classical
  exact
    { first := u
      last := v
      walk := p.bypass
      isPath := p.bypass_isPath }

@[simp]
lemma ofWalk_first {u v : α} (p : (⊤ : SimpleGraph α).Walk u v) : (ofWalk p).first = u := rfl

@[simp]
lemma ofWalk_last {u v : α} (p : (⊤ : SimpleGraph α).Walk u v) : (ofWalk p).last = v := rfl

lemma ofWalk_toSubgraph_le {u v : α} (p : (⊤ : SimpleGraph α).Walk u v) :
    (ofWalk p).toSubgraph ≤ p.toSubgraph := by
  classical
  exact p.toSubgraph_bypass_le_toSubgraph

lemma ofWalk_verts_subset {u v : α} (p : (⊤ : SimpleGraph α).Walk u v) :
    (ofWalk p).verts ⊆ p.toSubgraph.verts :=
  (ofWalk_toSubgraph_le p).1

/-- The reverse of a path `P`, from `P.last` to `P.first`. -/
def reverse (P : Path α) : Path α where
  first := P.last
  last := P.first
  walk := P.walk.reverse
  isPath := P.isPath.reverse

@[simp]
lemma reverse_first : P.reverse.first = P.last := rfl

@[simp]
lemma reverse_last : P.reverse.last = P.first := rfl

@[simp]
lemma reverse_reverse : P.reverse.reverse = P := by
  ext <;> simp [reverse]

@[simp]
lemma reverse_toSubgraph : P.reverse.toSubgraph = P.toSubgraph :=
  P.walk.toSubgraph_reverse

@[simp]
lemma reverse_verts : P.reverse.verts = P.verts := by
  simp [verts]

@[simp]
lemma reverse_precedes_iff : P.reverse.Precedes u v ↔ P.Precedes v u := by
  have haux : ∀ (Q : Path α) {a b : α}, Q.Precedes a b → Q.reverse.Precedes b a := by
    rintro Q a b ⟨i, j, hi, hj, hij, rfl, rfl⟩
    have hlen : Q.walk.support.length = Q.walk.length + 1 := Q.walk.length_support
    have hi' : Q.walk.length - i < Q.reverse.walk.support.length := by
      simp only [reverse, Walk.support_reverse, List.length_reverse, hlen]
      omega
    have hj' : Q.walk.length - j < Q.reverse.walk.support.length := by
      simp only [reverse, Walk.support_reverse, List.length_reverse, hlen]
      omega
    refine ⟨Q.walk.length - j, Q.walk.length - i, hj', hi', by omega, ?_, ?_⟩
    · simp only [reverse, Walk.support_reverse, List.getElem_reverse, Walk.length_support]
      congr 1
      omega
    · simp only [reverse, Walk.support_reverse, List.getElem_reverse, Walk.length_support]
      congr 1
      omega
  refine ⟨fun h ↦ ?_, haux P⟩
  simpa using haux P.reverse h

/-- The initial subpath of `P` from `P.first` to `u` (`u ∈ P.verts`). -/
noncomputable def takeUntil (u : α) (hu : u ∈ P.verts) : Path α := by
  classical
  exact
    { first := P.first
      last := u
      walk := P.walk.takeUntil u (P.mem_verts_iff.1 hu)
      isPath := P.isPath.takeUntil (P.mem_verts_iff.1 hu) }

/-- The terminal subpath of `P` from `u` to `P.last` (`u ∈ P.verts`). -/
noncomputable def dropUntil (u : α) (hu : u ∈ P.verts) : Path α := by
  classical
  exact
    { first := u
      last := P.last
      walk := P.walk.dropUntil u (P.mem_verts_iff.1 hu)
      isPath := P.isPath.dropUntil (P.mem_verts_iff.1 hu) }

@[simp]
lemma takeUntil_first (hu : u ∈ P.verts) : (P.takeUntil u hu).first = P.first := rfl

@[simp]
lemma takeUntil_last (hu : u ∈ P.verts) : (P.takeUntil u hu).last = u := rfl

@[simp]
lemma dropUntil_first (hu : u ∈ P.verts) : (P.dropUntil u hu).first = u := rfl

@[simp]
lemma dropUntil_last (hu : u ∈ P.verts) : (P.dropUntil u hu).last = P.last := rfl

lemma isSubwalk_takeUntil (hu : u ∈ P.verts) : (P.takeUntil u hu).walk.IsSubwalk P.walk := by
  classical
  exact P.walk.isSubwalk_takeUntil (P.mem_verts_iff.1 hu)

lemma isSubwalk_dropUntil (hu : u ∈ P.verts) : (P.dropUntil u hu).walk.IsSubwalk P.walk := by
  classical
  exact P.walk.isSubwalk_dropUntil (P.mem_verts_iff.1 hu)

lemma takeUntil_toSubgraph_le (hu : u ∈ P.verts) :
    (P.takeUntil u hu).toSubgraph ≤ P.toSubgraph :=
  P.toSubgraph_le_of_isSubwalk (P.isSubwalk_takeUntil hu)

lemma dropUntil_toSubgraph_le (hu : u ∈ P.verts) :
    (P.dropUntil u hu).toSubgraph ≤ P.toSubgraph :=
  P.toSubgraph_le_of_isSubwalk (P.isSubwalk_dropUntil hu)

lemma takeUntil_verts_subset (hu : u ∈ P.verts) : (P.takeUntil u hu).verts ⊆ P.verts :=
  (P.takeUntil_toSubgraph_le hu).1

lemma dropUntil_verts_subset (hu : u ∈ P.verts) : (P.dropUntil u hu).verts ⊆ P.verts :=
  (P.dropUntil_toSubgraph_le hu).1

lemma toSubgraph_takeUntil_sup_dropUntil (hu : u ∈ P.verts) :
    (P.takeUntil u hu).toSubgraph ⊔ (P.dropUntil u hu).toSubgraph = P.toSubgraph := by
  classical
  change (P.walk.takeUntil u (P.mem_verts_iff.1 hu)).toSubgraph ⊔
    (P.walk.dropUntil u (P.mem_verts_iff.1 hu)).toSubgraph = P.walk.toSubgraph
  rw [← Walk.toSubgraph_append, Walk.take_spec]

lemma mem_takeUntil_verts_iff (hu : u ∈ P.verts) :
    w ∈ (P.takeUntil u hu).verts ↔ w ∈ P.verts ∧ (P.Precedes w u ∨ w = u) := by
  classical
  have hu' : u ∈ P.walk.support := P.mem_verts_iff.1 hu
  have hsupp : (P.takeUntil u hu).walk.support =
      P.walk.support.take (P.walk.support.idxOf u + 1) := by
    change (P.walk.takeUntil u hu').support = _
    rw [Walk.takeUntil_eq_take, Walk.support_copy, Walk.support_take]
  rw [mem_verts_iff, hsupp, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_take] at hi
    have hi_len : i < P.walk.support.length := Nat.lt_of_lt_of_le hi (Nat.min_le_right _ _)
    have hi_idx : i ≤ P.walk.support.idxOf u :=
      Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hi (Nat.min_le_left _ _))
    rw [List.getElem_take]
    have hw : P.walk.support[i] ∈ P.verts := P.mem_verts_iff.2 (List.getElem_mem hi_len)
    refine ⟨hw, ?_⟩
    rcases lt_or_eq_of_le hi_idx with hlt | rfl
    · left
      rw [P.precedes_iff_idxOf]
      refine ⟨hw, hu, ?_⟩
      rwa [P.support_nodup.idxOf_getElem i hi_len]
    · right
      exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hu')
  · rintro ⟨hw, hprec | rfl⟩
    · rw [P.precedes_iff_idxOf] at hprec
      have hw' : w ∈ P.walk.support := P.mem_verts_iff.1 hw
      let i := P.walk.support.idxOf w
      have hi_len : i < P.walk.support.length := List.idxOf_lt_length_of_mem hw'
      have hi : i < (P.walk.support.take (P.walk.support.idxOf u + 1)).length := by
        rw [List.length_take]
        exact lt_min (Nat.lt_succ_of_lt hprec.2.2) hi_len
      refine ⟨i, hi, ?_⟩
      rw [List.getElem_take]
      exact List.getElem_idxOf hi_len
    · let i := P.walk.support.idxOf w
      have hw' : w ∈ P.walk.support := P.mem_verts_iff.1 hw
      have hi_len : i < P.walk.support.length := List.idxOf_lt_length_of_mem hw'
      have hi : i < (P.walk.support.take (P.walk.support.idxOf w + 1)).length := by
        rw [List.length_take]
        exact lt_min (Nat.lt_succ_self i) hi_len
      refine ⟨i, hi, ?_⟩
      rw [List.getElem_take]
      exact List.getElem_idxOf hi_len

lemma mem_dropUntil_verts_iff (hu : u ∈ P.verts) :
    w ∈ (P.dropUntil u hu).verts ↔ w ∈ P.verts ∧ (P.Precedes u w ∨ w = u) := by
  classical
  have hu' : u ∈ P.walk.support := P.mem_verts_iff.1 hu
  have hsupp : (P.dropUntil u hu).walk.support =
      P.walk.support.drop (P.walk.support.idxOf u) := by
    change (P.walk.dropUntil u hu').support = _
    rw [Walk.dropUntil_eq_drop, Walk.support_copy, Walk.drop_support_eq_support_drop_min]
    have hle : P.walk.support.idxOf u ≤ P.walk.length := by
      have := List.idxOf_lt_length_of_mem hu'
      rw [Walk.length_support] at this
      omega
    rw [min_eq_left hle]
  rw [mem_verts_iff, hsupp, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_drop] at hi
    rw [List.getElem_drop]
    have hi_len : P.walk.support.idxOf u + i < P.walk.support.length := by omega
    have hw : P.walk.support[P.walk.support.idxOf u + i] ∈ P.verts :=
      P.mem_verts_iff.2 (List.getElem_mem hi_len)
    refine ⟨hw, ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · right
      simp
    · left
      rw [P.precedes_iff_idxOf]
      refine ⟨hu, hw, ?_⟩
      rw [P.support_nodup.idxOf_getElem (P.walk.support.idxOf u + i) hi_len]
      omega
  · rintro ⟨hw, hprec | rfl⟩
    · rw [P.precedes_iff_idxOf] at hprec
      have hw' : w ∈ P.walk.support := P.mem_verts_iff.1 hw
      let j := P.walk.support.idxOf w
      let k := P.walk.support.idxOf u
      have hj_len : j < P.walk.support.length := List.idxOf_lt_length_of_mem hw'
      have hkj : k < j := hprec.2.2
      refine ⟨j - k, ?_, ?_⟩
      · rw [List.length_drop]
        omega
      · rw [List.getElem_drop]
        have hadd : k + (j - k) = j := Nat.add_sub_of_le (Nat.le_of_lt hkj)
        simp [k, j, hadd]
    · have hk_len : P.walk.support.idxOf w < P.walk.support.length :=
        List.idxOf_lt_length_of_mem hu'
      refine ⟨0, ?_, ?_⟩
      · rw [List.length_drop]
        omega
      · rw [List.getElem_drop]
        simp

/-- The subpath of `P` from `u` to `v` (`u, v ∈ P.verts` with `P.Precedes u v ∨ u = v`). -/
noncomputable def subpath (u v : α) (hu : u ∈ P.verts) (hv : v ∈ P.verts)
    (huv : P.Precedes u v ∨ u = v) : Path α :=
  (P.dropUntil u hu).takeUntil v ((P.mem_dropUntil_verts_iff hu).2 ⟨hv, huv.imp id Eq.symm⟩)

@[simp]
lemma subpath_first (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v ∨ u = v) :
    (P.subpath u v hu hv huv).first = u := rfl

@[simp]
lemma subpath_last (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v ∨ u = v) :
    (P.subpath u v hu hv huv).last = v := rfl

lemma isSubwalk_subpath (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v ∨ u = v) :
    (P.subpath u v hu hv huv).walk.IsSubwalk P.walk :=
  ((P.dropUntil u hu).isSubwalk_takeUntil _).trans (P.isSubwalk_dropUntil hu)

lemma subpath_toSubgraph_le (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v ∨ u = v) :
    (P.subpath u v hu hv huv).toSubgraph ≤ P.toSubgraph :=
  P.toSubgraph_le_of_isSubwalk (P.isSubwalk_subpath hu hv huv)

lemma subpath_verts_subset (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v ∨ u = v) :
    (P.subpath u v hu hv huv).verts ⊆ P.verts :=
  (P.subpath_toSubgraph_le hu hv huv).1

lemma mem_subpath_verts_iff (hu : u ∈ P.verts) (hv : v ∈ P.verts) (huv : P.Precedes u v ∨ u = v) :
    w ∈ (P.subpath u v hu hv huv).verts ↔
      w ∈ P.verts ∧ (P.Precedes u w ∨ w = u) ∧ (P.Precedes w v ∨ w = v) := by
  rw [subpath, mem_takeUntil_verts_iff, precedes_iff_of_isSubwalk P (P.isSubwalk_dropUntil hu),
    mem_dropUntil_verts_iff]
  have hv_drop : v ∈ (P.dropUntil u hu).verts :=
    (P.mem_dropUntil_verts_iff hu).2 ⟨hv, huv.imp id Eq.symm⟩
  tauto

/-- Concatenating two paths `P` and `Q` with `P.last = Q.first` that share only that vertex. -/
def append {P Q : Path α} (h : P.last = Q.first)
    (hdisj : ∀ x ∈ P.verts, ∀ y ∈ Q.verts, x = y → x = P.last) : Path α where
  first := P.first
  last := Q.last
  walk := P.walk.append (Q.walk.copy h.symm rfl)
  isPath := by
    rw [Walk.isPath_def, Walk.support_append, Walk.support_copy, List.nodup_append]
    refine ⟨P.support_nodup, Q.support_nodup.tail, fun x hx y hy hxy ↦ ?_⟩
    subst hxy
    have hxP : x ∈ P.verts := P.mem_verts_iff.2 hx
    have hxQ : x ∈ Q.verts := Q.mem_verts_iff.2 (List.mem_of_mem_tail hy)
    have hxl : x = P.last := hdisj x hxP x hxQ rfl
    subst hxl
    rw [h] at hy
    cases hQ : Q.walk.support with
    | nil => exact absurd hQ Q.walk.support_ne_nil
    | cons a l =>
      have ha : a = Q.first := by
        have := Q.walk.head_support
        simpa [hQ] using this
      subst ha
      have hnodup : (Q.first :: l).Nodup := hQ ▸ Q.support_nodup
      have hmem : Q.first ∈ l := by simpa [hQ] using hy
      exact (List.nodup_cons.1 hnodup).1 hmem

@[simp]
lemma append_first {P Q : Path α} (h : P.last = Q.first)
    (hdisj : ∀ x ∈ P.verts, ∀ y ∈ Q.verts, x = y → x = P.last) :
    (P.append h hdisj).first = P.first := rfl

@[simp]
lemma append_last {P Q : Path α} (h : P.last = Q.first)
    (hdisj : ∀ x ∈ P.verts, ∀ y ∈ Q.verts, x = y → x = P.last) :
    (P.append h hdisj).last = Q.last := rfl

@[simp]
lemma append_toSubgraph {P Q : Path α} (h : P.last = Q.first)
    (hdisj : ∀ x ∈ P.verts, ∀ y ∈ Q.verts, x = y → x = P.last) :
    (P.append h hdisj).toSubgraph = P.toSubgraph ⊔ Q.toSubgraph := by
  change (P.walk.append (Q.walk.copy h.symm rfl)).toSubgraph = P.walk.toSubgraph ⊔ Q.walk.toSubgraph
  rw [Walk.toSubgraph_append]
  congr 1
  ext x y
  · simp
  · simp [Walk.adj_toSubgraph_iff_mem_edges]

@[simp]
lemma append_verts {P Q : Path α} (h : P.last = Q.first)
    (hdisj : ∀ x ∈ P.verts, ∀ y ∈ Q.verts, x = y → x = P.last) :
    (P.append h hdisj).verts = P.verts ∪ Q.verts := by
  simp [verts, append_toSubgraph]

/-- If `P.verts ∩ S` is nonempty, there is a first vertex of `P` in `S`. -/
lemma exists_first_mem {S : Set α} (h : (P.verts ∩ S).Nonempty) :
    ∃ u ∈ P.verts ∩ S, ∀ w ∈ P.verts ∩ S, u = w ∨ P.Precedes u w := by
  classical
  let I : Set ℕ := (fun x ↦ P.walk.support.idxOf x) '' (P.verts ∩ S)
  have hI : I.Nonempty := h.image _
  let k := Nat.find hI
  have hk : k ∈ I := Nat.find_spec hI
  obtain ⟨u, hu, hku⟩ := hk
  refine ⟨u, hu, fun w hw ↦ ?_⟩
  have hkw : k ≤ P.walk.support.idxOf w := Nat.find_le ⟨w, hw, rfl⟩
  rw [← hku] at hkw
  rcases eq_or_lt_of_le hkw with heq | hlt
  · left
    exact (List.idxOf_inj (P.mem_verts_iff.1 hu.1)).1 heq
  · right
    exact P.precedes_iff_idxOf.2 ⟨hu.1, hw.1, hlt⟩

/-- If `P.verts ∩ S` is nonempty, there is a last vertex of `P` in `S`. -/
lemma exists_last_mem {S : Set α} (h : (P.verts ∩ S).Nonempty) :
    ∃ u ∈ P.verts ∩ S, ∀ w ∈ P.verts ∩ S, u = w ∨ P.Precedes w u := by
  have hrev : (P.reverse.verts ∩ S).Nonempty := by simpa using h
  obtain ⟨u, hu, hmin⟩ := P.reverse.exists_first_mem hrev
  rw [reverse_verts] at hu
  refine ⟨u, hu, fun w hw ↦ ?_⟩
  have h' := hmin w (by simpa using hw)
  rwa [reverse_precedes_iff] at h'

end Path

/-- In any preconnected subgraph `H`, any two vertices `u, v ∈ H.verts` are joined by a path in
`H`. -/
lemma exists_path_of_preconnected {H : (⊤ : SimpleGraph α).Subgraph} (hH : H.Preconnected)
    {u v : α} (hu : u ∈ H.verts) (hv : v ∈ H.verts) :
    ∃ P : Path α, P.toSubgraph ≤ H ∧ P.first = u ∧ P.last = v := by
  obtain ⟨p, hp⟩ := (Subgraph.preconnected_iff_forall_exists_walk_subgraph H).1 hH hu hv
  exact ⟨Path.ofWalk p, (Path.ofWalk_toSubgraph_le p).trans hp, rfl, rfl⟩

/-- If `H` is preconnected and meets both `A₁` and `A₂`, there is a path `P` in `H` from `A₁` to
`A₂` meeting `A₁` only in `P.first` and `A₂` only in `P.last`. -/
lemma exists_minimal_path_from_to {H : (⊤ : SimpleGraph α).Subgraph} (hH : H.Preconnected)
    {A₁ A₂ : Set α} (h₁ : (H.verts ∩ A₁).Nonempty) (h₂ : (H.verts ∩ A₂).Nonempty) :
    ∃ P : Path α, P.IsFromTo H A₁ A₂ ∧ P.verts ∩ A₁ = {P.first} ∧ P.verts ∩ A₂ = {P.last} := by
  obtain ⟨x₁, hx₁H, hx₁A⟩ := h₁
  obtain ⟨x₂, hx₂H, hx₂A⟩ := h₂
  obtain ⟨P₀, hP₀_le, hP₀_first, hP₀_last⟩ := exists_path_of_preconnected hH hx₁H hx₂H
  have hP₀_A₂ : (P₀.verts ∩ A₂).Nonempty :=
    ⟨x₂, hP₀_last ▸ P₀.last_mem_verts, hx₂A⟩
  obtain ⟨v, ⟨hvP₀, hvA₂⟩, hv_first⟩ := P₀.exists_first_mem hP₀_A₂
  let P₁ := P₀.takeUntil v hvP₀
  have hP₁_le : P₁.toSubgraph ≤ H := (P₀.takeUntil_toSubgraph_le hvP₀).trans hP₀_le
  have hP₁_A₂ : P₁.verts ∩ A₂ = {v} := by
    ext w
    simp only [P₁, Path.mem_takeUntil_verts_iff, mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨⟨hwP₀, hprec⟩, hwA₂⟩ ↦ ?_, ?_⟩
    · rcases hv_first w ⟨hwP₀, hwA₂⟩ with rfl | hvw
      · rfl
      · rcases hprec with hwv | rfl
        · exact absurd hwv hvw.asymm
        · rfl
    · rintro rfl
      exact ⟨⟨hvP₀, Or.inr rfl⟩, hvA₂⟩
  have hP₁_A₁ : (P₁.verts ∩ A₁).Nonempty := by
    refine ⟨x₁, ?_, hx₁A⟩
    rw [ ← hP₀_first, ← P₀.takeUntil_first hvP₀]
    exact P₁.first_mem_verts
  obtain ⟨u, ⟨huP₁, huA₁⟩, hu_last⟩ := P₁.exists_last_mem hP₁_A₁
  let P₂ := P₁.dropUntil u huP₁
  refine ⟨P₂, ⟨(P₁.dropUntil_toSubgraph_le huP₁).trans hP₁_le, huA₁, hvA₂⟩, ?_, ?_⟩
  · ext w
    simp only [P₂, Path.dropUntil_first, Path.mem_dropUntil_verts_iff, mem_inter_iff,
      mem_singleton_iff]
    refine ⟨fun ⟨⟨hwP₁, hprec⟩, hwA₁⟩ ↦ ?_, ?_⟩
    · rcases hu_last w ⟨hwP₁, hwA₁⟩ with rfl | hwu
      · rfl
      · rcases hprec with huw | rfl
        · exact absurd huw hwu.asymm
        · rfl
    · rintro rfl
      exact ⟨⟨huP₁, Or.inr rfl⟩, huA₁⟩
  · ext w
    simp only [P₂, Path.dropUntil_last, mem_inter_iff, mem_singleton_iff]
    refine ⟨fun ⟨hwP₂, hwA₂⟩ ↦ ?_, ?_⟩
    · have hw_in : w ∈ P₁.verts ∩ A₂ := ⟨P₁.dropUntil_verts_subset huP₁ hwP₂, hwA₂⟩
      rwa [hP₁_A₂, mem_singleton_iff] at hw_in
    · rintro rfl
      exact ⟨P₂.last_mem_verts, hvA₂⟩

end GraphMinor.GM01
