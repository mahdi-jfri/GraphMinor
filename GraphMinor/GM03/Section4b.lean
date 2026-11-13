module

public import GraphMinor.GM03.Section4a
public import GraphMinor.Minor.Model
import GraphMinor.GM07.CuffCells
import GraphMinor.GM07.CuffOrder
import GraphMinor.GM07.CuffSegments
import GraphMinor.GM09.PlanarNests

/-!
# Graph Minors III, Section 4 Helpers: Ordered Cylinder Pieces in Plane Drawings

This file constructs `OrderedNestedCylinderData` from a nested sequence of circuits and disjoint
radial paths in a plane drawing (`buildOrderedNestedCylinderData`), ordering the radial paths
consistently around all circuits via plane cuff cells (`GM07.exists_cell_family`) and splitting each
circuit into pairwise vertex-disjoint connected pieces joined by circular edges, for use in
Graph Minors III, (4.3) (page 61) and (4.5) (page 62).
-/

public section

namespace GraphMinor.GM03

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM07 GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM11 GraphMinor.GM12 GraphMinor.GM14 GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

local instance {G : Graph α β} (M : PlanarDrawing G) : T2Space M.S :=
  M.isClosedSurface.2.1

local instance {G : Graph α β} (M : PlanarDrawing G) : ConnectedSpace M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2

local instance {G : Graph α β} (M : PlanarDrawing G) : Nonempty M.S :=
  (GM11.IsSphere.isClosedSurface M.isSphere).2.toNonempty

/-- The union of two `GraphConnected` subgraphs sharing at least one vertex is `GraphConnected`. -/
theorem graphConnected_subgraphUnion {G K₁ K₂ : Graph α β} (h₁ : K₁ ≤ G) (h₂ : K₂ ≤ G)
    (hc₁ : GraphConnected K₁) (hc₂ : GraphConnected K₂) (hinter : (V(K₁) ∩ V(K₂)).Nonempty) :
    GraphConnected (subgraphUnion G K₁ K₂) := by
  obtain ⟨z₀, hz₁, hz₂⟩ := hinter
  have hle₁ : K₁ ≤ subgraphUnion G K₁ K₂ := le_subgraphUnion_left h₁ h₂
  have hle₂ : K₂ ≤ subgraphUnion G K₁ K₂ := le_subgraphUnion_right h₁ h₂
  have mono_rtg : ∀ {H₁ H₂ : Graph α β}, H₁ ≤ H₂ →
      ∀ {x y : α}, Relation.ReflTransGen H₁.Adj x y → Relation.ReflTransGen H₂.Adj x y := by
    intro H₁ H₂ hle x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _ hab ih =>
      obtain ⟨e, hl⟩ := hab
      exact ih.tail ⟨e, hl.mono hle⟩
  have to_z₀ : ∀ x ∈ V(subgraphUnion G K₁ K₂),
      Relation.ReflTransGen (subgraphUnion G K₁ K₂).Adj x z₀ := by
    intro x hx
    rw [vertexSet_subgraphUnion] at hx
    rcases hx with hx₁ | hx₂
    · exact mono_rtg hle₁ (hc₁.2 x hx₁ z₀ hz₁)
    · exact mono_rtg hle₂ (hc₂.2 x hx₂ z₀ hz₂)
  have symm_rtg : ∀ {H : Graph α β} {x y : α},
      Relation.ReflTransGen H.Adj x y → Relation.ReflTransGen H.Adj y x := by
    intro H x y hxy
    induction hxy with
    | refl => exact .refl
    | tail _ hab ih => exact Relation.ReflTransGen.head hab.symm ih
  refine ⟨⟨z₀, by rw [vertexSet_subgraphUnion]; exact Or.inl hz₁⟩, fun x hx y hy => ?_⟩
  exact (to_z₀ x hx).trans (symm_rtg (to_z₀ y hy))

/-- Intermediate walk-and-disc bundle for `buildOrderedNestedCylinderData`. -/
private structure WalkNestedSplit [Nonempty α] [Nonempty β] {G : Graph α β} (M : PlanarDrawing G)
    (r s : ℕ) (hs : 0 < s) (C : Fin s → Graph α β) (P : Fin r → Graph α β) where
  a : Fin r → α
  b : Fin r → α
  W : ∀ i : Fin r, GraphWalk G (a i) (b i)
  W_simple : ∀ i : Fin r, (W i).IsSimple
  a_mem : ∀ i : Fin r, a i ∈ V(C ⟨0, hs⟩)
  b_mem : ∀ i : Fin r, b i ∈ V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)
  P_le : ∀ i : Fin r, P i ≤ G
  P_V : ∀ i : Fin r, V(P i) = {z | z ∈ (W i).support}
  P_E : ∀ i : Fin r, E(P i) = {e | e ∈ (W i).edges}
  x : Fin r → Fin s → α
  y : Fin r → Fin s → α
  W_pre : ∀ (i : Fin r) (j : Fin s), GraphWalk G (a i) (x i j)
  W_mid : ∀ (i : Fin r) (j : Fin s), GraphWalk G (x i j) (y i j)
  W_post : ∀ (i : Fin r) (j : Fin s), GraphWalk G (y i j) (b i)
  W_split : ∀ (i : Fin r) (j : Fin s),
    W i = (W_pre i j).append ((W_mid i j).append (W_post i j))
  mid_V : ∀ (i : Fin r) (j : Fin s), {z | z ∈ (W_mid i j).support} = V(P i) ∩ V(C j)
  mid_E : ∀ (i : Fin r) (j : Fin s), {e | e ∈ (W_mid i j).edges} = E(P i) ∩ E(C j)
  x_only_pre : ∀ (i : Fin r) (j : Fin s) {z : α},
    z ∈ (W_pre i j).support → z ∈ V(C j) → z = x i j
  y_only_post : ∀ (i : Fin r) (j : Fin s) {z : α},
    z ∈ (W_post i j).support → z ∈ V(C j) → z = y i j
  x_zero : ∀ i : Fin r, x i ⟨0, hs⟩ = a i
  y_last : ∀ i : Fin r, y i ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = b i
  C_draw : Fin s → Drawing M.S
  Cd_circ : ∀ j : Fin s, (C_draw j).IsCircuit
  Cd_sub : ∀ j : Fin s, (C_draw j).IsSubdrawing M.drawing
  Cd_V : ∀ j : Fin s,
    (C_draw j).V = Function.invFunOn (drawingInvV M) M.drawing.V '' V(C j)
  Cd_E : ∀ j : Fin s,
    (C_draw j).E = Function.invFunOn (drawingInvE M) M.drawing.E '' E(C j)
  Δ : Fin s → Set M.S
  Δ_in : ∀ j : Fin s, IsInsideDisc M (C j) (Δ j)
  Δ_bd : ∀ j : Fin s, discBd (Δ j) = (C_draw j).U
  Δ_nested : ∀ {j₁ j₂ : Fin s}, j₁ < j₂ → Δ j₂ ⊆ Δ j₁ \ discBd (Δ j₁)
  between_post : ∀ (i : Fin r) {j₁ j₂ : Fin s}, j₁ < j₂ →
    ∃ R : GraphWalk G (y i j₁) (x i j₂),
      W_post i j₁ = R.append ((W_mid i j₂).append (W_post i j₂))

private theorem graphWalk_eq_of_support_edges {G : Graph α β} {u v : α}
    {W₁ W₂ : GraphWalk G u v} (hs : W₁.support = W₂.support) (he : W₁.edges = W₂.edges) :
    W₁ = W₂ := by
  induction W₁ with
  | nil _ =>
    cases W₂ with
    | nil _ => rfl
    | cons _ _ => cases he
  | @cons a b c e₁ hl₁ r₁ ih =>
    cases W₂ with
    | nil _ => cases he
    | @cons _ b' _ e₂ hl₂ r₂ =>
      have hb : b = b' := by
        have h1 := List.tail_eq_of_cons_eq hs
        rw [r₁.support_eq_cons, r₂.support_eq_cons] at h1
        exact (List.cons.inj h1).1
      subst hb
      have he_eq : e₁ = e₂ := (List.cons.inj he).1
      subst he_eq
      exact congrArg (GraphWalk.cons hl₁)
        (ih (List.tail_eq_of_cons_eq hs) (List.tail_eq_of_cons_eq he))

private theorem list_append_eq_of_nodup_getLast {X : Type*} {l₁ l₂ t₁ t₂ : List X} {v : X}
    (hnd : (l₁ ++ t₁).Nodup) (heq : l₁ ++ t₁ = l₂ ++ t₂)
    (hl₁ : l₁.getLast? = some v) (hl₂ : l₂.getLast? = some v) :
    l₁ = l₂ ∧ t₁ = t₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at hl₁
  | cons a s₁ ih =>
    cases l₂ with
    | nil => simp at hl₂
    | cons b s₂ =>
      simp only [List.cons_append, List.cons.injEq] at heq
      obtain ⟨rfl, hst⟩ := heq
      obtain ⟨ha_not, hnd_rest⟩ := List.nodup_cons.mp hnd
      by_cases hs₁ : s₁ = []
      · subst hs₁
        simp only [List.getLast?_singleton, Option.some.injEq] at hl₁
        subst hl₁
        by_cases hs₂ : s₂ = []
        · subst hs₂
          exact ⟨rfl, hst⟩
        · exfalso
          rw [List.getLast?_cons_of_ne_nil hs₂] at hl₂
          have ha_s₂ : a ∈ s₂ := List.mem_of_getLast? hl₂
          change a ∉ [] ++ t₁ at ha_not
          rw [hst] at ha_not
          exact ha_not (List.mem_append_left _ ha_s₂)
      · rw [List.getLast?_cons_of_ne_nil hs₁] at hl₁
        by_cases hs₂ : s₂ = []
        · exfalso
          subst hs₂
          simp only [List.getLast?_singleton, Option.some.injEq] at hl₂
          subst hl₂
          have ha_s₁ : a ∈ s₁ := List.mem_of_getLast? hl₁
          exact ha_not (List.mem_append_left _ ha_s₁)
        · rw [List.getLast?_cons_of_ne_nil hs₂] at hl₂
          obtain ⟨rfl, rfl⟩ := ih hnd_rest hst hl₁ hl₂
          exact ⟨rfl, rfl⟩

private theorem walk_suffix_eq_of_simple_aux {G : Graph α β} {u v w : α}
    {A₁ A₂ : GraphWalk G u v} {B₁ B₂ : GraphWalk G v w}
    (hsimp : (A₁.append B₁).IsSimple) (heq_w : A₁.append B₁ = A₂.append B₂) :
    B₁ = B₂ := by
  have hlast : ∀ {p q : α} (V : GraphWalk G p q), V.support.getLast? = some q := by
    intro p q V
    induction V with
    | nil _ => rfl
    | cons _ r ih =>
      have hne : r.support ≠ [] := by rw [r.support_eq_cons]; simp
      rw [GraphWalk.support, List.getLast?_cons_of_ne_nil hne, ih]
  have hlen_se : ∀ {p q : α} (V : GraphWalk G p q), V.support.length = V.edges.length + 1 := by
    intro p q V
    induction V with
    | nil _ => rfl
    | cons _ r ih => simp [GraphWalk.support, GraphWalk.edges, ih]
  have hsupp_eq := congrArg GraphWalk.support heq_w
  have hedges_eq := congrArg GraphWalk.edges heq_w
  rw [GraphWalk.support_append, GraphWalk.support_append] at hsupp_eq
  rw [GraphWalk.edges_append, GraphWalk.edges_append] at hedges_eq
  have hnd1 : (A₁.support ++ B₁.support.tail).Nodup := by
    have h' : (A₁.append B₁).support.Nodup := hsimp
    rwa [GraphWalk.support_append] at h'
  obtain ⟨hA_supp, hB_tail⟩ :=
    list_append_eq_of_nodup_getLast hnd1 hsupp_eq (hlast A₁) (hlast A₂)
  have hlenE : A₁.edges.length = A₂.edges.length := by
    have h1 := hlen_se A₁
    have h2 := hlen_se A₂
    have h3 := congrArg List.length hA_supp
    omega
  have hB_edges : B₁.edges = B₂.edges := List.append_inj_right hedges_eq hlenE
  have hB_supp : B₁.support = B₂.support := by
    rw [B₁.support_eq_cons, B₂.support_eq_cons, hB_tail]
  exact graphWalk_eq_of_support_edges hB_supp hB_edges

private noncomputable def buildWalkNestedSplit [Nonempty α] [Nonempty β] {G : Graph α β}
    (M : PlanarDrawing G) (r s : ℕ) (hs : 0 < s)
    (C : Fin s → Graph α β) (P : Fin r → Graph α β)
    (hC : IsNestedCircuitSeq M s C)
    (hP_path : ∀ i : Fin r, IsPathBetween G (P i)
      V(C ⟨0, hs⟩) V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩))
    (hP_inter : ∀ (i : Fin r) (j : Fin s), IsGraphPath G (subgraphInter G (P i) (C j))) :
    WalkNestedSplit M r s hs C P := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  let m := gmap_of_planarDrawing M
  let ms := m.symm
  have hex_W : ∀ i : Fin r, ∃ (a b : α) (W : GraphWalk G a b),
      a ∈ V(C ⟨0, hs⟩) ∧ b ∈ V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) ∧
      W.IsSimple ∧ P i ≤ G ∧
      V(P i) = {z | z ∈ W.support} ∧ E(P i) = {e | e ∈ W.edges} := by
    intro i
    obtain ⟨a, ha, b, hb, hPG, W₀, hW₀s, hV, hE⟩ := hP_path i
    obtain ⟨W, hsW, heW⟩ := exists_walk_up_of_le hPG W₀
    have hWs : W.IsSimple := by unfold GraphWalk.IsSimple; rw [hsW]; exact hW₀s
    exact ⟨a, b, W, ha, hb, hWs, hPG, by rw [hV, hsW], by rw [hE, heW]⟩
  choose a b W ha_mem hb_mem hW_simple hP_le hP_V hP_E using hex_W
  have hex_mid : ∀ (i : Fin r) (j : Fin s),
      ∃ (x y : α) (W₁ : GraphWalk G (a i) x) (W₂ : GraphWalk G x y) (W₃ : GraphWalk G y (b i)),
        W i = W₁.append (W₂.append W₃) ∧
        {z | z ∈ W₂.support} = V(P i) ∩ V(C j) ∧
        {e | e ∈ W₂.edges} = E(P i) ∩ E(C j) := by
    intro i j
    have hQP : subgraphInter G (P i) (C j) ≤ P i := subgraphInter_le_left (hP_le i) (hC.1 j).1
    obtain ⟨x, y, W₁, W₂, W₃, hsplit, hV_eq, hE_eq⟩ :=
      exists_contiguous_subwalk_of_isGraphPath (W i) (hW_simple i) (hP_V i) (hP_E i)
        hQP (hP_inter i j)
    rw [vertexSet_subgraphInter] at hV_eq
    rw [edgeSet_subgraphInter (hP_le i) (hC.1 j).1] at hE_eq
    exact ⟨x, y, W₁, W₂, W₃, hsplit, hV_eq.symm, hE_eq.symm⟩
  choose x y W_pre W_mid W_post hW_split hmid_V hmid_E using hex_mid
  have hx_only_pre : ∀ (i : Fin r) (j : Fin s) {z : α},
      z ∈ (W_pre i j).support → z ∈ V(C j) → z = x i j := by
    intro i j z hz_pre hzC
    have hzP : z ∈ V(P i) := by
      rw [hP_V i, mem_ofPred_eq, hW_split i j, GraphWalk.mem_support_append]
      exact Or.inl hz_pre
    have hz_mid : z ∈ (W_mid i j).support := by
      change z ∈ {w | w ∈ (W_mid i j).support}
      rw [hmid_V i j]; exact ⟨hzP, hzC⟩
    have hnd : ((W_pre i j).support ++ ((W_mid i j).append (W_post i j)).support.tail).Nodup := by
      have h' : (W i).support.Nodup := hW_simple i
      rwa [hW_split i j, GraphWalk.support_append] at h'
    rw [(W_mid i j).support_eq_cons] at hz_mid
    rcases List.mem_cons.mp hz_mid with rfl | hz_tail
    · rfl
    · exfalso
      have hz_tail' : z ∈ ((W_mid i j).append (W_post i j)).support.tail := by
        rw [GraphWalk.support_append, (W_mid i j).support_eq_cons]
        exact List.mem_append_left _ hz_tail
      exact (List.nodup_append.mp hnd).2.2 z hz_pre z hz_tail' rfl
  have hy_only_post : ∀ (i : Fin r) (j : Fin s) {z : α},
      z ∈ (W_post i j).support → z ∈ V(C j) → z = y i j := by
    intro i j z hz_post hzC
    have hzP : z ∈ V(P i) := by
      rw [hP_V i, mem_ofPred_eq, hW_split i j, GraphWalk.mem_support_append,
        GraphWalk.mem_support_append]
      exact Or.inr (Or.inr hz_post)
    have hz_mid : z ∈ (W_mid i j).support := by
      change z ∈ {w | w ∈ (W_mid i j).support}
      rw [hmid_V i j]; exact ⟨hzP, hzC⟩
    have hnd2 : ((W_mid i j).append (W_post i j)).support.Nodup :=
      (isSimple_of_append (hW_split i j ▸ hW_simple i)).2
    rw [GraphWalk.support_append] at hnd2
    rw [(W_post i j).support_eq_cons] at hz_post
    rcases List.mem_cons.mp hz_post with rfl | hz_tail
    · rfl
    · exact ((List.nodup_append.mp hnd2).2.2 z hz_mid z hz_tail rfl).elim
  have hx_zero : ∀ i : Fin r, x i ⟨0, hs⟩ = a i :=
    fun i => (hx_only_pre i ⟨0, hs⟩ (W_pre i ⟨0, hs⟩).start_mem_support (ha_mem i)).symm
  have hy_last : ∀ i : Fin r, y i ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ = b i := by
    intro i
    let jl : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
    exact (hy_only_post i jl (W_post i jl).end_mem_support (hb_mem i)).symm
  have hex_Cd : ∀ j : Fin s, ∃ R : Drawing M.S,
      R.IsCircuit ∧ R.IsSubdrawing M.drawing ∧
      R.V = V(ms.sub (C j)) ∧ R.E = E(ms.sub (C j)) :=
    fun j => GM14.exists_circuit_drawing (ms.circuit (hC.1 j))
  choose C_draw hCd_circ hCd_sub hCd_V hCd_E using hex_Cd
  have hCd_U : ∀ j : Fin s, graphDrawingSubgraphU M.graphDrawing (C j) = (C_draw j).U := by
    intro j
    have hmap : m.sub (C_draw j).toGraph = C j :=
      gmap_sub_eq_of_symm_sub' M (hC.1 j).1 (toGraph_le_of_isSubdrawing' (hCd_sub j))
        (hCd_V j) (hCd_E j)
    rw [← hmap]
    exact graphDrawingSubgraphU_gmap_sub M (hCd_sub j) (toGraph_le_of_isSubdrawing' (hCd_sub j))
  have hex_Δ : ∀ j : Fin s, ∃ Δ : Set M.S, IsInsideDisc M (C j) Δ :=
    fun j => exists_insideDisc_of_circuit M (hC.1 j)
  choose Δ hΔ_in using hex_Δ
  have hΔ_bd : ∀ j : Fin s, discBd (Δ j) = (C_draw j).U :=
    fun j => (hΔ_in j).2.1.trans (hCd_U j)
  have hΔ_nested : ∀ {j₁ j₂ : Fin s}, j₁ < j₂ → Δ j₂ ⊆ Δ j₁ \ discBd (Δ j₁) := by
    intro j₁ j₂ hj
    obtain ⟨hdisj_V, Δ₂', Δ₁', h₂', h₁', hsub⟩ := hC.2 hj
    rw [isInsideDisc_eq M (hΔ_in j₂) h₂', isInsideDisc_eq M (hΔ_in j₁) h₁']
    have hdisj_U : Disjoint (C_draw j₂).U (C_draw j₁).U := by
      have hdisj_dV : Disjoint (C_draw j₂).V (C_draw j₁).V := by
        rw [hCd_V j₂, hCd_V j₁, ms.vertexSet_sub, ms.vertexSet_sub]
        exact disjoint_image_of_injOn'
          (ms.bijV.injOn.mono (union_subset (hC.1 j₂).1.vertexSet_mono (hC.1 j₁).1.vertexSet_mono))
          subset_union_left subset_union_right hdisj_V.symm
      refine Set.disjoint_left.mpr fun z hz₂ hz₁ => ?_
      by_cases hzV : z ∈ M.drawing.V
      · have hz₂V : z ∈ (C_draw j₂).V := by
          by_contra hn; obtain ⟨e, he, hze⟩ := (C_draw j₂).exists_edge_of_mem hz₂ hn
          exact (((hCd_sub j₂).2 he).2.1 hze).2 hzV
        have hz₁V : z ∈ (C_draw j₁).V := by
          by_contra hn; obtain ⟨e, he, hze⟩ := (C_draw j₁).exists_edge_of_mem hz₁ hn
          exact (((hCd_sub j₁).2 he).2.1 hze).2 hzV
        exact Set.disjoint_left.mp hdisj_dV hz₂V hz₁V
      · obtain ⟨e₂, he₂, hze₂⟩ := (C_draw j₂).exists_edge_of_mem hz₂
          (fun h => hzV ((hCd_sub j₂).1 h))
        obtain ⟨e₁, he₁, hze₁⟩ := (C_draw j₁).exists_edge_of_mem hz₁
          (fun h => hzV ((hCd_sub j₁).1 h))
        have heq : e₂ = e₁ := M.drawing.edge_eq_of_mem ((hCd_sub j₂).2 he₂)
          ((hCd_sub j₁).2 he₁) hze₂ hze₁
        obtain ⟨x₀, y₀, hlM⟩ := M.drawing.toGraph.exists_isLink_of_mem_edgeSet ((hCd_sub j₂).2 he₂)
        have hl₂ : (C_draw j₂).toGraph.IsLink e₂ x₀ y₀ := ((hCd_sub j₂).isLink_iff he₂).mpr hlM
        have hl₁ : (C_draw j₁).toGraph.IsLink e₁ x₀ y₀ :=
          ((hCd_sub j₁).isLink_iff he₁).mpr (heq ▸ hlM)
        exact Set.disjoint_left.mp hdisj_dV hl₂.left_mem hl₁.left_mem
    intro z hz₂
    refine ⟨hsub hz₂, fun hz_bd₁ => ?_⟩
    rw [isInsideDisc_eq M h₁' (hΔ_in j₁), hΔ_bd j₁] at hz_bd₁
    have hman : ∀ x : M.S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
    have hopen : IsOpen (discInt Δ₂') := h₂'.1.isOpen_discInt hman
    by_cases hz_bd₂ : z ∈ discBd Δ₂'
    · rw [isInsideDisc_eq M h₂' (hΔ_in j₂), hΔ_bd j₂] at hz_bd₂
      exact Set.disjoint_left.mp hdisj_U hz_bd₂ hz_bd₁
    · have hz_int₂ : z ∈ discInt Δ₂' := ⟨hz₂, hz_bd₂⟩
      have hz_int₁ : z ∈ interior Δ₁' :=
        interior_maximal ((Surface.discInt_subset Δ₂').trans hsub) hopen hz_int₂
      have hfr₁ : frontier Δ₁' = discBd Δ₁' := GM11.IsClosedDisc.frontier_eq_discBd hS h₁'.1
      have hnot_fr : z ∉ frontier Δ₁' := fun hfr => hfr.2 hz_int₁
      rw [hfr₁, isInsideDisc_eq M h₁' (hΔ_in j₁), hΔ_bd j₁] at hnot_fr
      exact hnot_fr hz_bd₁
  let toS : α → M.S := Function.invFunOn (drawingInvV M) M.drawing.V
  let toE : β → Set M.S := Function.invFunOn (drawingInvE M) M.drawing.E
  have htoS_Cd : ∀ {j : Fin s} {z : α}, z ∈ V(C j) → toS z ∈ (C_draw j).V := by
    intro j z hz
    rw [hCd_V j, ms.vertexSet_sub]
    exact mem_image_of_mem _ hz
  have hCd_toS_inv : ∀ {j : Fin s} {z : α}, z ∈ V(G) → toS z ∈ (C_draw j).V → z ∈ V(C j) := by
    intro j z hzG hzS
    rw [hCd_V j, ms.vertexSet_sub] at hzS
    obtain ⟨w, hwC, hw_eq⟩ := hzS
    have hinv : InvOn (invFunOn (drawingInvV M) M.drawing.V) (drawingInvV M) M.drawing.V V(G) :=
      m.bijV.invOn_invFunOn
    have h1 := congrArg (drawingInvV M) hw_eq
    dsimp [toS] at h1
    change drawingInvV M (invFunOn (drawingInvV M) M.drawing.V w) =
      drawingInvV M (invFunOn (drawingInvV M) M.drawing.V z) at h1
    rw [hinv.2 ((hC.1 j).1.vertexSet_mono hwC), hinv.2 hzG] at h1
    exact h1 ▸ hwC
  have transfer_walk : ∀ {p q : α} (U : GraphWalk G p q),
      ∃ U_d : GraphWalk M.drawing.toGraph (toS p) (toS q),
        U_d.IsSimple = U.IsSimple ∧
        U_d.support = U.support.map toS ∧
        U_d.edges = U.edges.map toE ∧
        (∀ w ∈ U_d.support, ∃ z ∈ U.support, toS z = w) := by
    intro p q U
    have h_tr : ∀ {p q : α} (U : GraphWalk G p q),
        ∃ U_d : GraphWalk M.drawing.toGraph (toS p) (toS q),
          U_d.support = U.support.map toS ∧ U_d.edges = U.edges.map toE := by
      intro p q U
      induction U with
      | nil hp =>
        exact ⟨.nil (ms.bijV.mapsTo hp), rfl, rfl⟩
      | @cons u w q e hl r ih =>
        obtain ⟨r_d, hr_s, hr_e⟩ := ih
        have hl_d : M.drawing.toGraph.IsLink (toE e) (toS u) (toS w) := by
          have he := hl.edge_mem; have hu := hl.left_mem; have hw := hl.right_mem
          have hinvV := m.bijV.invOn_invFunOn
          have hinvE := m.bijE.invOn_invFunOn
          refine (m.link (ms.bijE.mapsTo he) (ms.bijV.mapsTo hu) (ms.bijV.mapsTo hw)).mpr ?_
          dsimp [toS, toE] at *
          rwa [hinvE.2 he, hinvV.2 hu, hinvV.2 hw]
        exact ⟨.cons hl_d r_d, by simp [GraphWalk.support, hr_s], by simp [GraphWalk.edges, hr_e]⟩
    obtain ⟨U_d, hsupp, hedges⟩ := h_tr U
    have hinj_supp : U.support.Nodup ↔ U_d.support.Nodup := by
      rw [hsupp]
      refine ⟨fun hnd => hnd.map_on fun z₁ hz₁ z₂ hz₂ heq => ?_, List.Nodup.of_map toS⟩
      exact ms.bijV.injOn (U.mem_vertexSet_of_mem_support hz₁)
        (U.mem_vertexSet_of_mem_support hz₂) heq
    refine ⟨U_d, propext hinj_supp.symm, hsupp, hedges, fun w hw => ?_⟩
    rw [hsupp, List.mem_map] at hw
    exact hw
  have hpre_disj_inner : ∀ (i : Fin r) {j₁ j₂ : Fin s}, j₁ < j₂ →
      ∀ z ∈ (W_pre i j₁).support, z ∉ V(C j₂) := by
    intro i j₁ j₂ hj z hz_pre hz_C₂
    by_cases hj10 : j₁.1 = 0
    · have hj1_eq : j₁ = ⟨0, hs⟩ := Fin.ext hj10
      subst hj1_eq
      have hpre_nil : (W_pre i ⟨0, hs⟩).support = [a i] := by
        have hnd : (W_pre i ⟨0, hs⟩).IsSimple :=
          (isSimple_of_append (hW_split i ⟨0, hs⟩ ▸ hW_simple i)).1
        have hnil_supp : ∀ {u w : α} (V : GraphWalk G u w), V.IsSimple → u = w → V.support = [u] := by
          intro u w V hVs huw
          cases huw
          cases V with
          | nil _ => rfl
          | cons _ r => exact ((List.nodup_cons.mp hVs).1 r.end_mem_support).elim
        exact hnil_supp (W_pre i ⟨0, hs⟩) hnd (hx_zero i).symm
      rw [hpre_nil, List.mem_singleton] at hz_pre
      subst hz_pre
      exact Set.disjoint_left.mp (hC.2 hj).1 (ha_mem i) hz_C₂
    · have h0_lt_j₁ : (⟨0, hs⟩ : Fin s) < j₁ := Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hj10)
      obtain ⟨U_d, hUd_s_eq, hUd_supp, _, hUd_mem⟩ := transfer_walk (W_pre i j₁)
      have hUs : U_d.IsSimple := hUd_s_eq.mpr
        (isSimple_of_append (hW_split i j₁ ▸ hW_simple i)).1
      have ha_out : toS (a i) ∉ Δ j₁ := by
        intro ha_in
        have ha_bd0 : toS (a i) ∈ discBd (Δ ⟨0, hs⟩) := by
          rw [hΔ_bd ⟨0, hs⟩]; exact (C_draw ⟨0, hs⟩).V_subset_U (htoS_Cd (ha_mem i))
        exact (hΔ_nested h0_lt_j₁ ha_in).2 ha_bd0
      have honly_d : ∀ w ∈ U_d.support, w ∈ (C_draw j₁).V → w = toS (x i j₁) := by
        intro w hw hwC₁
        obtain ⟨z₀, hz₀_supp, rfl⟩ := hUd_mem w hw
        have hz₀_C₁ : z₀ ∈ V(C j₁) :=
          hCd_toS_inv ((W_pre i j₁).mem_vertexSet_of_mem_support hz₀_supp) hwC₁
        exact congrArg toS (hx_only_pre i j₁ hz₀_supp hz₀_C₁)
      have hcap := walkDrawing_outside_disc_except_end hS (hCd_sub j₁) (hΔ_in j₁).1 (hΔ_bd j₁)
        U_d hUs ha_out (htoS_Cd (by
          have : x i j₁ ∈ V(P i) ∩ V(C j₁) := by
            rw [← hmid_V i j₁]; exact (W_mid i j₁).start_mem_support
          exact this.2)) honly_d
      have hz_Ud : toS z ∈ (walkDrawing M.drawing U_d).U :=
        (walkDrawing M.drawing U_d).V_subset_U
          (by rw [walkDrawing_V, hUd_supp]; exact List.mem_map_of_mem hz_pre)
      have hz_Δ₂ : toS z ∈ Δ j₂ :=
        Surface.discBd_subset (Δ j₂) (hΔ_bd j₂ ▸ (C_draw j₂).V_subset_U (htoS_Cd hz_C₂))
      have hz_Δ₁ : toS z ∈ Δ j₁ := (hΔ_nested hj hz_Δ₂).1
      have hz_eq_x : toS z = toS (x i j₁) := by
        have : toS z ∈ (walkDrawing M.drawing U_d).U ∩ Δ j₁ := ⟨hz_Ud, hz_Δ₁⟩
        rwa [hcap, mem_singleton_iff] at this
      have hzx : z = x i j₁ := ms.bijV.injOn
        ((W_pre i j₁).mem_vertexSet_of_mem_support hz_pre)
        ((W_pre i j₁).mem_vertexSet_of_mem_support (W_pre i j₁).end_mem_support) hz_eq_x
      subst hzx
      have hx_C₁ : x i j₁ ∈ V(C j₁) := by
        have : x i j₁ ∈ V(P i) ∩ V(C j₁) := by
          rw [← hmid_V i j₁]; exact (W_mid i j₁).start_mem_support
        exact this.2
      exact Set.disjoint_left.mp (hC.2 hj).1 hx_C₁ hz_C₂
  have hbetween_post : ∀ (i : Fin r) {j₁ j₂ : Fin s}, j₁ < j₂ →
      ∃ R : GraphWalk G (y i j₁) (x i j₂),
        W_post i j₁ = R.append ((W_mid i j₂).append (W_post i j₂)) := by
    intro i j₁ j₂ hj
    have hx₂_mem : x i j₂ ∈ V(P i) ∩ V(C j₂) := by
      rw [← hmid_V i j₂]; exact (W_mid i j₂).start_mem_support
    have hx₂_W : x i j₂ ∈ (W i).support := by
      have h := hx₂_mem.1; rwa [hP_V i] at h
    rw [hW_split i j₁, GraphWalk.mem_support_append, GraphWalk.mem_support_append] at hx₂_W
    have hx₂_post₁ : x i j₂ ∈ (W_post i j₁).support := by
      rcases hx₂_W with h_in_pre | h_in_mid | h_in_post
      · exact (hpre_disj_inner i hj _ h_in_pre hx₂_mem.2).elim
      · exfalso
        have h_in_C₁ : x i j₂ ∈ V(C j₁) := by
          have : x i j₂ ∈ {z | z ∈ (W_mid i j₁).support} := h_in_mid
          rw [hmid_V i j₁] at this; exact this.2
        exact Set.disjoint_left.mp (hC.2 hj).1 h_in_C₁ hx₂_mem.2
      · exact h_in_post
    obtain ⟨R, S_rest, hpost_eq⟩ := (W_post i j₁).exists_append_of_mem hx₂_post₁
    have hW_eq1 := hW_split i j₂
    have hW_eq2 : W i = ((W_pre i j₁).append ((W_mid i j₁).append R)).append S_rest := by
      rw [hW_split i j₁, hpost_eq, GraphWalk.append_assoc, GraphWalk.append_assoc]
    have hS_eq : S_rest = (W_mid i j₂).append (W_post i j₂) :=
      walk_suffix_eq_of_simple_aux (hW_eq2 ▸ hW_simple i) (hW_eq2.symm.trans hW_eq1)
    exact ⟨R, hpost_eq.trans (congrArg (R.append ·) hS_eq)⟩
  exact
    { a := a, b := b, W := W, W_simple := hW_simple, a_mem := ha_mem, b_mem := hb_mem,
      P_le := hP_le, P_V := hP_V, P_E := hP_E, x := x, y := y,
      W_pre := W_pre, W_mid := W_mid, W_post := W_post,
      W_split := hW_split, mid_V := hmid_V, mid_E := hmid_E,
      x_only_pre := hx_only_pre, y_only_post := hy_only_post,
      x_zero := hx_zero, y_last := hy_last,
      C_draw := C_draw, Cd_circ := hCd_circ, Cd_sub := hCd_sub,
      Cd_V := fun j => (hCd_V j).trans ms.vertexSet_sub,
      Cd_E := fun j => (hCd_E j).trans (ms.edgeSet_sub (hC.1 j).1),
      Δ := Δ, Δ_in := hΔ_in, Δ_bd := hΔ_bd, Δ_nested := hΔ_nested,
      between_post := hbetween_post }

/-- Construct `OrderedNestedCylinderData` for any nested sequence of circuits $C_1, \dots, C_s$
($s \ge 1$) and $r \ge 1$ vertex-disjoint paths $P_1, \dots, P_r$ with $P_i \cap C_j$ a path. -/
noncomputable def buildOrderedNestedCylinderData {G : Graph α β} (M : PlanarDrawing G)
    (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (C : Fin s → Graph α β) (P : Fin r → Graph α β)
    (hC : IsNestedCircuitSeq M s C)
    (hP_disj : Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P i₁) V(P i₂)))
    (hP_path : ∀ i : Fin r, IsPathBetween G (P i)
      V(C ⟨0, hs⟩) V(C ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩))
    (hP_inter : ∀ (i : Fin r) (j : Fin s), IsGraphPath G (subgraphInter G (P i) (C j))) :
    OrderedNestedCylinderData M r s hs C P := by
  have hS : IsClosedSurface M.S := M.isClosedSurface
  have hman : ∀ z : M.S, IsManifoldPoint z := fun z => (hS.2.2 z).isManifoldPoint
  have : Nonempty α := by obtain ⟨_, u, _⟩ := hC.1 ⟨0, hs⟩; exact ⟨u⟩
  have : Nonempty β := by
    obtain ⟨_, _, W, _, hlen, _, _⟩ := hC.1 ⟨0, hs⟩
    rcases W with _ | @⟨_, _, _, e, _, _⟩
    · simp at hlen
    · exact ⟨e⟩
  let m := gmap_of_planarDrawing M
  let ms := m.symm
  let sp := buildWalkNestedSplit M r s hs C P hC hP_path hP_inter
  let toS : α → M.S := Function.invFunOn (drawingInvV M) M.drawing.V
  let toE : β → Set M.S := Function.invFunOn (drawingInvE M) M.drawing.E
  have htoS_Cd : ∀ {j : Fin s} {z : α}, z ∈ V(C j) → toS z ∈ (sp.C_draw j).V := by
    intro j z hz; rw [sp.Cd_V j]; exact mem_image_of_mem _ hz
  have htoE_Cd : ∀ {j : Fin s} {e : β}, e ∈ E(C j) → toE e ∈ (sp.C_draw j).E := by
    intro j e he; rw [sp.Cd_E j]; exact mem_image_of_mem _ he
  have hCd_toS_inv : ∀ {j : Fin s} {z : α}, z ∈ V(G) → toS z ∈ (sp.C_draw j).V → z ∈ V(C j) := by
    intro j z hzG hzS
    rw [sp.Cd_V j] at hzS
    obtain ⟨w, hwC, hw_eq⟩ := hzS
    have hinv : InvOn (invFunOn (drawingInvV M) M.drawing.V) (drawingInvV M) M.drawing.V V(G) :=
      m.bijV.invOn_invFunOn
    have h1 := congrArg (drawingInvV M) hw_eq
    dsimp [toS] at h1
    change drawingInvV M (invFunOn (drawingInvV M) M.drawing.V w) =
      drawingInvV M (invFunOn (drawingInvV M) M.drawing.V z) at h1
    rw [hinv.2 ((hC.1 j).1.vertexSet_mono hwC), hinv.2 hzG] at h1
    exact h1 ▸ hwC
  have transfer_walk : ∀ {p q : α} (U : GraphWalk G p q),
      ∃ U_d : GraphWalk M.drawing.toGraph (toS p) (toS q),
        U_d.IsSimple = U.IsSimple ∧
        U_d.support = U.support.map toS ∧
        U_d.edges = U.edges.map toE ∧
        (∀ w ∈ U_d.support, ∃ z ∈ U.support, toS z = w) := by
    intro p q U
    have h_tr : ∀ {p q : α} (U : GraphWalk G p q),
        ∃ U_d : GraphWalk M.drawing.toGraph (toS p) (toS q),
          U_d.support = U.support.map toS ∧ U_d.edges = U.edges.map toE := by
      intro p q U
      induction U with
      | nil hp => exact ⟨.nil (ms.bijV.mapsTo hp), rfl, rfl⟩
      | @cons u w q e hl r ih =>
        obtain ⟨r_d, hr_s, hr_e⟩ := ih
        have hl_d : M.drawing.toGraph.IsLink (toE e) (toS u) (toS w) := by
          have he := hl.edge_mem; have hu := hl.left_mem; have hw := hl.right_mem
          have hinvV := m.bijV.invOn_invFunOn; have hinvE := m.bijE.invOn_invFunOn
          refine (m.link (ms.bijE.mapsTo he) (ms.bijV.mapsTo hu) (ms.bijV.mapsTo hw)).mpr ?_
          dsimp [toS, toE] at *
          rwa [hinvE.2 he, hinvV.2 hu, hinvV.2 hw]
        exact ⟨.cons hl_d r_d, by simp [GraphWalk.support, hr_s], by simp [GraphWalk.edges, hr_e]⟩
    obtain ⟨U_d, hsupp, hedges⟩ := h_tr U
    have hinj_supp : U.support.Nodup ↔ U_d.support.Nodup := by
      rw [hsupp]
      refine ⟨fun hnd => hnd.map_on fun z₁ hz₁ z₂ hz₂ heq => ?_, List.Nodup.of_map toS⟩
      exact ms.bijV.injOn (U.mem_vertexSet_of_mem_support hz₁)
        (U.mem_vertexSet_of_mem_support hz₂) heq
    refine ⟨U_d, propext hinj_supp.symm, hsupp, hedges, fun w hw => ?_⟩
    rw [hsupp, List.mem_map] at hw; exact hw
  have disjoint_U_of_disjoint_V : ∀ {D₁ D₂ : Drawing M.S},
      D₁.IsSubdrawing M.drawing → D₂.IsSubdrawing M.drawing →
      Disjoint D₁.V D₂.V → Disjoint D₁.U D₂.U := by
    intro D₁ D₂ h₁ h₂ hdV
    refine Set.disjoint_left.mpr fun w hw₁ hw₂ => ?_
    by_cases hwV : w ∈ M.drawing.V
    · have hw₁V : w ∈ D₁.V := by
        by_contra hn; obtain ⟨e, he, hwe⟩ := D₁.exists_edge_of_mem hw₁ hn
        exact ((h₁.2 he).2.1 hwe).2 hwV
      have hw₂V : w ∈ D₂.V := by
        by_contra hn; obtain ⟨e, he, hwe⟩ := D₂.exists_edge_of_mem hw₂ hn
        exact ((h₂.2 he).2.1 hwe).2 hwV
      exact Set.disjoint_left.mp hdV hw₁V hw₂V
    · obtain ⟨e₁, he₁, hwe₁⟩ := D₁.exists_edge_of_mem hw₁ (fun h => hwV (h₁.1 h))
      obtain ⟨e₂, he₂, hwe₂⟩ := D₂.exists_edge_of_mem hw₂ (fun h => hwV (h₂.1 h))
      have heq : e₁ = e₂ := M.drawing.edge_eq_of_mem (h₁.2 he₁) (h₂.2 he₂) hwe₁ hwe₂
      obtain ⟨p₀, q₀, hlM⟩ := M.drawing.toGraph.exists_isLink_of_mem_edgeSet (h₁.2 he₁)
      have hl₁ := (h₁.isLink_iff he₁).mpr hlM
      have hl₂ := (h₂.isLink_iff he₂).mpr (heq ▸ hlM)
      exact Set.disjoint_left.mp hdV hl₁.left_mem hl₂.left_mem
  have hex_σ_K : ∃ (σ : Equiv.Perm (Fin r))
      (K_circ : Fin r → Fin s → Graph α β) (e_circ : Fin r → Fin s → β),
      (∀ k j, K_circ k j ≤ (C j).deleteEdges (Set.range fun m => e_circ m j)) ∧
      (∀ k j, GraphConnected (K_circ k j)) ∧
      (∀ k j, V(P (σ k)) ∩ V(C j) ⊆ V(K_circ k j)) ∧
      (∀ j {k₁ k₂ : Fin r}, k₁ ≠ k₂ → Disjoint V(K_circ k₁ j) V(K_circ k₂ j)) ∧
      (∀ j, Function.Injective (fun m => e_circ m j)) ∧
      (∀ k j, ∃ u ∈ V(K_circ k j), ∃ w ∈ V(K_circ (nextSpoke k) j),
        (C j).IsLink (e_circ k j) u w) := by
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hr) with hr2 | hr1
    · -- Case `2 ≤ r`: subdrawings `W_draw i j` of `sp.C_draw j`.
      let W_draw : Fin r → Fin s → Drawing M.S :=
        fun i j => walkDrawing M.drawing (transfer_walk (sp.W_mid i j)).choose
      have hWd_sub_M : ∀ i j, (W_draw i j).IsSubdrawing M.drawing :=
        fun _ _ => walkDrawing_isSubdrawing M.drawing _
      have hWd_sub : ∀ i j, (W_draw i j).IsSubdrawing (sp.C_draw j) := by
        intro i j
        refine ⟨fun w hw => ?_, fun e_d he_d => ?_⟩
        · rw [walkDrawing_V] at hw
          obtain ⟨z, hz, rfl⟩ := (transfer_walk (sp.W_mid i j)).choose_spec.2.2.2 w hw
          have hzC : z ∈ V(C j) := by
            have : z ∈ {v | v ∈ (sp.W_mid i j).support} := hz
            rw [sp.mid_V i j] at this; exact this.2
          exact htoS_Cd hzC
        · rw [walkDrawing_E, mem_ofPred_eq,
            (transfer_walk (sp.W_mid i j)).choose_spec.2.2.1, List.mem_map] at he_d
          obtain ⟨e, he, rfl⟩ := he_d
          have heC : e ∈ E(C j) := by
            have : e ∈ {f | f ∈ (sp.W_mid i j).edges} := he
            rw [sp.mid_E i j] at this; exact this.2
          exact htoE_Cd heC
      have hWd_conn : ∀ i j, IsPreconnected (W_draw i j).U := by
        intro i j
        have hUs : (transfer_walk (sp.W_mid i j)).choose.IsSimple :=
          (transfer_walk (sp.W_mid i j)).choose_spec.1.mpr
            (isSimple_of_append (isSimple_of_append (sp.W_split i j ▸ sp.W_simple i)).2).1
        exact GM07.isPreconnected_of_isPathBetween (walkDrawing_isPathBetween M.drawing hUs)
      have hWd_disj_V : ∀ j {i₁ i₂ : Fin r}, i₁ ≠ i₂ → Disjoint (W_draw i₁ j).V (W_draw i₂ j).V := by
        intro j i₁ i₂ hne
        refine Set.disjoint_left.mpr fun w hw₁ hw₂ => ?_
        rw [walkDrawing_V] at hw₁ hw₂
        obtain ⟨z₁, hz₁, rfl⟩ := (transfer_walk (sp.W_mid i₁ j)).choose_spec.2.2.2 w hw₁
        obtain ⟨z₂, hz₂, heq⟩ := (transfer_walk (sp.W_mid i₂ j)).choose_spec.2.2.2 _ hw₂
        have hz₁P : z₁ ∈ V(P i₁) := by
          have : z₁ ∈ {v | v ∈ (sp.W_mid i₁ j).support} := hz₁
          rw [sp.mid_V i₁ j] at this; exact this.1
        have hz₂P : z₂ ∈ V(P i₂) := by
          have : z₂ ∈ {v | v ∈ (sp.W_mid i₂ j).support} := hz₂
          rw [sp.mid_V i₂ j] at this; exact this.1
        have hz_eq : z₁ = z₂ := ms.bijV.injOn
          ((sp.P_le i₁).vertexSet_mono hz₁P) ((sp.P_le i₂).vertexSet_mono hz₂P) heq.symm
        exact Set.disjoint_left.mp (hP_disj hne) hz₁P (hz_eq ▸ hz₂P)
      have hWd_disj : ∀ j {i₁ i₂ : Fin r}, i₁ ≠ i₂ → Disjoint (W_draw i₁ j).U (W_draw i₂ j).U :=
        fun j {_ _} hne => disjoint_U_of_disjoint_V (hWd_sub_M _ j) (hWd_sub_M _ j) (hWd_disj_V j hne)
      have hx_Wd : ∀ i j, toS (sp.x i j) ∈ (W_draw i j).V := by
        intro i j
        rw [walkDrawing_V, mem_ofPred_eq, (transfer_walk (sp.W_mid i j)).choose_spec.2.1]
        exact List.mem_map_of_mem (sp.W_mid i j).start_mem_support
      have hy_Wd : ∀ i j, toS (sp.y i j) ∈ (W_draw i j).V := by
        intro i j
        rw [walkDrawing_V, mem_ofPred_eq, (transfer_walk (sp.W_mid i j)).choose_spec.2.1]
        exact List.mem_map_of_mem (sp.W_mid i j).end_mem_support
      have hex_Ad : ∃ (σ : Equiv.Perm (Fin r)),
          ∀ j : Fin s, ∃ (A_d : Fin r → Drawing M.S) (u_d w_d : Fin r → M.S),
            (∀ k, (A_d k).IsSubdrawing (sp.C_draw j) ∧
              u_d k ∈ (W_draw (σ k) j).V ∧ w_d k ∈ (W_draw (σ (nextSpoke k)) j).V ∧
              u_d k ≠ w_d k ∧ (A_d k).IsPathBetween (u_d k) (w_d k) ∧
              IsLineWithEnds (A_d k).U (u_d k) (w_d k) ∧
              (A_d k).U ∩ (⋃ i, (W_draw i j).U) = {u_d k, w_d k}) ∧
            (∀ {k₁ k₂ : Fin r}, k₁ ≠ k₂ →
              Disjoint ((A_d k₁).U \ {u_d k₁, w_d k₁}) ((A_d k₂).U \ {u_d k₂, w_d k₂})) := by
        rcases lt_or_eq_of_le (Nat.succ_le_of_lt hr2) with hr3 | hr_eq2
        · let t₀ : Fin r → M.S := fun i => toS (sp.y i ⟨0, hs⟩)
          have ht₀_mem : ∀ i, t₀ i ∈ (sp.C_draw ⟨0, hs⟩).U := fun i =>
            (hWd_sub i ⟨0, hs⟩).U_subset ((W_draw i ⟨0, hs⟩).V_subset_U (hy_Wd i ⟨0, hs⟩))
          have ht₀_inj : Function.Injective t₀ := fun i₁ i₂ heq => by
            by_contra hne
            have heq' : toS (sp.y i₁ ⟨0, hs⟩) = toS (sp.y i₂ ⟨0, hs⟩) := heq
            exact Set.disjoint_left.mp (hWd_disj_V ⟨0, hs⟩ hne)
              (hy_Wd i₁ ⟨0, hs⟩) (heq' ▸ hy_Wd i₂ ⟨0, hs⟩)
          obtain ⟨σ, B₀, τ₀, hB₀⟩ :=
            exists_circle_spoke_params (IsCircuit.isOArc_U (sp.Cd_circ ⟨0, hs⟩))
              (Nat.succ_le_of_lt hr2) ht₀_mem ht₀_inj
          refine ⟨σ, fun j => ?_⟩
          have hdisj_from_ends : ∀ (A_d : Fin r → Drawing M.S) (u_d w_d : Fin r → M.S),
              (∀ k, (A_d k).IsSubdrawing (sp.C_draw j) ∧
                u_d k ∈ (W_draw (σ k) j).V ∧ w_d k ∈ (W_draw (σ (nextSpoke k)) j).V ∧
                u_d k ≠ w_d k ∧ (A_d k).IsPathBetween (u_d k) (w_d k) ∧
                IsLineWithEnds (A_d k).U (u_d k) (w_d k) ∧
                (A_d k).U ∩ (⋃ i, (W_draw i j).U) = {u_d k, w_d k}) →
              ∀ {k₁ k₂ : Fin r}, k₁ ≠ k₂ →
                Disjoint ((A_d k₁).U \ {u_d k₁, w_d k₁}) ((A_d k₂).U \ {u_d k₂, w_d k₂}) := by
            intro A_d u_d w_d hspec k₁ k₂ hne
            refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
            obtain ⟨hA₁_sub, hu₁, hw₁, huw₁, _, hL₁, hcap₁⟩ := hspec k₁
            obtain ⟨hA₂_sub, hu₂, hw₂, huw₂, _, hL₂, hcap₂⟩ := hspec k₂
            have hz_not_W : ∀ y ∈ (A_d k₁).U \ {u_d k₁, w_d k₁}, y ∉ ⋃ i, (W_draw i j).U := by
              intro y hy hyW
              have : y ∈ (A_d k₁).U ∩ (⋃ i, (W_draw i j).U) := ⟨hy.1, hyW⟩
              rw [hcap₁] at this
              exact hy.2 this
            have hu₂_W : u_d k₂ ∈ ⋃ i, (W_draw i j).U :=
              mem_iUnion.mpr ⟨σ k₂, (W_draw _ j).V_subset_U hu₂⟩
            have hw₂_W : w_d k₂ ∈ ⋃ i, (W_draw i j).U :=
              mem_iUnion.mpr ⟨σ (nextSpoke k₂), (W_draw _ j).V_subset_U hw₂⟩
            have hdiff_sub : (A_d k₁).U \ {u_d k₁, w_d k₁} ⊆ (A_d k₂).U :=
              GM07.subset_line_or_off (IsCircuit.isOArc_U (sp.Cd_circ j)) hL₂ hA₂_sub.U_subset huw₂
                hL₁.isPreconnected_diff (sdiff_subset.trans hA₁_sub.U_subset)
                (fun h => hz_not_W _ h hu₂_W) (fun h => hz_not_W _ h hw₂_W) hz₁ hz₂.1
            have hU₁_sub : (A_d k₁).U ⊆ (A_d k₂).U :=
              hL₁.subset_closure_diff.trans (closure_minimal hdiff_sub hL₂.isCompact.isClosed)
            have hu₁_in : u_d k₁ ∈ ({u_d k₂, w_d k₂} : Set M.S) := by
              rw [← hcap₂]
              exact ⟨hU₁_sub hL₁.left_mem, mem_iUnion.mpr ⟨σ k₁, (W_draw _ j).V_subset_U hu₁⟩⟩
            have hw₁_in : w_d k₁ ∈ ({u_d k₂, w_d k₂} : Set M.S) := by
              rw [← hcap₂]
              exact ⟨hU₁_sub hL₁.right_mem, mem_iUnion.mpr ⟨σ (nextSpoke k₁), (W_draw _ j).V_subset_U hw₁⟩⟩
            have hpair_σ : ({σ k₁, σ (nextSpoke k₁)} : Set (Fin r)) = {σ k₂, σ (nextSpoke k₂)} := by
              have idx_eq : ∀ {p q : Fin r} {a b : M.S}, a ∈ (W_draw p j).V → b ∈ (W_draw q j).V →
                  a = b → p = q := by
                intro p q a b ha hb hab
                by_contra hpq
                exact Set.disjoint_left.mp (hWd_disj_V j hpq) ha (hab ▸ hb)
              have h_sub1 : ({σ k₁, σ (nextSpoke k₁)} : Set (Fin r)) ⊆ {σ k₂, σ (nextSpoke k₂)} := by
                rintro _ (rfl | rfl)
                · rcases hu₁_in with h | h
                  · exact Or.inl (idx_eq hu₁ hu₂ h)
                  · exact Or.inr (idx_eq hu₁ hw₂ h)
                · rcases hw₁_in with h | h
                  · exact Or.inl (idx_eq hw₁ hu₂ h)
                  · exact Or.inr (idx_eq hw₁ hw₂ h)
              ext m
              refine ⟨fun hm => h_sub1 hm, fun hm => ?_⟩
              rcases hm with rfl | rfl
              · by_contra hnot
                rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
                rcases hu₁_in with h1 | h1 <;> rcases hw₁_in with h2 | h2
                · exact hnot.1 (idx_eq hu₁ hu₂ h1).symm
                · exact hnot.1 (idx_eq hu₁ hu₂ h1).symm
                · exact hnot.2 (idx_eq hw₁ hu₂ h2).symm
                · exact huw₁ (h1.trans h2.symm)
              · by_contra hnot
                rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hnot
                rcases hu₁_in with h1 | h1 <;> rcases hw₁_in with h2 | h2
                · exact huw₁ (h1.trans h2.symm)
                · exact hnot.2 (idx_eq hw₁ hw₂ h2).symm
                · exact hnot.1 (idx_eq hu₁ hw₂ h1).symm
                · exact hnot.1 (idx_eq hu₁ hw₂ h1).symm
            have hpair_k : ({k₁, nextSpoke k₁} : Set (Fin r)) = {k₂, nextSpoke k₂} := by
              ext m
              constructor <;> intro hm
              · have : σ m ∈ ({σ k₁, σ (nextSpoke k₁)} : Set (Fin r)) := by
                  rcases hm with rfl | rfl <;> simp
                rw [hpair_σ] at this
                rcases this with h | h
                · exact Or.inl (σ.injective h)
                · exact Or.inr (σ.injective h)
              · have : σ m ∈ ({σ k₂, σ (nextSpoke k₂)} : Set (Fin r)) := by
                  rcases hm with rfl | rfl <;> simp
                rw [← hpair_σ] at this
                rcases this with h | h
                · exact Or.inl (σ.injective h)
                · exact Or.inr (σ.injective h)
            exact hne (nextSpoke_pair_inj (Nat.succ_le_of_lt hr3) hpair_k)
          by_cases hj0 : j.1 = 0
          · have hjeq : j = ⟨0, hs⟩ := Fin.ext hj0
            subst hjeq
            have hex_k : ∀ k : Fin r, ∃ (A : Drawing M.S) (u w : M.S),
                A.IsSubdrawing (sp.C_draw ⟨0, hs⟩) ∧
                u ∈ (W_draw (σ k) ⟨0, hs⟩).V ∧ w ∈ (W_draw (σ (nextSpoke k)) ⟨0, hs⟩).V ∧
                u ≠ w ∧ A.IsPathBetween u w ∧ IsLineWithEnds A.U u w ∧
                A.U ∩ (⋃ i, (W_draw i ⟨0, hs⟩).U) = {u, w} := by
              intro k
              have hk_ne : σ k ≠ σ (nextSpoke k) := by
                refine σ.injective.ne fun hk_eq => ?_
                have hv := congrArg Fin.val hk_eq; dsimp [nextSpoke] at hv
                by_cases hklt : k.1 + 1 < r
                · rw [Nat.mod_eq_of_lt hklt] at hv; omega
                · have hkr : k.1 + 1 = r := by have := k.2; omega
                  rw [hkr, Nat.mod_self] at hv; omega
              obtain ⟨A, u, w, h1, h2, h3, h4, h5, h6, _, h8⟩ :=
                exists_spoke_arc_subdrawing (sp.Cd_circ ⟨0, hs⟩)
                  (fun i => hWd_sub i ⟨0, hs⟩) (fun i => hWd_conn i ⟨0, hs⟩)
                  (fun _ _ hne => hWd_disj ⟨0, hs⟩ hne) (fun i => hy_Wd i ⟨0, hs⟩)
                  hk_ne (hB₀ k).1 (hB₀ k).2.1 (hB₀ k).2.2
              exact ⟨A, u, w, h1, h2, h3, h4, h5, h6, h8⟩
            choose A_d u_d w_d hAd using hex_k
            exact ⟨A_d, u_d, w_d, hAd, hdisj_from_ends A_d u_d w_d hAd⟩
          · have h0j : (⟨0, hs⟩ : Fin s) < j := Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero hj0)
            let x_j : Fin r → M.S := fun i => toS (sp.x i j)
            choose R_0j hR_0j_eq using fun i => sp.between_post i h0j
            let q_d : Fin r → Set M.S :=
              fun i => (walkDrawing M.drawing (transfer_walk (R_0j i).reverse).choose).U
            have hq_cross : ∀ i : Fin r, GM07.IsCrossLine (sp.Δ j) (sp.Δ ⟨0, hs⟩) (q_d i) (x_j i) (t₀ i) := by
              intro i
              have hpost0_s : (sp.W_post i ⟨0, hs⟩).IsSimple :=
                (isSimple_of_append (isSimple_of_append (sp.W_split i ⟨0, hs⟩ ▸ sp.W_simple i)).2).2
              have hRs : (R_0j i).IsSimple :=
                (isSimple_of_append (hR_0j_eq i ▸ hpost0_s)).1
              let U_rev := (transfer_walk (R_0j i).reverse).choose
              have hU_rev_s_eq := (transfer_walk (R_0j i).reverse).choose_spec.1
              have hU_rev_supp := (transfer_walk (R_0j i).reverse).choose_spec.2.1
              have hU_rev_mem := (transfer_walk (R_0j i).reverse).choose_spec.2.2.2
              have hU_rev_s : U_rev.IsSimple := hU_rev_s_eq.mpr hRs.reverse
              have hxt_ne : x_j i ≠ t₀ i := by
                intro heq
                have hx_in : x_j i ∈ sp.Δ j :=
                  Surface.discBd_subset (sp.Δ j) (sp.Δ_bd j ▸ (sp.C_draw j).V_subset_U (htoS_Cd (by
                    have : sp.x i j ∈ V(P i) ∩ V(C j) := by
                      rw [← sp.mid_V i j]; exact (sp.W_mid i j).start_mem_support
                    exact this.2)))
                have ht_bd : t₀ i ∈ discBd (sp.Δ ⟨0, hs⟩) := sp.Δ_bd ⟨0, hs⟩ ▸ ht₀_mem i
                exact (sp.Δ_nested h0j hx_in).2 (heq ▸ ht_bd)
              have hline : IsLineWithEnds (q_d i) (x_j i) (t₀ i) :=
                GM14.isLine_of_isPathBetween (walkDrawing_isPathBetween M.drawing hU_rev_s) hxt_ne
              have hx_int0 : x_j i ∈ discInt (sp.Δ ⟨0, hs⟩) := by
                have hx_in : x_j i ∈ sp.Δ j :=
                  Surface.discBd_subset (sp.Δ j) (sp.Δ_bd j ▸ (sp.C_draw j).V_subset_U (htoS_Cd (by
                    have : sp.x i j ∈ V(P i) ∩ V(C j) := by
                      rw [← sp.mid_V i j]; exact (sp.W_mid i j).start_mem_support
                    exact this.2)))
                exact sp.Δ_nested h0j hx_in
              have honly_0 : ∀ w ∈ U_rev.support, w ∈ (sp.C_draw ⟨0, hs⟩).V → w = t₀ i := by
                intro w hw hwC0
                obtain ⟨z₀, hz₀_rev, rfl⟩ := hU_rev_mem w hw
                rw [GraphWalk.support_reverse, List.mem_reverse] at hz₀_rev
                have hz₀_post : z₀ ∈ (sp.W_post i ⟨0, hs⟩).support := by
                  rw [hR_0j_eq i, GraphWalk.mem_support_append]; exact Or.inl hz₀_rev
                have hz₀_C0 : z₀ ∈ V(C ⟨0, hs⟩) :=
                  hCd_toS_inv ((sp.W_post i ⟨0, hs⟩).mem_vertexSet_of_mem_support hz₀_post) hwC0
                exact congrArg toS (sp.y_only_post i ⟨0, hs⟩ hz₀_post hz₀_C0)
              obtain ⟨hsub0, htop0⟩ := walkDrawing_inside_disc_except_end hS (sp.Cd_sub ⟨0, hs⟩)
                (sp.Δ_in ⟨0, hs⟩).1 (sp.Δ_bd ⟨0, hs⟩) U_rev hU_rev_s hx_int0
                (htoS_Cd (by
                  have : sp.y i ⟨0, hs⟩ ∈ V(P i) ∩ V(C ⟨0, hs⟩) := by
                    rw [← sp.mid_V i ⟨0, hs⟩]; exact (sp.W_mid i ⟨0, hs⟩).end_mem_support
                  exact this.2)) honly_0
              obtain ⟨U_fwd, hU_fwd_s_eq, hU_fwd_supp, hU_fwd_edges, hU_fwd_mem⟩ :=
                transfer_walk (R_0j i)
              have hU_fwd_s : U_fwd.IsSimple := hU_fwd_s_eq.mpr hRs
              have hU_fwd_eq : (walkDrawing M.drawing U_fwd).U = q_d i := by
                have hrev_eq : U_fwd.reverse = U_rev := by
                  apply graphWalk_eq_of_support_edges
                  · rw [GraphWalk.support_reverse, hU_rev_supp, hU_fwd_supp,
                      GraphWalk.support_reverse, List.map_reverse]
                  · rw [GraphWalk.edges_reverse,
                      (transfer_walk (R_0j i).reverse).choose_spec.2.2.1,
                      hU_fwd_edges, GraphWalk.edges_reverse, List.map_reverse]
                rw [← walkDrawing_reverse, hrev_eq]
              have ht_out_j : t₀ i ∉ sp.Δ j :=
                fun ht_in => (sp.Δ_nested h0j ht_in).2 (sp.Δ_bd ⟨0, hs⟩ ▸ ht₀_mem i)
              have honly_j : ∀ w ∈ U_fwd.support, w ∈ (sp.C_draw j).V → w = x_j i := by
                intro w hw hwCj
                obtain ⟨z₀, hz₀_fwd, rfl⟩ := hU_fwd_mem w hw
                have hz₀_pre : z₀ ∈ (sp.W_pre i j).support := by
                  have hW_eq1 := sp.W_split i j
                  have hW_eq2 : sp.W i = ((sp.W_pre i ⟨0, hs⟩).append
                      ((sp.W_mid i ⟨0, hs⟩).append (R_0j i))).append
                      ((sp.W_mid i j).append (sp.W_post i j)) := by
                    rw [sp.W_split i ⟨0, hs⟩, hR_0j_eq i,
                      GraphWalk.append_assoc, GraphWalk.append_assoc]
                  have hboth :
                      (sp.W_pre i j).support ++ ((sp.W_mid i j).append (sp.W_post i j)).support.tail =
                        ((sp.W_pre i ⟨0, hs⟩).append ((sp.W_mid i ⟨0, hs⟩).append (R_0j i))).support ++
                          ((sp.W_mid i j).append (sp.W_post i j)).support.tail := by
                    rw [← GraphWalk.support_append, ← GraphWalk.support_append,
                      ← hW_eq1, ← hW_eq2]
                  have hpre_supp := List.append_inj_left' hboth rfl
                  rw [hpre_supp, GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                  exact Or.inr (Or.inr hz₀_fwd)
                have hz₀_Cj : z₀ ∈ V(C j) :=
                  hCd_toS_inv ((sp.W_pre i j).mem_vertexSet_of_mem_support hz₀_pre) hwCj
                exact congrArg toS (sp.x_only_pre i j hz₀_pre hz₀_Cj)
              have hbot_j := walkDrawing_outside_disc_except_end hS (sp.Cd_sub j)
                (sp.Δ_in j).1 (sp.Δ_bd j) U_fwd hU_fwd_s ht_out_j
                (htoS_Cd (by
                  have : sp.x i j ∈ V(P i) ∩ V(C j) := by
                    rw [← sp.mid_V i j]; exact (sp.W_mid i j).start_mem_support
                  exact this.2)) honly_j
              rw [hU_fwd_eq] at hbot_j
              refine ⟨hline, hsub0, hbot_j, htop0, ?_⟩
              rw [sp.Δ_bd j]
              exact (hWd_sub i j).U_subset ((W_draw i j).V_subset_U (hx_Wd i j))
            have hq_disj : ∀ i₁ i₂ : Fin r, i₁ ≠ i₂ → Disjoint (q_d i₁) (q_d i₂) := by
              intro i₁ i₂ hne
              refine disjoint_U_of_disjoint_V (walkDrawing_isSubdrawing M.drawing _)
                (walkDrawing_isSubdrawing M.drawing _) ?_
              refine Set.disjoint_left.mpr fun w hw₁ hw₂ => ?_
              rw [walkDrawing_V] at hw₁ hw₂
              obtain ⟨z₁, hz₁, rfl⟩ := (transfer_walk (R_0j i₁).reverse).choose_spec.2.2.2 w hw₁
              obtain ⟨z₂, hz₂, heq⟩ := (transfer_walk (R_0j i₂).reverse).choose_spec.2.2.2 _ hw₂
              rw [GraphWalk.support_reverse, List.mem_reverse] at hz₁ hz₂
              have hz₁P : z₁ ∈ V(P i₁) := by
                rw [sp.P_V i₁, mem_ofPred_eq, sp.W_split i₁ ⟨0, hs⟩, hR_0j_eq i₁]
                simp [GraphWalk.mem_support_append, hz₁]
              have hz₂P : z₂ ∈ V(P i₂) := by
                rw [sp.P_V i₂, mem_ofPred_eq, sp.W_split i₂ ⟨0, hs⟩, hR_0j_eq i₂]
                simp [GraphWalk.mem_support_append, hz₂]
              have hz_eq := ms.bijV.injOn
                ((sp.P_le i₁).vertexSet_mono hz₁P) ((sp.P_le i₂).vertexSet_mono hz₂P) heq.symm
              exact Set.disjoint_left.mp (hP_disj hne) hz₁P (hz_eq ▸ hz₂P)
            have hi01 : (⟨0, hr⟩ : Fin r) ≠ ⟨1, by omega⟩ := by intro h; cases h
            obtain ⟨F, hF⟩ := GM07.exists_cell_family hman (sp.Δ_in j).1 (sp.Δ_in ⟨0, hs⟩).1
              (sp.Δ_nested h0j) hq_cross hq_disj hi01
            have hex_k : ∀ k : Fin r, ∃ (A : Drawing M.S) (u w : M.S),
                A.IsSubdrawing (sp.C_draw j) ∧
                u ∈ (W_draw (σ k) j).V ∧ w ∈ (W_draw (σ (nextSpoke k)) j).V ∧
                u ≠ w ∧ A.IsPathBetween u w ∧ IsLineWithEnds A.U u w ∧
                A.U ∩ (⋃ i, (W_draw i j).U) = {u, w} := by
              intro k
              have hk_ne : σ k ≠ σ (nextSpoke k) := by
                refine σ.injective.ne fun hk_eq => ?_
                have hv := congrArg Fin.val hk_eq; dsimp [nextSpoke] at hv
                by_cases hklt : k.1 + 1 < r
                · rw [Nat.mod_eq_of_lt hklt] at hv; omega
                · have hkr : k.1 + 1 = r := by have := k.2; omega
                  rw [hkr, Nat.mod_self] at hv; omega
              obtain ⟨z₀, hz₀⟩ := GM07.exists_mem_diff_of_line (hB₀ k).1.isLine
              have hz₀_bd : z₀ ∈ discBd (sp.Δ ⟨0, hs⟩) :=
                (sp.Δ_bd ⟨0, hs⟩).symm ▸ (hB₀ k).2.1 hz₀.1
              obtain ⟨c, hcF, hz₀_cb⟩ := hF.topCover z₀ hz₀_bd
              have hcell := hF.cell c hcF
              have hci_ne : c.i ≠ c.i' := fun heq =>
                Set.disjoint_left.mp hcell.ll (hq_cross c.i).line.left_mem
                  (heq ▸ (hq_cross c.i').line.left_mem)
              have hcb_off : ∀ i : Fin r, i ≠ c.i → i ≠ c.i' → t₀ i ∉ c.b := by
                intro i hi1 hi2 ht_in
                obtain ⟨c', hc'F, hc'_side⟩ := hF.used i (mem_univ i)
                have hc_ne : c ≠ c' := by
                  rintro rfl
                  rcases hc'_side with rfl | rfl
                  · exact hi1 rfl
                  · exact hi2 rfl
                have ht_c' : t₀ i ∈ c'.R := by
                  have hcell' := hF.cell c' hc'F
                  rcases hc'_side with rfl | rfl
                  · exact Surface.discBd_subset _ (hcell'.l_sub hcell'.left.right_mem)
                  · exact Surface.discBd_subset _ (hcell'.r_sub hcell'.right.right_mem)
                obtain ⟨m₀, hm₀_c, _, ht_qm⟩ := hF.meet c hcF c' hc'F hc_ne (t₀ i)
                  (Surface.discBd_subset _ (hcell.b_sub ht_in)) ht_c'
                have hm₀_ne : i ≠ m₀ := by
                  rcases hm₀_c with rfl | rfl
                  · exact hi1
                  · exact hi2
                exact Set.disjoint_left.mp (hq_disj i m₀ hm₀_ne) (hq_cross i).line.right_mem ht_qm
              have hca_off : ∀ i : Fin r, i ≠ c.i → i ≠ c.i' → x_j i ∉ c.a := by
                intro i hi1 hi2 hx_in
                obtain ⟨c', hc'F, hc'_side⟩ := hF.used i (mem_univ i)
                have hc_ne : c ≠ c' := by
                  rintro rfl
                  rcases hc'_side with rfl | rfl
                  · exact hi1 rfl
                  · exact hi2 rfl
                have hx_c' : x_j i ∈ c'.R := by
                  have hcell' := hF.cell c' hc'F
                  rcases hc'_side with rfl | rfl
                  · exact Surface.discBd_subset _ (hcell'.l_sub hcell'.left.left_mem)
                  · exact Surface.discBd_subset _ (hcell'.r_sub hcell'.right.left_mem)
                obtain ⟨m₀, hm₀_c, _, hx_qm⟩ := hF.meet c hcF c' hc'F hc_ne (x_j i)
                  (Surface.discBd_subset _ (hcell.a_sub hx_in)) hx_c'
                have hm₀_ne : i ≠ m₀ := by
                  rcases hm₀_c with rfl | rfl
                  · exact hi1
                  · exact hi2
                exact Set.disjoint_left.mp (hq_disj i m₀ hm₀_ne) (hq_cross i).line.left_mem hx_qm
              have hz_not_t₀ : ∀ y ∈ B₀ k \ {t₀ (σ k), t₀ (σ (nextSpoke k))}, ∀ i : Fin r, y ≠ t₀ i := by
                rintro y ⟨hyB, hy_ends⟩ i rfl
                by_cases h1 : i = σ k
                · exact hy_ends (Or.inl (congrArg t₀ h1))
                · by_cases h2 : i = σ (nextSpoke k)
                  · exact hy_ends (Or.inr (congrArg t₀ h2))
                  · exact (hB₀ k).2.2 i h1 h2 hyB
              have hcb_sub_U0 : c.b ⊆ (sp.C_draw ⟨0, hs⟩).U := by
                rw [← sp.Δ_bd ⟨0, hs⟩]
                exact fun y hy => (hcell.topCap ▸ hy).2
              have hBk_diff_sub : B₀ k \ {t₀ (σ k), t₀ (σ (nextSpoke k))} ⊆ c.b :=
                GM07.subset_line_or_off (IsCircuit.isOArc_U (sp.Cd_circ ⟨0, hs⟩))
                  hcell.top hcb_sub_U0 (ht₀_inj.ne hci_ne)
                  (hB₀ k).1.isLine.isPreconnected_diff (sdiff_subset.trans (hB₀ k).2.1)
                  (fun h => hz_not_t₀ _ h c.i rfl) (fun h => hz_not_t₀ _ h c.i' rfl) hz₀ hz₀_cb
              have hBk_sub_cb : B₀ k ⊆ c.b :=
                (hB₀ k).1.isLine.subset_closure_diff.trans
                  (closure_minimal hBk_diff_sub hcell.top.isCompact.isClosed)
              have hσk_mem : σ k = c.i ∨ σ k = c.i' := by
                by_contra hnot; push Not at hnot
                exact hcb_off (σ k) hnot.1 hnot.2 (hBk_sub_cb (hB₀ k).1.isLine.left_mem)
              have hσnk_mem : σ (nextSpoke k) = c.i ∨ σ (nextSpoke k) = c.i' := by
                by_contra hnot; push Not at hnot
                exact hcb_off (σ (nextSpoke k)) hnot.1 hnot.2 (hBk_sub_cb (hB₀ k).1.isLine.right_mem)
              have hca_line : IsLineWithEnds c.a (x_j (σ k)) (x_j (σ (nextSpoke k))) ∧
                  (∀ i : Fin r, i ≠ σ k → i ≠ σ (nextSpoke k) → x_j i ∉ c.a) := by
                rcases hσk_mem with h1 | h1 <;> rcases hσnk_mem with h2 | h2
                · exact (hk_ne (h1.trans h2.symm)).elim
                · exact ⟨h1 ▸ h2 ▸ hcell.bottom, fun i hi1 hi2 => hca_off i (h1 ▸ hi1) (h2 ▸ hi2)⟩
                · exact ⟨h1 ▸ h2 ▸ hcell.bottom.symm, fun i hi1 hi2 => hca_off i (h2 ▸ hi2) (h1 ▸ hi1)⟩
                · exact (hk_ne (h1.trans h2.symm)).elim
              obtain ⟨τ_ca, hτ_ca⟩ := GM07.exists_isParam hca_line.1
              have hca_sub_Uj : c.a ⊆ (sp.C_draw j).U := by
                rw [← sp.Δ_bd j]; exact hcell.aBd
              obtain ⟨A, u, w, h1, h2, h3, h4, h5, h6, _, h8⟩ :=
                exists_spoke_arc_subdrawing (sp.Cd_circ j)
                  (fun i => hWd_sub i j) (fun i => hWd_conn i j)
                  (fun _ _ hne => hWd_disj j hne) (fun i => hx_Wd i j)
                  hk_ne hτ_ca hca_sub_Uj hca_line.2
              exact ⟨A, u, w, h1, h2, h3, h4, h5, h6, h8⟩
            choose A_d u_d w_d hAd using hex_k
            exact ⟨A_d, u_d, w_d, hAd, hdisj_from_ends A_d u_d w_d hAd⟩
        · -- `r = 2`: `(IsOArc).lines` splits `(sp.C_draw j).U` into `L₀, L₁` meeting only at `{t_j 0, t_j 1}`.
          cases hr_eq2
          refine ⟨Equiv.refl (Fin 2), fun j => ?_⟩
          let i₀ : Fin 2 := ⟨0, by decide⟩
          let i₁ : Fin 2 := ⟨1, by decide⟩
          have hi01 : i₀ ≠ i₁ := by decide
          let t_j : Fin 2 → M.S := fun i => toS (sp.x i j)
          have ht_U : ∀ i, t_j i ∈ (sp.C_draw j).U := fun i =>
            (hWd_sub i j).U_subset ((W_draw i j).V_subset_U (hx_Wd i j))
          have ht01_ne : t_j i₀ ≠ t_j i₁ := fun heq => by
            have heq' : toS (sp.x i₀ j) = toS (sp.x i₁ j) := heq
            exact Set.disjoint_left.mp (hWd_disj_V j hi01) (hx_Wd i₀ j) (heq' ▸ hx_Wd i₁ j)
          obtain ⟨L₀, L₁, hL₀, hL₁, hL_union, hL_cap⟩ :=
            (IsCircuit.isOArc_U (sp.Cd_circ j)).lines (ht_U i₀) (ht_U i₁) ht01_ne
          obtain ⟨τ₀, hτ₀⟩ := GM07.exists_isParam hL₀
          obtain ⟨τ₁, hτ₁⟩ := GM07.exists_isParam hL₁.symm
          have hoff0 : ∀ i : Fin 2, i ≠ i₀ → i ≠ i₁ → t_j i ∉ L₀ := by
            intro i h0 h1; fin_cases i
            · exact (h0 rfl).elim
            · exact (h1 rfl).elim
          have hoff1 : ∀ i : Fin 2, i ≠ i₁ → i ≠ i₀ → t_j i ∉ L₁ := by
            intro i h1 h0; fin_cases i
            · exact (h0 rfl).elim
            · exact (h1 rfl).elim
          obtain ⟨A₀, u₀, w₀, hA₀_sub, hu₀, hw₀, huw₀, hA₀_p, hA₀_l, hA₀_L, hA₀_cap⟩ :=
            exists_spoke_arc_subdrawing (sp.Cd_circ j)
              (fun i => hWd_sub i j) (fun i => hWd_conn i j)
              (fun _ _ hne => hWd_disj j hne) (fun i => hx_Wd i j)
              hi01 hτ₀ (subset_union_left.trans_eq hL_union) hoff0
          obtain ⟨A₁, u₁, w₁, hA₁_sub, hu₁, hw₁, huw₁, hA₁_p, hA₁_l, hA₁_L, hA₁_cap⟩ :=
            exists_spoke_arc_subdrawing (sp.Cd_circ j)
              (fun i => hWd_sub i j) (fun i => hWd_conn i j)
              (fun _ _ hne => hWd_disj j hne) (fun i => hx_Wd i j)
              hi01.symm hτ₁ (subset_union_right.trans_eq hL_union) hoff1
          let A_d : Fin 2 → Drawing M.S := fun k => if k = i₀ then A₀ else A₁
          let u_d : Fin 2 → M.S := fun k => if k = i₀ then u₀ else u₁
          let w_d : Fin 2 → M.S := fun k => if k = i₀ then w₀ else w₁
          have hdisj01 : Disjoint (A₀.U \ {u₀, w₀}) (A₁.U \ {u₁, w₁}) := by
            refine Set.disjoint_left.mpr fun z hz₀ hz₁ => ?_
            have hz_cap : z ∈ L₀ ∩ L₁ := ⟨hA₀_L hz₀.1, hA₁_L hz₁.1⟩
            rw [hL_cap] at hz_cap
            have hz_W : z ∈ ⋃ i, (W_draw i j).U := by
              rcases hz_cap with rfl | rfl
              · exact mem_iUnion.mpr ⟨i₀, (W_draw i₀ j).V_subset_U (hx_Wd i₀ j)⟩
              · exact mem_iUnion.mpr ⟨i₁, (W_draw i₁ j).V_subset_U (hx_Wd i₁ j)⟩
            have hz_ends : z ∈ ({u₀, w₀} : Set M.S) := by
              rw [← hA₀_cap]; exact ⟨hz₀.1, hz_W⟩
            exact hz₀.2 hz_ends
          refine ⟨A_d, u_d, w_d, fun k => ?_, fun {k₁ k₂} hne => ?_⟩
          · fin_cases k
            · have hn0 : nextSpoke i₀ = i₁ := by decide
              change A₀.IsSubdrawing (sp.C_draw j) ∧ u₀ ∈ (W_draw i₀ j).V ∧
                w₀ ∈ (W_draw (nextSpoke i₀) j).V ∧ u₀ ≠ w₀ ∧ A₀.IsPathBetween u₀ w₀ ∧
                IsLineWithEnds A₀.U u₀ w₀ ∧ A₀.U ∩ (⋃ i, (W_draw i j).U) = {u₀, w₀}
              rw [hn0]
              exact ⟨hA₀_sub, hu₀, hw₀, huw₀, hA₀_p, hA₀_l, hA₀_cap⟩
            · have hn1 : nextSpoke i₁ = i₀ := by decide
              have hA1 : A_d i₁ = A₁ := by dsimp only [A_d]; simp only [hi01.symm, ↓reduceIte]
              have hu1 : u_d i₁ = u₁ := by dsimp only [u_d]; simp only [hi01.symm, ↓reduceIte]
              have hw1 : w_d i₁ = w₁ := by dsimp only [w_d]; simp only [hi01.symm, ↓reduceIte]
              change (A_d i₁).IsSubdrawing (sp.C_draw j) ∧ u_d i₁ ∈ (W_draw i₁ j).V ∧
                w_d i₁ ∈ (W_draw (nextSpoke i₁) j).V ∧ u_d i₁ ≠ w_d i₁ ∧
                (A_d i₁).IsPathBetween (u_d i₁) (w_d i₁) ∧
                IsLineWithEnds (A_d i₁).U (u_d i₁) (w_d i₁) ∧
                (A_d i₁).U ∩ (⋃ i, (W_draw i j).U) = {u_d i₁, w_d i₁}
              rw [hA1, hu1, hw1, hn1]
              exact ⟨hA₁_sub, hu₁, hw₁, huw₁, hA₁_p, hA₁_l, hA₁_cap⟩
          · fin_cases k₁ <;> fin_cases k₂
            · exact (hne rfl).elim
            · exact hdisj01
            · exact hdisj01.symm
            · exact (hne rfl).elim
      -- Pull `A_d j k` back to simple walks `L_G j k` in `C j`, peel first edge `e_circ k j`,
      -- and form `K_circ k j`.
      obtain ⟨σ, hAd_all⟩ := hex_Ad
      choose A_d u_d w_d hAd_spec hAd_disj using hAd_all
      have hCd_invV : ∀ {j : Fin s} {p_d : M.S}, p_d ∈ (sp.C_draw j).V →
          drawingInvV M p_d ∈ V(C j) ∧ toS (drawingInvV M p_d) = p_d := by
        intro j p_d hp_d
        rw [sp.Cd_V j] at hp_d
        obtain ⟨z, hzC, rfl⟩ := hp_d
        have hinv := m.bijV.invOn_invFunOn.2 ((hC.1 j).1.vertexSet_mono hzC)
        exact ⟨hinv.symm ▸ hzC, congrArg toS hinv⟩
      have hCd_invE : ∀ {j : Fin s} {f_d : Set M.S}, f_d ∈ (sp.C_draw j).E →
          drawingInvE M f_d ∈ E(C j) ∧ toE (drawingInvE M f_d) = f_d := by
        intro j f_d hf_d
        rw [sp.Cd_E j] at hf_d
        obtain ⟨e, heC, rfl⟩ := hf_d
        have hinv := m.bijE.invOn_invFunOn.2 ((hC.1 j).1.edgeSet_mono heC)
        exact ⟨hinv.symm ▸ heC, congrArg toE hinv⟩
      have pullback_walk : ∀ (j : Fin s) {D : Drawing M.S} (hD : D.IsSubdrawing (sp.C_draw j))
          {p_d q_d : M.S} (L_d : GraphWalk D.toGraph p_d q_d),
          ∃ L_G : GraphWalk (C j) (drawingInvV M p_d) (drawingInvV M q_d),
            L_d.support = L_G.support.map toS ∧
            L_d.edges = L_G.edges.map toE ∧
            L_G.IsSimple = L_d.IsSimple := by
        intro j D hD p_d q_d L_d
        have h_pb : ∀ {p_d q_d : M.S} (L_d : GraphWalk D.toGraph p_d q_d),
            ∃ L_G : GraphWalk (C j) (drawingInvV M p_d) (drawingInvV M q_d),
              L_d.support = L_G.support.map toS ∧ L_d.edges = L_G.edges.map toE := by
          intro p_d q_d L_d
          induction L_d with
          | nil hp =>
            exact ⟨.nil (hCd_invV (hD.1 hp)).1,
              by simp [GraphWalk.support, (hCd_invV (hD.1 hp)).2], rfl⟩
          | @cons a_d b_d c_d f_d hl_d r_d ih =>
            obtain ⟨r_G, hrs, hre⟩ := ih
            have hl_Cd : (sp.C_draw j).toGraph.IsLink f_d a_d b_d :=
              hl_d.mono (toGraph_le_of_isSubdrawing' hD)
            have hl_M : M.drawing.toGraph.IsLink f_d a_d b_d :=
              hl_Cd.mono (toGraph_le_of_isSubdrawing' (sp.Cd_sub j))
            have hl_G : G.IsLink (drawingInvE M f_d) (drawingInvV M a_d) (drawingInvV M b_d) :=
              (m.link hl_M.edge_mem hl_M.left_mem hl_M.right_mem).mp hl_M
            have hl_Cj : (C j).IsLink (drawingInvE M f_d) (drawingInvV M a_d) (drawingInvV M b_d) :=
              ((hC.1 j).1.isLink_iff (hCd_invE hl_Cd.edge_mem).1).mpr hl_G
            exact ⟨.cons hl_Cj r_G,
              by simp [GraphWalk.support, hrs, (hCd_invV hl_Cd.left_mem).2],
              by simp [GraphWalk.edges, hre, (hCd_invE hl_Cd.edge_mem).2]⟩
        obtain ⟨L_G, hsupp, hedges⟩ := h_pb L_d
        have hnd_iff : L_G.support.Nodup ↔ L_d.support.Nodup := by
          rw [hsupp]
          refine ⟨fun hnd => hnd.map_on fun z₁ hz₁ z₂ hz₂ heq => ?_, List.Nodup.of_map toS⟩
          exact ms.bijV.injOn
            ((hC.1 j).1.vertexSet_mono (L_G.mem_vertexSet_of_mem_support hz₁))
            ((hC.1 j).1.vertexSet_mono (L_G.mem_vertexSet_of_mem_support hz₂)) heq
        exact ⟨L_G, hsupp, hedges, propext hnd_iff⟩
      have hex_LG : ∀ (j : Fin s) (k : Fin r),
          ∃ (u_G z_G w_G : α) (e₀ : β) (hl₀ : (C j).IsLink e₀ u_G z_G)
            (L_rest : GraphWalk (C j) z_G w_G),
            toS u_G = u_d j k ∧ toS w_G = w_d j k ∧
            u_G ∈ V(P (σ k)) ∩ V(C j) ∧ w_G ∈ V(P (σ (nextSpoke k))) ∩ V(C j) ∧
            (GraphWalk.cons hl₀ L_rest).IsSimple ∧
            (A_d j k).V = {p | p ∈ ((GraphWalk.cons hl₀ L_rest).support.map toS)} ∧
            (A_d j k).E = {f | f ∈ ((GraphWalk.cons hl₀ L_rest).edges.map toE)} := by
        intro j k
        obtain ⟨hA_sub, hu_Wd, hw_Wd, huw_ne, ⟨L_d, hLd_s, hAd_V, hAd_E⟩, _, _⟩ := hAd_spec j k
        obtain ⟨L_G, hsupp, hedges, hLG_s_eq⟩ := pullback_walk j hA_sub L_d
        have hLG_s : L_G.IsSimple := hLG_s_eq.mpr hLd_s
        have hu_d_Cd : u_d j k ∈ (sp.C_draw j).V := hA_sub.1 (by rw [hAd_V]; exact L_d.start_mem_support)
        have hw_d_Cd : w_d j k ∈ (sp.C_draw j).V := hA_sub.1 (by rw [hAd_V]; exact L_d.end_mem_support)
        have hu_toS : toS (drawingInvV M (u_d j k)) = u_d j k := (hCd_invV hu_d_Cd).2
        have hw_toS : toS (drawingInvV M (w_d j k)) = w_d j k := (hCd_invV hw_d_Cd).2
        have hu_PC : drawingInvV M (u_d j k) ∈ V(P (σ k)) ∩ V(C j) := by
          rw [walkDrawing_V] at hu_Wd
          obtain ⟨z₁, hz₁, hz₁_eq⟩ := (transfer_walk (sp.W_mid (σ k) j)).choose_spec.2.2.2 _ hu_Wd
          have hz₁_PC : z₁ ∈ V(P (σ k)) ∩ V(C j) := by rw [← sp.mid_V (σ k) j]; exact hz₁
          have heq : drawingInvV M (u_d j k) = z₁ := ms.bijV.injOn
            ((hC.1 j).1.vertexSet_mono (hCd_invV hu_d_Cd).1)
            ((hC.1 j).1.vertexSet_mono hz₁_PC.2) (hu_toS.trans hz₁_eq.symm)
          exact heq ▸ hz₁_PC
        have hw_PC : drawingInvV M (w_d j k) ∈ V(P (σ (nextSpoke k))) ∩ V(C j) := by
          rw [walkDrawing_V] at hw_Wd
          obtain ⟨z₂, hz₂, hz₂_eq⟩ :=
            (transfer_walk (sp.W_mid (σ (nextSpoke k)) j)).choose_spec.2.2.2 _ hw_Wd
          have hz₂_PC : z₂ ∈ V(P (σ (nextSpoke k))) ∩ V(C j) := by
            rw [← sp.mid_V (σ (nextSpoke k)) j]; exact hz₂
          have heq : drawingInvV M (w_d j k) = z₂ := ms.bijV.injOn
            ((hC.1 j).1.vertexSet_mono (hCd_invV hw_d_Cd).1)
            ((hC.1 j).1.vertexSet_mono hz₂_PC.2) (hw_toS.trans hz₂_eq.symm)
          exact heq ▸ hz₂_PC
        have hLG_ne : drawingInvV M (u_d j k) ≠ drawingInvV M (w_d j k) := fun heq =>
          huw_ne (hu_toS.symm.trans ((congrArg toS heq).trans hw_toS))
        have hcons : ∀ {p₀ q₀ : α} (V : GraphWalk (C j) p₀ q₀), p₀ ≠ q₀ →
            ∃ (z_G : α) (e₀ : β) (hl₀ : (C j).IsLink e₀ p₀ z_G) (L_rest : GraphWalk (C j) z_G q₀),
              V = .cons hl₀ L_rest := by
          intro p₀ q₀ V hpq
          cases V with
          | nil _ => exact (hpq rfl).elim
          | cons hl₀ L_rest => exact ⟨_, _, hl₀, L_rest, rfl⟩
        obtain ⟨z_G, e₀, hl₀, L_rest, hLG_eq⟩ := hcons L_G hLG_ne
        refine ⟨_, z_G, _, e₀, hl₀, L_rest, hu_toS, hw_toS, hu_PC, hw_PC,
          hLG_eq ▸ hLG_s, ?_, ?_⟩
        · rw [hAd_V, hsupp, hLG_eq]
        · rw [hAd_E, hedges, hLG_eq]
      choose u_G z_G w_G e_circ_sw hl_circ L_rest hu_toS hw_toS hu_PC hw_PC
        hLG_s hAd_V_eq hAd_E_eq using hex_LG
      -- Lift `sp.W_mid i j` to a walk `W_mid_C i j` in `C j`.
      have hex_Wmid_C : ∀ (i : Fin r) (j : Fin s),
          ∃ W_c : GraphWalk (C j) (sp.x i j) (sp.y i j),
            W_c.support = (sp.W_mid i j).support ∧ W_c.edges = (sp.W_mid i j).edges := by
        intro i j
        refine exists_walk_down_of_le (hC.1 j).1 (sp.W_mid i j) (fun z hz => ?_) (fun e he => ?_)
        · have : z ∈ {v | v ∈ (sp.W_mid i j).support} := hz
          rw [sp.mid_V i j] at this; exact this.2
        · have : e ∈ {f | f ∈ (sp.W_mid i j).edges} := he
          rw [sp.mid_E i j] at this; exact this.2
      choose W_mid_C hWmid_C_supp hWmid_C_edges using hex_Wmid_C
      let e_circ : Fin r → Fin s → β := fun k j => e_circ_sw j k
      let K_circ : Fin r → Fin s → Graph α β := fun k j =>
        subgraphUnion (C j)
          (walkSubgraph (W_mid_C (σ k) j))
          (walkSubgraph (L_rest j (prevSpoke k)))
      -- Every edge `f` of `cons (hl_circ j m) (L_rest j m)` has nonempty `toE f ⊆ (A_d j m).U \ {u_d j m, w_d j m}`.
      have hLG_edge_open : ∀ (j : Fin s) (m : Fin r) {f : β},
          f ∈ (GraphWalk.cons (hl_circ j m) (L_rest j m)).edges →
          (toE f).Nonempty ∧ toE f ⊆ (A_d j m).U \ {u_d j m, w_d j m} := by
        intro j m f hf
        have hf_Ad : toE f ∈ (A_d j m).E := by
          rw [hAd_E_eq j m, mem_ofPred_eq]; exact List.mem_map_of_mem hf
        have hne : (toE f).Nonempty := hf_Ad.1
        have hsub : toE f ⊆ (A_d j m).U \ (A_d j m).V := hf_Ad.2.1
        have hu_V : u_d j m ∈ (A_d j m).V := by
          rw [hAd_V_eq j m, mem_ofPred_eq, ← hu_toS j m]
          exact List.mem_map_of_mem (GraphWalk.cons (hl_circ j m) (L_rest j m)).start_mem_support
        have hw_V : w_d j m ∈ (A_d j m).V := by
          rw [hAd_V_eq j m, mem_ofPred_eq, ← hw_toS j m]
          exact List.mem_map_of_mem (GraphWalk.cons (hl_circ j m) (L_rest j m)).end_mem_support
        refine ⟨hne, fun p hp => ⟨(hsub hp).1, ?_⟩⟩
        rintro (rfl | rfl)
        · exact (hsub hp).2 hu_V
        · exact (hsub hp).2 hw_V
      refine ⟨σ, K_circ, e_circ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- `K_circ k j ≤ (C j).deleteEdges (Set.range fun m => e_circ m j)`
        intro k j
        have hK_le_C : K_circ k j ≤ C j :=
          subgraphUnion_le (walkSubgraph_le _) (walkSubgraph_le _)
        refine ⟨hK_le_C.vertexSet_mono, fun f p q hlf => ?_⟩
        rw [deleteEdges_isLink]
        refine ⟨hlf.mono hK_le_C, ?_⟩
        rintro ⟨m₀, rfl⟩
        have hf_E : e_circ m₀ j ∈ E(K_circ k j) := hlf.edge_mem
        rw [edgeSet_subgraphUnion (walkSubgraph_le _) (walkSubgraph_le _),
          edgeSet_walkSubgraph, edgeSet_walkSubgraph] at hf_E
        obtain ⟨⟨p₀, hp₀⟩, hopen_m⟩ := hLG_edge_open j m₀ List.mem_cons_self
        rcases hf_E with hf_mid | hf_rest
        · rw [mem_ofPred_eq, hWmid_C_edges (σ k) j] at hf_mid
          have htoE_Wd : toE (e_circ m₀ j) ∈ (W_draw (σ k) j).E := by
            rw [walkDrawing_E, mem_ofPred_eq,
              (transfer_walk (sp.W_mid (σ k) j)).choose_spec.2.2.1]
            exact List.mem_map_of_mem hf_mid
          have hp₀_Wd : p₀ ∈ (W_draw (σ k) j).U := htoE_Wd.2.1 hp₀ |>.1
          have hp₀_cap : p₀ ∈ (A_d j m₀).U ∩ (⋃ i, (W_draw i j).U) :=
            ⟨(hopen_m hp₀).1, mem_iUnion.mpr ⟨σ k, hp₀_Wd⟩⟩
          rw [(hAd_spec j m₀).2.2.2.2.2.2] at hp₀_cap
          exact (hopen_m hp₀).2 hp₀_cap
        · rw [mem_ofPred_eq] at hf_rest
          by_cases hmk : m₀ = prevSpoke k
          · rw [← hmk] at hf_rest
            have hopen_s := hLG_s j m₀
            obtain ⟨q₁, q₂, hl_r⟩ := (walkSubgraph (L_rest j m₀)).exists_isLink_of_mem_edgeSet
              (by rw [edgeSet_walkSubgraph]; exact hf_rest)
            have hq_supp := walk_isLink_mem_support (L_rest j m₀) hf_rest
              ((walkSubgraph_isLink (L_rest j m₀)).mp hl_r).2
            rcases (hl_circ j m₀).left_eq_or_eq ((walkSubgraph_isLink (L_rest j m₀)).mp hl_r).2 with
              rfl | rfl
            · exact (List.nodup_cons.mp hopen_s).1 hq_supp.1
            · exact (List.nodup_cons.mp hopen_s).1 hq_supp.2
          · obtain ⟨_, hopen_prev⟩ := hLG_edge_open j (prevSpoke k) (List.mem_cons_of_mem _ hf_rest)
            exact Set.disjoint_left.mp (hAd_disj j hmk) (hopen_m hp₀) (hopen_prev hp₀)
      · -- `GraphConnected (K_circ k j)`
        intro k j
        apply graphConnected_subgraphUnion (walkSubgraph_le _) (walkSubgraph_le _)
          (graphConnected_walkSubgraph _) (graphConnected_walkSubgraph _)
        refine ⟨w_G j (prevSpoke k), ?_, ?_⟩
        · rw [vertexSet_walkSubgraph, mem_ofPred_eq, hWmid_C_supp (σ k) j]
          change w_G j (prevSpoke k) ∈ {v | v ∈ (sp.W_mid (σ k) j).support}
          rw [sp.mid_V (σ k) j]
          have h := hw_PC j (prevSpoke k)
          rwa [nextSpoke_prevSpoke] at h
        · rw [vertexSet_walkSubgraph]
          exact (L_rest j (prevSpoke k)).end_mem_support
      · -- `V(P (σ k)) ∩ V(C j) ⊆ V(K_circ k j)`
        intro k j z hz
        rw [vertexSet_subgraphUnion, vertexSet_walkSubgraph]
        left
        rw [mem_ofPred_eq, hWmid_C_supp (σ k) j]
        change z ∈ {v | v ∈ (sp.W_mid (σ k) j).support}
        rwa [sp.mid_V (σ k) j]
      · -- `Disjoint V(K_circ k₁ j) V(K_circ k₂ j)` for `k₁ ≠ k₂`
        intro j k₁ k₂ hne
        have hV_loc : ∀ k z, z ∈ V(K_circ k j) →
            toS z ∈ (W_draw (σ k) j).U ∨
              toS z ∈ (A_d j (prevSpoke k)).U \ {u_d j (prevSpoke k), w_d j (prevSpoke k)} := by
          intro k z hz
          rw [vertexSet_subgraphUnion, vertexSet_walkSubgraph, vertexSet_walkSubgraph] at hz
          rcases hz with hz_mid | hz_rest
          · left
            rw [mem_ofPred_eq, hWmid_C_supp (σ k) j] at hz_mid
            exact (W_draw (σ k) j).V_subset_U (by
              rw [walkDrawing_V, mem_ofPred_eq, (transfer_walk (sp.W_mid (σ k) j)).choose_spec.2.1]
              exact List.mem_map_of_mem hz_mid)
          · rw [mem_ofPred_eq] at hz_rest
            by_cases hzw : z = w_G j (prevSpoke k)
            · left
              subst hzw
              have hw_mem := hw_PC j (prevSpoke k)
              rw [nextSpoke_prevSpoke] at hw_mem
              rw [← sp.mid_V (σ k) j] at hw_mem
              exact (W_draw (σ k) j).V_subset_U (by
                rw [walkDrawing_V, mem_ofPred_eq, (transfer_walk (sp.W_mid (σ k) j)).choose_spec.2.1]
                exact List.mem_map_of_mem hw_mem)
            · right
              have hz_Ad_V : toS z ∈ (A_d j (prevSpoke k)).V := by
                rw [hAd_V_eq j (prevSpoke k), mem_ofPred_eq]
                exact List.mem_map_of_mem (List.mem_cons_of_mem _ hz_rest)
              refine ⟨(A_d j (prevSpoke k)).V_subset_U hz_Ad_V, ?_⟩
              rintro (h_eq_u | h_eq_w)
              · rw [← hu_toS j (prevSpoke k)] at h_eq_u
                have hzu : z = u_G j (prevSpoke k) := ms.bijV.injOn
                  ((hC.1 j).1.vertexSet_mono ((L_rest j (prevSpoke k)).mem_vertexSet_of_mem_support hz_rest))
                  ((hC.1 j).1.vertexSet_mono (hu_PC j (prevSpoke k)).2) h_eq_u
                exact (List.nodup_cons.mp (hLG_s j (prevSpoke k))).1 (hzu ▸ hz_rest)
              · rw [← hw_toS j (prevSpoke k)] at h_eq_w
                have hzw' : z = w_G j (prevSpoke k) := ms.bijV.injOn
                  ((hC.1 j).1.vertexSet_mono ((L_rest j (prevSpoke k)).mem_vertexSet_of_mem_support hz_rest))
                  ((hC.1 j).1.vertexSet_mono (hw_PC j (prevSpoke k)).2) h_eq_w
                exact hzw hzw'
        refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
        have hprev_ne : prevSpoke k₁ ≠ prevSpoke k₂ := fun heq =>
          hne (by rw [← nextSpoke_prevSpoke k₁, heq, nextSpoke_prevSpoke])
        rcases hV_loc k₁ z hz₁ with h1W | h1A <;> rcases hV_loc k₂ z hz₂ with h2W | h2A
        · exact Set.disjoint_left.mp (hWd_disj j (σ.injective.ne hne)) h1W h2W
        · have : toS z ∈ (A_d j (prevSpoke k₂)).U ∩ (⋃ i, (W_draw i j).U) :=
            ⟨h2A.1, mem_iUnion.mpr ⟨σ k₁, h1W⟩⟩
          rw [(hAd_spec j (prevSpoke k₂)).2.2.2.2.2.2] at this
          exact h2A.2 this
        · have : toS z ∈ (A_d j (prevSpoke k₁)).U ∩ (⋃ i, (W_draw i j).U) :=
            ⟨h1A.1, mem_iUnion.mpr ⟨σ k₂, h2W⟩⟩
          rw [(hAd_spec j (prevSpoke k₁)).2.2.2.2.2.2] at this
          exact h1A.2 this
        · exact Set.disjoint_left.mp (hAd_disj j hprev_ne) h1A h2A
      · -- `Function.Injective (fun m => e_circ m j)`
        intro j m₁ m₂ heq
        by_contra hne
        have heq' : e_circ_sw j m₁ = e_circ_sw j m₂ := heq
        have hm₂_mem : e_circ_sw j m₁ ∈ (GraphWalk.cons (hl_circ j m₂) (L_rest j m₂)).edges := by
          change e_circ_sw j m₁ ∈ e_circ_sw j m₂ :: (L_rest j m₂).edges
          rw [heq']
          exact List.mem_cons_self
        obtain ⟨⟨p₀, hp₀⟩, hopen₁⟩ := hLG_edge_open j m₁ List.mem_cons_self
        obtain ⟨_, hopen₂⟩ := hLG_edge_open j m₂ hm₂_mem
        exact Set.disjoint_left.mp (hAd_disj j hne) (hopen₁ hp₀) (hopen₂ hp₀)
      · -- `∃ u ∈ V(K_circ k j), ∃ w ∈ V(K_circ (nextSpoke k) j), (C j).IsLink (e_circ k j) u w`
        intro k j
        refine ⟨u_G j k, ?_, z_G j k, ?_, hl_circ j k⟩
        · rw [vertexSet_subgraphUnion, vertexSet_walkSubgraph]
          left
          rw [mem_ofPred_eq, hWmid_C_supp (σ k) j]
          change u_G j k ∈ {v | v ∈ (sp.W_mid (σ k) j).support}
          rw [sp.mid_V (σ k) j]
          exact hu_PC j k
        · rw [vertexSet_subgraphUnion]
          right
          rw [prevSpoke_nextSpoke k, vertexSet_walkSubgraph]
          exact (L_rest j k).start_mem_support
    · -- Case `r = 1`: `K_circ 0 j := (C j).deleteEdges {e₀ j}` via `GM07.exists_split_at_edge`.
      cases hr1
      let i₀ : Fin 1 := ⟨0, by decide⟩
      have hex_e₀ : ∀ j : Fin s, ∃ e₀ ∈ E(C j), e₀ ∉ E(subgraphInter G (P i₀) (C j)) :=
        fun j => exists_edge_diff_of_circuit_of_path (hC.1 j) (hP_inter i₀ j)
      choose e₀ he₀_C _ using hex_e₀
      let K_circ : Fin 1 → Fin s → Graph α β := fun _ j => (C j).deleteEdges {e₀ j}
      let e_circ : Fin 1 → Fin s → β := fun _ j => e₀ j
      refine ⟨Equiv.refl (Fin 1), K_circ, e_circ, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _ j
        have hrng : (Set.range fun _ : Fin 1 => e₀ j) = {e₀ j} := by
          ext f; simp
        rw [hrng]
      · intro _ j
        obtain ⟨_, u₀, W_C, hWC_sc, _, hVC, hEC⟩ := hC.1 j
        have he₀_W : e₀ j ∈ W_C.edges := by have h := he₀_C j; rwa [hEC] at h
        obtain ⟨p₀, q₀, A_w, hl_e₀, B_w, hWC_split⟩ := GM07.exists_split_at_edge W_C he₀_W
        let L_open : GraphWalk (C j) q₀ p₀ := B_w.append A_w
        have he₀_not_open : e₀ j ∉ L_open.edges := by
          have hed : W_C.edges.Nodup := hWC_sc.2
          rw [hWC_split, GraphWalk.edges_append] at hed
          change (A_w.edges ++ (e₀ j :: B_w.edges)).Nodup at hed
          rw [List.nodup_append] at hed
          have hnotA : e₀ j ∉ A_w.edges := fun hA => hed.2.2 _ hA _ List.mem_cons_self rfl
          have hnotB : e₀ j ∉ B_w.edges := (List.nodup_cons.mp hed.2.1).1
          dsimp [L_open]
          rw [GraphWalk.edges_append, List.mem_append]
          rintro (hB | hA)
          · exact hnotB hB
          · exact hnotA hA
        have hopen_all : ∀ z ∈ V(C j), z ∈ L_open.support := by
          intro z hz
          rw [hVC, mem_ofPred_eq, hWC_split, GraphWalk.mem_support_append] at hz
          dsimp [L_open]
          rw [GraphWalk.mem_support_append]
          rcases hz with hzA | hz_cons
          · exact Or.inr hzA
          · rcases List.mem_cons.mp hz_cons with rfl | hzB
            · exact Or.inr A_w.end_mem_support
            · exact Or.inl hzB
        have hK_le : K_circ i₀ j ≤ C j := deleteEdges_le
        obtain ⟨L_del, hs_del, _⟩ := exists_walk_down_of_le hK_le L_open
          (fun z hz => L_open.mem_vertexSet_of_mem_support hz)
          (fun f hf => by
            rw [Graph.edgeSet_deleteEdges]
            exact ⟨walk_edges_subset_edgeSet L_open f hf, fun hf_eq =>
              he₀_not_open (mem_singleton_iff.mp hf_eq ▸ hf)⟩)
        refine graphConnected_of_walk (L_del.mem_vertexSet_of_mem_support L_del.start_mem_support)
          fun z hz => ?_
        have hz_supp : z ∈ L_del.support := by
          rw [hs_del]; exact hopen_all z hz
        obtain ⟨P_z, _, _⟩ := L_del.exists_append_of_mem hz_supp
        exact ⟨P_z⟩
      · intro k j z hz
        exact hz.2
      · intro j k₁ k₂ hne
        exact (hne (Subsingleton.elim k₁ k₂)).elim
      · intro j m₁ m₂ _
        exact Subsingleton.elim m₁ m₂
      · intro k j
        obtain ⟨u, w, hl⟩ := (C j).exists_isLink_of_mem_edgeSet (he₀_C j)
        exact ⟨u, hl.left_mem, w, hl.right_mem, hl⟩
  exact
    { a := sp.a, b := sp.b, W := sp.W, W_simple := sp.W_simple,
      a_mem := sp.a_mem, b_mem := sp.b_mem, P_V := sp.P_V, P_E := sp.P_E,
      x := sp.x, y := sp.y, W_pre := sp.W_pre, W_mid := sp.W_mid, W_post := sp.W_post,
      W_split := sp.W_split, mid_V := sp.mid_V, mid_E := sp.mid_E,
      x_zero := sp.x_zero, y_last := sp.y_last, between_post := sp.between_post,
      σ := hex_σ_K.choose,
      K_circ := hex_σ_K.choose_spec.choose,
      e_circ := hex_σ_K.choose_spec.choose_spec.choose,
      K_circ_le := hex_σ_K.choose_spec.choose_spec.choose_spec.1,
      K_circ_conn := hex_σ_K.choose_spec.choose_spec.choose_spec.2.1,
      inter_sub_K_circ := hex_σ_K.choose_spec.choose_spec.choose_spec.2.2.1,
      K_circ_disj := hex_σ_K.choose_spec.choose_spec.choose_spec.2.2.2.1,
      e_circ_inj := hex_σ_K.choose_spec.choose_spec.choose_spec.2.2.2.2.1,
      e_circ_link := hex_σ_K.choose_spec.choose_spec.choose_spec.2.2.2.2.2 }

end GraphMinor.GM03
end
