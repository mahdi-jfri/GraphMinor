module

public import GraphMinor.GM03.Defs
import GraphMinor.GM03.Section4a
import GraphMinor.GM03.Section4b
import GraphMinor.GM03.Section4c
import GraphMinor.GM03.Section4d
import GraphMinor.GM09.PlanarNests
import GraphMinor.GM16.LineDrawingPath

/-!
# Graph Minors III, Section 4: Sleeve-Union Surgery (`sleeve_of_sep`)

This file proves `sleeve_of_sep`, the middle-circuit separator surgery step in the proof of
Graph Minors III, (4.3) (page 61): when $M$ has a nested sequence of $s_0 > 2 \lfloor (r_0 + 1)/2 \rfloor$
circuits $C_1, \dots, C_{s_0}$ and $r_0$ vertex-disjoint radial paths $P_1, \dots, P_{r_0}$ meeting
every $C_j$ in a path, any separator $X \subseteq V(G)$ of size $|X| \le r_0$ separating the middle
circuits $V(C_{d+1})$ and $V(C_{s_0 - d})$ decomposes $G$ as a sleeve union of two planar graphs.
-/

public section

namespace GraphMinor.GM03

open Set Function Relation Classical
open Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM09.PlanarNests
open GraphMinor.GM16

universe u v

variable {α : Type u} {β : Type v}

private theorem graphConnected_of_isGraphCircuit {G K : Graph α β} (hK : IsGraphCircuit G K) :
    GraphConnected K := by
  obtain ⟨_, u₀, W₀, _, _, hVK, _⟩ := hK
  refine graphConnected_of_walk (by rw [hVK]; exact W₀.start_mem_support) fun z hz => ?_
  rw [hVK, mem_ofPred_eq] at hz
  obtain ⟨A, _, _⟩ := W₀.exists_append_of_mem hz
  exact ⟨A⟩

private theorem walk_ext {G : Graph α β} {a b : α} (W₁ W₂ : GraphWalk G a b)
    (hs : W₁.support = W₂.support) (he : W₁.edges = W₂.edges) : W₁ = W₂ := by
  induction W₁ with
  | nil _ =>
    cases W₂ with
    | nil _ => rfl
    | cons _ _ => cases he
  | @cons u v₁ w e₁ hl₁ r₁ ih =>
    cases W₂ with
    | nil _ => cases he
    | @cons _ v₂ _ e₂ hl₂ r₂ =>
      obtain ⟨rfl, he'⟩ := (List.cons.injEq _ _ _ _).mp he
      have hs' : v₁ :: r₁.support.tail = v₂ :: r₂.support.tail := by
        have h := (List.cons.injEq _ _ _ _).mp hs
        rw [r₁.support_eq_cons, r₂.support_eq_cons] at h
        exact h.2
      obtain ⟨rfl, htail⟩ := (List.cons.injEq _ _ _ _).mp hs'
      have hrs : r₁.support = r₂.support := by
        rw [r₁.support_eq_cons, r₂.support_eq_cons, htail]
      exact congrArg (GraphWalk.cons hl₁) (ih r₂ hrs he')

private theorem walk_append_cancel_right {G : Graph α β} {a b c : α}
    {W₁ W₂ : GraphWalk G a b} {Suf : GraphWalk G b c}
    (h : W₁.append Suf = W₂.append Suf) : W₁ = W₂ := by
  have hs : W₁.support = W₂.support := by
    have hs_app := congrArg GraphWalk.support h
    rw [GraphWalk.support_append, GraphWalk.support_append, List.append_cancel_right_eq] at hs_app
    exact hs_app
  have he : W₁.edges = W₂.edges := by
    have he_app := congrArg GraphWalk.edges h
    rw [GraphWalk.edges_append, GraphWalk.edges_append, List.append_cancel_right_eq] at he_app
    exact he_app
  exact walk_ext W₁ W₂ hs he

private theorem walkSubgraph_mono_of_sub {G : Graph α β} {a₁ b₁ a₂ b₂ : α}
    (W₁ : GraphWalk G a₁ b₁) (W₂ : GraphWalk G a₂ b₂)
    (hsupp : ∀ z ∈ W₁.support, z ∈ W₂.support)
    (hedges : ∀ e ∈ W₁.edges, e ∈ W₂.edges) :
    walkSubgraph W₁ ≤ walkSubgraph W₂ := by
  refine ⟨fun z hz => ?_, fun e x y hl => ?_⟩
  · rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hz ⊢
    exact hsupp z hz
  · rw [walkSubgraph_isLink] at hl ⊢
    exact ⟨hedges e hl.1, hl.2⟩

private theorem mem_tail_of_isSimple {H : Graph α β} {p q z : α}
    (U : GraphWalk H p q) (hUs : U.IsSimple) (hz : z ∈ U.support.tail) :
    z ∈ U.support ∧ z ≠ p := by
  have hcons := U.support_eq_cons
  have hnd : (p :: U.support.tail).Nodup := hcons ▸ hUs
  refine ⟨by rw [hcons]; exact List.mem_cons_of_mem _ hz, ?_⟩
  rintro rfl
  exact (List.nodup_cons.mp hnd).1 hz

private theorem length_pos_of_ne {H : Graph α β} {p q : α}
    (U : GraphWalk H p q) (hne : p ≠ q) : 0 < U.length := by
  cases U with
  | nil _ => exact (hne rfl).elim
  | cons _ _ => simp [GraphWalk.length, GraphWalk.edges]

/-- Middle-circuit separator surgery step of **Graph Minors III, (4.3)** (page 61):
"For $1 \le i \le r$, let $P'_i$ be the subpath of $P_i$ between $V(C_{d+1})$ and $V(C_{s-d})$, with
no internal vertex in $V(C_{d+1})$ or $V(C_{s-d})$. Then $X \cap V(P'_i) \ne \emptyset$; choose
$v_i \in X \cap V(P'_i)$ ($1 \le i \le r$). We have $\{v_1, \dots, v_r\} \subseteq X$ and
$|X| \le r$, and so $X = \{v_1, \dots, v_r\}$. Let $(H_1, H_2)$ be a separation of $G$ with
$V(H_1) \cap V(H_2) = X$, where $C_1, \dots, C_{d+1}$ are circuits of $H_1$ and
$C_{s-d}, \dots, C_s$ are circuits of $H_2$. Now $H_1$ has a proper minor isomorphic to the
$r \times d$ cylinder in the required way for sleeve unions, and so has $H_2$; thus $G$ is
expressible as a sleeve union of two planar graphs." -/
theorem sleeve_of_sep {G : Graph α β} (M : PlanarDrawing G) {r₀ s₀ : ℕ}
    (hs₀ : 2 * ((r₀ + 1) / 2) < s₀)
    (C : Fin s₀ → Graph α β) (P : Fin r₀ → Graph α β)
    (hC : IsNestedCircuitSeq M s₀ C)
    (hP_disj : Pairwise (fun i₁ i₂ : Fin r₀ => Disjoint V(P i₁) V(P i₂)))
    (hP_path : ∀ i : Fin r₀, IsPathBetween G (P i)
      V(C ⟨0, by omega⟩) V(C ⟨s₀ - 1, by omega⟩))
    (hP_inter : ∀ (i : Fin r₀) (j : Fin s₀), IsGraphPath G (subgraphInter G (P i) (C j)))
    (X : Set α) (hXV : X ⊆ V(G)) (hXcard : X.ncard ≤ r₀)
    (hXsep : Separates G X V(C ⟨(r₀ + 1) / 2, by omega⟩)
      V(C ⟨s₀ - (r₀ + 1) / 2 - 1, by omega⟩)) :
    IsExpressibleAsPlanarSleeveUnion G := by
  have hs₀_pos : 0 < s₀ := by omega
  have hX_fin : X.Finite := M.graphDrawing.finite_V.subset hXV
  by_cases hr₀ : 0 < r₀
  · let d : ℕ := (r₀ + 1) / 2
    have hd : 0 < d := by omega
    have hs_max_eq : max 1 ((r₀ + 1) / 2) = d := max_eq_right (by omega)
    let dat := buildOrderedNestedCylinderData M r₀ s₀ hr₀ hs₀_pos C P hC hP_disj hP_path hP_inter
    let j_L : Fin s₀ := ⟨d, by omega⟩
    let j_R : Fin s₀ := ⟨s₀ - d - 1, by omega⟩
    have hW_pre_succ : ∀ (i : Fin r₀) (q : Fin (s₀ - 1)),
        dat.W_pre i ⟨q.1 + 1, by omega⟩ =
          (dat.W_pre i ⟨q.1, by omega⟩).append
            ((dat.W_mid i ⟨q.1, by omega⟩).append (dat.R_adj i q)) := by
      intro i q
      apply walk_append_cancel_right
        (Suf := (dat.W_mid i ⟨q.1 + 1, by omega⟩).append (dat.W_post i ⟨q.1 + 1, by omega⟩))
      have h1 := dat.W_split i ⟨q.1 + 1, by omega⟩
      have h2 := dat.W_split i ⟨q.1, by omega⟩
      rw [dat.R_adj_spec i q, ← GraphWalk.append_assoc, ← GraphWalk.append_assoc,
        GraphWalk.append_assoc (dat.W_pre i ⟨q.1, by omega⟩)] at h2
      exact h1.symm.trans h2
    -- Spanning middle subwalk `W_span i` from `dat.x i j_L` to `dat.y i j_R`.
    have hex_span : ∀ i : Fin r₀, ∃ W_sp : GraphWalk G (dat.x i j_L) (dat.y i j_R),
        dat.W i = (dat.W_pre i j_L).append (W_sp.append (dat.W_post i j_R)) := by
      intro i
      by_cases hLR_eq : d = s₀ - d - 1
      · have hj_eq : j_L = j_R := Fin.ext hLR_eq
        have hcast : ∀ {j' : Fin s₀}, j_L = j' →
            ∃ W_sp : GraphWalk G (dat.x i j_L) (dat.y i j'),
              dat.W i = (dat.W_pre i j_L).append (W_sp.append (dat.W_post i j')) := by
          rintro _ rfl
          exact ⟨dat.W_mid i j_L, dat.W_split i j_L⟩
        exact hcast hj_eq
      · have hj_lt : j_L < j_R := Fin.mk_lt_mk.mpr (by omega)
        obtain ⟨R_LR, hR_LR⟩ := dat.between_post i hj_lt
        refine ⟨(dat.W_mid i j_L).append (R_LR.append (dat.W_mid i j_R)), ?_⟩
        rw [dat.W_split i j_L, hR_LR, GraphWalk.append_assoc, GraphWalk.append_assoc]
    choose W_span hW_span_eq using hex_span
    have hW_span_simple : ∀ i : Fin r₀, (W_span i).IsSimple := fun i =>
      (isSimple_of_append ((isSimple_of_append (hW_span_eq i ▸ dat.W_simple i)).2)).1
    have hW_span_sub_P : ∀ (i : Fin r₀) {z : α}, z ∈ (W_span i).support → z ∈ V(P i) := by
      intro i z hz
      rw [dat.P_V i, mem_ofPred_eq, hW_span_eq i,
        GraphWalk.mem_support_append, GraphWalk.mem_support_append]
      exact Or.inr (Or.inl hz)
    -- `X` meets `W_span i` for every `i : Fin r₀`.
    have hex_v_raw : ∀ i : Fin r₀, ∃ v_i ∈ (W_span i).support, v_i ∈ X := by
      intro i
      have hpath : IsPathBetween G (walkSubgraph (W_span i)) V(C j_L) V(C j_R) :=
        ⟨dat.x i j_L, (dat.mem_mid_V_ends i j_L).1.2,
         dat.y i j_R, (dat.mem_mid_V_ends i j_R).2.2,
         isGraphPathWithEnds_walkSubgraph (hW_span_simple i)⟩
      obtain ⟨z, hzW, hzX⟩ := Set.not_disjoint_iff.mp (hXsep (walkSubgraph (W_span i)) hpath)
      rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hzW
      exact ⟨z, hzW, hzX⟩
    choose v_raw hv_raw_span hv_raw_X using hex_v_raw
    have hv_raw_P : ∀ i : Fin r₀, v_raw i ∈ V(P i) :=
      fun i => hW_span_sub_P i (hv_raw_span i)
    have hv_raw_inj : Function.Injective v_raw := by
      intro i₁ i₂ heq
      by_contra hne
      exact disjoint_left.mp (hP_disj hne) (hv_raw_P i₁) (heq ▸ hv_raw_P i₂)
    have hrange_sub_X : Set.range v_raw ⊆ X := by
      rintro _ ⟨i, rfl⟩; exact hv_raw_X i
    have hX_eq_raw : X = Set.range v_raw := by
      have hcard_range : (Set.range v_raw).ncard = r₀ := by
        rw [Set.ncard_range_of_injective hv_raw_inj, Nat.card_eq_fintype_card, Fintype.card_fin]
      exact (Set.eq_of_subset_of_ncard_le hrange_sub_X (hXcard.trans_eq hcard_range.symm) hX_fin).symm
    have hv_unique_P : ∀ (i : Fin r₀) {z : α}, z ∈ V(P i) → z ∈ X → z = v_raw i := by
      intro i z hzP hzX
      rw [hX_eq_raw] at hzX
      obtain ⟨i', rfl⟩ := hzX
      have hi_eq : i' = i := by
        by_contra hne
        exact disjoint_left.mp (hP_disj hne) (hv_raw_P i') hzP
      exact congrArg v_raw hi_eq
    have hpre_j_L_of_lt : ∀ (i : Fin r₀) {j : Fin s₀} (hj : j < j_L),
        ∃ R : GraphWalk G (dat.y i j) (dat.x i j_L),
          dat.W_pre i j_L = (dat.W_pre i j).append ((dat.W_mid i j).append R) := by
      intro i j hj
      obtain ⟨R, hR⟩ := dat.between_post i hj
      refine ⟨R, walk_append_cancel_right (Suf := (dat.W_mid i j_L).append (dat.W_post i j_L)) ?_⟩
      have h1 := dat.W_split i j_L
      have h2 := dat.W_split i j
      rw [hR, ← GraphWalk.append_assoc, ← GraphWalk.append_assoc,
        GraphWalk.append_assoc (dat.W_pre i j)] at h2
      exact h1.symm.trans h2
    -- `W_span i` is disjoint from every outer circuit `C j` (`j < d`) and inner circuit (`j ≥ s₀ - d`).
    have hspan_disj_outer : ∀ (i : Fin r₀) (j : Fin s₀), j.1 < d →
        Disjoint {z | z ∈ (W_span i).support} V(C j) := by
      intro i j hj
      have hj_lt : j < j_L := Fin.mk_lt_mk.mpr hj
      obtain ⟨R₀, hpre_eq⟩ := hpre_j_L_of_lt i hj_lt
      refine disjoint_left.mpr fun z hz_sp hzC => ?_
      have hz_mid : z ∈ (dat.W_mid i j).support := by
        change z ∈ {w | w ∈ (dat.W_mid i j).support}
        rw [dat.mid_V i j]; exact ⟨hW_span_sub_P i hz_sp, hzC⟩
      have hz_pre_not_end : z ∈ (dat.W_pre i j_L).support ∧ z ≠ dat.x i j_L := by
        refine ⟨?_, fun hzx => disjoint_left.mp (hC.2 hj_lt).1 hzC
          (hzx ▸ (dat.mem_mid_V_ends i j_L).1.2)⟩
        rw [hpre_eq, GraphWalk.mem_support_append, GraphWalk.mem_support_append]
        exact Or.inr (Or.inl hz_mid)
      have hnd : ((dat.W_pre i j_L).support ++
          ((W_span i).append (dat.W_post i j_R)).support.tail).Nodup := by
        have h' : (dat.W i).support.Nodup := dat.W_simple i
        rwa [hW_span_eq i, GraphWalk.support_append] at h'
      have hz_sp_cons := (W_span i).support_eq_cons
      rw [hz_sp_cons] at hz_sp
      rcases List.mem_cons.mp hz_sp with rfl | htail
      · exact hz_pre_not_end.2 rfl
      · have htail' : z ∈ ((W_span i).append (dat.W_post i j_R)).support.tail := by
          rw [GraphWalk.support_append, hz_sp_cons]
          exact List.mem_append_left _ htail
        exact (List.nodup_append.mp hnd).2.2 z hz_pre_not_end.1 z htail' rfl
    have hspan_disj_inner : ∀ (i : Fin r₀) (j : Fin s₀), s₀ - d ≤ j.1 →
        Disjoint {z | z ∈ (W_span i).support} V(C j) := by
      intro i j hj
      have hj_gt : j_R < j := Fin.mk_lt_mk.mpr (by omega)
      obtain ⟨R₁, hR₁⟩ := dat.between_post i hj_gt
      have hne : dat.y i j_R ≠ dat.x i j := fun h =>
        disjoint_left.mp (hC.2 hj_gt).1
          (dat.mem_mid_V_ends i j_R).2.2 (h ▸ (dat.mem_mid_V_ends i j).1.2)
      obtain ⟨_, _, hl₁, R₁', hR₁_eq⟩ := walk_cons_of_ne R₁ hne
      refine disjoint_left.mpr fun z hz_sp hzC => ?_
      have hz_mid : z ∈ (dat.W_mid i j).support := by
        change z ∈ {w | w ∈ (dat.W_mid i j).support}
        rw [dat.mid_V i j]; exact ⟨hW_span_sub_P i hz_sp, hzC⟩
      have hW_eq : dat.W i =
          ((dat.W_pre i j_L).append (W_span i)).append (dat.W_post i j_R) := by
        rw [hW_span_eq i, GraphWalk.append_assoc]
      have hnd : (((dat.W_pre i j_L).append (W_span i)).support ++
          (dat.W_post i j_R).support.tail).Nodup := by
        have h' : (dat.W i).support.Nodup := dat.W_simple i
        rwa [hW_eq, GraphWalk.support_append] at h'
      have hz_left : z ∈ ((dat.W_pre i j_L).append (W_span i)).support := by
        rw [GraphWalk.mem_support_append]; exact Or.inr hz_sp
      have hz_tail : z ∈ (dat.W_post i j_R).support.tail := by
        have hcons : (GraphWalk.cons hl₁ R₁').append
            ((dat.W_mid i j).append (dat.W_post i j)) =
            GraphWalk.cons hl₁ (R₁'.append ((dat.W_mid i j).append (dat.W_post i j))) := rfl
        rw [hR₁, hR₁_eq, hcons, GraphWalk.support, List.tail_cons,
          GraphWalk.mem_support_append, GraphWalk.mem_support_append]
        exact Or.inr (Or.inl hz_mid)
      exact (List.nodup_append.mp hnd).2.2 z hz_left z hz_tail rfl
    have hC_disj_X_outer : ∀ (j : Fin s₀), j.1 < d → Disjoint V(C j) X := by
      intro j hj
      rw [hX_eq_raw, Set.disjoint_left]
      rintro z hzC ⟨i, rfl⟩
      exact disjoint_left.mp (hspan_disj_outer i j hj) (hv_raw_span i) hzC
    have hC_disj_X_inner : ∀ (j : Fin s₀), s₀ - d ≤ j.1 → Disjoint V(C j) X := by
      intro j hj
      rw [hX_eq_raw, Set.disjoint_left]
      rintro z hzC ⟨i, rfl⟩
      exact disjoint_left.mp (hspan_disj_inner i j hj) (hv_raw_span i) hzC
    -- Split `G` along `X` separating `V(C 0)` and `V(C (s₀ - 1))`.
    let j₀ : Fin s₀ := ⟨0, hs₀_pos⟩
    let j_last : Fin s₀ := ⟨s₀ - 1, by omega⟩
    have hXsep_outer : Separates G X V(C j₀) V(C j_last) :=
      separates_outer_inner_of_separates_mid M hd hs₀ C hC X hXsep
    let S := buildSepSplitData hXV (hC.1 j₀).1.vertexSet_mono (hC.1 j_last).1.vertexSet_mono
      (hC_disj_X_outer j₀ hd) (hC_disj_X_inner j_last (by dsimp [j_last, d]; omega)) hXsep_outer
    -- Split each `W_span i` at `v_raw i` into `M_left i` and `M_right i`.
    have hex_M : ∀ i : Fin r₀,
        ∃ (M_l : GraphWalk G (dat.x i j_L) (v_raw i))
          (M_r : GraphWalk G (v_raw i) (dat.y i j_R)),
          W_span i = M_l.append M_r :=
      fun i => (W_span i).exists_append_of_mem (hv_raw_span i)
    choose M_left M_right hM_split using hex_M
    let W_to_v : ∀ i : Fin r₀, GraphWalk G (dat.a i) (v_raw i) :=
      fun i => (dat.W_pre i j_L).append (M_left i)
    let W_from_v : ∀ i : Fin r₀, GraphWalk G (v_raw i) (dat.b i) :=
      fun i => (M_right i).append (dat.W_post i j_R)
    have hW_v_split : ∀ i : Fin r₀, dat.W i = (W_to_v i).append (W_from_v i) := by
      intro i
      dsimp only [W_to_v, W_from_v]
      rw [hW_span_eq i, hM_split i, GraphWalk.append_assoc, GraphWalk.append_assoc]
    have hW_to_v_simple : ∀ i : Fin r₀, (W_to_v i).IsSimple :=
      fun i => (isSimple_of_append (hW_v_split i ▸ dat.W_simple i)).1
    have hW_from_v_simple : ∀ i : Fin r₀, (W_from_v i).IsSimple :=
      fun i => (isSimple_of_append (hW_v_split i ▸ dat.W_simple i)).2
    have hW_to_v_le_H₁ : ∀ i : Fin r₀, walkSubgraph (W_to_v i) ≤ S.H₁ := by
      intro i
      refine walkSubgraph_le_H₁_of_end_only S (W_to_v i) (hW_to_v_simple i)
        (S.A_sub (dat.a_mem i)) (Or.inr (hv_raw_X i)) fun z hz hzX => ?_
      have hzP : z ∈ V(P i) := by
        rw [dat.P_V i, mem_ofPred_eq, hW_v_split i, GraphWalk.mem_support_append]
        exact Or.inl hz
      exact hv_unique_P i hzP hzX
    have hW_from_v_rev_le_H₂ : ∀ i : Fin r₀, walkSubgraph (W_from_v i).reverse ≤ S.H₂ := by
      intro i
      refine walkSubgraph_le_H₂_of_end_only S (W_from_v i).reverse
        (hW_from_v_simple i).reverse (S.B_sub (dat.b_mem i)) fun z hz hzX => ?_
      rw [GraphWalk.support_reverse, List.mem_reverse] at hz
      have hzP : z ∈ V(P i) := by
        rw [dat.P_V i, mem_ofPred_eq, hW_v_split i, GraphWalk.mem_support_append]
        exact Or.inr hz
      exact hv_unique_P i hzP hzX
    -- Every outer circuit `C j` (`j.1 < d`) lies in `S.H₁`, and inner circuit (`s₀ - d ≤ j.1`) in `S.H₂`.
    let i₀ : Fin r₀ := ⟨0, hr₀⟩
    have hC_le_H₁ : ∀ (j : Fin s₀), j.1 < d → V(C j) ⊆ S.V₁ ∧ C j ≤ S.H₁ := by
      intro j hj
      obtain ⟨R, hpre_eq⟩ := hpre_j_L_of_lt i₀ (Fin.mk_lt_mk.mpr hj)
      have hy_supp : dat.y i₀ j ∈ (W_to_v i₀).support := by
        dsimp only [W_to_v]
        rw [hpre_eq, GraphWalk.mem_support_append, GraphWalk.mem_support_append,
          GraphWalk.mem_support_append]
        exact Or.inl (Or.inr (Or.inl (dat.W_mid i₀ j).end_mem_support))
      have hy_H₁ : dat.y i₀ j ∈ V(S.H₁) :=
        (hW_to_v_le_H₁ i₀).vertexSet_mono (by rw [vertexSet_walkSubgraph]; exact hy_supp)
      rw [S.V_H₁] at hy_H₁
      have hy_C : dat.y i₀ j ∈ V(C j) := (dat.mem_mid_V_ends i₀ j).2.2
      have hy_V₁ : dat.y i₀ j ∈ S.V₁ :=
        hy_H₁.resolve_right (disjoint_left.mp (hC_disj_X_outer j hj) hy_C)
      exact connected_le_H₁_of_disjoint_X S (hC.1 j).1
        (graphConnected_of_isGraphCircuit (hC.1 j)) (hC_disj_X_outer j hj) hy_C hy_V₁
    have hC_le_H₂ : ∀ (j : Fin s₀), s₀ - d ≤ j.1 → V(C j) ⊆ S.V₂ ∧ C j ≤ S.H₂ := by
      intro j hj
      obtain ⟨R, hpost_eq⟩ := dat.between_post i₀ (show j_R < j from Fin.mk_lt_mk.mpr (by omega))
      have hx_supp : dat.x i₀ j ∈ (W_from_v i₀).reverse.support := by
        rw [GraphWalk.support_reverse, List.mem_reverse]
        dsimp only [W_from_v]
        rw [hpost_eq, GraphWalk.mem_support_append, GraphWalk.mem_support_append,
          GraphWalk.mem_support_append]
        exact Or.inr (Or.inr (Or.inl (dat.W_mid i₀ j).start_mem_support))
      have hx_H₂ : dat.x i₀ j ∈ V(S.H₂) :=
        (hW_from_v_rev_le_H₂ i₀).vertexSet_mono (by rw [vertexSet_walkSubgraph]; exact hx_supp)
      rw [S.V_H₂] at hx_H₂
      have hx_C : dat.x i₀ j ∈ V(C j) := (dat.mem_mid_V_ends i₀ j).1.2
      have hx_V₂ : dat.x i₀ j ∈ S.V₂ :=
        hx_H₂.resolve_right (disjoint_left.mp (hC_disj_X_inner j hj) hx_C)
      exact connected_le_H₂_of_disjoint_X S (hC.1 j).1
        (graphConnected_of_isGraphCircuit (hC.1 j)) (hC_disj_X_inner j hj) hx_C hx_V₂
    -- Ordered separator vertices `v k := v_raw (dat.σ k)`.
    let v : Fin r₀ → α := fun k => v_raw (dat.σ k)
    have hv_inj : Function.Injective v := hv_raw_inj.comp dat.σ.injective
    have hinter_S : V(S.H₁) ∩ V(S.H₂) = Set.range v := by
      rw [S.inter_eq, hX_eq_raw]
      ext z
      simp only [mem_range]
      exact ⟨fun ⟨i, hi⟩ => ⟨dat.σ.symm i, by simp [v, hi]⟩, fun ⟨k, hk⟩ => ⟨dat.σ k, hk⟩⟩
    -- 1. Proper `r₀ × d` cylinder minor in `S.H₁` (outer side).
    have hmin₁ : IsProperMinorWithMap (cylinderGraph r₀ d) S.H₁ v
        (fun k => (k, ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩)) := by
      let j₁_emb : Fin d → Fin s₀ := fun j => ⟨j.1, by omega⟩
      have hj₁_inj : Function.Injective j₁_emb := fun a b h =>
        Fin.ext (congrArg (fun x : Fin s₀ => x.1) h)
      obtain ⟨hK₁_le, hK₁_conn, hK₁_disj, he₁_not_K, he₁_inj, he₁_link⟩ :=
        dat.circlePieces_of_emb hC j₁_emb hj₁_inj (fun j => (hC_le_H₁ (j₁_emb j) j.2).2)
      let K₁ : Fin r₀ → Fin d → Graph α β := fun k j => dat.K_circ k (j₁_emb j)
      let e₁ : Fin r₀ → Fin d → β := fun k j => dat.e_circ k (j₁_emb j)
      let u₁_rad : Fin r₀ → Fin (d - 1) → α := fun k m => dat.y (dat.σ k) ⟨m.1, by omega⟩
      let w₁_rad : Fin r₀ → Fin (d - 1) → α := fun k m => dat.x (dat.σ k) ⟨m.1 + 1, by omega⟩
      have hRad₁_le : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          walkSubgraph (dat.R_adj (dat.σ k) ⟨m.1, by omega⟩) ≤ S.H₁ := by
        intro k m
        let i := dat.σ k
        let qm : Fin (s₀ - 1) := ⟨m.1, by omega⟩
        obtain ⟨R_m, hpre_eq⟩ := hpre_j_L_of_lt i
          (show (⟨m.1 + 1, by omega⟩ : Fin s₀) < j_L from Fin.mk_lt_mk.mpr (by omega))
        refine (walkSubgraph_mono_of_sub _ (W_to_v i) ?_ ?_).trans (hW_to_v_le_H₁ i)
        · intro z hz
          dsimp only [W_to_v]
          rw [hpre_eq, hW_pre_succ i qm, GraphWalk.mem_support_append,
            GraphWalk.mem_support_append, GraphWalk.mem_support_append,
            GraphWalk.mem_support_append]
          exact Or.inl (Or.inl (Or.inr (Or.inr hz)))
        · intro e he
          dsimp only [W_to_v]
          rw [hpre_eq, hW_pre_succ i qm, GraphWalk.edges_append,
            GraphWalk.edges_append, GraphWalk.edges_append, GraphWalk.edges_append]
          exact List.mem_append_left _ (List.mem_append_left _
            (List.mem_append_right _ (List.mem_append_right _ he)))
      have hex_R₁_rad : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          ∃ W' : GraphWalk S.H₁ (u₁_rad k m) (w₁_rad k m),
            W'.support = (dat.R_adj (dat.σ k) ⟨m.1, by omega⟩).support ∧
            W'.edges = (dat.R_adj (dat.σ k) ⟨m.1, by omega⟩).edges :=
        fun k m => liftWalkOfSubgraph _ (hRad₁_le k m)
      choose R₁_rad hR₁_rad_supp hR₁_rad_edges using hex_R₁_rad
      have hR₁_rad_simple : ∀ (k : Fin r₀) (m : Fin (d - 1)), (R₁_rad k m).IsSimple := by
        intro k m; unfold GraphWalk.IsSimple; rw [hR₁_rad_supp]; exact dat.R_adj_simple _ _
      -- Outer tail walk `T₁_G i` from `dat.y i ⟨d - 1, _⟩` to `v_raw i`.
      let q_d1 : Fin (s₀ - 1) := ⟨d - 1, by omega⟩
      have hj_d1_succ : (⟨q_d1.1 + 1, by omega⟩ : Fin s₀) = j_L := Fin.ext (by dsimp [q_d1, j_L]; omega)
      let u₁_tail : Fin r₀ → α := fun k => dat.y (dat.σ k) ⟨d - 1, by omega⟩
      have hex_T₁ : ∀ i : Fin r₀,
          ∃ T₁ : GraphWalk G (dat.y i ⟨d - 1, by omega⟩) (v_raw i),
            W_to_v i = (dat.W_pre i ⟨d - 1, by omega⟩).append
              ((dat.W_mid i ⟨d - 1, by omega⟩).append T₁) ∧
            (∀ z ∈ T₁.support,
              z ∈ (dat.R_adj i q_d1).support ∨ z ∈ (M_left i).support) := by
        intro i
        have hcast_q : ∀ {j' : Fin s₀}, (⟨q_d1.1 + 1, by omega⟩ : Fin s₀) = j' →
            ∃ R_d1 : GraphWalk G (dat.y i ⟨d - 1, by omega⟩) (dat.x i j'),
              dat.W_pre i j' = (dat.W_pre i ⟨d - 1, by omega⟩).append
                ((dat.W_mid i ⟨d - 1, by omega⟩).append R_d1) ∧
              (∀ z ∈ R_d1.support, z ∈ (dat.R_adj i q_d1).support) := by
          rintro _ rfl
          exact ⟨dat.R_adj i q_d1, hW_pre_succ i q_d1, fun _ h => h⟩
        obtain ⟨R_d1, hpre_d, hR_d1_supp⟩ := hcast_q hj_d1_succ
        let T₁ : GraphWalk G (dat.y i ⟨d - 1, by omega⟩) (v_raw i) := R_d1.append (M_left i)
        refine ⟨T₁, ?_, ?_⟩
        · dsimp only [W_to_v, T₁]
          rw [hpre_d, GraphWalk.append_assoc, GraphWalk.append_assoc]
        · intro z hz
          dsimp only [T₁] at hz
          rw [GraphWalk.mem_support_append] at hz
          rcases hz with h1 | h2
          · exact Or.inl (hR_d1_supp z h1)
          · exact Or.inr h2
      choose T₁_G hW_to_v_T₁ hT₁_supp_or using hex_T₁
      have hT₁_simple : ∀ i : Fin r₀, (T₁_G i).IsSimple := fun i =>
        (isSimple_of_append ((isSimple_of_append (hW_to_v_T₁ i ▸ hW_to_v_simple i)).2)).2
      have hT₁_le : ∀ i : Fin r₀, walkSubgraph (T₁_G i) ≤ S.H₁ := by
        intro i
        refine (walkSubgraph_mono_of_sub _ (W_to_v i) ?_ ?_).trans (hW_to_v_le_H₁ i)
        · intro z hz
          rw [hW_to_v_T₁ i, GraphWalk.mem_support_append, GraphWalk.mem_support_append]
          exact Or.inr (Or.inr hz)
        · intro e he
          rw [hW_to_v_T₁ i, GraphWalk.edges_append, GraphWalk.edges_append]
          exact List.mem_append_right _ (List.mem_append_right _ he)
      have hex_R₁_tail : ∀ k : Fin r₀,
          ∃ W' : GraphWalk S.H₁ (u₁_tail k) (v k),
            W'.support = (T₁_G (dat.σ k)).support ∧ W'.edges = (T₁_G (dat.σ k)).edges :=
        fun k => liftWalkOfSubgraph _ (hT₁_le (dat.σ k))
      choose R₁_tail hR₁_tail_supp hR₁_tail_edges using hex_R₁_tail
      have hR₁_tail_simple : ∀ k : Fin r₀, (R₁_tail k).IsSimple := by
        intro k; unfold GraphWalk.IsSimple; rw [hR₁_tail_supp]; exact hT₁_simple _
      have hu₁_rad_mem : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          u₁_rad k m ∈ V(K₁ k ⟨m.1, by omega⟩) :=
        fun k m => dat.inter_sub_K_circ k (j₁_emb ⟨m.1, by omega⟩)
          (dat.mem_mid_V_ends (dat.σ k) ⟨m.1, by omega⟩).2
      have hw₁_rad_mem : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          w₁_rad k m ∈ V(K₁ k ⟨m.1 + 1, by omega⟩) :=
        fun k m => dat.inter_sub_K_circ k (j₁_emb ⟨m.1 + 1, by omega⟩)
          (dat.mem_mid_V_ends (dat.σ k) ⟨m.1 + 1, by omega⟩).1
      have hu₁_tail_mem : ∀ k : Fin r₀,
          u₁_tail k ∈ V(K₁ k ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩) :=
        fun k => dat.inter_sub_K_circ k (j₁_emb ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩)
          (dat.mem_mid_V_ends (dat.σ k) ⟨d - 1, by omega⟩).2
      have hK₁_sub_C : ∀ (k' : Fin r₀) (j' : Fin d), V(K₁ k' j') ⊆ V(C (j₁_emb j')) :=
        fun k' j' => ((dat.K_circ_le k' (j₁_emb j')).trans deleteEdges_le).vertexSet_mono
      obtain ⟨H₁', hH₁'_le, C₁_contr, hC₁_sub, φ₁, hφ₁_v, hC₁_ne_imp⟩ :=
        exists_cylinder_contract_of_circle_pieces r₀ d hd K₁ e₁
          hK₁_le hK₁_conn (fun h => hK₁_disj h) he₁_not_K (fun h => he₁_inj h) he₁_link
          u₁_rad w₁_rad R₁_rad hR₁_rad_simple hu₁_rad_mem hw₁_rad_mem
          (fun k m k' j' z hzR hzK => by
            rw [hR₁_rad_supp] at hzR
            rcases dat.R_adj_inter_C hC (dat.σ k) ⟨m.1, by omega⟩ (j₁_emb j') hzR
              (hK₁_sub_C k' j' hzK) with ⟨hj_eq, hzy⟩ | ⟨hj_eq, hzx⟩
            · have hm_lt : m.1 < d := by have := m.2; omega
              have hj' : j' = ⟨m.1, hm_lt⟩ :=
                Fin.ext (congrArg (fun x : Fin s₀ => x.1) hj_eq)
              have hzu : z = u₁_rad k m := hzy
              have hk' : k' = k := by
                by_contra hne
                exact disjoint_left.mp (hK₁_disj (fun h => hne (congrArg Prod.fst h)))
                  (hj' ▸ hzK) (hzu ▸ hu₁_rad_mem k m)
              exact Or.inl ⟨hk', hj', hzu⟩
            · have hm1_lt : m.1 + 1 < d := by have := m.2; omega
              have hj' : j' = ⟨m.1 + 1, hm1_lt⟩ :=
                Fin.ext (congrArg (fun x : Fin s₀ => x.1) hj_eq)
              have hzw : z = w₁_rad k m := hzx
              have hk' : k' = k := by
                by_contra hne
                exact disjoint_left.mp (hK₁_disj (fun h => hne (congrArg Prod.fst h)))
                  (hj' ▸ hzK) (hzw ▸ hw₁_rad_mem k m)
              exact Or.inr ⟨hk', hj', hzw⟩)
          (fun {k₁ k₂ m₁ m₂} hne => by
            refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
            obtain ⟨hz₁_s, hz₁_ne⟩ := mem_tail_of_isSimple _ (hR₁_rad_simple k₁ m₁) hz₁
            obtain ⟨hz₂_s, hz₂_ne⟩ := mem_tail_of_isSimple _ (hR₁_rad_simple k₂ m₂) hz₂
            rw [hR₁_rad_supp] at hz₁_s hz₂_s
            by_cases hk : k₁ = k₂
            · subst hk
              have hm_ne : m₁.1 ≠ m₂.1 := fun h => hne (Prod.ext rfl (Fin.ext h))
              rcases lt_trichotomy m₁.1 m₂.1 with hlt | heq | hgt
              · obtain ⟨_, _, hzy⟩ := dat.R_adj_inter hC (dat.σ k₁)
                  (q₁ := ⟨m₁.1, by omega⟩) (q₂ := ⟨m₂.1, by omega⟩)
                  (Fin.mk_lt_mk.mpr hlt) hz₁_s hz₂_s
                exact hz₂_ne hzy
              · exact hm_ne heq
              · obtain ⟨_, _, hzy⟩ := dat.R_adj_inter hC (dat.σ k₁)
                  (q₁ := ⟨m₂.1, by omega⟩) (q₂ := ⟨m₁.1, by omega⟩)
                  (Fin.mk_lt_mk.mpr hgt) hz₂_s hz₁_s
                exact hz₁_ne hzy
            · have hzP₁ : z ∈ V(P (dat.σ k₁)) := by
                rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨m₁.1, by omega⟩,
                  dat.R_adj_spec _ ⟨m₁.1, by omega⟩, GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inr (Or.inl hz₁_s))
              have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
                rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨m₂.1, by omega⟩,
                  dat.R_adj_spec _ ⟨m₂.1, by omega⟩, GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inr (Or.inl hz₂_s))
              exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hk)) hzP₁ hzP₂)
          u₁_tail v R₁_tail hR₁_tail_simple hu₁_tail_mem
          (fun k k' j' z hzT hzK => by
            rw [hR₁_tail_supp] at hzT
            have hzC : z ∈ V(C (j₁_emb j')) := hK₁_sub_C k' j' hzK
            rcases hT₁_supp_or (dat.σ k) z hzT with hzR | hzM
            · rcases dat.R_adj_inter_C hC (dat.σ k) q_d1 (j₁_emb j') hzR hzC with
                ⟨hj_eq, hzy⟩ | ⟨hj_eq, _⟩
              · have hj' : j' = ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩ :=
                  Fin.ext (congrArg (fun x : Fin s₀ => x.1) hj_eq)
                have hzu : z = u₁_tail k := hzy
                have hk' : k' = k := by
                  by_contra hne
                  exact disjoint_left.mp (hK₁_disj (fun h => hne (congrArg Prod.fst h)))
                    (hj' ▸ hzK) (hzu ▸ hu₁_tail_mem k)
                exact ⟨hk', hj', hzu⟩
              · exfalso
                have := congrArg (fun x : Fin s₀ => x.1) hj_eq
                dsimp [j₁_emb, q_d1] at this
                omega
            · exfalso
              have hz_sp : z ∈ (W_span (dat.σ k)).support := by
                rw [hM_split, GraphWalk.mem_support_append]; exact Or.inl hzM
              exact disjoint_left.mp (hspan_disj_outer (dat.σ k) (j₁_emb j') j'.2) hz_sp hzC)
          (fun {k₁ k₂} hne => by
            refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
            rw [hR₁_tail_supp] at hz₁
            rw [hR₁_tail_supp] at hz₂
            have hzP₁ : z ∈ V(P (dat.σ k₁)) := by
              rw [dat.P_V, mem_ofPred_eq, hW_v_split, hW_to_v_T₁,
                GraphWalk.mem_support_append, GraphWalk.mem_support_append,
                GraphWalk.mem_support_append]
              exact Or.inl (Or.inr (Or.inr hz₁))
            have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
              rw [dat.P_V, mem_ofPred_eq, hW_v_split, hW_to_v_T₁,
                GraphWalk.mem_support_append, GraphWalk.mem_support_append,
                GraphWalk.mem_support_append]
              exact Or.inl (Or.inr (Or.inr hz₂))
            exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hne)) hzP₁ hzP₂)
          (fun k₁ k₂ m z hzT hzR_tail => by
            obtain ⟨hzR, _⟩ := mem_tail_of_isSimple _ (hR₁_rad_simple k₂ m) hzR_tail
            rw [hR₁_tail_supp] at hzT
            rw [hR₁_rad_supp] at hzR
            have hk_eq : k₁ = k₂ := by
              by_contra hne
              have hzP₁ : z ∈ V(P (dat.σ k₁)) := by
                rw [dat.P_V, mem_ofPred_eq, hW_v_split, hW_to_v_T₁,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append]
                exact Or.inl (Or.inr (Or.inr hzT))
              have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
                rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨m.1, by omega⟩,
                  dat.R_adj_spec _ ⟨m.1, by omega⟩, GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inr (Or.inl hzR))
              exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hne)) hzP₁ hzP₂
            subst hk_eq
            rcases hT₁_supp_or (dat.σ k₁) z hzT with hzR_d1 | hzM
            · obtain ⟨hsucc, hzx, _⟩ := dat.R_adj_inter hC (dat.σ k₁)
                (q₁ := ⟨m.1, by omega⟩) (q₂ := q_d1) (Fin.mk_lt_mk.mpr m.2) hzR hzR_d1
              exact ⟨rfl, hsucc, hzx⟩
            · exfalso
              obtain ⟨R_m, hpre_eq⟩ := hpre_j_L_of_lt (dat.σ k₁)
                (show (⟨m.1 + 1, by omega⟩ : Fin s₀) < j_L from Fin.mk_lt_mk.mpr (by omega))
              have hz_pre : z ∈ (dat.W_pre (dat.σ k₁) j_L).support := by
                rw [hpre_eq, hW_pre_succ (dat.σ k₁) ⟨m.1, by omega⟩,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append]
                exact Or.inl (Or.inr (Or.inr hzR))
              have hnd : ((dat.W_pre (dat.σ k₁) j_L).support ++
                  (M_left (dat.σ k₁)).support.tail).Nodup := by
                have h' : (W_to_v (dat.σ k₁)).support.Nodup := hW_to_v_simple (dat.σ k₁)
                dsimp only [W_to_v] at h'
                rwa [GraphWalk.support_append] at h'
              rw [(M_left (dat.σ k₁)).support_eq_cons] at hzM
              rcases List.mem_cons.mp hzM with rfl | htail
              · rcases dat.R_adj_inter_C hC (dat.σ k₁) ⟨m.1, by omega⟩ j_L hzR
                  (dat.mem_mid_V_ends (dat.σ k₁) j_L).1.2 with ⟨hj_eq, _⟩ | ⟨hj_eq, _⟩
                · have := congrArg (fun x : Fin s₀ => x.1) hj_eq; dsimp [j_L] at this; omega
                · have := congrArg (fun x : Fin s₀ => x.1) hj_eq; dsimp [j_L] at this; omega
              · exact (List.nodup_append.mp hnd).2.2 z hz_pre z htail rfl)
      have hC₁_ne : C₁_contr.Nonempty := by
        apply hC₁_ne_imp ⟨i₀, length_pos_of_ne (R₁_tail i₀) ?_⟩
        intro heq
        have hu_C : u₁_tail i₀ ∈ V(C ⟨d - 1, by omega⟩) :=
          (dat.mem_mid_V_ends (dat.σ i₀) ⟨d - 1, by omega⟩).2.2
        have hd1_lt : d - 1 < d := Nat.sub_lt hd zero_lt_one
        exact disjoint_left.mp (hC_disj_X_outer ⟨d - 1, by omega⟩ hd1_lt)
          hu_C (heq ▸ hv_raw_X (dat.σ i₀))
      exact ⟨H₁', hH₁'_le, C₁_contr, hC₁_sub, fun ⟨_, hEmpty⟩ =>
        hC₁_ne.ne_empty hEmpty, φ₁, fun k => ⟨Set.mem_univ _, hφ₁_v k⟩⟩
    -- 2. Proper `r₀ × d` cylinder minor in `S.H₂` (inner side).
    have hmin₂ : IsProperMinorWithMap (cylinderGraph r₀ d) S.H₂ v
        (fun k => (k, ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩)) := by
      let j₂_emb : Fin d → Fin s₀ := fun j => ⟨s₀ - 1 - j.1, by omega⟩
      have hj₂_inj : Function.Injective j₂_emb := by
        intro a b h
        have hval := congrArg (fun x : Fin s₀ => x.1) h
        dsimp [j₂_emb] at hval
        exact Fin.ext (by omega)
      obtain ⟨hK₂_le, hK₂_conn, hK₂_disj, he₂_not_K, he₂_inj, he₂_link⟩ :=
        dat.circlePieces_of_emb hC j₂_emb hj₂_inj
          (fun j => (hC_le_H₂ (j₂_emb j) (by dsimp [j₂_emb]; omega)).2)
      let K₂ : Fin r₀ → Fin d → Graph α β := fun k j => dat.K_circ k (j₂_emb j)
      let e₂ : Fin r₀ → Fin d → β := fun k j => dat.e_circ k (j₂_emb j)
      let q₂ : Fin (d - 1) → Fin (s₀ - 1) := fun m => ⟨s₀ - 2 - m.1, by omega⟩
      let u₂_rad : Fin r₀ → Fin (d - 1) → α :=
        fun k m => dat.x (dat.σ k) ⟨(q₂ m).1 + 1, by omega⟩
      let w₂_rad : Fin r₀ → Fin (d - 1) → α :=
        fun k m => dat.y (dat.σ k) ⟨(q₂ m).1, by omega⟩
      have hRad₂_le : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          walkSubgraph (dat.R_adj (dat.σ k) (q₂ m)).reverse ≤ S.H₂ := by
        intro k m
        let i := dat.σ k
        obtain ⟨R_m, hpost_eq⟩ := dat.between_post i
          (show j_R < ⟨(q₂ m).1, by omega⟩ from Fin.mk_lt_mk.mpr (by dsimp [j_R, q₂]; omega))
        refine (walkSubgraph_mono_of_sub _ (W_from_v i).reverse ?_ ?_).trans (hW_from_v_rev_le_H₂ i)
        · intro z hz
          rw [GraphWalk.support_reverse, List.mem_reverse] at hz ⊢
          dsimp only [W_from_v]
          rw [hpost_eq, dat.R_adj_spec i (q₂ m), GraphWalk.mem_support_append,
            GraphWalk.mem_support_append, GraphWalk.mem_support_append,
            GraphWalk.mem_support_append]
          exact Or.inr (Or.inr (Or.inr (Or.inl hz)))
        · intro e he
          rw [GraphWalk.edges_reverse, List.mem_reverse] at he ⊢
          dsimp only [W_from_v]
          rw [hpost_eq, dat.R_adj_spec i (q₂ m), GraphWalk.edges_append,
            GraphWalk.edges_append, GraphWalk.edges_append, GraphWalk.edges_append]
          exact List.mem_append_right _ (List.mem_append_right _
            (List.mem_append_right _ (List.mem_append_left _ he)))
      have hex_R₂_rad : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          ∃ W' : GraphWalk S.H₂ (u₂_rad k m) (w₂_rad k m),
            W'.support = (dat.R_adj (dat.σ k) (q₂ m)).reverse.support ∧
            W'.edges = (dat.R_adj (dat.σ k) (q₂ m)).reverse.edges :=
        fun k m => liftWalkOfSubgraph _ (hRad₂_le k m)
      choose R₂_rad hR₂_rad_supp hR₂_rad_edges using hex_R₂_rad
      have hR₂_rad_simple : ∀ (k : Fin r₀) (m : Fin (d - 1)), (R₂_rad k m).IsSimple := by
        intro k m; unfold GraphWalk.IsSimple; rw [hR₂_rad_supp]
        exact (dat.R_adj_simple _ _).reverse
      -- Inner tail walk `(T₂_G_fwd i).reverse` from `dat.x i ⟨s₀ - d - 1 + 1, _⟩` to `v_raw i`.
      let q_R : Fin (s₀ - 1) := ⟨s₀ - d - 1, by omega⟩
      let T₂_G_fwd : ∀ i : Fin r₀, GraphWalk G (v_raw i) (dat.x i ⟨q_R.1 + 1, by omega⟩) :=
        fun i => (M_right i).append (dat.R_adj i q_R)
      have hW_from_v_T₂ : ∀ i : Fin r₀,
          W_from_v i = (T₂_G_fwd i).append
            ((dat.W_mid i ⟨q_R.1 + 1, by omega⟩).append
              (dat.W_post i ⟨q_R.1 + 1, by omega⟩)) := by
        intro i
        dsimp only [W_from_v, T₂_G_fwd]
        have hspec := dat.R_adj_spec i q_R
        change dat.W_post i j_R = _ at hspec
        rw [hspec, GraphWalk.append_assoc]
      have hT₂_simple : ∀ i : Fin r₀, (T₂_G_fwd i).reverse.IsSimple := fun i =>
        ((isSimple_of_append (hW_from_v_T₂ i ▸ hW_from_v_simple i)).1).reverse
      have hT₂_le : ∀ i : Fin r₀, walkSubgraph (T₂_G_fwd i).reverse ≤ S.H₂ := by
        intro i
        refine (walkSubgraph_mono_of_sub _ (W_from_v i).reverse ?_ ?_).trans (hW_from_v_rev_le_H₂ i)
        · intro z hz
          rw [GraphWalk.support_reverse, List.mem_reverse] at hz ⊢
          rw [hW_from_v_T₂ i, GraphWalk.mem_support_append]
          exact Or.inl hz
        · intro e he
          rw [GraphWalk.edges_reverse, List.mem_reverse] at he ⊢
          rw [hW_from_v_T₂ i, GraphWalk.edges_append]
          exact List.mem_append_left _ he
      let u₂_tail : Fin r₀ → α := fun k => dat.x (dat.σ k) ⟨q_R.1 + 1, by omega⟩
      have hex_R₂_tail : ∀ k : Fin r₀,
          ∃ W' : GraphWalk S.H₂ (u₂_tail k) (v k),
            W'.support = (T₂_G_fwd (dat.σ k)).reverse.support ∧
            W'.edges = (T₂_G_fwd (dat.σ k)).reverse.edges :=
        fun k => liftWalkOfSubgraph _ (hT₂_le (dat.σ k))
      choose R₂_tail hR₂_tail_supp hR₂_tail_edges using hex_R₂_tail
      have hR₂_tail_simple : ∀ k : Fin r₀, (R₂_tail k).IsSimple := by
        intro k; unfold GraphWalk.IsSimple; rw [hR₂_tail_supp]; exact hT₂_simple _
      have hu₂_rad_mem : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          u₂_rad k m ∈ V(K₂ k ⟨m.1, by omega⟩) := by
        intro k m
        have hj_eq : (⟨(q₂ m).1 + 1, by omega⟩ : Fin s₀) = j₂_emb ⟨m.1, by omega⟩ :=
          Fin.ext (by dsimp [q₂, j₂_emb]; omega)
        dsimp only [K₂]
        rw [← hj_eq]
        exact dat.inter_sub_K_circ k _ (dat.mem_mid_V_ends (dat.σ k) _).1
      have hw₂_rad_mem : ∀ (k : Fin r₀) (m : Fin (d - 1)),
          w₂_rad k m ∈ V(K₂ k ⟨m.1 + 1, by omega⟩) := by
        intro k m
        have hj_eq : (⟨(q₂ m).1, by omega⟩ : Fin s₀) = j₂_emb ⟨m.1 + 1, by omega⟩ :=
          Fin.ext (by dsimp [q₂, j₂_emb]; omega)
        dsimp only [K₂]
        rw [← hj_eq]
        exact dat.inter_sub_K_circ k _ (dat.mem_mid_V_ends (dat.σ k) _).2
      have hu₂_tail_mem : ∀ k : Fin r₀,
          u₂_tail k ∈ V(K₂ k ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩) := by
        intro k
        have hj_eq : (⟨q_R.1 + 1, by omega⟩ : Fin s₀) =
            j₂_emb ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩ :=
          Fin.ext (by dsimp [q_R, j₂_emb]; omega)
        dsimp only [K₂]
        rw [← hj_eq]
        exact dat.inter_sub_K_circ k _ (dat.mem_mid_V_ends (dat.σ k) _).1
      have hK₂_sub_C : ∀ (k' : Fin r₀) (j' : Fin d), V(K₂ k' j') ⊆ V(C (j₂_emb j')) :=
        fun k' j' => ((dat.K_circ_le k' (j₂_emb j')).trans deleteEdges_le).vertexSet_mono
      obtain ⟨H₂', hH₂'_le, C₂_contr, hC₂_sub, φ₂, hφ₂_v, hC₂_ne_imp⟩ :=
        exists_cylinder_contract_of_circle_pieces r₀ d hd K₂ e₂
          hK₂_le hK₂_conn (fun h => hK₂_disj h) he₂_not_K (fun h => he₂_inj h) he₂_link
          u₂_rad w₂_rad R₂_rad hR₂_rad_simple hu₂_rad_mem hw₂_rad_mem
          (fun k m k' j' z hzR hzK => by
            rw [hR₂_rad_supp, GraphWalk.support_reverse, List.mem_reverse] at hzR
            rcases dat.R_adj_inter_C hC (dat.σ k) (q₂ m) (j₂_emb j') hzR
              (hK₂_sub_C k' j' hzK) with ⟨hj_eq, hzy⟩ | ⟨hj_eq, hzx⟩
            · have hm1_lt : m.1 + 1 < d := by have := m.2; omega
              have hval : s₀ - 1 - j'.1 = s₀ - 2 - m.1 := congrArg Fin.val hj_eq
              have hj' : j' = ⟨m.1 + 1, hm1_lt⟩ := Fin.ext (by
                change j'.1 = m.1 + 1
                have := j'.2; have := m.2; dsimp [d] at *; omega)
              have hzw : z = w₂_rad k m := hzy
              have hk' : k' = k := by
                by_contra hne
                exact disjoint_left.mp (hK₂_disj (fun h => hne (congrArg Prod.fst h)))
                  (hj' ▸ hzK) (hzw ▸ hw₂_rad_mem k m)
              exact Or.inr ⟨hk', hj', hzw⟩
            · have hm_lt : m.1 < d := by have := m.2; omega
              have hval : s₀ - 1 - j'.1 = (s₀ - 2 - m.1) + 1 := congrArg Fin.val hj_eq
              have hj' : j' = ⟨m.1, hm_lt⟩ := Fin.ext (by
                change j'.1 = m.1
                have := j'.2; have := m.2; dsimp [d] at *; omega)
              have hzu : z = u₂_rad k m := hzx
              have hk' : k' = k := by
                by_contra hne
                exact disjoint_left.mp (hK₂_disj (fun h => hne (congrArg Prod.fst h)))
                  (hj' ▸ hzK) (hzu ▸ hu₂_rad_mem k m)
              exact Or.inl ⟨hk', hj', hzu⟩)
          (fun {k₁ k₂ m₁ m₂} hne => by
            refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
            obtain ⟨hz₁_s, hz₁_ne⟩ := mem_tail_of_isSimple _ (hR₂_rad_simple k₁ m₁) hz₁
            obtain ⟨hz₂_s, hz₂_ne⟩ := mem_tail_of_isSimple _ (hR₂_rad_simple k₂ m₂) hz₂
            rw [hR₂_rad_supp, GraphWalk.support_reverse, List.mem_reverse] at hz₁_s hz₂_s
            by_cases hk : k₁ = k₂
            · subst hk
              have hm_ne : m₁.1 ≠ m₂.1 := fun h => hne (Prod.ext rfl (Fin.ext h))
              rcases lt_trichotomy (q₂ m₁).1 (q₂ m₂).1 with hlt | heq | hgt
              · obtain ⟨_, hzx, _⟩ := dat.R_adj_inter hC (dat.σ k₁)
                  (Fin.mk_lt_mk.mpr hlt) hz₁_s hz₂_s
                exact hz₁_ne hzx
              · dsimp [q₂] at heq; omega
              · obtain ⟨_, hzx, _⟩ := dat.R_adj_inter hC (dat.σ k₁)
                  (Fin.mk_lt_mk.mpr hgt) hz₂_s hz₁_s
                exact hz₂_ne hzx
            · have hzP₁ : z ∈ V(P (dat.σ k₁)) := by
                rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨(q₂ m₁).1, by omega⟩,
                  dat.R_adj_spec _ (q₂ m₁), GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inr (Or.inl hz₁_s))
              have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
                rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨(q₂ m₂).1, by omega⟩,
                  dat.R_adj_spec _ (q₂ m₂), GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inr (Or.inl hz₂_s))
              exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hk)) hzP₁ hzP₂)
          u₂_tail v R₂_tail hR₂_tail_simple hu₂_tail_mem
          (fun k k' j' z hzT hzK => by
            rw [hR₂_tail_supp, GraphWalk.support_reverse, List.mem_reverse] at hzT
            dsimp only [T₂_G_fwd] at hzT
            rw [GraphWalk.mem_support_append] at hzT
            have hzC : z ∈ V(C (j₂_emb j')) := hK₂_sub_C k' j' hzK
            rcases hzT with hzM | hzR
            · exfalso
              have hz_sp : z ∈ (W_span (dat.σ k)).support := by
                rw [hM_split, GraphWalk.mem_support_append]; exact Or.inr hzM
              exact disjoint_left.mp
                (hspan_disj_inner (dat.σ k) (j₂_emb j') (by dsimp [j₂_emb]; omega)) hz_sp hzC
            · rcases dat.R_adj_inter_C hC (dat.σ k) q_R (j₂_emb j') hzR hzC with
                ⟨hj_eq, _⟩ | ⟨hj_eq, hzx⟩
              · exfalso
                have := congrArg (fun x : Fin s₀ => x.1) hj_eq
                have := j'.2
                dsimp [j₂_emb, q_R, d] at *
                omega
              · have hj' : j' = ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩ := Fin.ext (by
                  change j'.1 = d - 1
                  have hval : s₀ - 1 - j'.1 = (s₀ - d - 1) + 1 := congrArg Fin.val hj_eq
                  have := j'.2
                  dsimp [d] at *
                  omega)
                have hzu : z = u₂_tail k := hzx
                have hk' : k' = k := by
                  by_contra hne
                  exact disjoint_left.mp (hK₂_disj (fun h => hne (congrArg Prod.fst h)))
                    (hj' ▸ hzK) (hzu ▸ hu₂_tail_mem k)
                exact ⟨hk', hj', hzu⟩)
          (fun {k₁ k₂} hne => by
            refine disjoint_left.mpr fun z hz₁ hz₂ => ?_
            change z ∈ (R₂_tail k₁).support at hz₁
            change z ∈ (R₂_tail k₂).support at hz₂
            rw [hR₂_tail_supp, GraphWalk.support_reverse, List.mem_reverse] at hz₁
            rw [hR₂_tail_supp, GraphWalk.support_reverse, List.mem_reverse] at hz₂
            have hzP₁ : z ∈ V(P (dat.σ k₁)) := by
              rw [dat.P_V, mem_ofPred_eq, hW_v_split, GraphWalk.mem_support_append]
              right
              rw [hW_from_v_T₂, GraphWalk.mem_support_append]
              exact Or.inl hz₁
            have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
              rw [dat.P_V, mem_ofPred_eq, hW_v_split, GraphWalk.mem_support_append]
              right
              rw [hW_from_v_T₂, GraphWalk.mem_support_append]
              exact Or.inl hz₂
            exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hne)) hzP₁ hzP₂)
          (fun k₁ k₂ m z hzT hzR_tail => by
            obtain ⟨hzR, _⟩ := mem_tail_of_isSimple _ (hR₂_rad_simple k₂ m) hzR_tail
            rw [hR₂_tail_supp, GraphWalk.support_reverse, List.mem_reverse] at hzT
            rw [hR₂_rad_supp, GraphWalk.support_reverse, List.mem_reverse] at hzR
            have hk_eq : k₁ = k₂ := by
              by_contra hne
              have hzP₁ : z ∈ V(P (dat.σ k₁)) := by
                rw [dat.P_V, mem_ofPred_eq, hW_v_split, GraphWalk.mem_support_append]
                right
                rw [hW_from_v_T₂, GraphWalk.mem_support_append]
                exact Or.inl hzT
              have hzP₂ : z ∈ V(P (dat.σ k₂)) := by
                rw [dat.P_V, mem_ofPred_eq, dat.W_split _ ⟨(q₂ m).1, by omega⟩,
                  dat.R_adj_spec _ (q₂ m), GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inr (Or.inl hzR))
              exact disjoint_left.mp (hP_disj (dat.σ.injective.ne hne)) hzP₁ hzP₂
            subst hk_eq
            dsimp only [T₂_G_fwd] at hzT
            rw [GraphWalk.mem_support_append] at hzT
            rcases hzT with hzM | hzR_qR
            · exfalso
              obtain ⟨R_m, hpost_eq⟩ := dat.between_post (dat.σ k₁)
                (show j_R < ⟨(q₂ m).1, by omega⟩ from
                  Fin.mk_lt_mk.mpr (by have := m.2; change s₀ - d - 1 < s₀ - 2 - m.1; omega))
              have hz_post : z ∈ (dat.W_post (dat.σ k₁) j_R).support := by
                rw [hpost_eq, dat.R_adj_spec _ (q₂ m), GraphWalk.mem_support_append,
                  GraphWalk.mem_support_append, GraphWalk.mem_support_append]
                exact Or.inr (Or.inr (Or.inl hzR))
              have hnd : ((M_right (dat.σ k₁)).support ++
                  (dat.W_post (dat.σ k₁) j_R).support.tail).Nodup := by
                have h' : (W_from_v (dat.σ k₁)).support.Nodup := hW_from_v_simple (dat.σ k₁)
                dsimp only [W_from_v] at h'
                rwa [GraphWalk.support_append] at h'
              rw [(dat.W_post (dat.σ k₁) j_R).support_eq_cons] at hz_post
              rcases List.mem_cons.mp hz_post with rfl | htail
              · rcases dat.R_adj_inter_C hC (dat.σ k₁) (q₂ m) j_R hzR
                  (dat.mem_mid_V_ends (dat.σ k₁) j_R).2.2 with ⟨hj_eq, _⟩ | ⟨hj_eq, _⟩
                · have := congrArg (fun x : Fin s₀ => x.1) hj_eq
                  have := m.2; dsimp [j_R, q₂, d] at *; omega
                · have := congrArg (fun x : Fin s₀ => x.1) hj_eq
                  have := m.2; dsimp [j_R, q₂, d] at *; omega
              · exact (List.nodup_append.mp hnd).2.2 z hzM z htail rfl
            · have hlt_q : q_R < q₂ m :=
                Fin.mk_lt_mk.mpr (by have := m.2; change s₀ - d - 1 < s₀ - 2 - m.1; omega)
              obtain ⟨hsucc, _, hzy⟩ := dat.R_adj_inter hC (dat.σ k₁) hlt_q hzR_qR hzR
              have hsucc' : (s₀ - d - 1) + 1 = s₀ - 2 - m.1 := hsucc
              have := m.2
              exact ⟨rfl, by omega, hzy⟩)
      have hC₂_ne : C₂_contr.Nonempty := by
        apply hC₂_ne_imp ⟨i₀, length_pos_of_ne (R₂_tail i₀) ?_⟩
        intro heq
        have hu_C : u₂_tail i₀ ∈ V(C ⟨q_R.1 + 1, by omega⟩) :=
          (dat.mem_mid_V_ends (dat.σ i₀) ⟨q_R.1 + 1, by omega⟩).1.2
        exact disjoint_left.mp
          (hC_disj_X_inner ⟨q_R.1 + 1, by omega⟩ (by dsimp [q_R]; omega))
          hu_C (heq ▸ hv_raw_X (dat.σ i₀))
      exact ⟨H₂', hH₂'_le, C₂_contr, hC₂_sub, fun ⟨_, hEmpty⟩ =>
        hC₂_ne.ne_empty hEmpty, φ₂, fun k => ⟨Set.mem_univ _, hφ₂_v k⟩⟩
    -- Assemble planar sleeve union from `hmin₁` and `hmin₂`.
    have hcast_min : ∀ {s' : ℕ} (hs' : 0 < s'), s' = d → ∀ {H : Graph α β},
        IsProperMinorWithMap (cylinderGraph r₀ d) H v
          (fun k => (k, ⟨d - 1, Nat.sub_lt hd zero_lt_one⟩)) →
        IsProperMinorWithMap (cylinderGraph r₀ s') H v
          (fun i => (i, ⟨s' - 1, Nat.sub_lt hs' zero_lt_one⟩)) := by
      rintro _ _ rfl _ h
      exact h
    exact isExpressibleAsPlanarSleeveUnion_of_sep M v hv_inj S.isSep hinter_S
      (hcast_min (Nat.le_max_left 1 _) hs_max_eq hmin₂)
      (hcast_min (Nat.le_max_left 1 _) hs_max_eq hmin₁)
  · -- Degenerate case `r₀ = 0`: `X = ∅`, `s = 1`, `cylinderGraph 0 1` is empty, both sides nonempty.
    have hr0 : r₀ = 0 := Nat.eq_zero_of_not_pos hr₀
    subst hr0
    have hX_empty : X = ∅ :=
      (Set.ncard_eq_zero (hs := hX_fin)).mp (Nat.eq_zero_of_le_zero hXcard)
    subst hX_empty
    let j₀ : Fin s₀ := ⟨0, hs₀_pos⟩
    let j_last : Fin s₀ := ⟨s₀ - 1, Nat.sub_lt hs₀_pos zero_lt_one⟩
    have hdisj₀ : Disjoint V(C j₀) (∅ : Set α) := disjoint_left.mpr fun _ _ h => h
    have hdisj_last : Disjoint V(C j_last) (∅ : Set α) := disjoint_left.mpr fun _ _ h => h
    let S := buildSepSplitData hXV (hC.1 j₀).1.vertexSet_mono (hC.1 j_last).1.vertexSet_mono
      hdisj₀ hdisj_last hXsep
    have hinter_S : V(S.H₁) ∩ V(S.H₂) = Set.range (Fin.elim0 : Fin 0 → α) := by
      rw [S.inter_eq]
      ext x
      exact ⟨False.elim, fun ⟨i, _⟩ => Fin.elim0 i⟩
    have hVc : V(cylinderGraph 0 1) = ∅ :=
      eq_empty_of_forall_notMem fun p _ => Fin.elim0 p.1
    have hEc : E(cylinderGraph 0 1) = ∅ := by
      refine eq_empty_of_forall_notMem fun e _ => ?_
      rcases e with p | p <;> exact Fin.elim0 p.1
    have hproper_empty_minor : ∀ {H : Graph α β}, V(H).Nonempty →
        IsProperMinorWithMap (cylinderGraph 0 1) H Fin.elim0
          (fun i => (i, ⟨0, zero_lt_one⟩)) := by
      intro H ⟨z₀, hz₀⟩
      let H' : Graph α β := H.induce ∅
      have hH'_le : H' ≤ H := H.induce_le (empty_subset _)
      have hVH' : V(H') = ∅ := by simp [H']
      have hEH' : E(H') = ∅ := by
        refine eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨x, _, hl⟩ := H'.exists_isLink_of_mem_edgeSet he
        have hx := hl.left_mem
        rw [hVH'] at hx
        exact hx
      have hVcH : V(contract H' (∅ : Set β)) = ∅ := by
        refine eq_empty_of_forall_notMem fun _ ⟨x, hx, _⟩ => ?_
        rw [hVH'] at hx; exact hx
      have hEcH : E(contract H' (∅ : Set β)) = ∅ := by
        refine eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨_, _, hl⟩ := (contract H' (∅ : Set β)).exists_isLink_of_mem_edgeSet he
        obtain ⟨⟨x, _, hlx, _, _⟩, _⟩ := hl
        have hx := hlx.left_mem
        rw [hVH'] at hx; exact hx
      obtain ⟨φ⟩ := isoOfEmpty (cylinderGraph 0 1) (contract H' (∅ : Set β)) hVc hEc hVcH hEcH
      have hne_H : H' ≠ H := by
        intro heq
        have hz₀' : z₀ ∈ V(H') := heq ▸ hz₀
        rw [hVH'] at hz₀'
        exact hz₀'
      exact ⟨H', hH'_le, ∅, empty_subset _, fun ⟨h, _⟩ => hne_H h, φ, fun i => Fin.elim0 i⟩
    obtain ⟨_, u₀, W₀, _, _, hVC₀, _⟩ := hC.1 j₀
    have hu₀_H₁ : u₀ ∈ V(S.H₁) := by
      rw [S.V_H₁]
      exact Or.inl (S.A_sub (by rw [hVC₀]; exact W₀.start_mem_support))
    obtain ⟨_, u_last, W_last, _, _, hVClast, _⟩ := hC.1 j_last
    have hu_last_H₂ : u_last ∈ V(S.H₂) := by
      rw [S.V_H₂]
      exact Or.inl (S.B_sub (by rw [hVClast]; exact W_last.start_mem_support))
    exact isExpressibleAsPlanarSleeveUnion_of_sep M Fin.elim0 (fun i => Fin.elim0 i)
      S.isSep hinter_S
      (hproper_empty_minor ⟨u_last, hu_last_H₂⟩)
      (hproper_empty_minor ⟨u₀, hu₀_H₁⟩)

end GraphMinor.GM03
end
