module

public import GraphMinor.GM03.Defs
public import GraphMinor.Minor.Model
public import GraphMinor.GM09.Basic
import GraphMinor.GM03.Section4a
import GraphMinor.GM03.Section4b

/-!
# Graph Minors III, Section 4 Helpers: Cylinder Minor Contraction Model

This file proves the unified contraction lemma `exists_cylinder_contract_of_circle_pieces`: given a
graph `H`, pairwise vertex-disjoint connected circle pieces `K_circ k j ≤ H` joined in cyclic order
by circular edges `e_circ k j`, simple radial walks `R_rad k m` between consecutive circles, and
simple tail walks `R_tail k` from the central circle to target vertices `v k`, contracting each
connected branch subgraph yields `contract H' C_contr` isomorphic to `cylinderGraph r s` with
`v k` in the contracted central-circle branch set `(k, s - 1)`. This serves both the sleeve-union
construction in Graph Minors III, (4.3) (page 61) and the cylinder minor step in (4.5) (page 62).
-/

public section

namespace GraphMinor.GM03

open Set Function Relation Classical
open Graph GraphMinor GraphMinor.Surface GraphMinor.GM09

universe u v

variable {α : Type u} {β : Type v}

private lemma not_isLink_self_of_mem_edges_of_isSimple {H : Graph α β} {p q : α}
    (W : GraphWalk H p q) (hs : W.IsSimple) {e : β} (he : e ∈ W.edges)
    {u : α} (hl : H.IsLink e u u) : False := by
  induction W with
  | nil _ => cases he
  | @cons a b c e' hl' W' ih =>
    have hnd := List.nodup_cons.mp hs
    rcases List.mem_cons.mp he with rfl | he'
    · have ha : a = u := (hl'.left_eq_or_eq hl).elim id id
      have hb : b = u := (hl'.symm.left_eq_or_eq hl).elim id id
      exact hnd.1 (ha.trans hb.symm ▸ W'.start_mem_support)
    · exact ih hnd.2 he'

/-- Explicit minor-to-contraction construction with prescribed connected branch subgraphs `B`,
recording the exact contracted vertex sets `(φ.vertexEquiv p).1 = V(B p.1)` and the
contracted edge set `⋃ p ∈ V(G₀), E(B p)`. -/
private theorem exists_contract_iso_of_explicit_model {α' β' : Type*}
    {G₀ : Graph α' β'} {H : Graph α β}
    {B : α' → Graph α β} {ηe : β' → β}
    (hmodel : IsMinorModel G₀ H (fun p => V(B p)) ηe)
    (hB_le : ∀ p ∈ V(G₀), B p ≤ H.deleteEdges (ηe '' E(G₀)))
    (hB_conn : ∀ p ∈ V(G₀), GraphConnected (B p)) :
    ∃ (H' : Graph α β) (_ : H' ≤ H) (C_contr : Set β) (_ : C_contr ⊆ E(H'))
      (φ : Iso G₀ (contract H' C_contr)),
      (∀ (p : α') (hp : p ∈ V(G₀)), (φ.vertexEquiv ⟨p, hp⟩).1 = V(B p)) ∧
      C_contr = ⋃ p ∈ V(G₀), E(B p) := by
  let ηv : α' → Set α := fun p => V(B p)
  let C_contr : Set β := ⋃ p ∈ V(G₀), E(B p)
  let H' : Graph α β := (H.induce (⋃ p ∈ V(G₀), ηv p)).restrict (ηe '' E(G₀) ∪ C_contr)
  have hB_le_H : ∀ {p : α'}, p ∈ V(G₀) → B p ≤ H :=
    fun hp => (hB_le _ hp).trans deleteEdges_le
  have hH'_le : H' ≤ H :=
    restrict_le.trans (H.induce_le (iUnion₂_subset hmodel.vertex_subset))
  have hC_sub : C_contr ⊆ E(H') := by
    rintro e ⟨_, ⟨p, rfl⟩, _, ⟨hp, rfl⟩, he⟩
    obtain ⟨x, y, hl⟩ := (B p).exists_isLink_of_mem_edgeSet he
    have hlH : H.IsLink e x y := hl.mono (hB_le_H hp)
    have hxU : x ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion hp hl.left_mem
    have hyU : y ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion hp hl.right_mem
    exact ⟨⟨x, y, hlH, hxU, hyU⟩, Or.inr (mem_iUnion₂_of_mem hp he)⟩
  have himg_sub : ηe '' E(G₀) ⊆ E(H') := by
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨u, w, huw⟩ := G₀.exists_isLink_of_mem_edgeSet he
    obtain ⟨x, hx, y, hy⟩ := (hmodel.inc_iff u huw.left_mem e he).1 huw.inc_left
    have hxU : x ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion huw.left_mem hx
    have hyU : y ∈ ⋃ q ∈ V(G₀), ηv q := by
      by_cases hloop : G₀.IsLoopAt e u
      · exact mem_biUnion huw.left_mem
          ((hmodel.isLoopAt_iff u huw.left_mem e he).1 hloop y hy.inc_right)
      · have huw_ne : u ≠ w := fun h' => hloop (h' ▸ huw)
        obtain ⟨z, hz, hincz⟩ := (hmodel.inc_iff w huw.right_mem e he).1 huw.inc_right
        have hxz : x ≠ z :=
          (hmodel.vertex_disjoint u huw.left_mem w huw.right_mem huw_ne).ne_of_mem hx hz
        have hzy : z = y := hincz.eq_of_isLink_of_ne_left hy hxz.symm
        exact mem_biUnion huw.right_mem (hzy ▸ hz)
    exact ⟨⟨x, y, hy, hxU, hyU⟩, Or.inl (mem_image_of_mem ηe he)⟩
  have hdisj_img_C : Disjoint (ηe '' E(G₀)) C_contr := by
    rw [Set.disjoint_left]
    rintro _ ⟨e, he, rfl⟩ ⟨_, ⟨p, rfl⟩, _, ⟨hp, rfl⟩, heB⟩
    exact ((hB_le p hp).edgeSet_mono heB).2 (mem_image_of_mem ηe he)
  have hE_contract : E(contract H' C_contr) = ηe '' E(G₀) := by
    change E(H') \ C_contr = ηe '' E(G₀)
    apply Subset.antisymm
    · rintro e ⟨⟨_, he | he⟩, heC⟩
      · exact he
      · exact absurd he heC
    · intro e he
      exact ⟨himg_sub he, hdisj_img_C.notMem_of_mem_left he⟩
  let compOf : α → Set α :=
    fun x => {y | ReflTransGen (fun a b => ∃ e ∈ C_contr, H'.IsLink e a b) x y}
  have hcomp_eq : ∀ {p : α'} (hp : p ∈ V(G₀)) {x : α}, x ∈ ηv p → compOf x = ηv p := by
    intro p hp x hx
    ext y
    simp only [compOf, mem_ofPred_eq]
    constructor
    · intro hxy
      induction hxy with
      | refl => exact hx
      | @tail a b _ hab ih =>
        obtain ⟨e, ⟨_, ⟨q, rfl⟩, _, ⟨hq, rfl⟩, heB⟩, hl⟩ := hab
        have hlB : (B q).IsLink e a b :=
          ((hB_le_H hq).isLink_iff heB).2 (hl.mono hH'_le)
        by_cases hpq : p = q
        · exact hpq ▸ hlB.right_mem
        · exact absurd hlB.left_mem
            ((hmodel.vertex_disjoint p hp q hq hpq).notMem_of_mem_left ih)
    · intro hy
      have hconn := (hB_conn p hp).2 x hx y hy
      induction hconn with
      | refl => exact .refl
      | @tail a b _ hab ih =>
        obtain ⟨e, hlB⟩ := hab
        have heC : e ∈ C_contr := mem_iUnion₂_of_mem hp hlB.edge_mem
        have hlH : H.IsLink e a b := hlB.mono (hB_le_H hp)
        have haU : a ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion hp hlB.left_mem
        have hbU : b ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion hp hlB.right_mem
        exact (ih hlB.left_mem).tail ⟨e, heC, Or.inr heC, hlH, haU, hbU⟩
  have hV_contract : V(contract H' C_contr) = ηv '' V(G₀) := by
    change compOf '' (⋃ p ∈ V(G₀), ηv p) = ηv '' V(G₀)
    ext X
    simp only [mem_image, mem_iUnion]
    constructor
    · rintro ⟨x, ⟨p, hp, hx⟩, rfl⟩
      exact ⟨p, hp, (hcomp_eq hp hx).symm⟩
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨x, hx⟩ := hmodel.vertex_nonempty p hp
      exact ⟨x, ⟨p, hp, hx⟩, hcomp_eq hp hx⟩
  have hηv_inj : InjOn ηv V(G₀) := by
    intro p₁ hp₁ p₂ hp₂ heq
    by_contra hne
    obtain ⟨x, hx⟩ := hmodel.vertex_nonempty p₁ hp₁
    have hx₂ : x ∈ ηv p₂ := heq ▸ hx
    exact (hmodel.vertex_disjoint p₁ hp₁ p₂ hp₂ hne).notMem_of_mem_left hx hx₂
  have hisLink_iff : ∀ {e : β'} (he : e ∈ E(G₀)) {u w : α'} (hu : u ∈ V(G₀)) (hw : w ∈ V(G₀)),
      G₀.IsLink e u w ↔ (contract H' C_contr).IsLink (ηe e) (ηv u) (ηv w) := by
    intro e he u w hu hw
    simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map]
    constructor
    · intro hl
      have heC : ηe e ∉ C_contr :=
        hdisj_img_C.notMem_of_mem_left (mem_image_of_mem ηe he)
      refine ⟨?_, heC⟩
      obtain ⟨x, hx, y, hy⟩ := (hmodel.inc_iff u hu e he).1 hl.inc_left
      have hxU : x ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion hu hx
      by_cases hloop : G₀.IsLoopAt e u
      · have huw : u = w := hloop.eq_of_inc hl.inc_right
        subst huw
        have hy_u : y ∈ ηv u := (hmodel.isLoopAt_iff u hu e he).1 hloop y hy.inc_right
        have hyU : y ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion hu hy_u
        have hlM : H'.IsLink (ηe e) x y :=
          ⟨Or.inl (mem_image_of_mem ηe he), hy, hxU, hyU⟩
        exact ⟨x, y, hlM, hcomp_eq hu hx, hcomp_eq hu hy_u⟩
      · have huw_ne : u ≠ w := fun h' => hloop (h' ▸ hl)
        obtain ⟨z, hz, hincz⟩ := (hmodel.inc_iff w hw e he).1 hl.inc_right
        have hxz : x ≠ z := (hmodel.vertex_disjoint u hu w hw huw_ne).ne_of_mem hx hz
        have hzy : z = y := hincz.eq_of_isLink_of_ne_left hy hxz.symm
        have hy_w : y ∈ ηv w := hzy ▸ hz
        have hyU : y ∈ ⋃ q ∈ V(G₀), ηv q := mem_biUnion hw hy_w
        have hlM : H'.IsLink (ηe e) x y :=
          ⟨Or.inl (mem_image_of_mem ηe he), hy, hxU, hyU⟩
        exact ⟨x, y, hlM, hcomp_eq hu hx, hcomp_eq hw hy_w⟩
    · rintro ⟨⟨x, y, hlM, hcx, hcy⟩, _⟩
      have hlH : H.IsLink (ηe e) x y := hlM.mono hH'_le
      obtain ⟨p₁, hp₁, hx₁⟩ := mem_iUnion₂.1 hlM.left_mem
      obtain ⟨p₂, hp₂, hy₂⟩ := mem_iUnion₂.1 hlM.right_mem
      have hpu : p₁ = u := hηv_inj hp₁ hu ((hcomp_eq hp₁ hx₁).symm.trans hcx)
      have hpw : p₂ = w := hηv_inj hp₂ hw ((hcomp_eq hp₂ hy₂).symm.trans hcy)
      have hx_u : x ∈ ηv u := hpu ▸ hx₁
      have hy_w : y ∈ ηv w := hpw ▸ hy₂
      have hinc_u : G₀.Inc e u := (hmodel.inc_iff u hu e he).2 ⟨x, hx_u, hlH.inc_left⟩
      have hinc_w : G₀.Inc e w := (hmodel.inc_iff w hw e he).2 ⟨y, hy_w, hlH.inc_right⟩
      rw [isLink_iff_inc]
      refine ⟨hinc_u, hinc_w, fun z hz => ?_⟩
      obtain ⟨a, ha_z, hinc_a⟩ := (hmodel.inc_iff z hz.vertex_mem e he).1 hz
      rcases hinc_a.eq_or_eq_of_isLink hlH with rfl | rfl
      · left
        by_contra hzu
        exact (hmodel.vertex_disjoint z hz.vertex_mem u hu hzu).notMem_of_mem_left ha_z hx_u
      · right
        by_contra hzw
        exact (hmodel.vertex_disjoint z hz.vertex_mem w hw hzw).notMem_of_mem_left ha_z hy_w
  let φ : Iso G₀ (contract H' C_contr) :=
    { vertexEquiv :=
        (Equiv.Set.imageOfInjOn ηv V(G₀) hηv_inj).trans
          (Equiv.subtypeEquivRight fun _ => by rw [hV_contract])
      edgeEquiv :=
        (Equiv.Set.imageOfInjOn ηe E(G₀) hmodel.edge_injOn).trans
          (Equiv.subtypeEquivRight fun _ => by rw [hE_contract])
      isLink_iff := fun ⟨e, he⟩ ⟨u, hu⟩ ⟨w, hw⟩ => hisLink_iff he hu hw }
  exact ⟨H', hH'_le, C_contr, hC_sub, φ, fun _ _ => rfl, rfl⟩

/-- Unified minor-contraction construction for `cylinderGraph r s` from pairwise vertex-disjoint
connected circle pieces `K_circ k j ≤ H`, circular edges `e_circ k j`, simple radial walks
`R_rad k m`, and simple tail walks `R_tail k` at the central circle `s - 1`. -/
theorem exists_cylinder_contract_of_circle_pieces {H : Graph α β}
    (r s : ℕ) (hs : 0 < s)
    (K_circ : Fin r → Fin s → Graph α β)
    (e_circ : Fin r → Fin s → β)
    (hK_le : ∀ (k : Fin r) (j : Fin s), K_circ k j ≤ H)
    (hK_conn : ∀ (k : Fin r) (j : Fin s), GraphConnected (K_circ k j))
    (hK_disj : ∀ {k₁ k₂ : Fin r} {j₁ j₂ : Fin s}, (k₁, j₁) ≠ (k₂, j₂) →
      Disjoint V(K_circ k₁ j₁) V(K_circ k₂ j₂))
    (he_circ_not_K : ∀ (m : Fin r) (j₀ : Fin s) (k : Fin r) (j : Fin s),
      e_circ m j₀ ∉ E(K_circ k j))
    (he_circ_inj : ∀ {k₁ k₂ : Fin r} {j₁ j₂ : Fin s},
      e_circ k₁ j₁ = e_circ k₂ j₂ → k₁ = k₂ ∧ j₁ = j₂)
    (he_circ_link : ∀ (k : Fin r) (j : Fin s),
      ∃ u ∈ V(K_circ k j), ∃ w ∈ V(K_circ (nextSpoke k) j), H.IsLink (e_circ k j) u w)
    (u_rad w_rad : Fin r → Fin (s - 1) → α)
    (R_rad : ∀ (k : Fin r) (m : Fin (s - 1)), GraphWalk H (u_rad k m) (w_rad k m))
    (hR_rad_simple : ∀ (k : Fin r) (m : Fin (s - 1)), (R_rad k m).IsSimple)
    (hu_rad_mem : ∀ (k : Fin r) (m : Fin (s - 1)),
      u_rad k m ∈ V(K_circ k ⟨m.1, by omega⟩))
    (hw_rad_mem : ∀ (k : Fin r) (m : Fin (s - 1)),
      w_rad k m ∈ V(K_circ k ⟨m.1 + 1, by omega⟩))
    (hR_rad_inter_K : ∀ (k : Fin r) (m : Fin (s - 1)) (k' : Fin r) (j' : Fin s) {z : α},
      z ∈ (R_rad k m).support → z ∈ V(K_circ k' j') →
        (k' = k ∧ j' = ⟨m.1, by omega⟩ ∧ z = u_rad k m) ∨
        (k' = k ∧ j' = ⟨m.1 + 1, by omega⟩ ∧ z = w_rad k m))
    (hR_rad_disj : ∀ {k₁ k₂ : Fin r} {m₁ m₂ : Fin (s - 1)}, (k₁, m₁) ≠ (k₂, m₂) →
      Disjoint {z | z ∈ (R_rad k₁ m₁).support.tail} {z | z ∈ (R_rad k₂ m₂).support.tail})
    (u_tail v : Fin r → α)
    (R_tail : ∀ k : Fin r, GraphWalk H (u_tail k) (v k))
    (hR_tail_simple : ∀ k : Fin r, (R_tail k).IsSimple)
    (hu_tail_mem : ∀ k : Fin r,
      u_tail k ∈ V(K_circ k ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩))
    (hR_tail_inter_K : ∀ (k k' : Fin r) (j' : Fin s) {z : α},
      z ∈ (R_tail k).support → z ∈ V(K_circ k' j') →
        k' = k ∧ j' = ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ ∧ z = u_tail k)
    (hR_tail_disj : ∀ {k₁ k₂ : Fin r}, k₁ ≠ k₂ →
      Disjoint {z | z ∈ (R_tail k₁).support} {z | z ∈ (R_tail k₂).support})
    (hR_tail_rad : ∀ (k₁ k₂ : Fin r) (m : Fin (s - 1)) {z : α},
      z ∈ (R_tail k₁).support → z ∈ (R_rad k₂ m).support.tail →
        k₁ = k₂ ∧ m.1 + 1 = s - 1 ∧ z = w_rad k₂ m) :
    ∃ (H' : Graph α β) (_ : H' ≤ H) (C_contr : Set β) (_ : C_contr ⊆ E(H'))
      (φ : Iso (cylinderGraph r s) (contract H' C_contr)),
      (∀ k : Fin r,
        v k ∈ (φ.vertexEquiv ⟨(k, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩), Set.mem_univ _⟩).1) ∧
      ((∃ k₀ : Fin r, 0 < (R_tail k₀).length) → C_contr.Nonempty) := by
  -- Peel the first edge `e_rad k m` of each radial walk `R_rad k m`.
  have hex_rad_cons : ∀ (k : Fin r) (m : Fin (s - 1)),
      ∃ (z : α) (e : β) (hl : H.IsLink e (u_rad k m) z) (R_rest : GraphWalk H z (w_rad k m)),
        R_rad k m = .cons hl R_rest := by
    intro k m
    have hne : u_rad k m ≠ w_rad k m := by
      intro heq
      have hdisj := hK_disj (k₁ := k) (k₂ := k)
        (j₁ := ⟨m.1, by omega⟩) (j₂ := ⟨m.1 + 1, by omega⟩)
        (fun h => by have := congrArg (fun p => p.2.1) h; dsimp at this; omega)
      exact Set.disjoint_left.mp hdisj (hu_rad_mem k m) (heq ▸ hw_rad_mem k m)
    have hcons : ∀ {p q : α} (V : GraphWalk H p q), p ≠ q →
        ∃ (z : α) (e : β) (hl : H.IsLink e p z) (R_rest : GraphWalk H z q),
          V = .cons hl R_rest := by
      intro p q V hpq
      cases V with
      | nil _ => exact (hpq rfl).elim
      | cons hl R_rest => exact ⟨_, _, hl, R_rest, rfl⟩
    exact hcons (R_rad k m) hne
  choose z_rad e_rad hl_rad R_rest hR_rad_eq using hex_rad_cons
  have hR_rest_supp : ∀ (k : Fin r) (m : Fin (s - 1)),
      (R_rest k m).support = (R_rad k m).support.tail := by
    intro k m
    rw [hR_rad_eq k m]; rfl
  have hu_not_rest : ∀ (k : Fin r) (m : Fin (s - 1)),
      u_rad k m ∉ (R_rest k m).support := by
    intro k m
    have hnd := hR_rad_simple k m
    unfold GraphWalk.IsSimple at hnd
    rw [hR_rad_eq k m, GraphWalk.support] at hnd
    exact (List.nodup_cons.mp hnd).1
  have hz_ne_u : ∀ (k : Fin r) (m : Fin (s - 1)), z_rad k m ≠ u_rad k m :=
    fun k m heq => hu_not_rest k m (heq ▸ (R_rest k m).start_mem_support)
  -- Define branch subgraphs `B p ≤ H` for `p : Fin r × Fin s`.
  let B₁ : Fin r → Fin s → Graph α β := fun k j =>
    if hj : 0 < j.1 then
      subgraphUnion H (K_circ k j) (walkSubgraph (R_rest k ⟨j.1 - 1, by omega⟩))
    else
      K_circ k j
  let B : (Fin r × Fin s) → Graph α β := fun p =>
    if p.2.1 = s - 1 then
      subgraphUnion H (B₁ p.1 p.2) (walkSubgraph (R_tail p.1))
    else
      B₁ p.1 p.2
  have hB₁_le : ∀ k j, B₁ k j ≤ H := by
    intro k j; dsimp only [B₁]
    split_ifs with hj
    · exact subgraphUnion_le (hK_le k j) (walkSubgraph_le _)
    · exact hK_le k j
  have hB_le_H : ∀ p, B p ≤ H := by
    intro p; dsimp only [B]
    split_ifs
    · exact subgraphUnion_le (hB₁_le p.1 p.2) (walkSubgraph_le _)
    · exact hB₁_le p.1 p.2
  have hK_le_B₁ : ∀ k j, K_circ k j ≤ B₁ k j := by
    intro k j; dsimp only [B₁]
    split_ifs
    · exact le_subgraphUnion_left (hK_le k j) (walkSubgraph_le _)
    · exact le_rfl
  have hK_le_B : ∀ k j, K_circ k j ≤ B (k, j) := by
    intro k j; dsimp only [B]
    split_ifs
    · exact (hK_le_B₁ k j).trans (le_subgraphUnion_left (hB₁_le k j) (walkSubgraph_le _))
    · exact hK_le_B₁ k j
  have hB_conn : ∀ p, GraphConnected (B p) := by
    intro ⟨k, j⟩
    have hB₁_conn : GraphConnected (B₁ k j) := by
      dsimp only [B₁]
      split_ifs with hj
      · apply graphConnected_subgraphUnion (hK_le k j) (walkSubgraph_le _)
          (hK_conn k j) (graphConnected_walkSubgraph _)
        refine ⟨w_rad k ⟨j.1 - 1, by omega⟩, ?_, ?_⟩
        · have hw := hw_rad_mem k ⟨j.1 - 1, by omega⟩
          have hj_eq : (⟨j.1 - 1 + 1, by omega⟩ : Fin s) = j := by ext; dsimp; omega
          rwa [hj_eq] at hw
        · rw [vertexSet_walkSubgraph]
          exact (R_rest k ⟨j.1 - 1, by omega⟩).end_mem_support
      · exact hK_conn k j
    dsimp only [B]
    split_ifs with hlast
    · apply graphConnected_subgraphUnion (hB₁_le k j) (walkSubgraph_le _)
        hB₁_conn (graphConnected_walkSubgraph _)
      refine ⟨u_tail k, ?_, ?_⟩
      · have hj_eq : j = ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩ := Fin.ext hlast
        exact (hK_le_B₁ k j).vertexSet_mono (hj_eq ▸ hu_tail_mem k)
      · rw [vertexSet_walkSubgraph]
        exact (R_tail k).start_mem_support
    · exact hB₁_conn
  have hB_V : ∀ (k : Fin r) (j : Fin s) {z : α},
      z ∈ V(B (k, j)) ↔
        z ∈ V(K_circ k j) ∨
        (∃ hj : 0 < j.1, z ∈ (R_rest k ⟨j.1 - 1, by omega⟩).support) ∨
        (j.1 = s - 1 ∧ z ∈ (R_tail k).support) := by
    intro k j z
    have hB₁_V : z ∈ V(B₁ k j) ↔
        z ∈ V(K_circ k j) ∨ (∃ hj : 0 < j.1, z ∈ (R_rest k ⟨j.1 - 1, by omega⟩).support) := by
      dsimp only [B₁]
      by_cases hj : 0 < j.1
      · simp only [hj, ↓reduceDIte, vertexSet_subgraphUnion, vertexSet_walkSubgraph,
          mem_union, mem_ofPred_eq, exists_true_left]
      · simp only [hj, ↓reduceDIte, IsEmpty.exists_iff, or_false]
    dsimp only [B]
    by_cases hlast : j.1 = s - 1
    · simp only [hlast, ↓reduceIte, vertexSet_subgraphUnion, vertexSet_walkSubgraph,
        mem_union, mem_ofPred_eq, true_and, hB₁_V, or_assoc]
    · simp only [hlast, ↓reduceIte, false_and, or_false, hB₁_V]
  have hB_E : ∀ (k : Fin r) (j : Fin s) {f : β},
      f ∈ E(B (k, j)) ↔
        f ∈ E(K_circ k j) ∨
        (∃ hj : 0 < j.1, f ∈ (R_rest k ⟨j.1 - 1, by omega⟩).edges) ∨
        (j.1 = s - 1 ∧ f ∈ (R_tail k).edges) := by
    intro k j f
    have hB₁_E : f ∈ E(B₁ k j) ↔
        f ∈ E(K_circ k j) ∨ (∃ hj : 0 < j.1, f ∈ (R_rest k ⟨j.1 - 1, by omega⟩).edges) := by
      dsimp only [B₁]
      by_cases hj : 0 < j.1
      · simp only [hj, ↓reduceDIte, edgeSet_subgraphUnion (hK_le k j) (walkSubgraph_le _),
          edgeSet_walkSubgraph, mem_union, mem_ofPred_eq, exists_true_left]
      · simp only [hj, ↓reduceDIte, IsEmpty.exists_iff, or_false]
    dsimp only [B]
    by_cases hlast : j.1 = s - 1
    · simp only [hlast, ↓reduceIte, edgeSet_subgraphUnion (hB₁_le k j) (walkSubgraph_le _),
        edgeSet_walkSubgraph, mem_union, mem_ofPred_eq, true_and, hB₁_E, or_assoc]
    · simp only [hlast, ↓reduceIte, false_and, or_false, hB₁_E]
  -- Pairwise vertex-disjointness of `B p`.
  have hB_disj : ∀ {p₁ p₂ : Fin r × Fin s}, p₁ ≠ p₂ → Disjoint V(B p₁) V(B p₂) := by
    rintro ⟨k₁, j₁⟩ ⟨k₂, j₂⟩ hne
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ => ?_
    rw [hB_V] at hz₁ hz₂
    have hK_vs_rest : ∀ (ka : Fin r) (ja : Fin s) (kb : Fin r) (jb : Fin s) (hjb : 0 < jb.1),
        (ka, ja) ≠ (kb, jb) → z ∈ V(K_circ ka ja) →
        z ∈ (R_rest kb ⟨jb.1 - 1, by omega⟩).support → False := by
      intro ka ja kb jb hjb hne' hza hzb
      let mb : Fin (s - 1) := ⟨jb.1 - 1, by omega⟩
      have hzb_rad : z ∈ (R_rad kb mb).support := by
        rw [hR_rad_eq kb mb]; exact List.mem_cons_of_mem _ hzb
      rcases hR_rad_inter_K kb mb ka ja hzb_rad hza with ⟨_, _, rfl⟩ | ⟨rfl, hja_eq, _⟩
      · exact hu_not_rest kb mb hzb
      · refine hne' (Prod.ext rfl (show ja = jb from Fin.ext ?_))
        have hv := congrArg Fin.val hja_eq; dsimp [mb] at hv; omega
    have hK_vs_tail : ∀ (ka : Fin r) (ja : Fin s) (kb : Fin r) (jb : Fin s),
        jb.1 = s - 1 → (ka, ja) ≠ (kb, jb) → z ∈ V(K_circ ka ja) →
        z ∈ (R_tail kb).support → False := by
      intro ka ja kb jb hjb hne' hza hzb
      obtain ⟨rfl, hja_eq, _⟩ := hR_tail_inter_K kb ka ja hzb hza
      exact hne' (Prod.ext rfl (show ja = jb from hja_eq.trans (Fin.ext hjb.symm)))
    have htail_vs_rest : ∀ (ka : Fin r) (ja : Fin s) (kb : Fin r) (jb : Fin s) (hjb : 0 < jb.1),
        ja.1 = s - 1 → (ka, ja) ≠ (kb, jb) → z ∈ (R_tail ka).support →
        z ∈ (R_rest kb ⟨jb.1 - 1, by omega⟩).support → False := by
      intro ka ja kb jb hjb hja hne' hza hzb
      rw [hR_rest_supp] at hzb
      obtain ⟨rfl, hmb_eq, _⟩ := hR_tail_rad ka kb ⟨jb.1 - 1, by omega⟩ hza hzb
      refine hne' (Prod.ext rfl (show ja = jb from Fin.ext ?_))
      dsimp at hmb_eq; omega
    rcases hz₁ with h1K | ⟨hj₁, h1R⟩ | ⟨hl₁, h1T⟩ <;>
      rcases hz₂ with h2K | ⟨hj₂, h2R⟩ | ⟨hl₂, h2T⟩
    · exact Set.disjoint_left.mp (hK_disj hne) h1K h2K
    · exact hK_vs_rest k₁ j₁ k₂ j₂ hj₂ hne h1K h2R
    · exact hK_vs_tail k₁ j₁ k₂ j₂ hl₂ hne h1K h2T
    · exact hK_vs_rest k₂ j₂ k₁ j₁ hj₁ hne.symm h2K h1R
    · have hm_ne : (k₁, (⟨j₁.1 - 1, by omega⟩ : Fin (s - 1))) ≠
          (k₂, ⟨j₂.1 - 1, by omega⟩) := by
        intro hm_eq
        apply hne
        have hk_eq : k₁ = k₂ := congrArg Prod.fst hm_eq
        have hj_eq : j₁.1 - 1 = j₂.1 - 1 := congrArg (fun p => p.2.1) hm_eq
        exact Prod.ext hk_eq (show j₁ = j₂ from Fin.ext (by omega))
      rw [hR_rest_supp] at h1R h2R
      exact Set.disjoint_left.mp (hR_rad_disj hm_ne) h1R h2R
    · exact htail_vs_rest k₂ j₂ k₁ j₁ hj₁ hl₂ hne.symm h2T h1R
    · exact hK_vs_tail k₂ j₂ k₁ j₁ hl₁ hne.symm h2K h1T
    · exact htail_vs_rest k₁ j₁ k₂ j₂ hj₂ hl₁ hne h1T h2R
    · have hk_ne : k₁ ≠ k₂ := fun hk_eq =>
        hne (Prod.ext hk_eq (Fin.ext (hl₁.trans hl₂.symm)))
      exact Set.disjoint_left.mp (hR_tail_disj hk_ne) h1T h2T
  -- Edge map `ηe` on `cylinderGraph r s`.
  let ηe : ((Fin r × Fin s) ⊕ (Fin r × Fin s)) → β := fun e =>
    match e with
    | Sum.inl p => e_circ p.1 p.2
    | Sum.inr p =>
      if hp : p.2.1 + 1 < s then e_rad p.1 ⟨p.2.1, by omega⟩ else e_circ p.1 p.2
  have hcyl_link_to_H : ∀ {e : (Fin r × Fin s) ⊕ (Fin r × Fin s)} {p q : Fin r × Fin s},
      (cylinderGraph r s).IsLink e p q →
        ∃ x ∈ V(B p), ∃ y ∈ V(B q), H.IsLink (ηe e) x y := by
    intro e p q hl
    cases e with
    | inl p₀ =>
      obtain ⟨u, hu, w, hw, hl_c⟩ := he_circ_link p₀.1 p₀.2
      have huB : u ∈ V(B p₀) := (hK_le_B p₀.1 p₀.2).vertexSet_mono hu
      have hwB : w ∈ V(B (nextSpoke p₀.1, p₀.2)) :=
        (hK_le_B (nextSpoke p₀.1) p₀.2).vertexSet_mono hw
      rcases hl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨u, huB, w, hwB, hl_c⟩
      · exact ⟨w, hwB, u, huB, hl_c.symm⟩
    | inr p₀ =>
      rcases hl with ⟨hlt, hpair⟩
      have hηe_eq : ηe (Sum.inr p₀) = e_rad p₀.1 ⟨p₀.2.1, by omega⟩ := by
        dsimp only [ηe]; simp only [hlt, ↓reduceDIte]
      rw [hηe_eq]
      let m₀ : Fin (s - 1) := ⟨p₀.2.1, by omega⟩
      have huB : u_rad p₀.1 m₀ ∈ V(B p₀) :=
        (hK_le_B p₀.1 p₀.2).vertexSet_mono (hu_rad_mem p₀.1 m₀)
      have hzB : z_rad p₀.1 m₀ ∈ V(B (p₀.1, ⟨p₀.2.1 + 1, hlt⟩)) := by
        rw [hB_V]
        exact Or.inr (Or.inl ⟨Nat.succ_pos _, (R_rest p₀.1 m₀).start_mem_support⟩)
      rcases hpair with ⟨hp_eq, hq_eq⟩ | ⟨hq_eq, hp_eq⟩
      · rw [hp_eq, hq_eq]
        exact ⟨u_rad p₀.1 m₀, huB, z_rad p₀.1 m₀, hzB, hl_rad p₀.1 m₀⟩
      · rw [hp_eq, hq_eq]
        exact ⟨z_rad p₀.1 m₀, hzB, u_rad p₀.1 m₀, huB, (hl_rad p₀.1 m₀).symm⟩
  -- Distinctness of circular and radial edges.
  have he_circ_ne_rad : ∀ (k₁ : Fin r) (j₁ : Fin s) (k₂ : Fin r) (m₂ : Fin (s - 1)),
      e_circ k₁ j₁ ≠ e_rad k₂ m₂ := by
    intro k₁ j₁ k₂ m₂ heq
    obtain ⟨u, hu, w, hw, hl_c⟩ := he_circ_link k₁ j₁
    have hl_r : H.IsLink (e_circ k₁ j₁) (u_rad k₂ m₂) (z_rad k₂ m₂) := heq ▸ hl_rad k₂ m₂
    have hj_eq : ∀ {k' : Fin r}, u_rad k₂ m₂ ∈ V(K_circ k' j₁) → j₁ = ⟨m₂.1, by omega⟩ := by
      intro k' hu_in
      by_contra hj_ne
      exact Set.disjoint_left.mp
        (hK_disj (fun h => hj_ne (congrArg Prod.snd h).symm)) (hu_rad_mem k₂ m₂) hu_in
    have hz_bad : ∀ {k' : Fin r}, z_rad k₂ m₂ ∈ V(K_circ k' j₁) → j₁ = ⟨m₂.1, by omega⟩ → False := by
      intro k' hz_in hj₁_eq
      have hz_supp : z_rad k₂ m₂ ∈ (R_rad k₂ m₂).support := by
        rw [hR_rad_eq k₂ m₂]
        exact List.mem_cons_of_mem _ (R_rest k₂ m₂).start_mem_support
      rcases hR_rad_inter_K k₂ m₂ k' j₁ hz_supp hz_in with ⟨_, _, hzu⟩ | ⟨_, hj_succ, _⟩
      · exact hz_ne_u k₂ m₂ hzu
      · have hv := congrArg Fin.val (hj₁_eq.symm.trans hj_succ); dsimp at hv; omega
    rcases hl_c.left_eq_or_eq hl_r with h1 | h1
    · have h2 := hl_c.right_unique (h1 ▸ hl_r)
      exact hz_bad (h2 ▸ hw) (hj_eq (h1 ▸ hu))
    · have h2 := hl_c.right_unique (h1 ▸ hl_r.symm)
      exact hz_bad (h1 ▸ hu) (hj_eq (h2 ▸ hw))
  have he_rad_inj : ∀ {k₁ k₂ : Fin r} {m₁ m₂ : Fin (s - 1)},
      e_rad k₁ m₁ = e_rad k₂ m₂ → k₁ = k₂ ∧ m₁ = m₂ := by
    intro k₁ k₂ m₁ m₂ heq
    by_contra hne_pair
    have hne : (k₁, m₁) ≠ (k₂, m₂) := fun h => hne_pair ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
    have hl₁ := hl_rad k₁ m₁
    have hl₂ : H.IsLink (e_rad k₁ m₁) (u_rad k₂ m₂) (z_rad k₂ m₂) := heq ▸ hl_rad k₂ m₂
    rcases hl₁.left_eq_or_eq hl₂ with hu_eq | huz₁
    · have hz_eq := hl₁.right_unique (hu_eq ▸ hl₂)
      have hz₁_in : z_rad k₁ m₁ ∈ {z | z ∈ (R_rad k₁ m₁).support.tail} := by
        rw [mem_ofPred_eq, ← hR_rest_supp]; exact (R_rest k₁ m₁).start_mem_support
      have hz₂_in : z_rad k₁ m₁ ∈ {z | z ∈ (R_rad k₂ m₂).support.tail} := by
        rw [hz_eq, mem_ofPred_eq, ← hR_rest_supp]; exact (R_rest k₂ m₂).start_mem_support
      exact Set.disjoint_left.mp (hR_rad_disj hne) hz₁_in hz₂_in
    · have huz₂ := hl₁.right_unique (huz₁ ▸ hl₂.symm)
      -- `u_rad k₁ m₁ = z_rad k₂ m₂` and `z_rad k₁ m₁ = u_rad k₂ m₂`.
      have hz₁_supp : z_rad k₁ m₁ ∈ (R_rad k₁ m₁).support := by
        rw [hR_rad_eq k₁ m₁]; exact List.mem_cons_of_mem _ (R_rest k₁ m₁).start_mem_support
      have hz₂_supp : z_rad k₂ m₂ ∈ (R_rad k₂ m₂).support := by
        rw [hR_rad_eq k₂ m₂]; exact List.mem_cons_of_mem _ (R_rest k₂ m₂).start_mem_support
      have hm₁₂ : m₂.1 = m₁.1 + 1 := by
        rcases hR_rad_inter_K k₁ m₁ k₂ ⟨m₂.1, by omega⟩ hz₁_supp (huz₂ ▸ hu_rad_mem k₂ m₂) with
          ⟨_, _, hzu⟩ | ⟨_, hj_eq, _⟩
        · exact (hz_ne_u k₁ m₁ hzu).elim
        · exact congrArg Fin.val hj_eq
      have hm₂₁ : m₁.1 = m₂.1 + 1 := by
        rcases hR_rad_inter_K k₂ m₂ k₁ ⟨m₁.1, by omega⟩ hz₂_supp (huz₁.symm ▸ hu_rad_mem k₁ m₁) with
          ⟨_, _, hzu⟩ | ⟨_, hj_eq, _⟩
        · exact (hz_ne_u k₂ m₂ hzu).elim
        · exact congrArg Fin.val hj_eq
      omega
  -- Disjointness of `ηe '' E(cylinderGraph r s)` from `E(B p)`.
  have hB_le_del : ∀ p ∈ V(cylinderGraph r s),
      B p ≤ H.deleteEdges (ηe '' E(cylinderGraph r s)) := by
    intro ⟨k, j⟩ _
    refine ⟨(hB_le_H (k, j)).vertexSet_mono, fun f x y hlf => ?_⟩
    rw [deleteEdges_isLink]
    refine ⟨hlf.mono (hB_le_H (k, j)), ?_⟩
    rintro ⟨e_cyl, he_cyl, rfl⟩
    have hfB : ηe e_cyl ∈ E(B (k, j)) := hlf.edge_mem
    rw [hB_E] at hfB
    cases e_cyl with
    | inl p₀ =>
      dsimp only [ηe] at hfB
      obtain ⟨u, hu, w, hw, hl_c⟩ := he_circ_link p₀.1 p₀.2
      rcases hfB with hfK | ⟨hj, hfR⟩ | ⟨_, hfT⟩
      · exact he_circ_not_K p₀.1 p₀.2 k j hfK
      · let m₀ : Fin (s - 1) := ⟨j.1 - 1, by omega⟩
        have hmem := walk_isLink_mem_support (R_rest k m₀) hfR hl_c
        have hu_rad_supp : u ∈ (R_rad k m₀).support := by
          rw [hR_rad_eq k m₀]; exact List.mem_cons_of_mem _ hmem.1
        have hw_rad_supp : w ∈ (R_rad k m₀).support := by
          rw [hR_rad_eq k m₀]; exact List.mem_cons_of_mem _ hmem.2
        have hu_eq : u = w_rad k m₀ := by
          rcases hR_rad_inter_K k m₀ p₀.1 p₀.2 hu_rad_supp hu with ⟨_, _, h1⟩ | ⟨_, _, h1⟩
          · exact (hu_not_rest k m₀ (h1 ▸ hmem.1)).elim
          · exact h1
        have hw_eq : w = w_rad k m₀ := by
          rcases hR_rad_inter_K k m₀ (nextSpoke p₀.1) p₀.2 hw_rad_supp hw with ⟨_, _, h1⟩ | ⟨_, _, h1⟩
          · exact (hu_not_rest k m₀ (h1 ▸ hmem.2)).elim
          · exact h1
        have hrest_s : (R_rest k m₀).IsSimple :=
          (List.nodup_cons.mp (hR_rad_eq k m₀ ▸ hR_rad_simple k m₀)).2
        exact not_isLink_self_of_mem_edges_of_isSimple (R_rest k m₀) hrest_s hfR
          (hu_eq ▸ hw_eq ▸ hl_c)
      · have hmem := walk_isLink_mem_support (R_tail k) hfT hl_c
        have hu_eq : u = u_tail k := (hR_tail_inter_K k p₀.1 p₀.2 hmem.1 hu).2.2
        have hw_eq : w = u_tail k := (hR_tail_inter_K k (nextSpoke p₀.1) p₀.2 hmem.2 hw).2.2
        exact not_isLink_self_of_mem_edges_of_isSimple (R_tail k) (hR_tail_simple k) hfT
          (hu_eq ▸ hw_eq ▸ hl_c)
    | inr p₀ =>
      have hp₀_lt : p₀.2.1 + 1 < s := he_cyl
      have hηe_eq : ηe (Sum.inr p₀) = e_rad p₀.1 ⟨p₀.2.1, by omega⟩ := by
        dsimp only [ηe]; simp only [hp₀_lt, ↓reduceDIte]
      rw [hηe_eq] at hfB
      let m₀ : Fin (s - 1) := ⟨p₀.2.1, by omega⟩
      rcases hfB with hfK | ⟨hj, hfR⟩ | ⟨_, hfT⟩
      · obtain ⟨x₀, y₀, hlK⟩ := (K_circ k j).exists_isLink_of_mem_edgeSet hfK
        have hlH := hlK.mono (hK_le k j)
        have hpair : ({u_rad p₀.1 m₀, z_rad p₀.1 m₀} : Set α) ⊆ V(K_circ k j) := by
          rcases (hl_rad p₀.1 m₀).left_eq_or_eq hlH with rfl | rfl
          · have hy := (hl_rad p₀.1 m₀).right_unique hlH
            rintro _ (rfl | rfl)
            · exact hlK.left_mem
            · exact hy ▸ hlK.right_mem
          · have hy := (hl_rad p₀.1 m₀).right_unique hlH.symm
            rintro _ (rfl | rfl)
            · exact hlK.right_mem
            · exact hy ▸ hlK.left_mem
        have hu_in : u_rad p₀.1 m₀ ∈ V(K_circ k j) := hpair (mem_insert _ _)
        have hz_in : z_rad p₀.1 m₀ ∈ V(K_circ k j) := hpair (mem_insert_of_mem _ rfl)
        have hkj_eq : (k, j) = (p₀.1, ⟨m₀.1, by omega⟩) := by
          by_contra hne
          exact Set.disjoint_left.mp (hK_disj hne) hu_in (hu_rad_mem p₀.1 m₀)
        have hj_eq : j = ⟨m₀.1, by omega⟩ := congrArg Prod.snd hkj_eq
        have hz_supp : z_rad p₀.1 m₀ ∈ (R_rad p₀.1 m₀).support := by
          rw [hR_rad_eq p₀.1 m₀]; exact List.mem_cons_of_mem _ (R_rest p₀.1 m₀).start_mem_support
        rcases hR_rad_inter_K p₀.1 m₀ k j hz_supp hz_in with ⟨_, _, hzu⟩ | ⟨_, hj_succ, _⟩
        · exact hz_ne_u p₀.1 m₀ hzu
        · have hv := congrArg Fin.val (hj_eq.symm.trans hj_succ); dsimp at hv; omega
      · let m₁ : Fin (s - 1) := ⟨j.1 - 1, by omega⟩
        by_cases hkm : (p₀.1, m₀) = (k, m₁)
        · have hk_eq : p₀.1 = k := congrArg Prod.fst hkm
          have hm_eq : m₀ = m₁ := congrArg Prod.snd hkm
          change e_rad p₀.1 m₀ ∈ (R_rest k m₁).edges at hfR
          rw [← hk_eq, ← hm_eq] at hfR
          have hed_nd : (R_rad p₀.1 m₀).edges.Nodup := (hR_rad_simple p₀.1 m₀).edges_nodup
          rw [hR_rad_eq p₀.1 m₀, GraphWalk.edges] at hed_nd
          exact (List.nodup_cons.mp hed_nd).1 hfR
        · have hmem := walk_isLink_mem_support (R_rest k m₁) hfR (hl_rad p₀.1 m₀)
          have hz_in₀ : z_rad p₀.1 m₀ ∈ {z | z ∈ (R_rad p₀.1 m₀).support.tail} := by
            rw [mem_ofPred_eq, ← hR_rest_supp]; exact (R_rest p₀.1 m₀).start_mem_support
          have hz_in₁ : z_rad p₀.1 m₀ ∈ {z | z ∈ (R_rad k m₁).support.tail} := by
            rw [mem_ofPred_eq, ← hR_rest_supp]; exact hmem.2
          exact Set.disjoint_left.mp (hR_rad_disj hkm) hz_in₀ hz_in₁
      · have hmem := walk_isLink_mem_support (R_tail k) hfT (hl_rad p₀.1 m₀)
        have hj_eq := (hR_tail_inter_K k p₀.1 ⟨m₀.1, by omega⟩ hmem.1 (hu_rad_mem p₀.1 m₀)).2.1
        have hv := congrArg Fin.val hj_eq; dsimp [m₀] at hv; omega
  -- Assemble `IsMinorModel (cylinderGraph r s) H (fun p => V(B p)) ηe`.
  have hmodel : IsMinorModel (cylinderGraph r s) H (fun p => V(B p)) ηe :=
    { vertex_nonempty := fun p _ => (hB_conn p).1
      vertex_subset := fun p _ => (hB_le_H p).vertexSet_mono
      edge_mem := fun e he => by
        obtain ⟨p, q, hl⟩ := (cylinderGraph r s).exists_isLink_of_mem_edgeSet he
        obtain ⟨_, _, _, _, hlH⟩ := hcyl_link_to_H hl
        exact hlH.edge_mem
      vertex_disjoint := fun _ _ _ _ hne => hB_disj hne
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
        cases e₁ with
        | inl p₁ =>
          cases e₂ with
          | inl p₂ =>
            obtain ⟨hk, hj⟩ := he_circ_inj heq
            exact congrArg Sum.inl (Prod.ext hk hj)
          | inr p₂ =>
            have hp₂ : p₂.2.1 + 1 < s := he₂
            have hη₂ : ηe (Sum.inr p₂) = e_rad p₂.1 ⟨p₂.2.1, by omega⟩ := by
              dsimp only [ηe]; simp only [hp₂, ↓reduceDIte]
            exact (he_circ_ne_rad p₁.1 p₁.2 p₂.1 ⟨p₂.2.1, by omega⟩ (heq.trans hη₂)).elim
        | inr p₁ =>
          have hp₁ : p₁.2.1 + 1 < s := he₁
          have hη₁ : ηe (Sum.inr p₁) = e_rad p₁.1 ⟨p₁.2.1, by omega⟩ := by
            dsimp only [ηe]; simp only [hp₁, ↓reduceDIte]
          cases e₂ with
          | inl p₂ =>
            exact (he_circ_ne_rad p₂.1 p₂.2 p₁.1 ⟨p₁.2.1, by omega⟩ (heq.symm.trans hη₁)).elim
          | inr p₂ =>
            have hp₂ : p₂.2.1 + 1 < s := he₂
            have hη₂ : ηe (Sum.inr p₂) = e_rad p₂.1 ⟨p₂.2.1, by omega⟩ := by
              dsimp only [ηe]; simp only [hp₂, ↓reduceDIte]
            obtain ⟨hk, hm⟩ := he_rad_inj (hη₁.symm.trans (heq.trans hη₂))
            have hj_val : p₁.2.1 = p₂.2.1 := congrArg (fun x : Fin (s - 1) => x.1) hm
            exact congrArg Sum.inr (Prod.ext hk (Fin.ext hj_val))
      inc_iff := fun p _ e he => by
        obtain ⟨q₁, q₂, hl_cyl⟩ := (cylinderGraph r s).exists_isLink_of_mem_edgeSet he
        obtain ⟨x, hx, y, hy, hlH⟩ := hcyl_link_to_H hl_cyl
        constructor
        · rintro ⟨w, hlw⟩
          rcases hlw.left_eq_or_eq hl_cyl with rfl | rfl
          · exact ⟨x, hx, hlH.inc_left⟩
          · exact ⟨y, hy, hlH.inc_right⟩
        · rintro ⟨z, hz, hincz⟩
          rcases hincz.eq_or_eq_of_isLink hlH with rfl | rfl
          · have hpq : p = q₁ := by
              by_contra hne; exact (hB_disj hne).notMem_of_mem_left hz hx
            exact hpq ▸ hl_cyl.inc_left
          · have hpq : p = q₂ := by
              by_contra hne; exact (hB_disj hne).notMem_of_mem_left hz hy
            exact hpq ▸ hl_cyl.inc_right
      isLoopAt_iff := fun p _ e he => by
        obtain ⟨q₁, q₂, hl_cyl⟩ := (cylinderGraph r s).exists_isLink_of_mem_edgeSet he
        obtain ⟨x, hx, y, hy, hlH⟩ := hcyl_link_to_H hl_cyl
        constructor
        · intro hloop z hincz
          have hq₁ : q₁ = p := (hl_cyl.left_eq_or_eq hloop).elim id id
          have hq₂ : q₂ = p := by
            rcases hl_cyl.left_eq_or_eq hloop with rfl | rfl
            · exact hl_cyl.right_unique hloop
            · exact hl_cyl.right_unique hloop.symm
          rcases hincz.eq_or_eq_of_isLink hlH with rfl | rfl
          · exact hq₁ ▸ hx
          · exact hq₂ ▸ hy
        · intro hall
          have hxp : x ∈ V(B p) := hall x hlH.inc_left
          have hyp : y ∈ V(B p) := hall y hlH.inc_right
          have hq₁ : q₁ = p := by
            by_contra hne; exact (hB_disj hne).notMem_of_mem_left hx hxp
          have hq₂ : q₂ = p := by
            by_contra hne; exact (hB_disj hne).notMem_of_mem_left hy hyp
          subst hq₁ hq₂
          exact hl_cyl
      connected := fun p hp => ⟨B p, hB_le_del p hp, rfl, hB_conn p⟩ }
  obtain ⟨H', hH'_le, C_contr, hC_sub, φ, hφ_V, hC_eq⟩ :=
    exists_contract_iso_of_explicit_model hmodel hB_le_del (fun p _ => hB_conn p)
  refine ⟨H', hH'_le, C_contr, hC_sub, φ, fun k => ?_, fun ⟨k₀, hlen⟩ => ?_⟩
  · rw [hφ_V (k, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩) (Set.mem_univ _), hB_V]
    exact Or.inr (Or.inr ⟨rfl, (R_tail k).end_mem_support⟩)
  · cases hed_eq : (R_tail k₀).edges with
    | nil =>
      exfalso
      have hlen0 : (R_tail k₀).length = 0 := by
        unfold GraphWalk.length; rw [hed_eq]; rfl
      omega
    | cons f₀ _ =>
      refine ⟨f₀, ?_⟩
      rw [hC_eq]
      refine mem_biUnion (x := (k₀, ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩)) (Set.mem_univ _) ?_
      rw [hB_E]
      refine Or.inr (Or.inr ⟨rfl, ?_⟩)
      rw [hed_eq]
      exact List.mem_cons_self

end GraphMinor.GM03
end
