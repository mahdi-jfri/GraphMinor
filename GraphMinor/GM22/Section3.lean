module

public import GraphMinor.GM22.Section2Forest
public import GraphMinor.GM22.Section3Haven
public import GraphMinor.GM22.Section3Disc

import GraphMinor.GM22.GM21Proved

/-!
# Graph Minors XXII, Section 3 (Part 4): Proof of 3.1

This file completes Section 3 of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 534–537), proving Claims (3)–(7) of **3.1**
and the main theorem **3.1** (`theorem_3_1`).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]

/-! ## 1. Edge Contraction and Uncontraction on `Graph α β` -/

section Contraction

/-- Vertex identification map sending `u'` to `u` and fixing all other vertices. -/
def contractVertMap [DecidableEq α] (u u' : α) (x : α) : α :=
  if x = u' then u else x

@[simp]
theorem contractVertMap_self [DecidableEq α] (u u' : α) :
    contractVertMap u u' u = u := by
  simp [contractVertMap]

@[simp]
theorem contractVertMap_other [DecidableEq α] (u u' : α) :
    contractVertMap u u' u' = u := by
  simp [contractVertMap]

theorem contractVertMap_eq_of_ne [DecidableEq α] {u u' x : α} (hx : x ≠ u') :
    contractVertMap u u' x = x := by
  simp [contractVertMap, hx]

theorem contractVertMap_idem [DecidableEq α] (u u' x : α) :
    contractVertMap u u' (contractVertMap u u' x) = contractVertMap u u' x := by
  by_cases hx : x = u' <;> simp [contractVertMap, hx]

theorem contractVertMap_eq_u_iff [DecidableEq α] {u u' x : α} :
    contractVertMap u u' x = u ↔ x = u ∨ x = u' := by
  by_cases hx : x = u' <;> simp [contractVertMap, hx]

/-- Contracting an edge `e₀` of `H` by identifying `u'` with `u` and deleting `e₀`. -/
def contractEdge [DecidableEq α] (H : Graph α β) (e₀ : β) (u u' : α) : Graph α β where
  vertexSet := contractVertMap u u' '' V(H)
  edgeSet := E(H) \ {e₀}
  IsLink e x y := e ≠ e₀ ∧ ∃ x₀ y₀, H.IsLink e x₀ y₀ ∧
    x = contractVertMap u u' x₀ ∧ y = contractVertMap u u' y₀
  isLink_symm _ _ := ⟨by
    rintro x y ⟨he, x₀, y₀, hl, rfl, rfl⟩
    exact ⟨he, y₀, x₀, hl.symm, rfl, rfl⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y z w ⟨_, x₀, y₀, hl₁, rfl, rfl⟩ ⟨_, z₀, w₀, hl₂, rfl, rfl⟩
    rcases hl₁.eq_and_eq_or_eq_and_eq hl₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  edge_mem_iff_exists_isLink e := by
    simp only [mem_sdiff, mem_singleton_iff]
    constructor
    · rintro ⟨heH, he₀⟩
      obtain ⟨x₀, y₀, hl⟩ := H.exists_isLink_of_mem_edgeSet heH
      exact ⟨contractVertMap u u' x₀, contractVertMap u u' y₀, he₀, x₀, y₀, hl, rfl, rfl⟩
    · rintro ⟨_, _, he₀, x₀, y₀, hl, _, _⟩
      exact ⟨hl.edge_mem, he₀⟩
  left_mem_of_isLink := by
    rintro e x y ⟨_, x₀, _, hl, rfl, _⟩
    exact mem_image_of_mem _ hl.left_mem

@[simp]
theorem vertexSet_contractEdge [DecidableEq α] (H : Graph α β) (e₀ : β) (u u' : α) :
    V(contractEdge H e₀ u u') = contractVertMap u u' '' V(H) := rfl

@[simp]
theorem edgeSet_contractEdge [DecidableEq α] (H : Graph α β) (e₀ : β) (u u' : α) :
    E(contractEdge H e₀ u u') = E(H) \ {e₀} := rfl

theorem contractEdge_mono [DecidableEq α] {H₁ H₂ : Graph α β} (hle : H₁ ≤ H₂)
    (e₀ : β) (u u' : α) :
    contractEdge H₁ e₀ u u' ≤ contractEdge H₂ e₀ u u' where
  vertexSet_mono := image_mono hle.vertexSet_mono
  isLink_mono := by
    rintro e x y ⟨he₀, x₀, y₀, hl, rfl, rfl⟩
    exact ⟨he₀, x₀, y₀, hle.isLink_mono hl, rfl, rfl⟩

theorem vertexSet_contractEdge_eq_sdiff [DecidableEq α] {H : Graph α β} {e₀ : β} {u u' : α}
    (hu : u ∈ V(H)) (hne : u ≠ u') :
    V(contractEdge H e₀ u u') = V(H) \ {u'} := by
  ext x
  simp only [vertexSet_contractEdge, mem_image, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro ⟨x₀, hx₀, rfl⟩
    by_cases hx₀_u' : x₀ = u'
    · subst hx₀_u'
      simp [contractVertMap, hne, hu]
    · rw [contractVertMap_eq_of_ne hx₀_u']
      exact ⟨hx₀, hx₀_u'⟩
  · rintro ⟨hx, hx_ne⟩
    exact ⟨x, hx, contractVertMap_eq_of_ne hx_ne⟩

theorem size_contractEdge_lt [DecidableEq α] {G : Graph α β} {e₀ : β} {u u' : α}
    (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hl₀ : G.IsLink e₀ u u') (hne : u ≠ u') :
    V(contractEdge G e₀ u u').ncard + E(contractEdge G e₀ u u').ncard <
      V(G).ncard + E(G).ncard := by
  rw [vertexSet_contractEdge_eq_sdiff hl₀.left_mem hne, edgeSet_contractEdge]
  have h1 : (V(G) \ {u'}).ncard < V(G).ncard :=
    ncard_lt_ncard (sdiff_singleton_ssubset.mpr hl₀.right_mem) hVG
  have h2 : (E(G) \ {e₀}).ncard < E(G).ncard :=
    ncard_lt_ncard (sdiff_singleton_ssubset.mpr hl₀.edge_mem) hEG
  omega

theorem contractEdge_eq_self_of_notMem [DecidableEq α] {H : Graph α β} {e₀ : β} {u u' : α}
    (hu' : u' ∉ V(H)) (he₀ : e₀ ∉ E(H)) :
    contractEdge H e₀ u u' = H := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext x
    simp only [vertexSet_contractEdge, mem_image]
    constructor
    · rintro ⟨x₀, hx₀, rfl⟩
      have hx₀_ne : x₀ ≠ u' := fun h => hu' (h ▸ hx₀)
      rwa [contractVertMap_eq_of_ne hx₀_ne]
    · intro hx
      have hx_ne : x ≠ u' := fun h => hu' (h ▸ hx)
      exact ⟨x, hx, contractVertMap_eq_of_ne hx_ne⟩
  · constructor
    · rintro ⟨_, x₀, y₀, hl, rfl, rfl⟩
      have hx₀_ne : x₀ ≠ u' := fun h => hu' (h ▸ hl.left_mem)
      have hy₀_ne : y₀ ≠ u' := fun h => hu' (h ▸ hl.right_mem)
      rwa [contractVertMap_eq_of_ne hx₀_ne, contractVertMap_eq_of_ne hy₀_ne]
    · intro hl
      have hx_ne : x ≠ u' := fun h => hu' (h ▸ hl.left_mem)
      have hy_ne : y ≠ u' := fun h => hu' (h ▸ hl.right_mem)
      have he_ne : e ≠ e₀ := fun h => he₀ (h ▸ hl.edge_mem)
      exact ⟨he_ne, x, y, hl, (contractVertMap_eq_of_ne hx_ne).symm,
        (contractVertMap_eq_of_ne hy_ne).symm⟩

theorem walk_contractEdge_of_isLink [DecidableEq α] {H : Graph α β} {e₀ : β} {u u' : α}
    (hl₀ : H.IsLink e₀ u u') {a b : α} (W : GraphWalk H a b) :
    Nonempty (GraphWalk (contractEdge H e₀ u u')
      (contractVertMap u u' a) (contractVertMap u u' b)) := by
  induction W with
  | @nil x hx =>
    exact ⟨.nil (mem_image_of_mem _ hx)⟩
  | @cons x y c e hl rest ih =>
    obtain ⟨W'⟩ := ih
    by_cases he : e = e₀
    · subst he
      have hxy : contractVertMap u u' x = contractVertMap u u' y := by
        rcases hl.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp [contractVertMap]
      rw [hxy]
      exact ⟨W'⟩
    · have hl' : (contractEdge H e₀ u u').IsLink e
          (contractVertMap u u' x) (contractVertMap u u' y) :=
        ⟨he, x, y, hl, rfl, rfl⟩
      exact ⟨.cons hl' W'⟩

theorem walk_contractEdge_of_notMem [DecidableEq α] {H : Graph α β} {e₀ : β} {u u' : α}
    (he₀ : e₀ ∉ E(H)) {a b : α} (W : GraphWalk H a b) :
    Nonempty (GraphWalk (contractEdge H e₀ u u')
      (contractVertMap u u' a) (contractVertMap u u' b)) := by
  induction W with
  | @nil x hx =>
    exact ⟨.nil (mem_image_of_mem _ hx)⟩
  | @cons x y c e hl rest ih =>
    obtain ⟨W'⟩ := ih
    have he : e ≠ e₀ := fun h => he₀ (h ▸ hl.edge_mem)
    exact ⟨.cons ⟨he, x, y, hl, rfl, rfl⟩ W'⟩

theorem isGraphConnected_contractEdge_of_isLink [DecidableEq α] {H : Graph α β} {e₀ : β}
    {u u' : α} (hl₀ : H.IsLink e₀ u u') (hconn : IsGraphConnected H) :
    IsGraphConnected (contractEdge H e₀ u u') := by
  rcases hconn with ⟨⟨z, hz⟩, hreach⟩
  refine ⟨⟨contractVertMap u u' z, mem_image_of_mem _ hz⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨W⟩ := hreach a ha b hb
  exact walk_contractEdge_of_isLink hl₀ W

theorem isGraphConnected_contractEdge_of_notMem [DecidableEq α] {H : Graph α β} {e₀ : β}
    {u u' : α} (he₀ : e₀ ∉ E(H)) (hconn : IsGraphConnected H) :
    IsGraphConnected (contractEdge H e₀ u u') := by
  rcases hconn with ⟨⟨z, hz⟩, hreach⟩
  refine ⟨⟨contractVertMap u u' z, mem_image_of_mem _ hz⟩, ?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨W⟩ := hreach a ha b hb
  exact walk_contractEdge_of_notMem he₀ W

/-- Uncontracting a subgraph `H' ≤ contractEdge G e₀ u u'` back to a subgraph of `G` by lifting
vertices and edges and including `e₀` with its endpoints `u, u'`. -/
def uncontractSubgraph [DecidableEq α] (G H' : Graph α β) (e₀ : β) (u u' : α) : Graph α β :=
  (G.induce ({x ∈ V(G) | contractVertMap u u' x ∈ V(H')} ∪ {u, u'})).restrict (E(H') ∪ {e₀})

theorem uncontractSubgraph_le [DecidableEq α] {G H' : Graph α β} {e₀ : β} {u u' : α}
    (hl₀ : G.IsLink e₀ u u') :
    uncontractSubgraph G H' e₀ u u' ≤ G := by
  refine restrict_le.trans (induce_le ?_)
  rintro x (hx | rfl | rfl)
  · exact hx.1
  · exact hl₀.left_mem
  · exact hl₀.right_mem

theorem isLink_e₀_uncontractSubgraph [DecidableEq α] {G H' : Graph α β} {e₀ : β} {u u' : α}
    (hl₀ : G.IsLink e₀ u u') :
    (uncontractSubgraph G H' e₀ u u').IsLink e₀ u u' := by
  unfold uncontractSubgraph
  rw [restrict_isLink, induce_isLink]
  exact ⟨Or.inr rfl, hl₀, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩

theorem vertex_mem_uncontractSubgraph_iff [DecidableEq α] {G H' : Graph α β} {e₀ : β} {u u' : α}
    {x : α} :
    x ∈ V(uncontractSubgraph G H' e₀ u u') ↔
      (x ∈ V(G) ∧ contractVertMap u u' x ∈ V(H')) ∨ x = u ∨ x = u' := by
  rfl

theorem walk_between_same_contractVertMap [DecidableEq α] {H : Graph α β} {e₀ : β}
    {u u' : α} (hl₀ : H.IsLink e₀ u u') {a b : α} (ha : a ∈ V(H))
    (hab : contractVertMap u u' a = contractVertMap u u' b) :
    Nonempty (GraphWalk H a b) := by
  by_cases ha_u' : a = u'
  · subst ha_u'
    rw [contractVertMap_other] at hab
    rcases contractVertMap_eq_u_iff.mp hab.symm with rfl | rfl
    · exact ⟨.cons hl₀.symm (.nil hl₀.left_mem)⟩
    · exact ⟨.nil hl₀.right_mem⟩
  · rw [contractVertMap_eq_of_ne ha_u'] at hab
    by_cases hb_u' : b = u'
    · subst hb_u'
      rw [contractVertMap_other] at hab
      subst hab
      exact ⟨.cons hl₀ (.nil hl₀.right_mem)⟩
    · rw [contractVertMap_eq_of_ne hb_u'] at hab
      subst hab
      exact ⟨.nil ha⟩

theorem lift_walk_of_contractEdge [DecidableEq α] {H : Graph α β} {e₀ : β} {u u' : α}
    (hl₀ : H.IsLink e₀ u u') {x y : α}
    (W' : GraphWalk (contractEdge H e₀ u u') x y)
    {a b : α} (ha : a ∈ V(H)) (_hb : b ∈ V(H))
    (hax : contractVertMap u u' a = x) (hby : contractVertMap u u' b = y) :
    Nonempty (GraphWalk H a b) := by
  induction W' generalizing a with
  | nil _ =>
    exact walk_between_same_contractVertMap hl₀ ha (hax.trans hby.symm)
  | @cons x₁ y₁ z₁ e hl' rest ih =>
    rcases hl' with ⟨_, x₀, y₀, hl_e, hx₁_eq, hy₁_eq⟩
    obtain ⟨W_pre⟩ := walk_between_same_contractVertMap hl₀ ha (hax.trans hx₁_eq)
    obtain ⟨W_rest⟩ := ih hl_e.right_mem hy₁_eq.symm hby
    exact ⟨W_pre.append (.cons hl_e W_rest)⟩

theorem areConnectedIn_contractEdge_iff [DecidableEq α] {H : Graph α β} {e₀ : β} {u u' : α}
    (hl₀ : H.IsLink e₀ u u') {a b : α} (ha : a ∉ ({u, u'} : Set α)) (hb : b ∉ ({u, u'} : Set α)) :
    AreConnectedIn (contractEdge H e₀ u u') a b ↔ AreConnectedIn H a b := by
  have ha_ne : a ≠ u' := fun h => ha (Or.inr h)
  have hb_ne : b ≠ u' := fun h => hb (Or.inr h)
  have ha_map : contractVertMap u u' a = a := contractVertMap_eq_of_ne ha_ne
  have hb_map : contractVertMap u u' b = b := contractVertMap_eq_of_ne hb_ne
  rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
  constructor
  · rintro ⟨⟨a₀, ha₀, ha_eq⟩, ⟨b₀, hb₀, hb_eq⟩, ⟨W'⟩⟩
    have ha_H : a ∈ V(H) := by
      by_cases ha₀_u' : a₀ = u'
      · subst ha₀_u'
        rw [contractVertMap_other] at ha_eq
        exact (ha (Or.inl ha_eq.symm)).elim
      · rw [contractVertMap_eq_of_ne ha₀_u'] at ha_eq
        exact ha_eq ▸ ha₀
    have hb_H : b ∈ V(H) := by
      by_cases hb₀_u' : b₀ = u'
      · subst hb₀_u'
        rw [contractVertMap_other] at hb_eq
        exact (hb (Or.inl hb_eq.symm)).elim
      · rw [contractVertMap_eq_of_ne hb₀_u'] at hb_eq
        exact hb_eq ▸ hb₀
    exact ⟨ha_H, hb_H, lift_walk_of_contractEdge hl₀ W' ha_H hb_H ha_map hb_map⟩
  · rintro ⟨ha_H, hb_H, ⟨W⟩⟩
    obtain ⟨W'⟩ := walk_contractEdge_of_isLink hl₀ W
    rw [ha_map, hb_map] at W'
    exact ⟨ha_map ▸ mem_image_of_mem _ ha_H, hb_map ▸ mem_image_of_mem _ hb_H, ⟨W'⟩⟩

theorem contractEdge_uncontractSubgraph_links [DecidableEq α] {G H' : Graph α β} {e₀ : β}
    {u u' : α} (hH' : H' ≤ contractEdge G e₀ u u') :
    ∀ {e x y}, (contractEdge (uncontractSubgraph G H' e₀ u u') e₀ u u').IsLink e x y ↔
      H'.IsLink e x y := by
  intro e x y
  constructor
  · rintro ⟨he₀, x₀, y₀, hl_un, rfl, rfl⟩
    unfold uncontractSubgraph at hl_un
    rw [restrict_isLink, induce_isLink] at hl_un
    rcases hl_un with ⟨he_or, hlG, _, _⟩
    have heH' : e ∈ E(H') := he_or.resolve_right he₀
    have hl_c : (contractEdge G e₀ u u').IsLink e
        (contractVertMap u u' x₀) (contractVertMap u u' y₀) :=
      ⟨he₀, x₀, y₀, hlG, rfl, rfl⟩
    exact (hH'.isLink_iff heH').mpr hl_c
  · intro hl'
    have hl_c := hH'.isLink_mono hl'
    rcases hl_c with ⟨he₀, x₀, y₀, hlG, rfl, rfl⟩
    refine ⟨he₀, x₀, y₀, ?_, rfl, rfl⟩
    unfold uncontractSubgraph
    rw [restrict_isLink, induce_isLink]
    exact ⟨Or.inl hl'.edge_mem, hlG,
      Or.inl ⟨hlG.left_mem, hl'.left_mem⟩,
      Or.inl ⟨hlG.right_mem, hl'.right_mem⟩⟩

theorem areConnectedIn_uncontractSubgraph_iff [DecidableEq α] {G H' : Graph α β} {e₀ : β}
    {u u' : α} (hl₀ : G.IsLink e₀ u u') (hH' : H' ≤ contractEdge G e₀ u u')
    {a b : α} (ha : a ∉ ({u, u'} : Set α)) (hb : b ∉ ({u, u'} : Set α)) :
    AreConnectedIn (uncontractSubgraph G H' e₀ u u') a b ↔ AreConnectedIn H' a b := by
  let U := uncontractSubgraph G H' e₀ u u'
  have hl_U : U.IsLink e₀ u u' := isLink_e₀_uncontractSubgraph hl₀
  rw [← areConnectedIn_contractEdge_iff hl_U ha hb]
  have ha_ne : a ≠ u' := fun h => ha (Or.inr h)
  have hb_ne : b ≠ u' := fun h => hb (Or.inr h)
  have hV_iff : ∀ z : α, z ∉ ({u, u'} : Set α) →
      (z ∈ V(contractEdge U e₀ u u') ↔ z ∈ V(H')) := by
    intro z hz
    have hz_ne : z ≠ u' := fun h => hz (Or.inr h)
    constructor
    · rintro ⟨z₀, hz₀, hz_eq⟩
      by_cases hz₀_u' : z₀ = u'
      · subst hz₀_u'
        rw [contractVertMap_other] at hz_eq
        exact (hz (Or.inl hz_eq.symm)).elim
      · rw [contractVertMap_eq_of_ne hz₀_u'] at hz_eq
        subst hz_eq
        rcases vertex_mem_uncontractSubgraph_iff.mp hz₀ with ⟨_, hzH'⟩ | rfl | rfl
        · rwa [contractVertMap_eq_of_ne hz₀_u'] at hzH'
        · exact (hz (Or.inl rfl)).elim
        · exact (hz (Or.inr rfl)).elim
    · intro hzH'
      have hz_G : z ∈ V(G) := by
        rcases hH'.vertexSet_mono hzH' with ⟨z₀, hz₀, hz_eq⟩
        by_cases hz₀_u' : z₀ = u'
        · subst hz₀_u'
          rw [contractVertMap_other] at hz_eq
          exact (hz (Or.inl hz_eq.symm)).elim
        · rw [contractVertMap_eq_of_ne hz₀_u'] at hz_eq
          exact hz_eq ▸ hz₀
      refine ⟨z, vertex_mem_uncontractSubgraph_iff.mpr (Or.inl ⟨hz_G, ?_⟩),
        contractVertMap_eq_of_ne hz_ne⟩
      rwa [contractVertMap_eq_of_ne hz_ne]
  have hwalk_iff : ∀ {x y : α}, x ∈ V(H') →
      (Nonempty (GraphWalk (contractEdge U e₀ u u') x y) ↔ Nonempty (GraphWalk H' x y)) := by
    intro x y hxH'
    constructor
    · rintro ⟨W⟩
      induction W with
      | nil _ => exact ⟨.nil hxH'⟩
      | cons hl rest ih =>
        have hl' := (contractEdge_uncontractSubgraph_links hH').mp hl
        obtain ⟨W'⟩ := ih hl'.right_mem
        exact ⟨.cons hl' W'⟩
    · rintro ⟨W⟩
      induction W with
      | @nil z hz =>
        have hzU : z ∈ V(contractEdge U e₀ u u') := by
          rcases hH'.vertexSet_mono hz with ⟨z₀, hz₀, rfl⟩
          exact ⟨z₀, vertex_mem_uncontractSubgraph_iff.mpr (Or.inl ⟨hz₀,
            (contractVertMap_idem u u' z₀).symm ▸ hz⟩), rfl⟩
        exact ⟨.nil hzU⟩
      | cons hl rest ih =>
        have hl_c := (contractEdge_uncontractSubgraph_links hH').mpr hl
        obtain ⟨W'⟩ := ih hl.right_mem
        exact ⟨.cons hl_c W'⟩
  rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk, hV_iff a ha, hV_iff b hb]
  exact ⟨fun ⟨haH', hbH', hW⟩ => ⟨haH', hbH', (hwalk_iff haH').mp hW⟩,
    fun ⟨haH', hbH', hW⟩ => ⟨haH', hbH', (hwalk_iff haH').mpr hW⟩⟩

/-- Adding a single edge `e₀` of `G` and its endpoints `u, u'` to a subgraph `L' ≤ G`. -/
def addEdgeAndEnds (G L' : Graph α β) (e₀ : β) (u u' : α) : Graph α β :=
  (G.induce (V(L') ∪ {u, u'})).restrict (E(L') ∪ {e₀})

theorem addEdgeAndEnds_le {G L' : Graph α β} (hL'G : L' ≤ G) {e₀ : β} {u u' : α}
    (hl₀ : G.IsLink e₀ u u') :
    addEdgeAndEnds G L' e₀ u u' ≤ G := by
  refine restrict_le.trans (induce_le ?_)
  rintro x (hx | rfl | rfl)
  · exact hL'G.vertexSet_mono hx
  · exact hl₀.left_mem
  · exact hl₀.right_mem

theorem isLink_addEdgeAndEnds_iff {G L' : Graph α β} (hL'G : L' ≤ G) {e₀ : β} {u u' : α}
    (hl₀ : G.IsLink e₀ u u') {e : β} {x y : α} :
    (addEdgeAndEnds G L' e₀ u u').IsLink e x y ↔
      L'.IsLink e x y ∨ (e = e₀ ∧ G.IsLink e₀ x y) := by
  unfold addEdgeAndEnds
  rw [restrict_isLink, induce_isLink]
  constructor
  · rintro ⟨heL' | rfl, hlG, _, _⟩
    · exact Or.inl ((hL'G.isLink_iff heL').mpr hlG)
    · exact Or.inr ⟨rfl, hlG⟩
  · rintro (hlL' | ⟨rfl, hlG⟩)
    · exact ⟨Or.inl hlL'.edge_mem, hL'G.isLink_mono hlL',
        Or.inl hlL'.left_mem, Or.inl hlL'.right_mem⟩
    · rcases hlG.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨Or.inr rfl, hlG, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
      · exact ⟨Or.inr rfl, hlG, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩

theorem hasSameEffectOn_addEdgeAndEnds_of_notMem [DecidableEq α] {G L' : Graph α β}
    (hL'G : L' ≤ G) {e₀ : β} {u u' : α} (hl₀ : G.IsLink e₀ u u')
    (hu_not : u ∉ V(L')) {Z : Set α} (huZ : u ∉ Z) (hu'Z : u' ∉ Z) :
    HasSameEffectOn (addEdgeAndEnds G L' e₀ u u') L' Z := by
  rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
  intro a haZ b hbZ
  rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
  have ha_ne_u : a ≠ u := fun h => huZ (h ▸ haZ)
  have hb_ne_u : b ≠ u := fun h => huZ (h ▸ hbZ)
  have ha_ne_u' : a ≠ u' := fun h => hu'Z (h ▸ haZ)
  have hb_ne_u' : b ≠ u' := fun h => hu'Z (h ▸ hbZ)
  have hle : L' ≤ addEdgeAndEnds G L' e₀ u u' := by
    refine ⟨fun x hx => Or.inl hx, fun e x y hl => ?_⟩
    exact (isLink_addEdgeAndEnds_iff hL'G hl₀).mpr (Or.inl hl)
  constructor
  · rintro ⟨ha_mem, hb_mem, ⟨W⟩⟩
    have haL' : a ∈ V(L') := ha_mem.resolve_right
      (by rintro (rfl | rfl); exact ha_ne_u rfl; exact ha_ne_u' rfl)
    have hbL' : b ∈ V(L') := hb_mem.resolve_right
      (by rintro (rfl | rfl); exact hb_ne_u rfl; exact hb_ne_u' rfl)
    refine ⟨haL', hbL', ?_⟩
    have hproj : ∀ {x y : α} (W₀ : GraphWalk (addEdgeAndEnds G L' e₀ u u') x y),
        contractVertMap u' u x ∈ V(L') → contractVertMap u' u y ∈ V(L') →
        Nonempty (GraphWalk L' (contractVertMap u' u x) (contractVertMap u' u y)) := by
      intro x y W₀ hx hy
      induction W₀ with
      | nil _ => exact ⟨.nil hx⟩
      | @cons x₁ y₁ z₁ e hl rest ih =>
        rcases (isLink_addEdgeAndEnds_iff hL'G hl₀).mp hl with hlL' | ⟨rfl, hlG⟩
        · have hx₁_ne : x₁ ≠ u := fun h => hu_not (h ▸ hlL'.left_mem)
          have hy₁_ne : y₁ ≠ u := fun h => hu_not (h ▸ hlL'.right_mem)
          have hy₁_map : contractVertMap u' u y₁ ∈ V(L') := by
            rw [contractVertMap_eq_of_ne hy₁_ne]
            exact hlL'.right_mem
          obtain ⟨W_rest⟩ := ih hy₁_map hy
          rw [contractVertMap_eq_of_ne hy₁_ne] at W_rest
          rw [contractVertMap_eq_of_ne hx₁_ne]
          exact ⟨.cons hlL' W_rest⟩
        · have hxy_eq : contractVertMap u' u x₁ = contractVertMap u' u y₁ := by
            rcases hlG.eq_and_eq_or_eq_and_eq hl₀ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              simp [contractVertMap]
          rw [hxy_eq] at hx ⊢
          exact ih hx hy
    have ha_map : contractVertMap u' u a = a := contractVertMap_eq_of_ne ha_ne_u
    have hb_map : contractVertMap u' u b = b := contractVertMap_eq_of_ne hb_ne_u
    obtain ⟨W'⟩ := hproj W (ha_map.symm ▸ haL') (hb_map.symm ▸ hbL')
    rw [ha_map, hb_map] at W'
    exact ⟨W'⟩
  · rintro ⟨haL', hbL', ⟨W⟩⟩
    obtain ⟨W', _, _⟩ := exists_walk_up_of_le hle W
    exact ⟨hle.vertexSet_mono haL', hle.vertexSet_mono hbL', ⟨W'⟩⟩

/-- If `C` is a connected component of `H₀`, any edge of `H₀` incident with a vertex in `V(C)` is an
edge of `C`. -/
theorem isLink_of_mem_graphComponents {H₀ C : Graph α β} (hC : C ∈ graphComponents H₀)
    {e : β} {x y : α} (hl : H₀.IsLink e x y) (hx : x ∈ V(C)) :
    C.IsLink e x y := by
  let K := addEdgeAndEnds H₀ C e x y
  have hCK : C ≤ K := by
    refine ⟨fun z hz => Or.inl hz, fun f a b hlf => ?_⟩
    exact (isLink_addEdgeAndEnds_iff hC.1 hl).mpr (Or.inl hlf)
  have hKH₀ : K ≤ H₀ := addEdgeAndEnds_le hC.1 hl
  have hle_walk : ∀ {a b : α}, Nonempty (GraphWalk C a b) → Nonempty (GraphWalk K a b) := by
    rintro a b ⟨W⟩
    obtain ⟨W', _, _⟩ := exists_walk_up_of_le hCK W
    exact ⟨W'⟩
  have hlK : K.IsLink e x y := (isLink_addEdgeAndEnds_iff hC.1 hl).mpr (Or.inr ⟨rfl, hl⟩)
  have hto_x : ∀ z ∈ V(K), Nonempty (GraphWalk K z x) := by
    rintro z (hzC | rfl | rfl)
    · exact hle_walk (hC.2.1.2 z hzC x hx)
    · exact ⟨.nil (hCK.vertexSet_mono hx)⟩
    · exact ⟨.cons hlK.symm (.nil (hCK.vertexSet_mono hx))⟩
  have hK_conn : IsGraphConnected K := by
    refine ⟨⟨x, hCK.vertexSet_mono hx⟩, fun a ha b hb => ?_⟩
    obtain ⟨Wa⟩ := hto_x a ha
    obtain ⟨Wb⟩ := hto_x b hb
    exact ⟨Wa.append Wb.reverse⟩
  have h_eq : K = C := hC.2.2 K hCK hKH₀ hK_conn
  exact h_eq ▸ hlK

/-- Deleting a loop `e₀` (where `G.IsLink e₀ u u`) from a connected graph `H` preserves
connectivity. -/
theorem isGraphConnected_deleteEdges_singleton_of_loop {H : Graph α β} {e₀ : β} {u : α}
    (hloop : ∀ x y, H.IsLink e₀ x y → x = u ∧ y = u)
    (hconn : IsGraphConnected H) :
    IsGraphConnected (H.deleteEdges {e₀}) := by
  rcases hconn with ⟨⟨z, hz⟩, hreach⟩
  refine ⟨⟨z, hz⟩, fun a ha b hb => ?_⟩
  obtain ⟨W⟩ := hreach a ha b hb
  have hwalk : ∀ {x y : α}, GraphWalk H x y → Nonempty (GraphWalk (H.deleteEdges {e₀}) x y) := by
    intro x y W₀
    induction W₀ with
    | nil hx => exact ⟨.nil hx⟩
    | @cons x₁ y₁ z₁ e hl rest ih =>
      obtain ⟨W'⟩ := ih
      by_cases he : e = e₀
      · subst he
        obtain ⟨rfl, rfl⟩ := hloop x₁ y₁ hl
        exact ⟨W'⟩
      · have hl_del : (H.deleteEdges {e₀}).IsLink e x₁ y₁ := by
          rw [deleteEdges_isLink]
          exact ⟨hl, he⟩
        exact ⟨.cons hl_del W'⟩
  exact hwalk W

/-- Deleting a loop `e₀` (where `G.IsLink e₀ u u`) from `L'` preserves `effectOn L' Z`. -/
theorem hasSameEffectOn_deleteEdges_singleton_of_loop {L' : Graph α β} {e₀ : β} {u : α}
    (hloop : ∀ x y, L'.IsLink e₀ x y → x = u ∧ y = u) (Z : Set α) :
    HasSameEffectOn (L'.deleteEdges {e₀}) L' Z := by
  rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
  intro a _ b _
  constructor
  · exact fun h => h.mono deleteEdges_le
  · rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
    rintro ⟨ha, hb, ⟨W⟩⟩
    have hwalk : ∀ {x y : α}, GraphWalk L' x y →
        Nonempty (GraphWalk (L'.deleteEdges {e₀}) x y) := by
      intro x y W₀
      induction W₀ with
      | nil hx => exact ⟨.nil hx⟩
      | @cons x₁ y₁ z₁ e hl rest ih =>
        obtain ⟨W'⟩ := ih
        by_cases he : e = e₀
        · subst he
          obtain ⟨rfl, rfl⟩ := hloop x₁ y₁ hl
          exact ⟨W'⟩
        · have hl_del : (L'.deleteEdges {e₀}).IsLink e x₁ y₁ := by
            rw [deleteEdges_isLink]
            exact ⟨hl, he⟩
          exact ⟨.cons hl_del W'⟩
    exact ⟨ha, hb, hwalk W⟩

/-- If `(A, B)` is a separation of `G` with `(V(A) ∩ V(B)).ncard ≤ 1` and `Z ⊆ V(B)`, then
`subgraphInter G L B` has the same effect on `Z` as `L`. -/
theorem hasSameEffectOn_subgraphInter_of_separation_ncard_le_one [DecidableEq α]
    {G L A B : Graph α β} {Z : Set α}
    (hLG : L ≤ G) (hsep : IsGraphSeparation G A B)
    (hfin : (V(A) ∩ V(B)).Finite)
    (hcard : (V(A) ∩ V(B)).ncard ≤ 1) (hZB : Z ⊆ V(B)) :
    HasSameEffectOn (subgraphInter G L B) L Z := by
  rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
  intro a haZ b hbZ
  have hle : subgraphInter G L B ≤ L := subgraphInter_le_left hLG hsep.2.1
  constructor
  · exact fun h => h.mono hle
  · rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
    rintro ⟨haL, hbL, ⟨W⟩⟩
    have haB : a ∈ V(B) := hZB haZ
    have hbB : b ∈ V(B) := hZB hbZ
    refine ⟨⟨haL, haB⟩, ⟨hbL, hbB⟩, ?_⟩
    -- Project vertices in `V(L) \ V(B)` to the unique vertex `c₀ ∈ V(A) ∩ V(B)` if it exists.
    by_cases hne : (V(A) ∩ V(B)).Nonempty
    · rcases hne with ⟨c₀, hc₀⟩
      have h_uniq : ∀ z ∈ V(A) ∩ V(B), z = c₀ :=
        fun z hz => (ncard_le_one_iff hfin).mp hcard hz hc₀
      classical
      let f (x : α) : α := if x ∈ V(B) then x else c₀
      have hf_B : ∀ x, x ∈ V(B) → f x = x := fun x hx => by simp [f, hx]
      have hf_notB : ∀ x, x ∉ V(B) → f x = c₀ := fun x hx => by simp [f, hx]
      have hf_AB : ∀ x ∈ V(A), f x ∈ V(B) := by
        intro x hxA
        by_cases hxB : x ∈ V(B)
        · rw [hf_B x hxB]; exact hxB
        · rw [hf_notB x hxB]; exact hc₀.2
      have hproj : ∀ {x y : α} (W₀ : GraphWalk L x y),
          f x ∈ V(L) ∩ V(B) → f y ∈ V(L) ∩ V(B) →
          Nonempty (GraphWalk (subgraphInter G L B) (f x) (f y)) := by
        intro x y W₀ hfx hfy
        induction W₀ with
        | nil _ => exact ⟨.nil hfx⟩
        | @cons x₁ y₁ z₁ e hl rest ih =>
          have hlG := hLG.isLink_mono hl
          have heG := hlG.edge_mem
          rw [ ← hsep.2.2.2.1] at heG
          rcases heG with heA | heB
          · have hlA := (hsep.1.isLink_iff heA).mpr hlG
            have hx₁_c₀ : f x₁ = c₀ := by
              by_cases hx₁B : x₁ ∈ V(B)
              · rw [hf_B x₁ hx₁B]; exact h_uniq x₁ ⟨hlA.left_mem, hx₁B⟩
              · exact hf_notB x₁ hx₁B
            have hy₁_c₀ : f y₁ = c₀ := by
              by_cases hy₁B : y₁ ∈ V(B)
              · rw [hf_B y₁ hy₁B]; exact h_uniq y₁ ⟨hlA.right_mem, hy₁B⟩
              · exact hf_notB y₁ hy₁B
            have hxy_eq : f x₁ = f y₁ := hx₁_c₀.trans hy₁_c₀.symm
            rw [hxy_eq] at hfx ⊢
            exact ih hfx hfy
          · have hlB := (hsep.2.1.isLink_iff heB).mpr hlG
            have hx₁B : x₁ ∈ V(B) := hlB.left_mem
            have hy₁B : y₁ ∈ V(B) := hlB.right_mem
            have hy₁_mem : f y₁ ∈ V(L) ∩ V(B) := by
              rw [hf_B y₁ hy₁B]
              exact ⟨hl.right_mem, hy₁B⟩
            obtain ⟨W_rest⟩ := ih hy₁_mem hfy
            rw [hf_B y₁ hy₁B] at W_rest
            rw [hf_B x₁ hx₁B]
            have hl_inter : (subgraphInter G L B).IsLink e x₁ y₁ := by
              rw [subgraphInter, restrict_isLink, induce_isLink]
              exact ⟨⟨hl.edge_mem, heB⟩, hlG, ⟨hl.left_mem, hx₁B⟩, ⟨hl.right_mem, hy₁B⟩⟩
            exact ⟨.cons hl_inter W_rest⟩
      obtain ⟨W'⟩ := hproj W (by rw [hf_B a haB]; exact ⟨haL, haB⟩)
        (by rw [hf_B b hbB]; exact ⟨hbL, hbB⟩)
      exact ⟨by simpa only [hf_B a haB, hf_B b hbB] using W'⟩
    · -- `V(A) ∩ V(B) = ∅`, so any walk starting in `V(B)` stays in `B`.
      have hdisj : Disjoint V(A) V(B) :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)
      have hstay : ∀ {x y : α} (W₀ : GraphWalk L x y),
          x ∈ V(B) → Nonempty (GraphWalk (subgraphInter G L B) x y) := by
        intro x y W₀ hxB
        induction W₀ with
        | nil hxL => exact ⟨.nil ⟨hxL, hxB⟩⟩
        | @cons x₁ y₁ z₁ e hl rest ih =>
          have hlG := hLG.isLink_mono hl
          have he_not_A : e ∉ E(A) := by
            intro heA
            have hlA := (hsep.1.isLink_iff heA).mpr hlG
            exact disjoint_left.mp hdisj hlA.left_mem hxB
          have heB : e ∈ E(B) := by
            have heG := hlG.edge_mem
            rw [← hsep.2.2.2.1] at heG
            exact heG.resolve_left he_not_A
          have hlB := (hsep.2.1.isLink_iff heB).mpr hlG
          obtain ⟨W_rest⟩ := ih hlB.right_mem
          have hl_inter : (subgraphInter G L B).IsLink e x₁ y₁ := by
            rw [subgraphInter, restrict_isLink, induce_isLink]
            exact ⟨⟨hl.edge_mem, heB⟩, hlG, ⟨hl.left_mem, hxB⟩, ⟨hl.right_mem, hlB.right_mem⟩⟩
          exact ⟨.cons hl_inter W_rest⟩
      exact hstay W haB

/-- Adding an edge `e₀` of `G` with endpoints `u, u'`, where `u ∉ V(L')`, preserves `effectOn L' Z`
provided `Z ⊆ V(L')`. -/
theorem hasSameEffectOn_addEdgeAndEnds_of_notMem_left {G L' : Graph α β} {e₀ : β} {u u' : α}
    {Z : Set α} (hL'G : L' ≤ G) (hl₀ : G.IsLink e₀ u u')
    (hu_not_L' : u ∉ V(L')) (hZL' : Z ⊆ V(L')) :
    HasSameEffectOn (addEdgeAndEnds G L' e₀ u u') L' Z := by
  let L'' := addEdgeAndEnds G L' e₀ u u'
  have hL'_le : L' ≤ L'' := by
    refine ⟨fun z hz => Or.inl hz, fun f x y hl => ?_⟩
    exact (isLink_addEdgeAndEnds_iff hL'G hl₀).mpr (Or.inl hl)
  rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
  intro a haZ b hbZ
  constructor
  · rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
    rintro ⟨_, _, ⟨W⟩⟩
    have haL' : a ∈ V(L') := hZL' haZ
    have hbL' : b ∈ V(L') := hZL' hbZ
    refine ⟨haL', hbL', ?_⟩
    have hmain : ∀ (n : ℕ) {x : α} (W₀ : GraphWalk L'' x b),
        W₀.length = n → x ∈ V(L') → Nonempty (GraphWalk L' x b) := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro x W₀ hlen hxL'
        cases W₀ with
        | nil _ => exact ⟨.nil hxL'⟩
        | @cons x y _ e₁ hl₁ W₁ =>
          rcases (isLink_addEdgeAndEnds_iff hL'G hl₀).mp hl₁ with hl₁' | ⟨he₁, hlG₁⟩
          · obtain ⟨W₁'⟩ := ih W₁.length (by subst hlen; exact Nat.lt_succ_self _)
              W₁ rfl hl₁'.right_mem
            exact ⟨.cons hl₁' W₁'⟩
          · subst he₁
            have hxy := hlG₁.eq_and_eq_or_eq_and_eq hl₀
            have hx_ne_u : x ≠ u := fun h => hu_not_L' (h ▸ hxL')
            have hy_u : y = u := (hxy.resolve_left fun h => hx_ne_u h.1).2
            cases W₁ with
            | nil _ => exact (hu_not_L' (hy_u ▸ hbL')).elim
            | @cons _ z _ e₂ hl₂ W₂ =>
              rcases (isLink_addEdgeAndEnds_iff hL'G hl₀).mp hl₂ with hl₂' | ⟨he₂, hlG₂⟩
              · exact (hu_not_L' (hy_u ▸ hl₂'.left_mem)).elim
              · subst he₂
                rcases hlG₂.eq_and_eq_or_eq_and_eq hl₀ with ⟨_, hz_u'⟩ | ⟨_, hz_u⟩
                · have hzx : z = x := by
                    have hx_u' : x = u' := (hxy.resolve_left fun h => hx_ne_u h.1).1
                    exact hz_u'.trans hx_u'.symm
                  subst hzx
                  exact ih W₂.length (by subst hlen; dsimp [GraphWalk.length]; omega) W₂ rfl hxL'
                · have hzy : z = y := hz_u.trans hy_u.symm
                  subst hzy
                  let W_short : GraphWalk L'' x b := .cons hl₁ W₂
                  exact ih W_short.length
                    (by subst hlen; dsimp [W_short, GraphWalk.length]; omega) W_short rfl hxL'
    exact hmain W.length W rfl haL'
  · exact fun h => h.mono hL'_le

/-- If `L'` has the same effect on `Z` as `L` and `Z ⊆ V(L)`, then `Z ⊆ V(L')`. -/
theorem subset_vertexSet_of_hasSameEffectOn {L' L : Graph α β} {Z : Set α}
    (hSame : HasSameEffectOn L' L Z) (hZL : Z ⊆ V(L)) :
    Z ⊆ V(L') := by
  intro z hz
  have hconn : AreConnectedIn L z z := by
    rw [areConnectedIn_iff_walk]
    exact ⟨hZL hz, hZL hz, ⟨.nil (hZL hz)⟩⟩
  have hconn' : AreConnectedIn L' z z :=
    (effectOn_eq_iff_areConnectedIn.mp hSame z hz z hz).mpr hconn
  rw [areConnectedIn_iff_walk] at hconn'
  exact hconn'.1

/-- The union of a subgraph `L' ≤ G` and a family of subgraphs `C : ι → Graph α β` in `G`. -/
def subgraphUnionFamily {ι : Type*} (G L' : Graph α β) (C : ι → Graph α β) : Graph α β :=
  (G.induce (V(L') ∪ ⋃ i, V(C i))).restrict (E(L') ∪ ⋃ i, E(C i))

theorem subgraphUnionFamily_le {ι : Type*} {G L' : Graph α β} {C : ι → Graph α β}
    (hL' : L' ≤ G) (hC : ∀ i, C i ≤ G) :
    subgraphUnionFamily G L' C ≤ G :=
  restrict_le.trans (induce_le (union_subset hL'.vertexSet_mono
    (iUnion_subset fun i => (hC i).vertexSet_mono)))

@[simp]
theorem vertexSet_subgraphUnionFamily {ι : Type*} (G L' : Graph α β) (C : ι → Graph α β) :
    V(subgraphUnionFamily G L' C) = V(L') ∪ ⋃ i, V(C i) := rfl

theorem isLink_subgraphUnionFamily_iff {ι : Type*} {G L' : Graph α β} {C : ι → Graph α β}
    (hL' : L' ≤ G) (hC : ∀ i, C i ≤ G) {e : β} {x y : α} :
    (subgraphUnionFamily G L' C).IsLink e x y ↔
      (e ∈ E(L') ∪ ⋃ i, E(C i)) ∧ G.IsLink e x y := by
  unfold subgraphUnionFamily
  rw [restrict_isLink, induce_isLink]
  refine ⟨fun ⟨he, hlG, _, _⟩ => ⟨he, hlG⟩, fun ⟨he, hlG⟩ => ⟨he, hlG, ?_⟩⟩
  rcases he with heL' | heC
  · have hl := (hL'.isLink_iff heL').mpr hlG
    exact ⟨Or.inl hl.left_mem, Or.inl hl.right_mem⟩
  · rcases mem_iUnion.mp heC with ⟨i, hei⟩
    have hl := ((hC i).isLink_iff hei).mpr hlG
    exact ⟨Or.inr (mem_iUnion.mpr ⟨i, hl.left_mem⟩), Or.inr (mem_iUnion.mpr ⟨i, hl.right_mem⟩)⟩

theorem edgeSet_subgraphUnionFamily {ι : Type*} {G L' : Graph α β} {C : ι → Graph α β}
    (hL' : L' ≤ G) (hC : ∀ i, C i ≤ G) :
    E(subgraphUnionFamily G L' C) = E(L') ∪ ⋃ i, E(C i) := by
  ext e
  rw [(subgraphUnionFamily G L' C).edge_mem_iff_exists_isLink]
  simp only [isLink_subgraphUnionFamily_iff hL' hC]
  refine ⟨fun ⟨_, _, he, _⟩ => he, fun he => ?_⟩
  rcases he with heL' | heC
  · obtain ⟨x, y, hl⟩ := L'.exists_isLink_of_mem_edgeSet heL'
    exact ⟨x, y, Or.inl heL', hL'.isLink_mono hl⟩
  · rcases mem_iUnion.mp heC with ⟨i, hei⟩
    obtain ⟨x, y, hl⟩ := (C i).exists_isLink_of_mem_edgeSet hei
    exact ⟨x, y, Or.inr (mem_iUnion.mpr ⟨i, hei⟩), (hC i).isLink_mono hl⟩

theorem le_subgraphUnionFamily_left {ι : Type*} {G L' : Graph α β} {C : ι → Graph α β}
    (hL' : L' ≤ G) (hC : ∀ i, C i ≤ G) :
    L' ≤ subgraphUnionFamily G L' C := by
  refine ⟨subset_union_left, fun e x y hl => ?_⟩
  rw [isLink_subgraphUnionFamily_iff hL' hC]
  exact ⟨Or.inl hl.edge_mem, hL'.isLink_mono hl⟩

theorem le_subgraphUnionFamily_right {ι : Type*} {G L' : Graph α β} {C : ι → Graph α β}
    (hL' : L' ≤ G) (hC : ∀ i, C i ≤ G) (i : ι) :
    C i ≤ subgraphUnionFamily G L' C := by
  refine ⟨fun x hx => Or.inr (mem_iUnion.mpr ⟨i, hx⟩), fun e x y hl => ?_⟩
  rw [isLink_subgraphUnionFamily_iff hL' hC]
  exact ⟨Or.inr (mem_iUnion.mpr ⟨i, hl.edge_mem⟩), (hC i).isLink_mono hl⟩

theorem contractVertMap_eq_iff [DecidableEq α] {u u' x y : α} :
    contractVertMap u u' x = contractVertMap u u' y ↔
      x = y ∨ ((x = u ∨ x = u') ∧ (y = u ∨ y = u')) := by
  constructor
  · intro h
    by_cases hx : x = u' <;> by_cases hy : y = u' <;> simp_all [contractVertMap]
  · rintro (rfl | ⟨rfl | rfl, rfl | rfl⟩) <;> simp [contractVertMap]

theorem deleteEdges_mono {H₁ H₂ : Graph α β} (hle : H₁ ≤ H₂) (E₀ : Set β) :
    H₁.deleteEdges E₀ ≤ H₂.deleteEdges E₀ := by
  refine ⟨hle.vertexSet_mono, fun e x y hl => ?_⟩
  rw [deleteEdges_isLink] at hl ⊢
  exact ⟨hle.isLink_mono hl.1, hl.2⟩

/-! ## 3. Combinatorial Reduction (Claims (3)–(7)) and Proof of Theorem (3.1) -/

/-- The combinatorial configuration extracted from the insulated surface drawing in the proof of
**3.1** (pages 535–537), closed under edge deletion of loops and edge contraction of non-loop edges
in `E(L') ∩ E(C i)`. -/
private structure InsulatedSystem (α : Type u) (β : Type v) (w : ℕ) where
  G : Graph α β
  L : Graph α β
  Γ₁ : Graph α β
  Z : Set α
  C : Fin (w + 2) → Graph α β
  hG_finV : V(G).Finite
  hG_finE : E(G).Finite
  hLG : L ≤ G
  hΓ₁G : Γ₁ ≤ G
  hZL : Z ⊆ V(L)
  hZ_disj : ∀ i, Disjoint Z V(C i)
  hC_Γ₁ : ∀ i, C i ≤ Γ₁
  hC_conn : ∀ i, IsGraphConnected (C i)
  hC_disj : ∀ i j, i ≠ j → Disjoint V(C i) V(C j)
  hVG : V(G) = V(L) ∪ ⋃ i, V(C i)
  hEG : E(G) = E(L) ∪ ⋃ i, E(C i)
  hCore : ∀ L_star ≤ G, HasSameEffectOn L_star L Z →
    ∃ D : Fin (w + 2) → Graph α β,
      (∀ r, D r ≤ subgraphInter G L_star Γ₁) ∧
      (∀ r, IsGraphConnected (D r)) ∧
      (∀ r e x y, (subgraphInter G L_star Γ₁).IsLink e x y → x ∈ V(D r) → (D r).IsLink e x y) ∧
      (∀ r₁ r₂, r₁ ≠ r₂ → Disjoint V(D r₁) V(D r₂)) ∧
      (∀ r i, (V(D r) ∩ V(C i)).Nonempty)

theorem subgraphInter_subgraphInter_right {G G₁ L_star Γ₁ : Graph α β}
    (hG₁G : G₁ ≤ G) (hL_star : L_star ≤ G₁) :
    subgraphInter G₁ L_star (subgraphInter G G₁ Γ₁) = subgraphInter G L_star Γ₁ := by
  refine Graph.ext ?_ fun e x y => ?_
  · ext z
    change z ∈ V(L_star) ∩ (V(G₁) ∩ V(Γ₁)) ↔ z ∈ V(L_star) ∩ V(Γ₁)
    exact ⟨fun ⟨hzL, _, hzΓ⟩ => ⟨hzL, hzΓ⟩,
      fun ⟨hzL, hzΓ⟩ => ⟨hzL, hL_star.vertexSet_mono hzL, hzΓ⟩⟩
  · simp only [subgraphInter, restrict_isLink, induce_isLink, mem_inter_iff]
    constructor
    · rintro ⟨⟨heL, heG₁_Γ₁⟩, hlG₁, ⟨hxL, _, hxΓ⟩, ⟨hyL, _, hyΓ⟩⟩
      have heΓ : e ∈ E(Γ₁) := heG₁_Γ₁.2.2
      exact ⟨⟨heL, heΓ⟩, hG₁G.isLink_mono hlG₁, ⟨hxL, hxΓ⟩, ⟨hyL, hyΓ⟩⟩
    · rintro ⟨⟨heL, heΓ⟩, hlG, ⟨hxL, hxΓ⟩, ⟨hyL, hyΓ⟩⟩
      have heG₁ : e ∈ E(G₁) := hL_star.edgeSet_mono heL
      have hlG₁ : G₁.IsLink e x y := (hG₁G.isLink_iff heG₁).mpr hlG
      have he_inter : e ∈ E((G.induce (V(G₁) ∩ V(Γ₁))).restrict (E(G₁) ∩ E(Γ₁))) := by
        rw [((G.induce (V(G₁) ∩ V(Γ₁))).restrict (E(G₁) ∩ E(Γ₁))).edge_mem_iff_exists_isLink]
        refine ⟨x, y, ?_⟩
        rw [restrict_isLink, induce_isLink]
        exact ⟨⟨heG₁, heΓ⟩, hlG, ⟨hlG₁.left_mem, hxΓ⟩, ⟨hlG₁.right_mem, hyΓ⟩⟩
      exact ⟨⟨heL, he_inter⟩, hlG₁,
        ⟨hxL, hlG₁.left_mem, hxΓ⟩, ⟨hyL, hlG₁.right_mem, hyΓ⟩⟩

/-- Claim (4) of **3.1** (page 536): replacing `L` by any `L' ≤ G` with the same effect on `Z` as `L`
and shrinking `G` to `L' ∪ ⋃ i, C i` yields an `InsulatedSystem` with `G₁ ≤ G`. -/
private def InsulatedSystem.shrinkTo {w : ℕ} (S : InsulatedSystem α β w)
    {L' : Graph α β} (hL'G : L' ≤ S.G) (hSame : HasSameEffectOn L' S.L S.Z) :
    InsulatedSystem α β w :=
  let hC_G : ∀ i, S.C i ≤ S.G := fun i => (S.hC_Γ₁ i).trans S.hΓ₁G
  let G₁ := subgraphUnionFamily S.G L' S.C
  let hG₁G : G₁ ≤ S.G := subgraphUnionFamily_le hL'G hC_G
  let Γ₁' := subgraphInter S.G G₁ S.Γ₁
  { G := G₁
    L := L'
    Γ₁ := Γ₁'
    Z := S.Z
    C := S.C
    hG_finV := S.hG_finV.subset hG₁G.vertexSet_mono
    hG_finE := S.hG_finE.subset hG₁G.edgeSet_mono
    hLG := le_subgraphUnionFamily_left hL'G hC_G
    hΓ₁G := subgraphInter_le_left hG₁G S.hΓ₁G
    hZL := subset_vertexSet_of_hasSameEffectOn hSame S.hZL
    hZ_disj := S.hZ_disj
    hC_Γ₁ := fun i => by
      have hCi_G₁ : S.C i ≤ G₁ := le_subgraphUnionFamily_right hL'G hC_G i
      refine ⟨fun x hx => ⟨hCi_G₁.vertexSet_mono hx, (S.hC_Γ₁ i).vertexSet_mono hx⟩,
        fun e x y hl => ?_⟩
      change ((S.G.induce (V(G₁) ∩ V(S.Γ₁))).restrict (E(G₁) ∩ E(S.Γ₁))).IsLink e x y
      rw [restrict_isLink, induce_isLink]
      exact ⟨⟨hCi_G₁.edgeSet_mono hl.edge_mem, (S.hC_Γ₁ i).edgeSet_mono hl.edge_mem⟩,
        (hC_G i).isLink_mono hl,
        ⟨hCi_G₁.vertexSet_mono hl.left_mem, (S.hC_Γ₁ i).vertexSet_mono hl.left_mem⟩,
        ⟨hCi_G₁.vertexSet_mono hl.right_mem, (S.hC_Γ₁ i).vertexSet_mono hl.right_mem⟩⟩
    hC_conn := S.hC_conn
    hC_disj := S.hC_disj
    hVG := rfl
    hEG := edgeSet_subgraphUnionFamily hL'G hC_G
    hCore := fun L_star hL_star hSame_star => by
      have hSame_L : HasSameEffectOn L_star S.L S.Z := hSame_star.trans hSame
      obtain ⟨D, hD_le, hD_conn, hD_link, hD_disj, hD_meet⟩ :=
        S.hCore L_star (hL_star.trans hG₁G) hSame_L
      have hInter_eq : subgraphInter G₁ L_star Γ₁' = subgraphInter S.G L_star S.Γ₁ :=
        subgraphInter_subgraphInter_right hG₁G hL_star
      rw [hInter_eq]
      exact ⟨D, hD_le, hD_conn, hD_link, hD_disj, hD_meet⟩ }

/-- Deleting a loop `e₀ ∈ E(L') ∩ E(C i₀)` yields an `InsulatedSystem` with strictly fewer edges. -/
private def InsulatedSystem.deleteLoop {w : ℕ} (S : InsulatedSystem α β w)
    {e₀ : β} {u : α} (hl₀ : S.G.IsLink e₀ u u) :
    InsulatedSystem α β w :=
  let hloop : ∀ H ≤ S.G, ∀ x y, H.IsLink e₀ x y → x = u ∧ y = u := fun H hHG x y hl => by
    rcases (hHG.isLink_mono hl).eq_and_eq_or_eq_and_eq hl₀ with h | h <;> exact h
  { G := S.G.deleteEdges {e₀}
    L := S.L.deleteEdges {e₀}
    Γ₁ := S.Γ₁.deleteEdges {e₀}
    Z := S.Z
    C := fun i => (S.C i).deleteEdges {e₀}
    hG_finV := S.hG_finV
    hG_finE := S.hG_finE.subset (deleteEdges_le.edgeSet_mono)
    hLG := deleteEdges_mono S.hLG {e₀}
    hΓ₁G := deleteEdges_mono S.hΓ₁G {e₀}
    hZL := S.hZL
    hZ_disj := S.hZ_disj
    hC_Γ₁ := fun i => deleteEdges_mono (S.hC_Γ₁ i) {e₀}
    hC_conn := fun i => isGraphConnected_deleteEdges_singleton_of_loop
      (hloop (S.C i) ((S.hC_Γ₁ i).trans S.hΓ₁G)) (S.hC_conn i)
    hC_disj := S.hC_disj
    hVG := S.hVG
    hEG := by
      ext e
      simp only [edgeSet_deleteEdges, mem_sdiff, mem_union, mem_iUnion]
      rw [S.hEG]
      simp only [mem_union, mem_iUnion]
      tauto
    hCore := fun L_star hL_star hSame_star => by
      have hSame_L : HasSameEffectOn L_star S.L S.Z :=
        hSame_star.trans (hasSameEffectOn_deleteEdges_singleton_of_loop (hloop S.L S.hLG) S.Z)
      obtain ⟨D, hD_le, hD_conn, hD_link, hD_disj, hD_meet⟩ :=
        S.hCore L_star (hL_star.trans deleteEdges_le) hSame_L
      have hInter_eq :
          subgraphInter (S.G.deleteEdges {e₀}) L_star (S.Γ₁.deleteEdges {e₀}) =
            subgraphInter S.G L_star S.Γ₁ := by
        refine Graph.ext rfl fun e x y => ?_
        simp only [subgraphInter, restrict_isLink, induce_isLink, edgeSet_deleteEdges,
          vertexSet_deleteEdges, deleteEdges_isLink, mem_inter_iff, mem_sdiff]
        exact ⟨fun ⟨⟨heL, heΓ, _⟩, ⟨hlG, _⟩, hx, hy⟩ => ⟨⟨heL, heΓ⟩, hlG, hx, hy⟩,
          fun ⟨⟨heL, heΓ⟩, hlG, hx, hy⟩ => by
            have he_not : e ∉ ({e₀} : Set β) := (hL_star.edgeSet_mono heL).2
            exact ⟨⟨heL, heΓ, he_not⟩, ⟨hlG, he_not⟩, hx, hy⟩⟩
      rw [hInter_eq]
      exact ⟨D, hD_le, hD_conn, hD_link, hD_disj, hD_meet⟩ }

/-- Contracting a non-loop edge `e₀ ∈ E(L) ∩ E(C i₀)` yields an `InsulatedSystem` with strictly
smaller `|V(G)| + |E(G)|`. -/
private def InsulatedSystem.contractNonLoop [DecidableEq α] {w : ℕ} (S : InsulatedSystem α β w)
    {i₀ : Fin (w + 2)} {e₀ : β} {u u' : α}
    (hl_L : S.L.IsLink e₀ u u') (hl_C : (S.C i₀).IsLink e₀ u u') :
    InsulatedSystem α β w :=
  let hl_Γ₁ : S.Γ₁.IsLink e₀ u u' := (S.hC_Γ₁ i₀).isLink_mono hl_C
  let hl_G : S.G.IsLink e₀ u u' := S.hΓ₁G.isLink_mono hl_Γ₁
  let f := contractVertMap u u'
  have hu_C : u ∈ V(S.C i₀) := hl_C.left_mem
  have hu'_C : u' ∈ V(S.C i₀) := hl_C.right_mem
  have hf_Z_id : ∀ z ∈ S.Z, f z = z := fun z hz => by
    have hz_ne_u' : z ≠ u' := fun h => disjoint_left.mp (S.hZ_disj i₀) hz (h ▸ hu'_C)
    exact contractVertMap_eq_of_ne hz_ne_u'
  have hf_Z_eq : f '' S.Z = S.Z := by
    ext z
    refine ⟨?_, fun hz => ⟨z, hz, hf_Z_id z hz⟩⟩
    rintro ⟨w, hwZ, rfl⟩
    rw [hf_Z_id w hwZ]
    exact hwZ
  { G := contractEdge S.G e₀ u u'
    L := contractEdge S.L e₀ u u'
    Γ₁ := contractEdge S.Γ₁ e₀ u u'
    Z := S.Z
    C := fun i => contractEdge (S.C i) e₀ u u'
    hG_finV := S.hG_finV.image f
    hG_finE := S.hG_finE.subset sdiff_subset
    hLG := contractEdge_mono S.hLG e₀ u u'
    hΓ₁G := contractEdge_mono S.hΓ₁G e₀ u u'
    hZL := by
      rw [vertexSet_contractEdge, ← hf_Z_eq]
      exact image_mono S.hZL
    hZ_disj := fun i => by
      rw [vertexSet_contractEdge]
      refine disjoint_left.mpr fun z hzZ ⟨x, hxC, hfx⟩ => ?_
      have hfz : f z = z := hf_Z_id z hzZ
      rcases contractVertMap_eq_iff.mp (hfx.trans hfz.symm) with rfl | ⟨_, hz⟩
      · exact disjoint_left.mp (S.hZ_disj i) hzZ hxC
      · rcases hz with rfl | rfl
        · exact disjoint_left.mp (S.hZ_disj i₀) hzZ hu_C
        · exact disjoint_left.mp (S.hZ_disj i₀) hzZ hu'_C
    hC_Γ₁ := fun i => contractEdge_mono (S.hC_Γ₁ i) e₀ u u'
    hC_conn := fun i => by
      by_cases hi : i = i₀
      · subst hi
        exact isGraphConnected_contractEdge_of_isLink hl_C (S.hC_conn i)
      · have hdisj := S.hC_disj i i₀ hi
        have he₀_not : e₀ ∉ E(S.C i) := by
          intro he
          have hl_i := (((S.hC_Γ₁ i).trans S.hΓ₁G).isLink_iff he).mpr hl_G
          exact disjoint_left.mp hdisj hl_i.left_mem hu_C
        exact isGraphConnected_contractEdge_of_notMem he₀_not (S.hC_conn i)
    hC_disj := fun i j hij => by
      simp only [vertexSet_contractEdge]
      refine disjoint_left.mpr ?_
      rintro _ ⟨x, hxC, rfl⟩ ⟨y, hyC, hfy⟩
      rcases contractVertMap_eq_iff.mp hfy.symm with rfl | ⟨hx_uu', hy_uu'⟩
      · exact disjoint_left.mp (S.hC_disj i j hij) hxC hyC
      · have hx_i₀ : x ∈ V(S.C i₀) := by rcases hx_uu' with rfl | rfl <;> assumption
        have hy_i₀ : y ∈ V(S.C i₀) := by rcases hy_uu' with rfl | rfl <;> assumption
        have hi : i = i₀ := by_contra fun hne => disjoint_left.mp (S.hC_disj i i₀ hne) hxC hx_i₀
        have hj : j = i₀ := by_contra fun hne => disjoint_left.mp (S.hC_disj j i₀ hne) hyC hy_i₀
        exact hij (hi.trans hj.symm)
    hVG := by
      simp only [vertexSet_contractEdge]
      rw [S.hVG, image_union, image_iUnion]
    hEG := by
      ext e
      simp only [edgeSet_contractEdge, mem_sdiff, mem_union, mem_iUnion]
      rw [S.hEG]
      simp only [mem_union, mem_iUnion]
      tauto
    hCore := fun H' hH' hSame_H' => by
      let U := uncontractSubgraph S.G H' e₀ u u'
      have hU_G : U ≤ S.G := uncontractSubgraph_le hl_G
      have hZ_not_uu' : ∀ z ∈ S.Z, z ∉ ({u, u'} : Set α) := by
        rintro z hz (rfl | rfl)
        · exact disjoint_left.mp (S.hZ_disj i₀) hz hu_C
        · exact disjoint_left.mp (S.hZ_disj i₀) hz hu'_C
      have hSame_U : HasSameEffectOn U S.L S.Z := by
        rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
        intro a ha b hb
        have h1 := areConnectedIn_uncontractSubgraph_iff hl_G hH'
          (hZ_not_uu' a ha) (hZ_not_uu' b hb)
        have h2 := effectOn_eq_iff_areConnectedIn.mp hSame_H' a ha b hb
        have h3 := areConnectedIn_contractEdge_iff hl_L
          (hZ_not_uu' a ha) (hZ_not_uu' b hb)
        exact h1.trans (h2.trans h3)
      obtain ⟨D, hD_le, hD_conn, hD_link, hD_disj, hD_meet⟩ := S.hCore U hU_G hSame_U
      have hl₀_inter : (subgraphInter S.G U S.Γ₁).IsLink e₀ u u' := by
        rw [subgraphInter, restrict_isLink, induce_isLink]
        have hl_U : U.IsLink e₀ u u' := isLink_e₀_uncontractSubgraph hl_G
        exact ⟨⟨hl_U.edge_mem, hl_Γ₁.edge_mem⟩, hl_G,
          ⟨hl_U.left_mem, hl_Γ₁.left_mem⟩, ⟨hl_U.right_mem, hl_Γ₁.right_mem⟩⟩
      have hD_e₀ : ∀ r, (u ∈ V(D r) ∨ u' ∈ V(D r)) → (D r).IsLink e₀ u u' := by
        rintro r (hu | hu')
        · exact hD_link r e₀ u u' hl₀_inter hu
        · exact (hD_link r e₀ u' u hl₀_inter.symm hu').symm
      have hwalk_H' : ∀ {a b : α},
          GraphWalk (contractEdge U e₀ u u') a b → a ∈ V(H') → b ∈ V(H') := by
        intro a b W haH'
        induction W with
        | nil _ => exact haH'
        | cons hl _ ih =>
          exact ih ((contractEdge_uncontractSubgraph_links hH').mp hl).right_mem
      have hf_mem_H' : ∀ r, ∀ x ∈ V(D r), f x ∈ V(H') := by
        intro r x hxD
        let i0_fin : Fin (w + 2) := ⟨0, Nat.succ_pos _⟩
        let i1_fin : Fin (w + 2) := ⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩
        let j : Fin (w + 2) := if i₀ = i0_fin then i1_fin else i0_fin
        have hj_ne : j ≠ i₀ := by
          by_cases h : i₀ = i0_fin
          · have hj_eq : j = i1_fin := by simp [j, h]
            rw [hj_eq, h]
            intro h01
            exact Nat.one_ne_zero (congrArg Fin.val h01)
          · have hj_eq : j = i0_fin := by simp [j, h]
            rw [hj_eq]
            exact Ne.symm h
        obtain ⟨y, hyD, hyC⟩ := hD_meet r j
        have hy_not_uu' : y ∉ ({u, u'} : Set α) := by
          rintro (rfl | rfl)
          · exact disjoint_left.mp (S.hC_disj j i₀ hj_ne) hyC hu_C
          · exact disjoint_left.mp (S.hC_disj j i₀ hj_ne) hyC hu'_C
        have hyU : y ∈ V(U) := ((hD_le r).trans (subgraphInter_le_left hU_G S.hΓ₁G)).vertexSet_mono hyD
        have hfy_H' : f y ∈ V(H') := by
          rcases vertex_mem_uncontractSubgraph_iff.mp hyU with ⟨_, hfy⟩ | rfl | rfl
          · exact hfy
          · exact (hy_not_uu' (Or.inl rfl)).elim
          · exact (hy_not_uu' (Or.inr rfl)).elim
        obtain ⟨W⟩ := (hD_conn r).2 y hyD x hxD
        obtain ⟨W_U, _, _⟩ := exists_walk_up_of_le
          ((hD_le r).trans (subgraphInter_le_left hU_G S.hΓ₁G)) W
        obtain ⟨W_c⟩ := walk_contractEdge_of_isLink (isLink_e₀_uncontractSubgraph hl_G) W_U
        exact hwalk_H' W_c hfy_H'
      refine ⟨fun r => contractEdge (D r) e₀ u u', ?_, ?_, ?_, ?_, ?_⟩
      · intro r
        refine ⟨?_, ?_⟩
        · rintro _ ⟨x, hxD, rfl⟩
          exact ⟨hf_mem_H' r x hxD, mem_image_of_mem f ((hD_le r).vertexSet_mono hxD).2⟩
        · rintro e a b ⟨he₀, x, y, hlD, rfl, rfl⟩
          have hl_inter := (hD_le r).isLink_mono hlD
          rw [subgraphInter, restrict_isLink, induce_isLink] at hl_inter
          rcases hl_inter with ⟨⟨heU, heΓ₁⟩, hlG, ⟨hxU, hxΓ₁⟩, ⟨hyU, hyΓ₁⟩⟩
          have hlU : U.IsLink e x y := (hU_G.isLink_iff heU).mpr hlG
          have hlΓ₁ : S.Γ₁.IsLink e x y := (S.hΓ₁G.isLink_iff heΓ₁).mpr hlG
          have hlH' : H'.IsLink e (f x) (f y) :=
            (contractEdge_uncontractSubgraph_links hH').mp ⟨he₀, x, y, hlU, rfl, rfl⟩
          have hlΓ₁' : (contractEdge S.Γ₁ e₀ u u').IsLink e (f x) (f y) :=
            ⟨he₀, x, y, hlΓ₁, rfl, rfl⟩
          have hlG' : (contractEdge S.G e₀ u u').IsLink e (f x) (f y) :=
            ⟨he₀, x, y, hlG, rfl, rfl⟩
          rw [subgraphInter, restrict_isLink, induce_isLink]
          exact ⟨⟨hlH'.edge_mem, hlΓ₁'.edge_mem⟩, hlG',
            ⟨hlH'.left_mem, hlΓ₁'.left_mem⟩, ⟨hlH'.right_mem, hlΓ₁'.right_mem⟩⟩
      · intro r
        by_cases h_uu' : u ∈ V(D r) ∨ u' ∈ V(D r)
        · exact isGraphConnected_contractEdge_of_isLink (hD_e₀ r h_uu') (hD_conn r)
        · have he₀_not_D : e₀ ∉ E(D r) := by
            intro he₀D
            have hlD := (((hD_le r).trans (subgraphInter_le hU_G)).isLink_iff he₀D).mpr hl_G
            exact h_uu' (Or.inl hlD.left_mem)
          exact isGraphConnected_contractEdge_of_notMem he₀_not_D (hD_conn r)
      · rintro r e a b hl_inter ⟨z, hzD, hfz⟩
        rw [subgraphInter, restrict_isLink, induce_isLink] at hl_inter
        rcases hl_inter with ⟨⟨heH', heΓ₁'⟩, hlG', ⟨haH', haΓ₁'⟩, ⟨hbH', hbΓ₁'⟩⟩
        have hlΓ₁' : (contractEdge S.Γ₁ e₀ u u').IsLink e a b :=
          ((contractEdge_mono S.hΓ₁G e₀ u u').isLink_iff heΓ₁').mpr hlG'
        rcases hlΓ₁' with ⟨he₀, x, y, hlΓ₁, rfl, rfl⟩
        have hlG : S.G.IsLink e x y := S.hΓ₁G.isLink_mono hlΓ₁
        have hlU : U.IsLink e x y := by
          unfold U uncontractSubgraph
          rw [restrict_isLink, induce_isLink]
          exact ⟨Or.inl heH', hlG, Or.inl ⟨hlG.left_mem, haH'⟩, Or.inl ⟨hlG.right_mem, hbH'⟩⟩
        have hl_inter_orig : (subgraphInter S.G U S.Γ₁).IsLink e x y := by
          rw [subgraphInter, restrict_isLink, induce_isLink]
          exact ⟨⟨hlU.edge_mem, hlΓ₁.edge_mem⟩, hlG,
            ⟨hlU.left_mem, hlΓ₁.left_mem⟩, ⟨hlU.right_mem, hlΓ₁.right_mem⟩⟩
        have hxD : x ∈ V(D r) := by
          rcases contractVertMap_eq_iff.mp hfz.symm with rfl | ⟨hx_uu', hz_uu'⟩
          · exact hzD
          · have h_or : u ∈ V(D r) ∨ u' ∈ V(D r) := by
              rcases hz_uu' with rfl | rfl
              · exact Or.inl hzD
              · exact Or.inr hzD
            have hl_e₀_D := hD_e₀ r h_or
            rcases hx_uu' with rfl | rfl
            · exact hl_e₀_D.left_mem
            · exact hl_e₀_D.right_mem
        have hlD : (D r).IsLink e x y := hD_link r e x y hl_inter_orig hxD
        exact ⟨he₀, x, y, hlD, rfl, rfl⟩
      · intro r₁ r₂ hr_ne
        simp only [vertexSet_contractEdge]
        refine disjoint_left.mpr ?_
        rintro _ ⟨x₁, hx₁, rfl⟩ ⟨x₂, hx₂, hfx⟩
        rcases contractVertMap_eq_iff.mp hfx.symm with rfl | ⟨hx₁_uu', hx₂_uu'⟩
        · exact disjoint_left.mp (hD_disj r₁ r₂ hr_ne) hx₁ hx₂
        · have h_or : u ∈ V(D r₁) ∨ u' ∈ V(D r₁) := by
            rcases hx₁_uu' with rfl | rfl
            · exact Or.inl hx₁
            · exact Or.inr hx₁
          have hl_e₀_D₁ := hD_e₀ r₁ h_or
          have hx₂_D₁ : x₂ ∈ V(D r₁) := by
            rcases hx₂_uu' with rfl | rfl
            · exact hl_e₀_D₁.left_mem
            · exact hl_e₀_D₁.right_mem
          exact disjoint_left.mp (hD_disj r₁ r₂ hr_ne) hx₂_D₁ hx₂
      · intro r i
        obtain ⟨z, hzD, hzC⟩ := hD_meet r i
        exact ⟨f z, mem_image_of_mem f hzD, mem_image_of_mem f hzC⟩ }

/-- Claim (6) of **3.1** (page 536): in an `InsulatedSystem` of minimum size `|V(G)| + |E(G)|`,
`L` is vital for `Z` in `G`. -/
private theorem lemma_3_1_claim_6 [DecidableEq α] {w : ℕ} (S : InsulatedSystem α β w)
    (hmin : ∀ S' : InsulatedSystem α β w, S'.Z = S.Z →
      V(S.G).ncard + E(S.G).ncard ≤ V(S'.G).ncard + E(S'.G).ncard) :
    IsVitalFor S.G S.L S.Z := by
  refine ⟨S.hLG, S.hZL, fun L' hL'G hSame => ?_⟩
  -- For any `H ≤ S.G` with `HasSameEffectOn H S.L S.Z`, shrinking to `H ∪ ⋃ i, C i` preserves `G`.
  have hshrink_eq : ∀ {H : Graph α β} (hHG : H ≤ S.G) (hSame_H : HasSameEffectOn H S.L S.Z),
      V(S.G) = V(H) ∪ ⋃ i, V(S.C i) ∧ E(S.G) = E(H) ∪ ⋃ i, E(S.C i) := by
    intro H hHG hSame_H
    let S_H := S.shrinkTo hHG hSame_H
    have hV_sub : V(S_H.G) ⊆ V(S.G) :=
      (subgraphUnionFamily_le hHG (fun i => (S.hC_Γ₁ i).trans S.hΓ₁G)).vertexSet_mono
    have hE_sub : E(S_H.G) ⊆ E(S.G) :=
      (subgraphUnionFamily_le hHG (fun i => (S.hC_Γ₁ i).trans S.hΓ₁G)).edgeSet_mono
    have hV_le : V(S_H.G).ncard ≤ V(S.G).ncard := ncard_le_ncard hV_sub S.hG_finV
    have hE_le : E(S_H.G).ncard ≤ E(S.G).ncard := ncard_le_ncard hE_sub S.hG_finE
    have hmin_H : V(S.G).ncard + E(S.G).ncard ≤ V(S_H.G).ncard + E(S_H.G).ncard :=
      hmin S_H rfl
    have hV_card : V(S_H.G).ncard = V(S.G).ncard := by omega
    have hE_card : E(S_H.G).ncard = E(S.G).ncard := by omega
    have hV_eq : V(S_H.G) = V(S.G) := eq_of_subset_of_ncard_le hV_sub hV_card.ge S.hG_finV
    have hE_eq : E(S_H.G) = E(S.G) := eq_of_subset_of_ncard_le hE_sub hE_card.ge S.hG_finE
    exact ⟨hV_eq.symm.trans S_H.hVG, hE_eq.symm.trans S_H.hEG⟩
  -- For any `H ≤ S.G` with `HasSameEffectOn H S.L S.Z`, `E(H)` is disjoint from `⋃ i, E(C i)`.
  have hdisj_E : ∀ {H : Graph α β} (hHG : H ≤ S.G) (hSame_H : HasSameEffectOn H S.L S.Z),
      Disjoint E(H) (⋃ i, E(S.C i)) := by
    intro H hHG hSame_H
    refine disjoint_left.mpr ?_
    intro e₀ heH heC_union
    rcases mem_iUnion.mp heC_union with ⟨i₀, heC⟩
    let S_H := S.shrinkTo hHG hSame_H
    have hSH_G : S_H.G ≤ S.G :=
      subgraphUnionFamily_le hHG (fun i => (S.hC_Γ₁ i).trans S.hΓ₁G)
    have hV_le : V(S_H.G).ncard ≤ V(S.G).ncard :=
      ncard_le_ncard hSH_G.vertexSet_mono S.hG_finV
    have hE_le : E(S_H.G).ncard ≤ E(S.G).ncard :=
      ncard_le_ncard hSH_G.edgeSet_mono S.hG_finE
    obtain ⟨u, u', hl_C⟩ := (S_H.C i₀).exists_isLink_of_mem_edgeSet heC
    have hl_SH_G : S_H.G.IsLink e₀ u u' :=
      ((S_H.hC_Γ₁ i₀).trans S_H.hΓ₁G).isLink_mono hl_C
    have hl_SH_L : S_H.L.IsLink e₀ u u' :=
      (S_H.hLG.isLink_iff heH).mpr hl_SH_G
    by_cases huu' : u = u'
    · subst huu'
      let S' := S_H.deleteLoop hl_SH_G
      have hmin' := hmin S' rfl
      have hV' : V(S'.G).ncard = V(S_H.G).ncard := rfl
      have hE' : E(S'.G).ncard < E(S_H.G).ncard :=
        ncard_lt_ncard (sdiff_singleton_ssubset.mpr hl_SH_G.edge_mem) S_H.hG_finE
      omega
    · let S' := S_H.contractNonLoop hl_SH_L hl_C
      have hmin' := hmin S' rfl
      have hlt := size_contractEdge_lt S_H.hG_finV S_H.hG_finE hl_SH_G huu'
      change V(S'.G).ncard + E(S'.G).ncard < V(S_H.G).ncard + E(S_H.G).ncard at hlt
      omega
  have ⟨hVG_L', hEG_L'⟩ := hshrink_eq hL'G hSame
  have hdisj_L' := hdisj_E hL'G hSame
  have hdisj_L := hdisj_E S.hLG rfl
  have hE_eq : E(L') = E(S.L) := by
    have h1 : E(L') = E(S.G) \ ⋃ i, E(S.C i) := by
      rw [hEG_L', union_sdiff_cancel_right (disjoint_iff_inter_eq_empty.mp hdisj_L' ▸ subset_rfl)]
    have h2 : E(S.L) = E(S.G) \ ⋃ i, E(S.C i) := by
      rw [S.hEG, union_sdiff_cancel_right (disjoint_iff_inter_eq_empty.mp hdisj_L ▸ subset_rfl)]
    exact h1.trans h2.symm
  -- Show `V(H) = V(S.G)` for any `H ≤ S.G` with `HasSameEffectOn H S.L S.Z` by Claims (5) & (6)
  -- of 3.1: adding an edge of `C i₀` incident with `u ∈ V(S.G) \ V(H)` preserves `effectOn · Z`
  -- and creates an edge in `E(L'') ∩ E(C i₀)`.
  have hVH_G : ∀ {H : Graph α β} (hHG : H ≤ S.G) (hSame_H : HasSameEffectOn H S.L S.Z),
      V(H) = V(S.G) := by
    intro H hHG hSame_H
    have ⟨hVG_H, _⟩ := hshrink_eq hHG hSame_H
    refine Subset.antisymm hHG.vertexSet_mono (fun u huG => ?_)
    by_contra hu_not_H
    have hu_union : u ∈ ⋃ i, V(S.C i) := by
      rw [hVG_H] at huG
      exact huG.resolve_left hu_not_H
    rcases mem_iUnion.mp hu_union with ⟨i₀, hu_Ci₀⟩
    obtain ⟨D, _, _, _, hD_disj, hD_meet⟩ := S.hCore S.L S.hLG rfl
    let r0 : Fin (w + 2) := ⟨0, Nat.succ_pos _⟩
    let r1 : Fin (w + 2) := ⟨1, Nat.succ_lt_succ (Nat.succ_pos _)⟩
    have hr01 : r0 ≠ r1 := fun h => Nat.zero_ne_one (congrArg Fin.val h)
    obtain ⟨x₀, hx₀D, hx₀C⟩ := hD_meet r0 i₀
    obtain ⟨x₁, hx₁D, hx₁C⟩ := hD_meet r1 i₀
    have hx01 : x₀ ≠ x₁ := fun h =>
      disjoint_left.mp (hD_disj r0 r1 hr01) hx₀D (h ▸ hx₁D)
    obtain ⟨v, hvC, huv⟩ : ∃ v ∈ V(S.C i₀), u ≠ v := by
      by_cases hux₀ : u = x₀
      · exact ⟨x₁, hx₁C, hux₀ ▸ hx01⟩
      · exact ⟨x₀, hx₀C, hux₀⟩
    obtain ⟨W⟩ := (S.hC_conn i₀).2 u hu_Ci₀ v hvC
    cases W with
    | nil _ => exact (huv rfl).elim
    | @cons _ u' _ e₀ hl₀ _ =>
      have hl₀_G : S.G.IsLink e₀ u u' :=
        ((S.hC_Γ₁ i₀).trans S.hΓ₁G).isLink_mono hl₀
      let L'' := addEdgeAndEnds S.G H e₀ u u'
      have hL''G : L'' ≤ S.G := addEdgeAndEnds_le hHG hl₀_G
      have hSame_L'' : HasSameEffectOn L'' S.L S.Z :=
        (hasSameEffectOn_addEdgeAndEnds_of_notMem_left hHG hl₀_G hu_not_H
          (subset_vertexSet_of_hasSameEffectOn hSame_H S.hZL)).trans hSame_H
      have hdisj_L'' := hdisj_E hL''G hSame_L''
      have he₀_L'' : e₀ ∈ E(L'') := by
        have hl_e₀ : L''.IsLink e₀ u u' :=
          (isLink_addEdgeAndEnds_iff hHG hl₀_G).mpr (Or.inr ⟨rfl, hl₀_G⟩)
        exact hl_e₀.edge_mem
      have he₀_C : e₀ ∈ ⋃ i, E(S.C i) := mem_iUnion.mpr ⟨i₀, hl₀.edge_mem⟩
      exact disjoint_left.mp hdisj_L'' he₀_L'' he₀_C
  have hV_eq : V(L') = V(S.L) :=
    (hVH_G hL'G hSame).trans (hVH_G S.hLG rfl).symm
  refine Graph.ext hV_eq fun e x y => ?_
  constructor
  · intro hl
    have heL : e ∈ E(S.L) := hE_eq ▸ hl.edge_mem
    exact (S.hLG.isLink_iff heL).mpr (hL'G.isLink_mono hl)
  · intro hl
    have heL' : e ∈ E(L') := hE_eq.symm ▸ hl.edge_mem
    exact (hL'G.isLink_iff heL').mpr (S.hLG.isLink_mono hl)

/-- Claim (7) of **3.1** (page 536): combining Claim (6) (`lemma_3_1_claim_6`), **2.1**, and **3.2**,
no `InsulatedSystem` can exist for `w` chosen via **2.1**. The subproof of (7) ends "Thus
$2t \le \omega + 1$", a misprint for $2t \le w + 1$, which is what the Lean uses
(see the correction to the proof of (3.1) in `corrections/GM22.md`). -/
private theorem InsulatedSystem.false_of_exists [DecidableEq α] {p w : ℕ}
    (hw : ∀ (G L : Graph α β) (Z : Set α),
      V(G).Finite → E(G).Finite → Z ⊆ V(G) → Z.ncard ≤ p →
      IsVitalFor G L Z → TreeWidthLE G w)
    (S₀ : InsulatedSystem α β w) (hZp : S₀.Z.ncard ≤ p) :
    False := by
  have hmain : ∀ (n : ℕ) (S : InsulatedSystem α β w),
      V(S.G).ncard + E(S.G).ncard = n → S.Z = S₀.Z → False := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hlen hZ_eq
      by_cases hmin : ∀ S' : InsulatedSystem α β w, S'.Z = S.Z →
          V(S.G).ncard + E(S.G).ncard ≤ V(S'.G).ncard + E(S'.G).ncard
      · have hvit : IsVitalFor S.G S.L S.Z := lemma_3_1_claim_6 S hmin
        have hZG : S.Z ⊆ V(S.G) := S.hZL.trans S.hLG.vertexSet_mono
        have hZp' : S.Z.ncard ≤ p := hZ_eq ▸ hZp
        have htw : TreeWidthLE S.G w := hw S.G S.L S.Z S.hG_finV S.hG_finE hZG hZp' hvit
        obtain ⟨D, hD_le, hD_conn, _, hD_disj, hD_meet⟩ :=
          S.hCore S.L S.hLG rfl
        have hC_G : ∀ i : Fin (w + 2), S.C i ≤ S.G :=
          fun i => (S.hC_Γ₁ i).trans S.hΓ₁G
        have hD_G : ∀ j : Fin (w + 2), D j ≤ S.G :=
          fun j => (hD_le j).trans (subgraphInter_le S.hLG)
        have hCD_inter : ∀ i j : Fin (w + 2), (V(S.C i) ∩ V(D j)).Nonempty :=
          fun i j => inter_comm V(D j) V(S.C i) ▸ hD_meet j i
        have hle := (theorem_3_2_proof S.hG_finV S.C D hC_G S.hC_conn S.hC_disj
          hD_G hD_conn hD_disj hCD_inter).1 w htw
        omega
      · push Not at hmin
        rcases hmin with ⟨S', hS'_Z, hlt⟩
        exact ih (V(S'.G).ncard + E(S'.G).ncard) (hlen ▸ hlt) S' rfl (hS'_Z.trans hZ_eq)
  exact hmain (V(S₀.G).ncard + E(S₀.G).ncard) S₀ rfl rfl

theorem exists_inj_of_le_ncard {γ : Type*} {s : Set γ} {k : ℕ}
    (hk0 : 0 < k) (hk : k ≤ s.ncard) :
    ∃ f : Fin k → γ, (∀ r, f r ∈ s) ∧ Function.Injective f := by
  obtain ⟨t, hts, ht_card⟩ := exists_subset_card_eq hk
  have ht_fin : t.Finite := finite_of_ncard_pos (ht_card ▸ hk0)
  have : Finite t := ht_fin.to_subtype
  have hcard_eq : Nat.card t = k := by rw [Nat.card_coe_set_eq, ht_card]
  let e : t ≃ Fin k := (Finite.equivFin t).trans (finCongr hcard_eq)
  refine ⟨fun r => (e.symm r).1, fun r => hts (e.symm r).2, fun r₁ r₂ h => ?_⟩
  exact e.symm.injective (Subtype.ext h)

/-- Constructing the initial `InsulatedSystem` from the surface drawing `D` when no subgraph `L'`
of `G \ {v}` has the same effect on `Z` as `L` with `L' ∩ K ⊆ L`. -/
private theorem exists_insulatedSystem_of_no_delete_v [T2Space S] (hS : IsSurface S)
    {G Γ K L : Graph α β} (hVG : V(G).Finite) (hEG_fin : E(G).Finite)
    (hΓG : Γ ≤ G) (hKG : K ≤ G)
    (hUG : V(G) = V(Γ) ∪ V(K)) (hEG : E(G) = E(Γ) ∪ E(K))
    {D : Drawing S} {ιV : S ↪ α} {ιE : Set S ↪ β} (hΓD : Γ = D.toEmbeddedGraph ιV ιE)
    {w h : ℕ} (hw_h : 2 * w + 3 ≤ h) {v₀ : S} (hv₀_V : v₀ ∈ D.V)
    (hIns : IsInsulated D (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀)
    {Z : Set α} (hZK : Z ⊆ V(K)) (hLG : L ≤ G)
    (hno : ¬ ∃ L' : Graph α β, L' ≤ G.deleteVerts {ιV v₀} ∧
      HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L) :
    ∃ S₀ : InsulatedSystem α β w, S₀.Z = Z ∩ V(L) := by
  rcases hIns with ⟨Δ, hΔ_props, hΔ_nest, hΔ_ends⟩
  have hΔ_disc : ∀ i : Fin h, IsClosedDisc (Δ i) := fun i => (hΔ_props i).1
  have hΔ_bd : ∀ i : Fin h, subBd (Δ i) = discBd (Δ i) := fun i => (hΔ_props i).2.1
  have hΔ_subU : ∀ i : Fin h, subBd (Δ i) ⊆ D.U := fun i => (hΔ_props i).2.2
  have hv₀_last : ∀ hpos : 0 < h,
      v₀ ∈ Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩ \
        subBd (Δ ⟨h - 1, Nat.sub_lt hpos zero_lt_one⟩) := fun hpos => (hΔ_ends hpos).1
  have hΔ₀_K : ∀ hpos : 0 < h, Disjoint (ιV ⁻¹' (V(Γ) ∩ V(K))) (Δ ⟨0, hpos⟩) :=
    fun hpos => (hΔ_ends hpos).2
  have h0 : 0 < h := by omega
  have hw2 : w + 2 < h := by omega
  let idx (i : Fin (w + 2)) : Fin h := ⟨i.1, by omega⟩
  let Γ₁₀ := (D.interSet (Δ ⟨0, h0⟩)).toEmbeddedGraph ιV ιE
  let C (i : Fin (w + 2)) : Graph α β :=
    (D.interSet (subBd (Δ (idx i)))).toEmbeddedGraph ιV ιE
  have hΔ_cl : ∀ m : Fin h, IsClosed (Δ m) := fun m => (hΔ_disc m).isCompact.isClosed
  have hbd_cl : ∀ m : Fin h, IsClosed (subBd (Δ m)) :=
    fun _ => isClosed_closure.inter isClosed_closure
  have hbd_sub_self : ∀ m : Fin h, subBd (Δ m) ⊆ Δ m :=
    fun m z hz => (hΔ_cl m).closure_eq ▸ hz.1
  have hΔ_sub_0 : ∀ i : Fin (w + 2), Δ (idx i) ⊆ Δ ⟨0, h0⟩ := by
    intro i
    by_cases hi0 : i.1 = 0
    · have h_eq : idx i = ⟨0, h0⟩ := Fin.ext hi0
      rw [h_eq]
    · have hlt : (⟨0, h0⟩ : Fin h).1 < (idx i).1 := Nat.pos_of_ne_zero hi0
      exact (insulated_disc_subset_sdiff_of_lt hΔ_nest hlt).trans sdiff_subset
  have hC_Γ₁₀ : ∀ i : Fin (w + 2), C i ≤ Γ₁₀ := fun i =>
    interSet_toEmbeddedGraph_mono D (hbd_cl (idx i)) (hΔ_cl ⟨0, h0⟩)
      ((hbd_sub_self (idx i)).trans (hΔ_sub_0 i)) ιV ιE
  have hΓ₁₀_G : Γ₁₀ ≤ G :=
    (interSet_toEmbeddedGraph_le D (hΔ_cl ⟨0, h0⟩) ιV ιE).trans (hΓD ▸ hΓG)
  have hC_G : ∀ i : Fin (w + 2), C i ≤ G := fun i => (hC_Γ₁₀ i).trans hΓ₁₀_G
  have hVK_disj_Γ₁₀ : Disjoint V(K) V(Γ₁₀) := by
    refine disjoint_left.mpr fun x hxK hx₁ => ?_
    rw [vertexSet_interSet_toEmbeddedGraph D (hΔ_cl ⟨0, h0⟩)] at hx₁
    rcases hx₁ with ⟨u, ⟨huV, huΔ₀⟩, rfl⟩
    have huΓ : ιV u ∈ V(Γ) := by rw [hΓD]; exact mem_image_of_mem ιV huV
    exact disjoint_left.mp (hΔ₀_K h0) ⟨huΓ, hxK⟩ huΔ₀
  have hC_disj : ∀ i j : Fin (w + 2), i ≠ j → Disjoint V(C i) V(C j) := by
    have hlt_disj : ∀ i j : Fin (w + 2), i.1 < j.1 → Disjoint V(C i) V(C j) := by
      intro i j hij
      refine disjoint_left.mpr fun x hx_i hx_j => ?_
      rw [vertexSet_interSet_toEmbeddedGraph D (hbd_cl (idx i))] at hx_i
      rw [vertexSet_interSet_toEmbeddedGraph D (hbd_cl (idx j))] at hx_j
      rcases hx_i with ⟨u, ⟨_, hu_i⟩, rfl⟩
      rcases hx_j with ⟨v, ⟨_, hv_j⟩, huv⟩
      obtain rfl : u = v := ιV.injective huv.symm
      have hv_in : u ∈ Δ (idx i) \ subBd (Δ (idx i)) :=
        insulated_disc_subset_sdiff_of_lt hΔ_nest hij (hbd_sub_self (idx j) hv_j)
      exact hv_in.2 hu_i
    intro i j hij
    rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · exact hlt_disj i j hlt
    · exact (hij (Fin.ext heq)).elim
    · exact (hlt_disj j i hgt).symm
  -- Core component extraction for any `L_star ≤ G` with `HasSameEffectOn L_star L Z`
  -- and `subgraphInter G L_star K ≤ L`.
  have hCore_ext : ∀ L_star ≤ G, HasSameEffectOn L_star L Z → subgraphInter G L_star K ≤ L →
      ∃ D_comp : Fin (w + 2) → Graph α β,
        (∀ r, D_comp r ≤ subgraphInter G L_star Γ₁₀) ∧
        (∀ r, IsGraphConnected (D_comp r)) ∧
        (∀ r e x y, (subgraphInter G L_star Γ₁₀).IsLink e x y →
          x ∈ V(D_comp r) → (D_comp r).IsLink e x y) ∧
        (∀ r₁ r₂, r₁ ≠ r₂ → Disjoint V(D_comp r₁) V(D_comp r₂)) ∧
        (∀ r i, (V(D_comp r) ∩ V(C i)).Nonempty) := by
    intro L_star hL_star_G hSame_star hInter_star
    obtain ⟨C_core, hC_core_sub, hC_core_card, hC_core_meet⟩ :=
      exists_components_meeting_core_of_no_delete_v hS hΓG hKG hUG hEG hΓD hw_h hv₀_V
        hΔ_disc hΔ_bd hΔ_subU hΔ_nest hv₀_last hΔ₀_K hZK hLG hL_star_G hSame_star hInter_star hno
    have hmeet_all : ∀ C_c ∈ C_core, ∀ i : Fin (w + 2), (V(C_c) ∩ V(C i)).Nonempty := by
      intro C_c hCc i
      obtain ⟨hCc_core, hCc_C₀⟩ := hC_core_meet C_c hCc
      by_cases hi0 : i.1 = 0
      · have h_idx0 : idx i = ⟨0, h0⟩ := Fin.ext hi0
        dsimp only [C]
        rw [h_idx0]
        exact hCc_C₀
      · have hlt0 : (⟨0, h0⟩ : Fin h).1 < (idx i).1 := Nat.pos_of_ne_zero hi0
        have hlt_w2 : (idx i).1 < (⟨w + 2, hw2⟩ : Fin h).1 := i.2
        have hK_disj_i : Disjoint (ιV ⁻¹' V(K) ∩ D.V) (Δ (idx i)) := by
          refine disjoint_left.mpr fun z ⟨hzK, hzV⟩ hzA => ?_
          have hzΓ : ιV z ∈ V(Γ) := by rw [hΓD]; exact mem_image_of_mem ιV hzV
          exact disjoint_left.mp (hΔ₀_K h0) ⟨hzΓ, hzK⟩ (hΔ_sub_0 i hzA)
        let A_i := (D.interSet (Δ (idx i))).toEmbeddedGraph ιV ιE
        let B_i := discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD (Δ (idx i))
          (hΔ_disc (idx i)) (hΔ_bd (idx i)) (hΔ_subU (idx i)) hK_disj_i
        have hCc_G : C_c ≤ G :=
          (hC_core_sub hCc).1.trans (subgraphInter_le hL_star_G)
        have hCc_conn : IsGraphConnected C_c := (hC_core_sub hCc).2.1
        have hUG_i := vertexSet_union_discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD (Δ (idx i))
          (hΔ_disc (idx i)) (hΔ_bd (idx i)) (hΔ_subU (idx i)) hK_disj_i
        have hEG_i := edgeSet_union_discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD (Δ (idx i))
          (hΔ_disc (idx i)) (hΔ_bd (idx i)) (hΔ_subU (idx i)) hK_disj_i
        have hInter_i := vertexSet_inter_discExteriorSubgraph hS hΓG hKG hEG D ιV ιE hΓD (Δ (idx i))
          (hΔ_disc (idx i)) (hΔ_bd (idx i)) (hΔ_subU (idx i)) hK_disj_i
        have hA_i_G : A_i ≤ G :=
          (interSet_toEmbeddedGraph_le D (hΔ_cl (idx i)) ιV ιE).trans (hΓD ▸ hΓG)
        have hB_i_G : B_i ≤ G := discExteriorSubgraph_le hS hΓG hKG hEG D ιV ιE hΓD (Δ (idx i))
          (hΔ_disc (idx i)) (hΔ_bd (idx i)) (hΔ_subU (idx i)) hK_disj_i
        have hCc_A : (V(C_c) ∩ V(A_i)).Nonempty := by
          rcases hCc_core with ⟨x_c, hx_Cc, hx_core⟩
          have hcore_sub : Δ ⟨w + 2, hw2⟩ ⊆ Δ (idx i) :=
            (insulated_disc_subset_sdiff_of_lt hΔ_nest hlt_w2).trans sdiff_subset
          have hx_Ai : x_c ∈ V(A_i) :=
            (interSet_toEmbeddedGraph_mono D (hΔ_cl ⟨w + 2, hw2⟩) (hΔ_cl (idx i))
              hcore_sub ιV ιE).vertexSet_mono hx_core
          exact ⟨x_c, hx_Cc, hx_Ai⟩
        have hCc_B : (V(C_c) ∩ V(B_i)).Nonempty := by
          rcases hCc_C₀ with ⟨y_b, hy_Cc, hy_C₀⟩
          have hy_not_Ai : y_b ∉ V(A_i) := by
            rw [vertexSet_interSet_toEmbeddedGraph D (hbd_cl ⟨0, h0⟩)] at hy_C₀
            rw [vertexSet_interSet_toEmbeddedGraph D (hΔ_cl (idx i))]
            rcases hy_C₀ with ⟨u, ⟨_, hu_bd0⟩, rfl⟩
            rintro ⟨v, ⟨_, hv_i⟩, huv⟩
            obtain rfl : u = v := ιV.injective huv.symm
            exact (insulated_disc_subset_sdiff_of_lt hΔ_nest hlt0 hv_i).2 hu_bd0
          have hy_G : y_b ∈ V(G) := hCc_G.vertexSet_mono hy_Cc
          rw [hUG_i] at hy_G
          exact ⟨y_b, hy_Cc, hy_G.resolve_left hy_not_Ai⟩
        rw [← hInter_i]
        exact connected_meets_inter_of_union hA_i_G hB_i_G hEG_i hCc_G hCc_conn hCc_A hCc_B
    obtain ⟨D_comp, hD_mem, hD_inj⟩ :=
      exists_inj_of_le_ncard (Nat.succ_pos (w + 1)) (by omega : w + 2 ≤ C_core.ncard)
    refine ⟨D_comp, fun r => (hC_core_sub (hD_mem r)).1,
      fun r => (hC_core_sub (hD_mem r)).2.1,
      fun r e x y hl hx => isLink_of_mem_graphComponents (hC_core_sub (hD_mem r)) hl hx,
      fun r₁ r₂ hr_ne => (hC_core_sub (hD_mem r₁)).disjoint_vertexSet_of_ne
        (hC_core_sub (hD_mem r₂)) (fun h => hr_ne (hD_inj h)),
      fun r i => hmeet_all (D_comp r) (hD_mem r) i⟩
  -- Deduce `IsGraphConnected (C i)` using `isGraphConnected_interSet_of_oArc`.
  have hC_conn : ∀ i : Fin (w + 2), IsGraphConnected (C i) := by
    intro i
    have hOArc : IsOArc (subBd (Δ (idx i))) := by
      rw [hΔ_bd (idx i)]
      exact IsClosedDisc.isOArc_discBd (hΔ_disc (idx i))
    dsimp only [C]
    rw [toEmbeddedGraph_eq_mapEmbed, isGraphConnected_mapEmbed_iff]
    exact isGraphConnected_interSet_of_oArc hOArc (hΔ_subU (idx i))
  -- Construct `G₀ = L ∪ ⋃ i, C i`, `Γ₁ = G₀ ∩ Γ₁₀`, and `Z₀ = Z ∩ V(L)`.
  let G₀ := subgraphUnionFamily G L C
  have hG₀G : G₀ ≤ G := subgraphUnionFamily_le hLG hC_G
  let Γ₁ := subgraphInter G G₀ Γ₁₀
  let Z₀ := Z ∩ V(L)
  have hZ_disj_C : ∀ i : Fin (w + 2), Disjoint Z V(C i) :=
    fun i => (hVK_disj_Γ₁₀.mono_left hZK).mono_right (hC_Γ₁₀ i).vertexSet_mono
  refine ⟨{
    G := G₀
    L := L
    Γ₁ := Γ₁
    Z := Z₀
    C := C
    hG_finV := hVG.subset hG₀G.vertexSet_mono
    hG_finE := hEG_fin.subset hG₀G.edgeSet_mono
    hLG := le_subgraphUnionFamily_left hLG hC_G
    hΓ₁G := subgraphInter_le_left hG₀G hΓ₁₀_G
    hZL := inter_subset_right
    hZ_disj := fun i => (hZ_disj_C i).mono_left inter_subset_left
    hC_Γ₁ := fun i => by
      have hCi_G₀ : C i ≤ G₀ := le_subgraphUnionFamily_right hLG hC_G i
      refine ⟨fun x hx => ⟨hCi_G₀.vertexSet_mono hx, (hC_Γ₁₀ i).vertexSet_mono hx⟩,
        fun e x y hl => ?_⟩
      change ((G.induce (V(G₀) ∩ V(Γ₁₀))).restrict (E(G₀) ∩ E(Γ₁₀))).IsLink e x y
      rw [restrict_isLink, induce_isLink]
      exact ⟨⟨hCi_G₀.edgeSet_mono hl.edge_mem, (hC_Γ₁₀ i).edgeSet_mono hl.edge_mem⟩,
        (hC_G i).isLink_mono hl,
        ⟨hCi_G₀.vertexSet_mono hl.left_mem, (hC_Γ₁₀ i).vertexSet_mono hl.left_mem⟩,
        ⟨hCi_G₀.vertexSet_mono hl.right_mem, (hC_Γ₁₀ i).vertexSet_mono hl.right_mem⟩⟩
    hC_conn := hC_conn
    hC_disj := hC_disj
    hVG := rfl
    hEG := edgeSet_subgraphUnionFamily hLG hC_G
    hCore := fun L_star hL_star hSame_Z₀ => by
      have hL_star_G : L_star ≤ G := hL_star.trans hG₀G
      have hVL_star_Z : V(L_star) ∩ Z ⊆ Z₀ := by
        rintro x ⟨hx_star, hxZ⟩
        have hxG₀ : x ∈ V(L) ∪ ⋃ i, V(C i) := hL_star.vertexSet_mono hx_star
        rcases hxG₀ with hxL | hxC
        · exact ⟨hxZ, hxL⟩
        · rcases mem_iUnion.mp hxC with ⟨i, hxi⟩
          exact (disjoint_left.mp (hZ_disj_C i) hxZ hxi).elim
      have hSame_Z : HasSameEffectOn L_star L Z := by
        rw [HasSameEffectOn, effectOn_eq_iff_areConnectedIn]
        intro a haZ b hbZ
        by_cases haL : a ∈ V(L) <;> by_cases hbL : b ∈ V(L)
        · exact effectOn_eq_iff_areConnectedIn.mp hSame_Z₀ a ⟨haZ, haL⟩ b ⟨hbZ, hbL⟩
        · have hb_not_star : b ∉ V(L_star) := fun hb_s => hbL (hVL_star_Z ⟨hb_s, hbZ⟩).2
          rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
          exact ⟨fun ⟨_, hb_s, _⟩ => (hb_not_star hb_s).elim, fun ⟨_, hb_l, _⟩ => (hbL hb_l).elim⟩
        · have ha_not_star : a ∉ V(L_star) := fun ha_s => haL (hVL_star_Z ⟨ha_s, haZ⟩).2
          rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
          exact ⟨fun ⟨ha_s, _, _⟩ => (ha_not_star ha_s).elim, fun ⟨ha_l, _, _⟩ => (haL ha_l).elim⟩
        · have ha_not_star : a ∉ V(L_star) := fun ha_s => haL (hVL_star_Z ⟨ha_s, haZ⟩).2
          rw [areConnectedIn_iff_walk, areConnectedIn_iff_walk]
          exact ⟨fun ⟨ha_s, _, _⟩ => (ha_not_star ha_s).elim, fun ⟨ha_l, _, _⟩ => (haL ha_l).elim⟩
      have hInter_K : subgraphInter G L_star K ≤ L := by
        refine ⟨?_, ?_⟩
        · rintro x ⟨hx_star, hxK⟩
          rcases hL_star.vertexSet_mono hx_star with hxL | hxC
          · exact hxL
          · rcases mem_iUnion.mp hxC with ⟨i, hxi⟩
            exact (disjoint_left.mp hVK_disj_Γ₁₀ hxK ((hC_Γ₁₀ i).vertexSet_mono hxi)).elim
        · rintro e x y hl
          rw [subgraphInter, restrict_isLink, induce_isLink] at hl
          rcases hl with ⟨⟨he_star, heK⟩, hlG, _, _⟩
          have heG₀ : e ∈ E(L) ∪ ⋃ i, E(C i) :=
            edgeSet_subgraphUnionFamily hLG hC_G ▸ hL_star.edgeSet_mono he_star
          rcases heG₀ with heL | heC
          · exact (hLG.isLink_iff heL).mpr hlG
          · rcases mem_iUnion.mp heC with ⟨i, hei⟩
            have hlC := ((hC_G i).isLink_iff hei).mpr hlG
            have hlK := (hKG.isLink_iff heK).mpr hlG
            exact (disjoint_left.mp hVK_disj_Γ₁₀ hlK.left_mem
              ((hC_Γ₁₀ i).vertexSet_mono hlC.left_mem)).elim
      obtain ⟨D_comp, hD_le, hD_conn, hD_link, hD_disj, hD_meet⟩ :=
        hCore_ext L_star hL_star_G hSame_Z hInter_K
      have hInter_eq : subgraphInter G₀ L_star Γ₁ = subgraphInter G L_star Γ₁₀ :=
        subgraphInter_subgraphInter_right hG₀G hL_star
      rw [hInter_eq]
      exact ⟨D_comp, hD_le, hD_conn, hD_link, hD_disj, hD_meet⟩
  }, rfl⟩

/-- **3.1** (Graph Minors XXII, page 534):
"For every integer $p \ge 0$ there exists $h \ge 1$ with the following property. Let $\Gamma, K$
be subgraphs of a graph $G$ with $G = \Gamma \cup K$, and let $\Gamma$ be a drawing in a surface
$\Sigma$. Let $v \in V(\Gamma)$ be $h$-insulated from $V(\Gamma \cap K)$ by $\Gamma$, let
$Z \subseteq V(K)$ with $|Z| \le p$, and let $L \subseteq G$. Then there is a subgraph $L'$ of
$G \setminus \{v\}$ with the same effect on $Z$ as $L$ and with $L' \cap K \subseteq L$." -/
theorem theorem_3_1_proof  (p : ℕ) :
    ∃ h ≥ 1, ∀ {S : Type w} [TopologicalSpace S] [T2Space S], IsSurface S →
      ∀ {α : Type u} {β : Type v} (G Γ K L : Graph α β), V(G).Finite → E(G).Finite →
        Γ ≤ G → K ≤ G → V(G) = V(Γ) ∪ V(K) → E(G) = E(Γ) ∪ E(K) →
        ∀ (D : Drawing S) (ιV : S ↪ α) (ιE : Set S ↪ β), Γ = D.toEmbeddedGraph ιV ιE →
        ∀ v₀ ∈ D.V, IsInsulated D (ιV ⁻¹' (V(Γ) ∩ V(K))) h v₀ →
        ∀ Z ⊆ V(K), Z.ncard ≤ p → L ≤ G →
        ∃ L' ≤ G.deleteVerts {ιV v₀},
          HasSameEffectOn L' L Z ∧ subgraphInter G L' K ≤ L := by
  classical
  obtain ⟨w, hw⟩ := theorem_2_1_proof.{u, v} p
  refine ⟨2 * w + 3, by omega, ?_⟩
  intro S _ _ hS α β G Γ K L hVG hEG_fin hΓG hKG hUG hEG D ιV ιE hΓD v₀ hv₀ hIns Z hZK hZp hLG
  by_contra hno
  obtain ⟨S₀, hZ₀_eq⟩ := exists_insulatedSystem_of_no_delete_v hS hVG hEG_fin hΓG hKG hUG hEG
    hΓD (le_refl (2 * w + 3)) hv₀ hIns hZK hLG hno
  have hZ₀_p : S₀.Z.ncard ≤ p := by
    rw [hZ₀_eq]
    have hZ_fin : Z.Finite := hVG.subset (hZK.trans hKG.vertexSet_mono)
    exact (ncard_le_ncard inter_subset_left hZ_fin).trans hZp
  exact InsulatedSystem.false_of_exists (@hw α β) S₀ hZ₀_p









end Contraction

end GraphMinor.GM22
