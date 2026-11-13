module

public import GraphMinor.GM05.Section3
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graph Minors V, Section 4 (Part 1): (4.1) and (4.2)

This file formalizes (4.1) and (4.2) of Section 4 of N. Robertson and P. D. Seymour,
*Graph Minors. V. Excluding a planar graph*, J. Combin. Theory Ser. B **41** (1986), 92–114
(pages 97–98):

- `theorem_4_1`: if `G ∈ 𝓕_θ` has disjoint connected subgraphs `A₁, …, Aₘ, B₁, …, Bₙ` with an edge
  between `A_i` and `B_j` for all `i, j`, then `m < θ²/2` or `n < θ²/2`.
- `theorem_4_2`: if `A₁, …, A_{θ²/2}` are disjoint connected subgraphs of `G ∈ 𝓕_θ` (where `G` has
  maximum valency at most `4`) and `B₁, …, Bₙ` are pairwise edge-disjoint connected subgraphs of `G`
  each meeting each `A_i` in a single vertex of valency `1` in `B_j`, then `n < θ₁`.
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set GM01

universe u

variable {V : Type u}

/-! ### Complete bipartite graph and (4.1) -/

/-- The complete bipartite simple graph `K_{m, n}` on `Fin m ⊕ Fin n`. -/
def completeBipartiteSimpleGraph (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y :=
    match x, y with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False
  symm := ⟨fun x y ↦ by cases x <;> cases y <;> simp⟩
  loopless := ⟨fun x ↦ by cases x <;> simp⟩

private lemma grid_bipartite_idx_lt {θ : ℕ} (heven : Even θ) (p : Fin θ × Fin θ) :
    p.1.1 * (θ / 2) + p.2.1 / 2 < θ ^ 2 / 2 := by
  obtain ⟨k, hk⟩ := heven
  have hθ : θ = 2 * k := by omega
  have hp1 : p.1.1 < 2 * k := hθ ▸ p.1.2
  have hp2 : p.2.1 < 2 * k := hθ ▸ p.2.2
  have hdiv : θ / 2 = k := by omega
  have hsq : θ ^ 2 / 2 = 2 * k * k := by
    have : θ ^ 2 = 2 * (2 * k * k) := by rw [hθ]; ring
    omega
  rw [hdiv, hsq]
  have hp2_div : p.2.1 / 2 < k := by omega
  have hle : (p.1.1 + 1) * k ≤ 2 * k * k := by
    have : p.1.1 + 1 ≤ 2 * k := by omega
    exact Nat.mul_le_mul_right k this
  linarith

/-- Embedding the vertices of the `θ`-grid into the bipartition `Fin (θ²/2) ⊕ Fin (θ²/2)` for even
`θ` according to the parity of `i + j`. -/
def gridToBipartite {θ : ℕ} (heven : Even θ) (p : Fin θ × Fin θ) :
    Fin (θ ^ 2 / 2) ⊕ Fin (θ ^ 2 / 2) :=
  let idx : Fin (θ ^ 2 / 2) := ⟨p.1.1 * (θ / 2) + p.2.1 / 2, grid_bipartite_idx_lt heven p⟩
  if (p.1.1 + p.2.1) % 2 = 0 then Sum.inl idx else Sum.inr idx

private lemma gridToBipartite_injective {θ : ℕ} (heven : Even θ) :
    Function.Injective (gridToBipartite heven) := by
  intro p q hpq
  dsimp [gridToBipartite] at hpq
  obtain ⟨k, hk⟩ := heven
  have hθ : θ = 2 * k := by omega
  have hdiv : θ / 2 = k := by omega
  have hp2 : p.2.1 / 2 < k := by have := p.2.2; omega
  have hq2 : q.2.1 / 2 < k := by have := q.2.2; omega
  have h_extract :
      (p.1.1 + p.2.1) % 2 = (q.1.1 + q.2.1) % 2 ∧
        p.1.1 * k + p.2.1 / 2 = q.1.1 * k + q.2.1 / 2 := by
    by_cases hp : (p.1.1 + p.2.1) % 2 = 0 <;>
      by_cases hq : (q.1.1 + q.2.1) % 2 = 0 <;>
      simp only [hp, hq, ↓reduceIte] at hpq
    · injection hpq with hidx
      have hval := congrArg Fin.val hidx
      dsimp at hval
      rw [hdiv] at hval
      exact ⟨by omega, hval⟩
    · nomatch hpq
    · nomatch hpq
    · injection hpq with hidx
      have hval := congrArg Fin.val hidx
      dsimp at hval
      rw [hdiv] at hval
      exact ⟨by omega, hval⟩
  obtain ⟨hmod, hlin⟩ := h_extract
  have hp1_eq : p.1.1 = q.1.1 := by
    rcases lt_trichotomy p.1.1 q.1.1 with hlt | heq | hgt
    · have hmul : (p.1.1 + 1) * k ≤ q.1.1 * k := Nat.mul_le_mul_right k hlt
      rw [Nat.add_one_mul] at hmul
      omega
    · exact heq
    · have hmul : (q.1.1 + 1) * k ≤ p.1.1 * k := Nat.mul_le_mul_right k hgt
      rw [Nat.add_one_mul] at hmul
      omega
  have hp2_eq : p.2.1 = q.2.1 := by
    rw [hp1_eq] at hlin
    omega
  exact Prod.ext (Fin.ext hp1_eq) (Fin.ext hp2_eq)

private lemma gridToBipartite_adj {θ : ℕ} (heven : Even θ) {p q : Fin θ × Fin θ}
    (hadj : (pathGraph θ □ pathGraph θ).Adj p q) :
    (completeBipartiteSimpleGraph (θ ^ 2 / 2) (θ ^ 2 / 2)).Adj
      (gridToBipartite heven p) (gridToBipartite heven q) := by
  rw [boxProd_adj, pathGraph_adj, pathGraph_adj] at hadj
  have hparity : (p.1.1 + p.2.1) % 2 ≠ (q.1.1 + q.2.1) % 2 := by
    rcases hadj with ⟨h1 | h1, h2⟩ | ⟨h2 | h2, h1⟩
    · have h2' : p.2.1 = q.2.1 := congrArg Fin.val h2
      omega
    · have h2' : p.2.1 = q.2.1 := congrArg Fin.val h2
      omega
    · have h1' : p.1.1 = q.1.1 := congrArg Fin.val h1
      omega
    · have h1' : p.1.1 = q.1.1 := congrArg Fin.val h1
      omega
  dsimp [gridToBipartite, completeBipartiteSimpleGraph]
  split_ifs with hp hq hq
  · omega
  · trivial
  · trivial
  · omega

/-- Claim in the proof of Graph Minors V, (4.1) (page 97):
"`K_{θ²/2, θ²/2} ∉ 𝓕_θ`." -/
theorem isIsoMinor_gridGraph_completeBipartite {θ : ℕ} (heven : Even θ) :
    IsIsoMinor (gridGraph θ)
      (Graph.ofSimpleGraph (completeBipartiteSimpleGraph (θ ^ 2 / 2) (θ ^ 2 / 2))) := by
  rw [gridGraph, ofSimpleGraph_eq_toGraph (completeBipartiteSimpleGraph _ _)]
  let G_bip : (⊤ : SimpleGraph (Fin (θ ^ 2 / 2) ⊕ Fin (θ ^ 2 / 2))).Subgraph :=
    SimpleGraph.toSubgraph (completeBipartiteSimpleGraph (θ ^ 2 / 2) (θ ^ 2 / 2)) le_top
  let K : Fin θ × Fin θ → (⊤ : SimpleGraph (Fin (θ ^ 2 / 2) ⊕ Fin (θ ^ 2 / 2))).Subgraph :=
    fun p ↦ (GM01.Path.singleton (gridToBipartite heven p)).toSubgraph
  apply isIsoMinor_ofSimpleGraph_of_connected_subgraphs (pathGraph θ □ pathGraph θ)
    (Set.toFinite G_bip.verts) K
  · intro p
    refine ⟨fun _ _ ↦ trivial, fun x y hxy ↦ ?_⟩
    have : ¬ (GM01.Path.singleton (gridToBipartite heven p)).toSubgraph.Adj x y := by
      simp [GM01.Path.singleton, GM01.Path.toSubgraph]
    exact absurd hxy this
  · intro p
    exact (GM01.Path.singleton _).connected_toSubgraph
  · intro p q hne
    change Disjoint (GM01.Path.singleton (gridToBipartite heven p)).verts
      (GM01.Path.singleton (gridToBipartite heven q)).verts
    rw [GM01.Path.singleton_verts, GM01.Path.singleton_verts, Set.disjoint_singleton]
    exact (gridToBipartite_injective heven).ne hne
  · intro p q hadj
    refine ⟨gridToBipartite heven p, ?_, gridToBipartite heven q, ?_,
      gridToBipartite_adj heven hadj⟩
    · change gridToBipartite heven p ∈ (GM01.Path.singleton _).verts
      simp
    · change gridToBipartite heven q ∈ (GM01.Path.singleton _).verts
      simp

/-- Graph Minors V, (4.1) (page 97):
"Let $G \in \mathcal{F}_\theta$. Let $A_1, \dots, A_m, B_1, \dots, B_n$ be disjoint connected
subgraphs of $G$ such that for $1 \le i \le m$, $1 \le j \le n$ there is a vertex of $A_i$
and a vertex of $B_j$ which are adjacent in $G$. Then either $m < \theta^2/2$ or $n <
\theta^2/2$." -/
theorem theorem_4_1_simple {G : (⊤ : SimpleGraph V).Subgraph} {θ m n : ℕ}
    (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (A : Fin m → (⊤ : SimpleGraph V).Subgraph) (B : Fin n → (⊤ : SimpleGraph V).Subgraph)
    (hA_le : ∀ i, A i ≤ G) (hB_le : ∀ j, B j ≤ G)
    (hA_conn : ∀ i, (A i).Connected) (hB_conn : ∀ j, (B j).Connected)
    (hA_disj : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hAB_disj : ∀ i j, Disjoint (A i).verts (B j).verts)
    (hadj : ∀ i j, ∃ u ∈ (A i).verts, ∃ v ∈ (B j).verts, G.Adj u v) :
    m < θ ^ 2 / 2 ∨ n < θ ^ 2 / 2 := by
  by_contra! hge
  obtain ⟨hm, hn⟩ := hge
  let K : Fin (θ ^ 2 / 2) ⊕ Fin (θ ^ 2 / 2) → (⊤ : SimpleGraph V).Subgraph :=
    Sum.elim (fun i ↦ A (Fin.castLE hm i)) (fun j ↦ B (Fin.castLE hn j))
  have hminor_bip :
      IsIsoMinor (Graph.ofSimpleGraph (completeBipartiteSimpleGraph (θ ^ 2 / 2) (θ ^ 2 / 2)))
        (toGraph G) := by
    apply isIsoMinor_ofSimpleGraph_of_connected_subgraphs
      (completeBipartiteSimpleGraph (θ ^ 2 / 2) (θ ^ 2 / 2)) hG_fin K
    · rintro (i | j)
      · exact hA_le _
      · exact hB_le _
    · rintro (i | j)
      · exact hA_conn _
      · exact hB_conn _
    · rintro (i₁ | j₁) (i₂ | j₂) hne
      ·exact hA_disj ((Fin.castLE_injective hm).ne (fun h ↦ hne (congrArg Sum.inl h)))
      · exact hAB_disj _ _
      · exact (hAB_disj _ _).symm
      · exact hB_disj ((Fin.castLE_injective hn).ne (fun h ↦ hne (congrArg Sum.inr h)))
    · rintro (i | j) (i' | j') h_adj
      · exact False.elim h_adj
      · exact hadj (Fin.castLE hm i) (Fin.castLE hn j')
      · obtain ⟨u, hu, v, hv, huv⟩ := hadj (Fin.castLE hm i') (Fin.castLE hn j)
        exact ⟨v, hv, u, hu, huv.symm⟩
      · exact False.elim h_adj
  exact hG ((isIsoMinor_gridGraph_completeBipartite heven).trans hminor_bip)

/-! ### Deleting degree-1 vertices and (4.2) -/

/-- Any internal vertex of a simple path in `H` has at least two distinct neighbors in `H`. -/
private lemma exists_two_adj_of_internal_isPath {H : (⊤ : SimpleGraph V).Subgraph} {x y : V}
    (w : (⊤ : SimpleGraph V).Walk x y) (hw : w.IsPath) (hle : w.toSubgraph ≤ H)
    {z : V} (hz : z ∈ w.support) (hzx : z ≠ x) (hzy : z ≠ y) :
    ∃ a b : V, a ≠ b ∧ H.Adj z a ∧ H.Adj z b := by
  induction w with
  | nil =>
    simp only [Walk.support_nil, List.mem_singleton] at hz
    exact absurd hz hzx
  | @cons x x' y hadj rest ih =>
    rw [Walk.cons_isPath_iff] at hw
    rw [Walk.toSubgraph, sup_le_iff] at hle
    have hadj₁ : H.Adj x x' := hle.1.2 (by simp)
    rw [Walk.support_cons, List.mem_cons] at hz
    have hz_rest : z ∈ rest.support := hz.resolve_left hzx
    by_cases hzx' : z = x'
    · subst hzx'
      cases rest with
      | nil => exact absurd rfl hzy
      | @cons _ x'' y hadj₂ rest₂ =>
        rw [Walk.toSubgraph, sup_le_iff] at hle
        have hadj₂H : H.Adj z x'' := hle.2.1.2 (by simp)
        have hx''_mem : x'' ∈ (Walk.cons hadj₂ rest₂).support := by simp
        have hne : x ≠ x'' := fun h ↦ hw.2 (h ▸ hx''_mem)
        exact ⟨x, x'', hne, hadj₁.symm, hadj₂H⟩
    · exact ih hw.1 hle.2 hz_rest hzx' hzy

/-- Deleting a set `L` of vertices from a connected subgraph `H`, where `H.verts \ L` is nonempty
and every vertex of `L ∩ H.verts` has at most one neighbor in `H`, leaves `H.deleteVerts L`
connected. -/
private lemma connected_deleteVerts_of_subsingleton_neighborSet
    {H : (⊤ : SimpleGraph V).Subgraph} (hH : H.Connected) (L : Set V)
    (hne : (H.verts \ L).Nonempty)
    (hL : ∀ v ∈ L, v ∈ H.verts → (H.neighborSet v).Subsingleton) :
    (H.deleteVerts L).Connected := by
  rw [Subgraph.connected_iff_forall_exists_walk_subgraph]
  refine ⟨by simpa using hne, fun {u v} hu hv ↦ ?_⟩
  simp only [Subgraph.deleteVerts_verts, Set.mem_sdiff] at hu hv
  obtain ⟨P, hPH, rfl, rfl⟩ := exists_path_of_preconnected hH.preconnected hu.1 hv.1
  refine ⟨P.walk, ?_⟩
  have hP_verts : P.verts ⊆ H.verts \ L := by
    intro z hzP
    refine ⟨hPH.1 hzP, fun hzL ↦ ?_⟩
    have hzx : z ≠ P.first := fun h ↦ hu.2 (h ▸ hzL)
    have hzy : z ≠ P.last := fun h ↦ hv.2 (h ▸ hzL)
    obtain ⟨a, b, hab, hadja, hadjb⟩ :=
      exists_two_adj_of_internal_isPath P.walk P.isPath hPH (P.mem_verts_iff.1 hzP) hzx hzy
    exact hab (hL z hzL (hPH.1 hzP) hadja hadjb)
  refine ⟨hP_verts, fun a b hab ↦ ?_⟩
  have ha : a ∈ P.verts := P.walk.toSubgraph.edge_vert hab
  have hb : b ∈ P.verts := P.walk.toSubgraph.edge_vert hab.symm
  simp only [Subgraph.deleteVerts_adj]
  exact ⟨(hP_verts ha).1, (hP_verts ha).2, (hP_verts hb).1, (hP_verts hb).2, hPH.2 hab⟩

/-- In a connected subgraph `H`, a leaf `v` (`IsLeafOf H v`) has a unique neighbor in `H`. -/
private lemma exists_unique_adj_of_isLeafOf {H : (⊤ : SimpleGraph V).Subgraph}
    (hH_fin : H.verts.Finite) {v : V} (hleaf : IsLeafOf H v) :
    ∃ u ∈ H.verts, H.Adj v u ∧ ∀ w, H.Adj v w ↔ w = u := by
  have hfin_nb : (H.neighborSet v).Finite :=
    hH_fin.subset (fun x hx ↦ H.edge_vert (H.mem_neighborSet v x |>.1 hx).symm)
  obtain ⟨u, hu_eq⟩ := Set.ncard_eq_one.1 hleaf.2
  have hu_mem : u ∈ H.neighborSet v := hu_eq ▸ Set.mem_singleton u
  have hadj : H.Adj v u := (H.mem_neighborSet v u).1 hu_mem
  refine ⟨u, H.edge_vert hadj.symm, hadj, fun w ↦ ?_⟩
  rw [← H.mem_neighborSet v w, hu_eq, Set.mem_singleton_iff]

/-- If `u` and `v` are adjacent vertices in a connected subgraph `H`, and each has no other
neighbor in `H`, then `H.verts ⊆ {v, u}`. -/
private lemma verts_subset_pair_of_unique_neighbors {H : (⊤ : SimpleGraph V).Subgraph}
    (hH : H.Connected) {v u : V} (hv : v ∈ H.verts)
    (hvu : ∀ w, H.Adj v w ↔ w = u) (huv : ∀ w, H.Adj u w ↔ w = v) :
    H.verts ⊆ {v, u} := by
  intro z hz
  obtain ⟨p, hp⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph H).1 hH).2 hv hz
  have haux : ∀ {a b : V} (q : (⊤ : SimpleGraph V).Walk a b),
      q.toSubgraph ≤ H → a ∈ ({v, u} : Set V) → b ∈ ({v, u} : Set V) := by
    intro a b q hq ha
    induction q with
    | nil => exact ha
    | @cons a c b _ rest ih =>
      rw [Walk.toSubgraph, sup_le_iff] at hq
      have hadj : H.Adj a c := hq.1.2 (by simp)
      have hc : c ∈ ({v, u} : Set V) := by
        rcases ha with rfl | rfl
        · exact Or.inr ((hvu c).1 hadj)
        · exact Or.inl ((huv c).1 hadj)
      exact ih hq.2 hc
  exact haux p hp (Or.inl rfl)

/-- Replacing a finite connected subgraph `B` containing a vertex set `S` by a minimal connected
subgraph `T ≤ B` with `S ⊆ T.verts`: every vertex `x ∈ T.verts \ S` has at least `2` neighbors in
`T`. -/
private lemma exists_minimal_connected_subgraph_containing {B : (⊤ : SimpleGraph V).Subgraph}
    (hB_fin : B.verts.Finite) (hB_conn : B.Connected) (S : Set V)
    (hS_sub : S ⊆ B.verts) (hS_nonempty : S.Nonempty) :
    ∃ T : (⊤ : SimpleGraph V).Subgraph,
      T ≤ B ∧ T.Connected ∧ S ⊆ T.verts ∧
      ∀ x ∈ T.verts \ S, 2 ≤ (T.neighborSet x).ncard := by
  classical
  have hex : ∃ n : ℕ, ∃ T : (⊤ : SimpleGraph V).Subgraph,
      T ≤ B ∧ T.Connected ∧ S ⊆ T.verts ∧ T.verts.ncard = n :=
    ⟨B.verts.ncard, B, le_rfl, hB_conn, hS_sub, rfl⟩
  obtain ⟨T, hTB, hTconn, hST, hTcard⟩ := Nat.find_spec hex
  have hT_fin : T.verts.Finite := hB_fin.subset hTB.1
  refine ⟨T, hTB, hTconn, hST, fun x hx ↦ ?_⟩
  by_contra! hlt
  have hnb_fin : (T.neighborSet x).Finite :=
    hT_fin.subset (fun w hw ↦ T.edge_vert ((T.mem_neighborSet x w).1 hw).symm)
  have hsub_nb : (T.neighborSet x).Subsingleton :=
    (Set.ncard_le_one_iff_eq hnb_fin).1 (by omega) |> fun h ↦ by
      rcases h with h0 | ⟨u, hu⟩
      · rw [h0]
        exact Set.subsingleton_empty
      · rw [hu]
        exact Set.subsingleton_singleton
  have hS_diff : S ⊆ T.verts \ {x} := fun s hs ↦ ⟨hST hs, fun hsx ↦ hx.2 (hsx ▸ hs)⟩
  have hT'_conn : (T.deleteVerts {x}).Connected :=
    connected_deleteVerts_of_subsingleton_neighborSet hTconn {x}
      (hS_nonempty.mono hS_diff) (fun v hv _ ↦ by
        rw [Set.mem_singleton_iff] at hv
        subst hv
        exact hsub_nb)
  have hT'_le : T.deleteVerts {x} ≤ B := (Subgraph.deleteVerts_le).trans hTB
  have hT'_card : (T.deleteVerts {x}).verts.ncard < Nat.find hex := by
    rw [← hTcard, Subgraph.deleteVerts_verts]
    exact Set.ncard_sdiff_singleton_lt_of_mem hx.1 hT_fin
  exact Nat.find_min hex hT'_card ⟨T.deleteVerts {x}, hT'_le, hT'_conn, hS_diff, rfl⟩

/-- Counting step in the proof of Graph Minors V (4.2), pages 97–98.
It suffices to bound the sum of the branch subgraphs' neighbor counts at
any vertex by four. This also applies when these counts are bounded by
distinct actual edges of a multigraph. -/
theorem card_lt_thetaOne_of_neighbor_sum_le_four {G : (⊤ : SimpleGraph V).Subgraph} {θ n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (A : Fin (θ ^ 2 / 2) → (⊤ : SimpleGraph V).Subgraph)
    (B : Fin n → (⊤ : SimpleGraph V).Subgraph)
    (hA_le : ∀ i, A i ≤ G) (hA_conn : ∀ i, (A i).Connected)
    (hA_disj : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts)
    (hB_le : ∀ j, B j ≤ G) (hB_conn : ∀ j, (B j).Connected)
    (hAB : ∀ i j, ∃ v, (A i).verts ∩ (B j).verts = {v} ∧ IsLeafOf (B j) v)
    (hdeg : ∀ v ∈ G.verts, ∑ j : Fin n, ((B j).neighborSet v).ncard ≤ 4) :
    n < θ₁ θ := by
  classical
  let m := θ ^ 2 / 2
  have hm_ge : 18 ≤ m := by
    dsimp [m]
    have h36 : 6 * 6 ≤ θ * θ := Nat.mul_le_mul hθ hθ
    rw [sq]
    omega
  choose v hv_inter hv_leaf using hAB
  have hv_mem_A : ∀ i j, v i j ∈ (A i).verts := by
    intro i j
    have : v i j ∈ (A i).verts ∩ (B j).verts := by
      rw [hv_inter i j]
      exact Set.mem_singleton _
    exact this.1
  have hv_mem_B : ∀ i j, v i j ∈ (B j).verts := fun i j ↦ (hv_leaf i j).1
  have hv_inj : ∀ j, Function.Injective (fun i : Fin m ↦ v i j) := by
    intro j i₁ i₂ heq
    by_contra hne
    have hmem₂ : v i₁ j ∈ (A i₂).verts := by
      change (fun i ↦ v i j) i₁ ∈ (A i₂).verts
      rw [heq]
      exact hv_mem_A i₂ j
    exact Set.disjoint_left.1 (hA_disj hne) (hv_mem_A i₁ j) hmem₂
  let S : Fin n → Set V := fun j ↦ Set.range (fun i : Fin m ↦ v i j)
  have hS_sub : ∀ j, S j ⊆ (B j).verts := by
    rintro j _ ⟨i, rfl⟩
    exact hv_mem_B i j
  have hS_nonempty : ∀ j, (S j).Nonempty := by
    intro j
    exact ⟨v ⟨0, by omega⟩ j, ⟨⟨0, by omega⟩, rfl⟩⟩
  have hT_ex : ∀ j, ∃ T : (⊤ : SimpleGraph V).Subgraph,
      T ≤ B j ∧ T.Connected ∧ S j ⊆ T.verts ∧
      ∀ x ∈ T.verts \ S j, 2 ≤ (T.neighborSet x).ncard :=
    fun j ↦ exists_minimal_connected_subgraph_containing (hG_fin.subset (hB_le j).1)
      (hB_conn j) (S j) (hS_sub j) (hS_nonempty j)
  choose T hTB hTconn hST hTdeg using hT_ex
  have hu_ex : ∀ i j, ∃ u ∈ (B j).verts, (B j).Adj (v i j) u ∧ ∀ w, (B j).Adj (v i j) w ↔ w = u :=
    fun i j ↦ exists_unique_adj_of_isLeafOf (hG_fin.subset (hB_le j).1) (hv_leaf i j)
  choose u hu_mem_B huv_adj huv_uniq using hu_ex
  have huv_T : ∀ i j, (T j).Adj (v i j) (u i j) ∧ ∀ w, (T j).Adj (v i j) w ↔ w = u i j := by
    intro i j
    have hvT : v i j ∈ (T j).verts := hST j ⟨i, rfl⟩
    let i₀ : Fin m := ⟨0, by omega⟩
    let i₁ : Fin m := ⟨1, by omega⟩
    have hne_01 : i₀ ≠ i₁ := by
      intro h
      have := congrArg Fin.val h
      dsimp [i₀, i₁] at this
      omega
    have hex_other : ∃ z ∈ (T j).verts, z ≠ v i j := by
      by_cases hi : i = i₀
      · exact ⟨v i₁ j, hST j ⟨i₁, rfl⟩, (hv_inj j).ne (hi ▸ hne_01.symm)⟩
      · exact ⟨v i₀ j, hST j ⟨i₀, rfl⟩, (hv_inj j).ne (Ne.symm hi)⟩
    obtain ⟨z, hzT, hzne⟩ := hex_other
    obtain ⟨p, hp⟩ := ((Subgraph.connected_iff_forall_exists_walk_subgraph (T j)).1
      (hTconn j)).2 hvT hzT
    have hex_adj : ∃ w, (T j).Adj (v i j) w := by
      cases p with
      | nil => exact absurd rfl hzne
      | @cons _ w _ _ _ =>
        rw [Walk.toSubgraph, sup_le_iff] at hp
        exact ⟨w, hp.1.2 (by simp)⟩
    obtain ⟨w₀, hw₀⟩ := hex_adj
    have hw₀_eq : w₀ = u i j := (huv_uniq i j w₀).1 ((hTB j).2 hw₀)
    subst hw₀_eq
    exact ⟨hw₀, fun w ↦ ⟨fun h ↦ (huv_uniq i j w).1 ((hTB j).2 h), fun h ↦ h ▸ hw₀⟩⟩
  have hu_not_S : ∀ i j, u i j ∉ S j := by
    rintro i j ⟨i', hi'⟩
    have hi'_eq : v i' j = u i j := hi'
    have hsub : (B j).verts ⊆ {v i j, u i j} := by
      apply verts_subset_pair_of_unique_neighbors (hB_conn j) (hv_mem_B i j) (huv_uniq i j)
      intro w
      rw [← hi'_eq, huv_uniq i' j w]
      have h1 : (B j).Adj (v i' j) (v i j) := by
        rw [hi'_eq]
        exact (huv_adj i j).symm
      have h2 : v i j = u i' j := (huv_uniq i' j (v i j)).1 h1
      rw [h2]
    have hS_card : (S j).ncard = m := by
      dsimp [S]
      rw [Set.ncard_range_of_injective (hv_inj j), Nat.card_fin]
    have hpair_le : ({v i j, u i j} : Set V).ncard ≤ 2 :=
      (Set.ncard_insert_le _ _).trans (by simp)
    have hle2 : (S j).ncard ≤ 2 :=
      (Set.ncard_le_ncard ((hS_sub j).trans hsub) (Set.toFinite _)).trans hpair_le
    omega
  have hu_mem_T_diff : ∀ i j, u i j ∈ (T j).verts \ S j := by
    intro i j
    exact ⟨(T j).edge_vert (huv_T i j).1.symm, hu_not_S i j⟩
  let UA : Set V := ⋃ i : Fin m, (A i).verts
  have hT_inter_UA : ∀ j, (T j).verts ∩ UA = S j := by
    intro j
    ext x
    simp only [UA, S, Set.mem_inter_iff, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨hxT, i, hxA⟩
      have hxB : x ∈ (B j).verts := (hTB j).1 hxT
      have hxv : x = v i j := by
        have : x ∈ (A i).verts ∩ (B j).verts := ⟨hxA, hxB⟩
        rwa [hv_inter i j, Set.mem_singleton_iff] at this
      exact ⟨i, hxv.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨hST j ⟨i, rfl⟩, i, hv_mem_A i j⟩
  let G' : (⊤ : SimpleGraph V).Subgraph := G.deleteVerts UA
  have hG'_le : G' ≤ G := Subgraph.deleteVerts_le
  have hG'_fin : G'.verts.Finite := hG_fin.subset hG'_le.1
  have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
  let B' : Fin n → (⊤ : SimpleGraph V).Subgraph := fun j ↦ (T j).deleteVerts (S j)
  have hB'_le : ∀ j, B' j ≤ G' := by
    intro j
    have hT_G : T j ≤ G := (hTB j).trans (hB_le j)
    refine ⟨fun x hx ↦ ?_, fun x y hxy ↦ ?_⟩
    · simp only [B', G', Subgraph.deleteVerts_verts, Set.mem_sdiff] at hx ⊢
      exact ⟨hT_G.1 hx.1, fun hxUA ↦ hx.2 ((hT_inter_UA j).subset ⟨hx.1, hxUA⟩)⟩
    · simp only [B', G', Subgraph.deleteVerts_adj] at hxy ⊢
      obtain ⟨hxT, hxS, hyT, hyS, hadjT⟩ := hxy
      exact ⟨hT_G.1 hxT, fun hxUA ↦ hxS ((hT_inter_UA j).subset ⟨hxT, hxUA⟩),
        hT_G.1 hyT, fun hyUA ↦ hyS ((hT_inter_UA j).subset ⟨hyT, hyUA⟩), hT_G.2 hadjT⟩
  have hB'_conn : ∀ j, (B' j).Connected := by
    intro j
    apply connected_deleteVerts_of_subsingleton_neighborSet (hTconn j) (S j)
    · exact ⟨u ⟨0, by omega⟩ j, hu_mem_T_diff ⟨0, by omega⟩ j⟩
    · rintro x ⟨i, rfl⟩ _ y hy z hz
      rw [(T j).mem_neighborSet (v i j), (huv_T i j).2] at hy hz
      exact hy.trans hz.symm
  let V_set : Fin m → Set V := fun i ↦ Set.range (fun j : Fin n ↦ u i j)
  have hV_sub : ∀ i, V_set i ⊆ G'.verts := by
    rintro i _ ⟨j, rfl⟩
    exact (hB'_le j).1 (hu_mem_T_diff i j)
  have hnot_m : ¬ HasDisjointConnectedMeeting G' V_set m := by
    rintro ⟨D, hDG', hDconn, hDdisj, hDmeet⟩
    have hAD_disj : ∀ i k, Disjoint (A i).verts (D k).verts := by
      intro i k
      rw [Set.disjoint_left]
      intro x hxA hxD
      have hxG' : x ∈ G'.verts := (hDG' k).1 hxD
      exact hxG'.2 (Set.mem_iUnion.2 ⟨i, hxA⟩)
    have hAD_adj : ∀ i k, ∃ a ∈ (A i).verts, ∃ d ∈ (D k).verts, G.Adj a d := by
      intro i k
      obtain ⟨x, hxD, j, rfl⟩ := hDmeet i k
      exact ⟨v i j, hv_mem_A i j, u i j, hxD, (hB_le j).2 (huv_adj i j)⟩
    have h41 := theorem_4_1_simple heven hG_fin hG A D hA_le
      (fun k ↦ (hDG' k).trans hG'_le) hA_conn hDconn hA_disj hDdisj hAD_disj hAD_adj
    omega
  rcases theorem_3_2_simple hθ heven hG'_fin hG'_mem (by omega) V_set hV_sub with
    h_has | ⟨X, hX_sub, hX_card, hX_meet⟩
  · exact False.elim (hnot_m h_has)
  · have hX_meets_B' : ∀ j : Fin n, ((B' j).verts ∩ X).Nonempty := by
      intro j
      apply hX_meet (B' j) (hB'_le j) (hB'_conn j)
      intro i
      exact ⟨u i j, hu_mem_T_diff i j, j, rfl⟩
    have hdeg_bound : ∀ x ∈ X, (Finset.univ.filter (fun j : Fin n ↦ x ∈ (B' j).verts)).card ≤ 2 := by
      intro x hxX
      have hxG : x ∈ G.verts := hG'_le.1 (hX_sub hxX)
      let Jx := Finset.univ.filter (fun j : Fin n ↦ x ∈ (B' j).verts)
      have hnb_fin : ∀ j : Fin n, ((T j).neighborSet x).Finite :=
        fun j ↦ hG_fin.subset (fun w hw ↦
          ((hTB j).trans (hB_le j)).1 ((T j).edge_vert (((T j).mem_neighborSet x w).1 hw).symm))
      let F : Fin n → Finset V := fun j ↦ (hnb_fin j).toFinset
      have hsum_le : ∑ j ∈ Jx, (F j).card ≤
          ∑ j : Fin n, ((B j).neighborSet x).ncard := by
        calc
          ∑ j ∈ Jx, (F j).card ≤ ∑ j ∈ Jx, ((B j).neighborSet x).ncard := by
            apply Finset.sum_le_sum
            intro j _
            have hfinB : ((B j).neighborSet x).Finite :=
              hG_fin.subset (fun y hy => (hB_le j).1 ((B j).edge_vert hy.symm))
            change (hnb_fin j).toFinset.card ≤ _
            rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
            exact Set.ncard_le_ncard (fun y hy => (hTB j).2 hy) hfinB
          _ ≤ ∑ j : Fin n, ((B j).neighborSet x).ncard :=
            Finset.sum_le_sum_of_subset (Finset.subset_univ Jx)
      have h2_le : ∀ j ∈ Jx, 2 ≤ (F j).card := by
        intro j hj
        rw [Finset.mem_filter] at hj
        have h := hTdeg j x hj.2
        rwa [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
      have hsum_ge : 2 * Jx.card ≤ ∑ j ∈ Jx, (F j).card := by
        have := Finset.card_nsmul_le_sum Jx (fun j ↦ (F j).card) 2 h2_le
        rw [smul_eq_mul, mul_comm] at this
        exact this
      have hx_le4 := hdeg x hxG
      change Jx.card ≤ 2
      omega
    have hX_fin : X.Finite := hG'_fin.subset hX_sub
    let Xf : Finset V := hX_fin.toFinset
    have hXf_card : Xf.card = X.ncard := by
      rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    have hn_le_sum : n ≤ ∑ x ∈ Xf, (Finset.univ.filter (fun j : Fin n ↦ x ∈ (B' j).verts)).card := by
      have h_bipartite :
          ∑ j : Fin n, (Xf.filter (fun x ↦ x ∈ (B' j).verts)).card =
            ∑ x ∈ Xf, (Finset.univ.filter (fun j : Fin n ↦ x ∈ (B' j).verts)).card := by
        simp_rw [Finset.card_filter]
        exact Finset.sum_comm
      rw [← h_bipartite]
      have h1 : ∀ j : Fin n, 1 ≤ (Xf.filter (fun x ↦ x ∈ (B' j).verts)).card := by
        intro j
        obtain ⟨x, hxB', hxX⟩ := hX_meets_B' j
        exact Finset.card_pos.2 ⟨x, Finset.mem_filter.2 ⟨hX_fin.mem_toFinset.2 hxX, hxB'⟩⟩
      simpa using Finset.card_nsmul_le_sum Finset.univ
        (fun j : Fin n ↦ (Xf.filter (fun x ↦ x ∈ (B' j).verts)).card) 1 (fun j _ ↦ h1 j)
    have hsum_le :
        ∑ x ∈ Xf, (Finset.univ.filter (fun j : Fin n ↦ x ∈ (B' j).verts)).card ≤ 2 * Xf.card := by
      have := Finset.sum_le_card_nsmul Xf
        (fun x ↦ (Finset.univ.filter (fun j : Fin n ↦ x ∈ (B' j).verts)).card) 2
        (fun x hx ↦ hdeg_bound x (hX_fin.mem_toFinset.1 hx))
      rw [smul_eq_mul, mul_comm] at this
      exact this
    rw [θ₁]
    dsimp [m] at hX_card
    omega

/-- Graph Minors V, (4.2) (page 97):
"Let $A_1, \dots, A_{\theta^2/2}$ be disjoint connected subgraphs of $G \in
\mathcal{F}_\theta$, and let $B_1, \dots, B_n$ be pairwise edge-disjoint connected subgraphs
of $G$. Suppose that for $1 \le i \le \theta^2/2$, $1 \le j \le n$ there is a unique vertex
$v_{ij}$ in $V(A_i) \cap V(B_j)$, and it has valency 1 in $B_j$. Suppose in addition that
all vertices of $G$ have valency $\le 4$. Then $n < \theta_1$, where $\theta_1$ is as
defined in Section 2." -/
theorem theorem_4_2_simple {G : (⊤ : SimpleGraph V).Subgraph} {θ n : ℕ}
    (hθ : 6 ≤ θ) (heven : Even θ) (hG_fin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    (A : Fin (θ ^ 2 / 2) → (⊤ : SimpleGraph V).Subgraph)
    (B : Fin n → (⊤ : SimpleGraph V).Subgraph)
    (hA_le : ∀ i, A i ≤ G) (hA_conn : ∀ i, (A i).Connected)
    (hA_disj : Pairwise fun i i' ↦ Disjoint (A i).verts (A i').verts)
    (hB_le : ∀ j, B j ≤ G) (hB_conn : ∀ j, (B j).Connected)
    (hB_edisj : Pairwise fun j j' ↦ Disjoint (B j).edgeSet (B j').edgeSet)
    (hAB : ∀ i j, ∃ v, (A i).verts ∩ (B j).verts = {v} ∧ IsLeafOf (B j) v)
    (hdeg : ∀ v ∈ G.verts, (G.neighborSet v).ncard ≤ 4) : n < θ₁ θ := by
  classical
  apply card_lt_thetaOne_of_neighbor_sum_le_four hθ heven hG_fin hG
    A B hA_le hA_conn hA_disj hB_le hB_conn hAB
  intro x hx
  have hnb_fin : ∀ j, ((B j).neighborSet x).Finite :=
    fun j => hG_fin.subset (fun y hy => (hB_le j).1 ((B j).edge_vert hy.symm))
  have hnbG : (G.neighborSet x).Finite :=
    hG_fin.subset (fun y hy => G.edge_vert hy.symm)
  let F : Fin n → Finset V := fun j => (hnb_fin j).toFinset
  have hdisj : ((Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint F := by
    intro i _ j _ hij
    change Disjoint (F i) (F j)
    rw [Finset.disjoint_left]
    intro y hi hj
    have hi' : (B i).Adj x y := (hnb_fin i).mem_toFinset.mp hi
    have hj' : (B j).Adj x y := (hnb_fin j).mem_toFinset.mp hj
    have hei : s(x, y) ∈ (B i).edgeSet := hi'
    have hej : s(x, y) ∈ (B j).edgeSet := hj'
    exact Set.disjoint_left.mp (hB_edisj hij) hei hej
  have hsub : Finset.univ.biUnion F ⊆ hnbG.toFinset := by
    intro y hy
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hy
    exact hnbG.mem_toFinset.mpr ((hB_le j).2 ((hnb_fin j).mem_toFinset.mp hj))
  calc
    ∑ j : Fin n, ((B j).neighborSet x).ncard = ∑ j : Fin n, (F j).card := by
      apply Finset.sum_congr rfl
      intro j _
      change _ = (hnb_fin j).toFinset.card
      rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    _ = (Finset.univ.biUnion F).card := (Finset.card_biUnion hdisj).symm
    _ ≤ hnbG.toFinset.card := Finset.card_le_card hsub
    _ = (G.neighborSet x).ncard := by
      rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
    _ ≤ 4 := hdeg x hx

end GraphMinor.GM05
