module

public import GraphMinor.GM01.Defs
public import GraphMinor.GM01.Basic
import GraphMinor.GM01.GridPaths
import GraphMinor.GM01.UniquePaths
import GraphMinor.GM01.Separators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Graph Minors I, (2.8): Disconnected Subgraphs Separating Two Vertex Sets

This file formalizes (2.8) of Robertson and Seymour, *Graph Minors I. Excluding a forest*
(pages 48–49):
* Connected component subgraphs `compSubgraph H c` for a connected component `c` of `H.coe`, and
  the bound on the number of components of `B_j \ X` containing no neighbor of `X ∩ V(B_j)`.
* The grid minor model inside a complete bipartite structure `K_{θ²/2, θ²/2}` in `G`
  (`isIsoMinor_gridGraph_of_bipartite_subgraphs`).
* `GM01.theorem_2_8`: if `B₁, …, Bₙ` are disjoint subgraphs of `G ∈ 𝓕_θ`, each with at most `d`
  components, `|X| ≤ r n`, `X ∪ V(Bⱼ)` separates `A₁` and `A₂`, and there are `m` disjoint paths
  in `G` from `A₁` to `A₂` avoiding `X`, then with `s = d + r (θ² - 1)` either `m < s θ² / 2` or
  `n < 2^{s θ² / 2} (θ² + 2 s θ^{2θ})`.
-/

public section

namespace GraphMinor.GM01

open SimpleGraph Set

variable {α : Type*}

/-! ### Connected component subgraphs -/

/-- The induced subgraph of `H` on the vertex set of a connected component `c` of `H.coe`. -/
@[expose]
noncomputable def compSubgraph (H : (⊤ : SimpleGraph α).Subgraph)
    (c : H.coe.ConnectedComponent) : (⊤ : SimpleGraph α).Subgraph :=
  H.induce (Subtype.val '' c.supp)

@[simp]
lemma compSubgraph_verts (H : (⊤ : SimpleGraph α).Subgraph) (c : H.coe.ConnectedComponent) :
    (compSubgraph H c).verts = Subtype.val '' c.supp :=
  rfl

lemma compSubgraph_le (H : (⊤ : SimpleGraph α).Subgraph) (c : H.coe.ConnectedComponent) :
    compSubgraph H c ≤ H := by
  refine ⟨?_, fun x y hxy ↦ ?_⟩
  · rintro x ⟨v, _, rfl⟩
    exact v.2
  · rw [compSubgraph, Subgraph.induce_adj] at hxy
    exact hxy.2.2

lemma mem_compSubgraph_verts (H : (⊤ : SimpleGraph α).Subgraph) (v : H.verts) :
    v.1 ∈ (compSubgraph H (H.coe.connectedComponentMk v)).verts :=
  ⟨v, rfl, rfl⟩

lemma compSubgraph_disjoint (H : (⊤ : SimpleGraph α).Subgraph)
    {c₁ c₂ : H.coe.ConnectedComponent} (hne : c₁ ≠ c₂) :
    Disjoint (compSubgraph H c₁).verts (compSubgraph H c₂).verts := by
  rw [compSubgraph_verts, compSubgraph_verts, Set.disjoint_left]
  rintro _ ⟨u₁, hu₁, rfl⟩ ⟨u₂, hu₂, heq⟩
  have hu_eq : u₁ = u₂ := Subtype.ext heq.symm
  subst hu_eq
  exact hne (hu₁.symm.trans hu₂)

lemma compSubgraph_connected (H : (⊤ : SimpleGraph α).Subgraph) (c : H.coe.ConnectedComponent) :
    (compSubgraph H c).Connected := by
  have hne : (compSubgraph H c).verts.Nonempty := by
    rcases c.nonempty_supp with ⟨v, hv⟩
    exact ⟨v.1, v, hv, rfl⟩
  refine Subgraph.connected_iff.2 ⟨⟨fun x y ↦ ?_⟩, hne⟩
  rcases x with ⟨x, u, hu, rfl⟩
  rcases y with ⟨y, v, hv, rfl⟩
  have hreach : H.coe.Reachable u v :=
    SimpleGraph.ConnectedComponent.eq.1 (hu.trans hv.symm)
  rcases hreach with ⟨w⟩
  have hw_lift : ∀ {a b : H.verts} (p : H.coe.Walk a b) (ha : a ∈ c.supp) (hb : b ∈ c.supp),
      (compSubgraph H c).coe.Reachable ⟨a.1, a, ha, rfl⟩ ⟨b.1, b, hb, rfl⟩ := by
    intro a b p ha hb
    induction p with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a b d hadj p' ih =>
      have hb_c : b ∈ c.supp := by
        rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at ha ⊢
        exact (SimpleGraph.ConnectedComponent.eq.2 hadj.symm.reachable).trans ha
      have hadj_comp : (compSubgraph H c).coe.Adj ⟨a.1, a, ha, rfl⟩ ⟨b.1, b, hb_c, rfl⟩ := by
        change (H.induce (Subtype.val '' c.supp)).Adj a.1 b.1
        rw [Subgraph.induce_adj]
        exact ⟨⟨a, ha, rfl⟩, ⟨b, hb_c, rfl⟩, hadj⟩
      exact hadj_comp.reachable.trans (ih hb_c hb)
  exact hw_lift w hu hv

/-- Deleting an isolated vertex `v₀` of `G` from a subgraph `H ≤ G` does not increase
`numComponents`. -/
lemma numComponents_deleteVerts_singleton_le_of_isolated
    {G H : (⊤ : SimpleGraph α).Subgraph} (hH_fin : H.verts.Finite) (hH_le : H ≤ G)
    {v₀ : α} (hiso : ¬ ∃ u₀, G.Adj u₀ v₀) :
    numComponents (H.deleteVerts {v₀}) ≤ numComponents H := by
  let H' := H.deleteVerts {v₀}
  have : Finite H.verts := hH_fin.to_subtype
  let : Fintype H.verts := Fintype.ofFinite H.verts
  have : Finite H.coe.ConnectedComponent := Quot.finite _
  let ι_v (x : H'.verts) : H.verts := ⟨x.1, x.2.1⟩
  have h_walk : ∀ {a b : H.verts} (w : H.coe.Walk a b) (ha : a.1 ≠ v₀) (hb : b.1 ≠ v₀),
      H'.coe.Reachable ⟨a.1, a.2, by simpa using ha⟩ ⟨b.1, b.2, by simpa using hb⟩ := by
    intro a b w ha hb
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a d b hadj w' ih =>
      have hadj_H : H.Adj a.1 d.1 := hadj
      have hd_ne : d.1 ≠ v₀ := by
        intro heq
        apply hiso
        refine ⟨a.1, (hH_le.2 (heq ▸ hadj_H))⟩
      have hadj' : H'.coe.Adj ⟨a.1, a.2, by simpa using ha⟩ ⟨d.1, d.2, by simpa using hd_ne⟩ := by
        change (H.deleteVerts {v₀}).Adj a.1 d.1
        rw [Subgraph.deleteVerts_adj]
        exact ⟨a.2, by simpa using ha, d.2, by simpa using hd_ne, hadj_H⟩
      exact hadj'.reachable.trans (ih hd_ne hb)
  let Φ : H'.coe.ConnectedComponent → H.coe.ConnectedComponent :=
    Quot.lift (fun x ↦ H.coe.connectedComponentMk (ι_v x)) (fun x y h ↦ by
      rcases h with ⟨w⟩
      refine SimpleGraph.ConnectedComponent.eq.2 ?_
      have h_imp : ∀ {a b : H'.verts} (p : H'.coe.Walk a b), H.coe.Reachable (ι_v a) (ι_v b) := by
        intro a b p
        induction p with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons a d b hadj p' ihp =>
          have hadj_H : H.coe.Adj (ι_v a) (ι_v d) := (Subgraph.deleteVerts_adj.1 hadj).2.2.2.2
          exact hadj_H.reachable.trans ihp
      exact h_imp w)
  have hΦ_inj : Function.Injective Φ := by
    intro c₁ c₂ heq
    rcases Quot.exists_rep c₁ with ⟨x, rfl⟩
    rcases Quot.exists_rep c₂ with ⟨y, rfl⟩
    have hreach : H.coe.Reachable (ι_v x) (ι_v y) :=
      SimpleGraph.ConnectedComponent.eq.1 heq
    rcases hreach with ⟨w⟩
    have hx_ne : x.1 ≠ v₀ := by simpa using x.2.2
    have hy_ne : y.1 ≠ v₀ := by simpa using y.2.2
    exact SimpleGraph.ConnectedComponent.eq.2 (h_walk w hx_ne hy_ne)
  exact Nat.card_le_card_of_injective Φ hΦ_inj

/-- Paper (page 49): "A component of $B_j \setminus X$ which includes no element of $N(Y_j)$ is a
component of $B_j$, and hence $B_j \setminus X$ has at most $d$ such components." -/
lemma ncard_components_avoiding_neighbors_le
    {G B : (⊤ : SimpleGraph α).Subgraph} (hB_fin : B.verts.Finite) (hB_le : B ≤ G)
    (X : Set α) :
    {c : (B.deleteVerts X).coe.ConnectedComponent |
      ∀ y ∈ X ∩ B.verts, ∀ u ∈ (compSubgraph (B.deleteVerts X) c).verts, ¬ G.Adj y u}.ncard ≤
      numComponents B := by
  let H := B.deleteVerts X
  have hH_fin : H.verts.Finite := hB_fin.subset B.deleteVerts_le.1
  have : Finite B.verts := hB_fin.to_subtype
  let : Fintype B.verts := Fintype.ofFinite B.verts
  have : Finite B.coe.ConnectedComponent := Quot.finite _
  have : Finite H.verts := hH_fin.to_subtype
  let : Fintype H.verts := Fintype.ofFinite H.verts
  have : Finite H.coe.ConnectedComponent := Quot.finite _
  let S := {c : H.coe.ConnectedComponent |
    ∀ y ∈ X ∩ B.verts, ∀ u ∈ (compSubgraph H c).verts, ¬ G.Adj y u}
  let ι_v (x : H.verts) : B.verts := ⟨x.1, x.2.1⟩
  let Φ : H.coe.ConnectedComponent → B.coe.ConnectedComponent :=
    Quot.lift (fun x ↦ B.coe.connectedComponentMk (ι_v x)) (fun x y h ↦ by
      rcases h with ⟨w⟩
      refine SimpleGraph.ConnectedComponent.eq.2 ?_
      have h_imp : ∀ {a b : H.verts} (p : H.coe.Walk a b), B.coe.Reachable (ι_v a) (ι_v b) := by
        intro a b p
        induction p with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons a d b hadj p' ihp =>
          have hadj_B : B.coe.Adj (ι_v a) (ι_v d) := (Subgraph.deleteVerts_adj.1 hadj).2.2.2.2
          exact hadj_B.reachable.trans ihp
      exact h_imp w)
  have h_walk : ∀ {a b : B.verts} (w : B.coe.Walk a b) (ha : a.1 ∉ X)
      (hc : H.coe.connectedComponentMk ⟨a.1, a.2, ha⟩ ∈ S),
      ∃ hb : b.1 ∉ X,
        H.coe.Reachable ⟨a.1, a.2, ha⟩ ⟨b.1, b.2, hb⟩ := by
    intro a b w ha hc
    induction w with
    | nil => exact ⟨ha, SimpleGraph.Reachable.refl _⟩
    | @cons a d b hadj w' ih =>
      have hadj_B : B.Adj a.1 d.1 := hadj
      have hd_not_X : d.1 ∉ X := by
        intro hdX
        have hd_Y : d.1 ∈ X ∩ B.verts := ⟨hdX, d.2⟩
        have ha_comp : a.1 ∈ (compSubgraph H (H.coe.connectedComponentMk ⟨a.1, a.2, ha⟩)).verts :=
          mem_compSubgraph_verts H ⟨a.1, a.2, ha⟩
        exact hc d.1 hd_Y a.1 ha_comp (hB_le.2 hadj_B.symm)
      have hadj_H : H.coe.Adj ⟨a.1, a.2, ha⟩ ⟨d.1, d.2, hd_not_X⟩ := by
        change (B.deleteVerts X).Adj a.1 d.1
        rw [Subgraph.deleteVerts_adj]
        exact ⟨a.2, ha, d.2, hd_not_X, hadj_B⟩
      have hc_d : H.coe.connectedComponentMk ⟨d.1, d.2, hd_not_X⟩ ∈ S := by
        have heq_c : H.coe.connectedComponentMk ⟨d.1, d.2, hd_not_X⟩ =
            H.coe.connectedComponentMk ⟨a.1, a.2, ha⟩ :=
          SimpleGraph.ConnectedComponent.eq.2 hadj_H.symm.reachable
        rwa [heq_c]
      rcases ih hd_not_X hc_d with ⟨hb_not_X, hreach⟩
      exact ⟨hb_not_X, hadj_H.reachable.trans hreach⟩
  have hΦ_inj : Function.Injective (fun c : S ↦ Φ c.1) := by
    rintro ⟨c₁, hc₁⟩ ⟨c₂, hc₂⟩ heq
    apply Subtype.ext
    rcases Quot.exists_rep c₁ with ⟨x, rfl⟩
    rcases Quot.exists_rep c₂ with ⟨y, rfl⟩
    have hreach_B : B.coe.Reachable (ι_v x) (ι_v y) :=
      SimpleGraph.ConnectedComponent.eq.1 heq
    rcases hreach_B with ⟨w⟩
    rcases h_walk w x.2.2 hc₁ with ⟨_, hreach_H⟩
    exact SimpleGraph.ConnectedComponent.eq.2 hreach_H
  exact Nat.card_le_card_of_injective (fun c : S ↦ Φ c.1) hΦ_inj

/-! ### Grid minor model from a complete bipartite structure `K_{θ²/2, θ²/2}` -/

private def bipartiteIdx {θ : ℕ} (heven : Even θ) (r c : Fin θ) : Fin (θ ^ 2 / 2) :=
  ⟨r.val * (θ / 2) + c.val / 2, by
    rcases heven with ⟨k, hk⟩
    have hk_div : θ / 2 = k := by omega
    have hsq_div : θ ^ 2 / 2 = θ * k := by
      have hsq : θ ^ 2 = 2 * (θ * k) := by rw [sq, hk]; ring
      rw [hsq, Nat.mul_div_cancel_left _ (by omega)]
    rw [hk_div, hsq_div]
    have hr_le : r.val + 1 ≤ θ := r.isLt
    have hc_lt : c.val / 2 < k := by omega
    calc
      r.val * k + c.val / 2 < r.val * k + k := by omega
      _ = (r.val + 1) * k := by ring
      _ ≤ θ * k := Nat.mul_le_mul_right k hr_le⟩

private lemma bipartiteIdx_injective_of_mod_eq {θ : ℕ} (heven : Even θ)
    {p₁ p₂ : Fin θ × Fin θ}
    (hmod : (p₁.1.val + p₁.2.val) % 2 = (p₂.1.val + p₂.2.val) % 2)
    (hidx : bipartiteIdx heven p₁.1 p₁.2 = bipartiteIdx heven p₂.1 p₂.2) :
    p₁ = p₂ := by
  rcases p₁ with ⟨r₁, c₁⟩
  rcases p₂ with ⟨r₂, c₂⟩
  dsimp at hmod hidx
  have hval : r₁.val * (θ / 2) + c₁.val / 2 = r₂.val * (θ / 2) + c₂.val / 2 :=
    Fin.mk.inj hidx
  rcases heven with ⟨k, hk⟩
  have hk_div : θ / 2 = k := by omega
  rw [hk_div] at hval
  have hc₁_lt : c₁.val / 2 < k := by omega
  have hc₂_lt : c₂.val / 2 < k := by omega
  have hr_eq : r₁.val = r₂.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (r₁.val + 1) * k ≤ r₂.val * k := Nat.mul_le_mul_right k hlt
      have : r₁.val * k + k ≤ r₂.val * k := by linarith [add_mul r₁.val 1 k]
      omega
    · have hle : (r₂.val + 1) * k ≤ r₁.val * k := Nat.mul_le_mul_right k hgt
      have : r₂.val * k + k ≤ r₁.val * k := by linarith [add_mul r₂.val 1 k]
      omega
  have hc_div : c₁.val / 2 = c₂.val / 2 := by
    rw [hr_eq] at hval
    omega
  have hc_eq : c₁.val = c₂.val := by omega
  exact Prod.ext (Fin.ext hr_eq) (Fin.ext hc_eq)

/-- Paper (page 49): if `Q_1, …, Q_{θ²/2}` are pairwise disjoint connected subgraphs of `G`
disjoint from `X`, and `v_1, …, v_{θ²/2}` are distinct vertices in `X ∩ V(G)` each adjacent in `G`
to a vertex of every `Q_i`, then `G` has a minor isomorphic to the `θ`-grid. -/
lemma isIsoMinor_gridGraph_of_bipartite_subgraphs {θ : ℕ} (heven : Even θ)
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) {X : Set α}
    (Q : Fin (θ ^ 2 / 2) → (⊤ : SimpleGraph α).Subgraph)
    (hQ_le : ∀ i, Q i ≤ G)
    (hQ_conn : ∀ i, (Q i).Connected)
    (hQ_disj : Pairwise fun i₁ i₂ ↦ Disjoint (Q i₁).verts (Q i₂).verts)
    (hQ_disj_X : ∀ i, Disjoint (Q i).verts X)
    (v : Fin (θ ^ 2 / 2) → α)
    (hv_inj : Function.Injective v)
    (hv_X : ∀ b, v b ∈ X)
    (hv_G : ∀ b, v b ∈ G.verts)
    (hadj : ∀ i b, ∃ u ∈ (Q i).verts, G.Adj (v b) u) :
    IsIsoMinor (gridGraph θ) (toGraph G) := by
  let B (p : Fin θ × Fin θ) : (⊤ : SimpleGraph α).Subgraph :=
    if (p.1.val + p.2.val) % 2 = 0 then
      Q (bipartiteIdx heven p.1 p.2)
    else
      (⊤ : SimpleGraph α).singletonSubgraph (v (bipartiteIdx heven p.1 p.2))
  refine isIsoMinor_ofSimpleGraph_of_connected_subgraphs (pathGraph θ □ pathGraph θ) hfin B
    ?_ ?_ ?_ ?_
  · intro p
    dsimp [B]
    split_ifs
    · exact hQ_le _
    · rw [singletonSubgraph_le_iff]
      exact hv_G _
  · intro p
    dsimp [B]
    split_ifs
    · exact hQ_conn _
    · exact Subgraph.singletonSubgraph_connected
  · intro p₁ p₂ hne
    dsimp [B]
    split_ifs with h₁ h₂
    · refine hQ_disj (fun heq ↦ hne (bipartiteIdx_injective_of_mod_eq heven (h₁.trans h₂.symm) heq))
    · rw [singletonSubgraph_verts, Set.disjoint_singleton_right]
      exact (hQ_disj_X _).notMem_of_mem_right (hv_X _)
    · rw [singletonSubgraph_verts, Set.disjoint_singleton_left]
      exact (hQ_disj_X _).notMem_of_mem_right (hv_X _)
    · rw [singletonSubgraph_verts, singletonSubgraph_verts, Set.disjoint_singleton]
      have hmod : (p₁.1.val + p₁.2.val) % 2 = (p₂.1.val + p₂.2.val) % 2 := by omega
      exact fun heq ↦ hne (bipartiteIdx_injective_of_mod_eq heven hmod (hv_inj heq))
  · rintro ⟨r₁, c₁⟩ ⟨r₂, c₂⟩ hadj_grid
    have hmod_ne : (r₁.val + c₁.val) % 2 ≠ (r₂.val + c₂.val) % 2 := by
      simp only [boxProd_adj, pathGraph_adj] at hadj_grid
      rcases hadj_grid with ⟨hstep | hstep, rfl⟩ | ⟨hstep | hstep, rfl⟩ <;> omega
    dsimp [B]
    split_ifs with h₁ h₂
    · exact (hmod_ne (h₁.trans h₂.symm)).elim
    · rcases hadj (bipartiteIdx heven r₁ c₁) (bipartiteIdx heven r₂ c₂) with ⟨u, hu, huv⟩
      exact ⟨u, hu, v (bipartiteIdx heven r₂ c₂), rfl, huv.symm⟩
    · rcases hadj (bipartiteIdx heven r₂ c₂) (bipartiteIdx heven r₁ c₁) with ⟨u, hu, huv⟩
      exact ⟨v (bipartiteIdx heven r₁ c₁), rfl, u, hu, huv⟩
    · omega

/-! ### Minimal family of components meeting at least `K` paths -/

/-- If a finite set `C₀` of components meets at least `K` paths in `P`, and each component meets at
most `L` paths with `L * (B - 1) < K` (and `1 ≤ B`), then there is a subset `D ⊆ C₀` of size `B`
and an injection `f : D → Fin m` such that for each `c ∈ D`, `P (f c)` meets `c` and meets no other
component in `D`. -/
private lemma exists_private_paths_of_minimal_components
    {m : ℕ} {H : (⊤ : SimpleGraph α).Subgraph} (hH_fin : H.verts.Finite)
    (P : Fin m → Path α)
    (C₀ : Set H.coe.ConnectedComponent)
    {K B : ℕ} (hB_pos : 1 ≤ B)
    (hK_gt : (B - 1) * (B - 1) < K)
    (h_each : ∀ c ∈ C₀, {i : Fin m | ((P i).verts ∩ (compSubgraph H c).verts).Nonempty}.ncard < B)
    (h_total : K ≤ {i : Fin m | ∃ c ∈ C₀, ((P i).verts ∩ (compSubgraph H c).verts).Nonempty}.ncard) :
    ∃ (I : Set (Fin m)) (D : Fin m → H.coe.ConnectedComponent),
      I.ncard = B ∧
      (∀ i ∈ I, D i ∈ C₀) ∧
      (∀ i ∈ I, ((P i).verts ∩ (compSubgraph H (D i)).verts).Nonempty) ∧
      (∀ i ∈ I, ∀ i' ∈ I, i' ≠ i → Disjoint (P i').verts (compSubgraph H (D i)).verts) := by
  classical
  have : Finite H.verts := hH_fin.to_subtype
  let : Fintype H.verts := Fintype.ofFinite H.verts
  have : Finite H.coe.ConnectedComponent := Quot.finite _
  let : Fintype H.coe.ConnectedComponent := Fintype.ofFinite H.coe.ConnectedComponent
  let PathsOf (D : Set H.coe.ConnectedComponent) : Set (Fin m) :=
    {i : Fin m | ∃ c ∈ D, ((P i).verts ∩ (compSubgraph H c).verts).Nonempty}
  let Good (k : ℕ) : Prop := ∃ D ⊆ C₀, D.ncard = k ∧ K ≤ (PathsOf D).ncard
  have hex_good : ∃ k, Good k := ⟨C₀.ncard, C₀, Subset.rfl, rfl, h_total⟩
  let k₀ := Nat.find hex_good
  rcases Nat.find_spec hex_good with ⟨D₀, hD₀_sub, hD₀_card, hD₀_paths⟩
  change D₀.ncard = k₀ at hD₀_card
  have hD₀_min : ∀ D' ⊆ C₀, D'.ncard < k₀ → (PathsOf D').ncard < K := by
    intro D' hD'_sub hlt
    by_contra hge
    exact Nat.find_min hex_good hlt ⟨D', hD'_sub, rfl, not_lt.1 hge⟩
  -- Show `B ≤ k₀`: since each `c ∈ D₀` meets at most `B - 1` paths, `(PathsOf D₀).ncard ≤ k₀ * (B - 1)`.
  have hPathsOf_le : ∀ (S : Finset H.coe.ConnectedComponent),
      (↑S : Set H.coe.ConnectedComponent) ⊆ C₀ →
      (PathsOf ↑S).ncard ≤ S.card * (B - 1) := by
    intro S hS
    induction S using Finset.induction with
    | empty =>
      have hempty : PathsOf (↑(∅ : Finset H.coe.ConnectedComponent) : Set _) = ∅ := by
        ext i; simp [PathsOf]
      rw [hempty, Set.ncard_empty, Finset.card_empty, zero_mul]
    | @insert c S hc_not_mem ih =>
      have hS_sub : (↑S : Set H.coe.ConnectedComponent) ⊆ C₀ :=
        (Finset.coe_subset.2 (Finset.subset_insert c S)).trans hS
      have hc_C₀ : c ∈ C₀ := hS (Finset.mem_insert_self c S)
      have hunion : PathsOf (↑(insert c S) : Set H.coe.ConnectedComponent) =
          {i : Fin m | ((P i).verts ∩ (compSubgraph H c).verts).Nonempty} ∪ PathsOf ↑S := by
        ext i
        simp only [PathsOf, Finset.coe_insert, mem_insert_iff, mem_ofPred_eq, mem_union]
        constructor
        · rintro ⟨d, rfl | hd, h⟩
          · exact Or.inl h
          · exact Or.inr ⟨d, hd, h⟩
        · rintro (h | ⟨d, hd, h⟩)
          · exact ⟨c, Or.inl rfl, h⟩
          · exact ⟨d, Or.inr hd, h⟩
      have hc_le : {i : Fin m | ((P i).verts ∩ (compSubgraph H c).verts).Nonempty}.ncard ≤ B - 1 := by
        have hlt := h_each c hc_C₀
        omega
      calc
        (PathsOf (↑(insert c S) : Set _)).ncard
          ≤ {i : Fin m | ((P i).verts ∩ (compSubgraph H c).verts).Nonempty}.ncard +
              (PathsOf ↑S).ncard := by
            rw [hunion]
            exact Set.ncard_union_le _ _
        _ ≤ (B - 1) + S.card * (B - 1) := Nat.add_le_add hc_le (ih hS_sub)
        _ = (insert c S).card * (B - 1) := by
          rw [Finset.card_insert_of_notMem hc_not_mem, add_mul, one_mul, add_comm]
  have hk₀_ge_B : B ≤ k₀ := by
    by_contra hlt
    have hk₀_le : k₀ ≤ B - 1 := by omega
    have hcard_eq : D₀.toFinset.card = k₀ := by
      rw [← hD₀_card, Set.ncard_eq_toFinset_card']
    have hle := hPathsOf_le D₀.toFinset (by simpa using hD₀_sub)
    simp only [Set.coe_toFinset] at hle
    rw [hcard_eq] at hle
    have hmul_le : k₀ * (B - 1) ≤ (B - 1) * (B - 1) := Nat.mul_le_mul_right (B - 1) hk₀_le
    omega
  -- For each `c ∈ D₀`, by minimality of `D₀`, there is a path `i(c)` meeting `c` and no other `c' ∈ D₀`.
  have hex_priv : ∀ c : D₀, ∃ i : Fin m,
      ((P i).verts ∩ (compSubgraph H c.1).verts).Nonempty ∧
      ∀ c' : D₀, c' ≠ c → Disjoint (P i).verts (compSubgraph H c'.1).verts := by
    rintro ⟨c, hc⟩
    have hlt_card : (D₀ \ {c}).ncard < k₀ := by
      rw [← hD₀_card]
      exact Set.ncard_sdiff_singleton_lt_of_mem hc (Set.toFinite D₀)
    have hlt_K : (PathsOf (D₀ \ {c})).ncard < K :=
      hD₀_min (D₀ \ {c}) (sdiff_subset.trans hD₀_sub) hlt_card
    have hnot_sub : ¬ PathsOf D₀ ⊆ PathsOf (D₀ \ {c}) := by
      intro hsub
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    rcases Set.not_subset.1 hnot_sub with ⟨i, hi_D₀, hi_not_diff⟩
    refine ⟨i, ?_, ?_⟩
    · rcases hi_D₀ with ⟨c', hc'_D₀, hmeet⟩
      by_cases heq : c' = c
      · subst heq; exact hmeet
      · exact (hi_not_diff ⟨c', ⟨hc'_D₀, heq⟩, hmeet⟩).elim
    · rintro ⟨c', hc'⟩ hne
      have hne_val : c' ≠ c := fun h ↦ hne (Subtype.ext h)
      rw [Set.disjoint_left]
      intro x hxP hxC
      exact hi_not_diff ⟨c', ⟨hc', hne_val⟩, x, hxP, hxC⟩
  choose f hf_meet hf_disj using hex_priv
  have hf_inj : Function.Injective f := by
    intro c₁ c₂ heq
    by_contra hne
    rcases hf_meet c₁ with ⟨x, hxP, hxC⟩
    rw [heq] at hxP
    exact (hf_disj c₂ c₁ hne).notMem_of_mem_left hxP hxC
  -- Take a subset `D₁ ⊆ Set.univ : Set D₀` of size `B`.
  have hD₀_univ_card : (Set.univ : Set D₀).ncard = k₀ := by
    rw [← Set.ncard_image_of_injective Set.univ Subtype.val_injective]
    have himg : Subtype.val '' (Set.univ : Set D₀) = D₀ := by ext x; simp
    rw [himg, hD₀_card]
  rcases Set.exists_subset_card_eq (s := (Set.univ : Set D₀)) (by omega : B ≤ (Set.univ : Set D₀).ncard)
    with ⟨D₁, _, hD₁_card⟩
  let I := f '' D₁
  have hI_card : I.ncard = B := by
    rw [Set.ncard_image_of_injective D₁ hf_inj, hD₁_card]
  have hc_nonempty : Nonempty H.coe.ConnectedComponent := by
    rcases Set.nonempty_of_ncard_ne_zero (s := D₁) (by omega) with ⟨c, _⟩
    exact ⟨c.1⟩
  let D (i : Fin m) : H.coe.ConnectedComponent :=
    if hi : ∃ c ∈ D₁, f c = i then (Classical.choose hi).1 else Classical.arbitrary _
  have hD_spec : ∀ c ∈ D₁, D (f c) = c.1 := by
    intro c hc
    have hex : ∃ c' ∈ D₁, f c' = f c := ⟨c, hc, rfl⟩
    have hD_eq : D (f c) = (Classical.choose hex).1 := by
      dsimp [D]
      rw [dite_eq_left_of_eq_true (eq_true hex)]
    rcases Classical.choose_spec hex with ⟨_, hfc'⟩
    rw [hD_eq, hf_inj hfc']
  refine ⟨I, D, hI_card, ?_, ?_, ?_⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [hD_spec c hc]
    exact hD₀_sub c.2
  · rintro _ ⟨c, hc, rfl⟩
    rw [hD_spec c hc]
    exact hf_meet c
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨c', hc', rfl⟩ hne
    rw [hD_spec c hc]
    have hc_ne : c' ≠ c := fun heq ↦ hne (congrArg f heq)
    exact hf_disj c' c hc_ne.symm

/-- Connectedness of the union of a path `P` with a family of connected subgraphs `D b` that each
meet `P`. -/
private lemma connected_path_sup_biUnion {ι : Type*} (P : Path α) (S : Set ι)
    (D : ι → (⊤ : SimpleGraph α).Subgraph)
    (hD_conn : ∀ b ∈ S, (D b).Connected)
    (hD_meet : ∀ b ∈ S, (P.verts ∩ (D b).verts).Nonempty) :
    (P.toSubgraph ⊔ ⨆ b ∈ S, D b).Connected := by
  let Q := P.toSubgraph ⊔ ⨆ b ∈ S, D b
  have hP_le : P.toSubgraph ≤ Q := le_sup_left
  have hD_le : ∀ b ∈ S, D b ≤ Q := fun b hb ↦
    (le_biSup D hb).trans le_sup_right
  have hQ_verts : Q.verts = P.verts ∪ ⋃ b ∈ S, (D b).verts := by
    simp [Q, Path.verts, Subgraph.verts_sup, Subgraph.verts_iSup]
  have hreach_P : ∀ {x : Q.verts}, x.1 ∈ P.verts →
      Q.coe.Reachable ⟨P.first, hP_le.1 P.first_mem_verts⟩ x := by
    intro x hxP
    rcases (P.connected_toSubgraph.preconnected ⟨P.first, P.first_mem_verts⟩ ⟨x.1, hxP⟩) with ⟨w⟩
    exact (w.map (Subgraph.inclusion hP_le)).reachable
  have hreach_Q : ∀ (x : Q.verts), Q.coe.Reachable ⟨P.first, hP_le.1 P.first_mem_verts⟩ x := by
    intro x
    have hx_mem : x.1 ∈ P.verts ∪ ⋃ b ∈ S, (D b).verts := hQ_verts ▸ x.2
    rcases hx_mem with hxP | hxD
    · exact hreach_P hxP
    · rcases mem_iUnion₂.1 hxD with ⟨b, hbS, hxb⟩
      rcases hD_meet b hbS with ⟨z, hzP, hzD⟩
      have hreach_z : Q.coe.Reachable ⟨P.first, hP_le.1 P.first_mem_verts⟩ ⟨z, hP_le.1 hzP⟩ :=
        hreach_P hzP
      rcases (hD_conn b hbS).preconnected ⟨z, hzD⟩ ⟨x.1, hxb⟩ with ⟨w⟩
      have hreach_zx : Q.coe.Reachable ⟨z, hP_le.1 hzP⟩ x :=
        (w.map (Subgraph.inclusion (hD_le b hbS))).reachable
      exact hreach_z.trans hreach_zx
  exact Subgraph.connected_iff.2
    ⟨⟨fun x y ↦ (hreach_Q x).symm.trans (hreach_Q y)⟩, ⟨P.first, hP_le.1 P.first_mem_verts⟩⟩

/-! ### Proof of (2.8) (pages 48–49) -/

/-- **Graph Minors I, (2.8)** (page 48):
"Let $A_1, A_2, X \subseteq V(G)$, where $G \in \mathscr{F}_\theta$, and let $B_1, \dots, B_n$ be
disjoint subgraphs of $G$, each with at most $d$ components. Suppose that the following conditions
are satisfied:
(i) $|X| \le rn$, for some integer $r \ge 0$;
(ii) for $1 \le j \le n$, $X \cup V(B_j)$ separates $A_1$ and $A_2$;
(iii) there are $m$ disjoint paths in $G$ from $A_1$ to $A_2$, each avoiding $X$.
Let $s = d + r(\theta^2 - 1)$. Then either $m < \frac{1}{2}s\theta^2$ or
$n < 2^{s\theta^2/2}(\theta^2 + 2s\theta^{2\theta})$."

Note: we include `(hs : 0 < d + r)` to exclude the degenerate `d = 0, r = 0` case (`s = 0, m = 0,
X = ∅, Bⱼ = ⊥`), where `m < 0` is impossible and `n` can be arbitrary.
The corrected general-graph form is `GM01.Full.theorem_2_8_proof`. -/
theorem theorem_2_8_simple {θ d r m n : ℕ} (hθ : 6 ≤ θ) (heven : Even θ) (hs : 0 < d + r)
    {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
    {A₁ A₂ X : Set α} (hA₁ : A₁ ⊆ G.verts) (hA₂ : A₂ ⊆ G.verts) (hX : X ⊆ G.verts)
    (hX_card : X.ncard ≤ r * n)
    (P : Fin m → Path α) (hP_fam : IsDisjointPathFamily G A₁ A₂ P)
    (hP_avoids : ∀ i, (P i).Avoids X)
    (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
    (hB_comp : ∀ j, numComponents (B j) ≤ d)
    (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
    (hB_sep : ∀ j, Separates G (X ∪ (B j).verts) A₁ A₂) :
    let s := d + r * (θ ^ 2 - 1)
    m < s * θ ^ 2 / 2 ∨ n < 2 ^ (s * θ ^ 2 / 2) * (θ ^ 2 + 2 * s * θ ^ (2 * θ)) := by
  classical
  intro s
  -- Strong induction on `|V(G)| + |E(G)| + m` ("If possible, choose a counterexample with
  -- `|V(G)| + |E(G)| + m` minimum", page 48).
  suffices hind :
      ∀ (N : ℕ) {m : ℕ} {G : (⊤ : SimpleGraph α).Subgraph} (hfin : G.verts.Finite) (hG : G ∈ 𝓕 θ)
        {A₁ A₂ X : Set α} (hA₁ : A₁ ⊆ G.verts) (hA₂ : A₂ ⊆ G.verts) (hX : X ⊆ G.verts)
        (hX_card : X.ncard ≤ r * n)
        (P : Fin m → Path α) (hP_fam : IsDisjointPathFamily G A₁ A₂ P)
        (hP_avoids : ∀ i, (P i).Avoids X)
        (B : Fin n → (⊤ : SimpleGraph α).Subgraph) (hB_le : ∀ j, B j ≤ G)
        (hB_comp : ∀ j, numComponents (B j) ≤ d)
        (hB_disj : Pairwise fun j j' ↦ Disjoint (B j).verts (B j').verts)
        (hB_sep : ∀ j, Separates G (X ∪ (B j).verts) A₁ A₂),
        G.verts.ncard + G.edgeSet.ncard + m = N →
        m < s * θ ^ 2 / 2 ∨ n < 2 ^ (s * θ ^ 2 / 2) * (θ ^ 2 + 2 * s * θ ^ (2 * θ)) by
    exact hind _ hfin hG hA₁ hA₂ hX hX_card P hP_fam hP_avoids B hB_le hB_comp hB_disj hB_sep rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro m G hfin hG A₁ A₂ X hA₁ hA₂ hX hX_card P hP_fam hP_avoids B hB_le hB_comp hB_disj hB_sep hN
    by_contra hnot
    rcases not_or.1 hnot with ⟨hm_ge, hn_ge⟩
    have hm_ge' : s * θ ^ 2 / 2 ≤ m := not_lt.1 hm_ge
    -- "Then evidently we have `m = ½ s θ²`."
    rcases lt_or_eq_of_le hm_ge' with hm_gt | hm_eq
    · let P' (i : Fin (m - 1)) : Path α := P ⟨i.val, by omega⟩
      have hP'_fam : IsDisjointPathFamily G A₁ A₂ P' :=
        ⟨fun i ↦ hP_fam.1 ⟨i.val, by omega⟩,
          fun i₁ i₂ hne ↦ hP_fam.2 (fun h ↦ hne (Fin.ext (Fin.mk.inj h)))⟩
      have hP'_avoids : ∀ i, (P' i).Avoids X := fun i ↦ hP_avoids ⟨i.val, by omega⟩
      have hlt : G.verts.ncard + G.edgeSet.ncard + (m - 1) < N := by omega
      rcases ih _ hlt hfin hG hA₁ hA₂ hX hX_card P' hP'_fam hP'_avoids B hB_le hB_comp hB_disj
        hB_sep rfl with h1 | h2
      · omega
      · exact hn_ge h2
    have hθ_sq : 36 ≤ θ ^ 2 := by rw [sq]; exact Nat.mul_le_mul hθ hθ
    have hs_pos : 1 ≤ s := by
      dsimp [s]
      rcases ( by omega : 1 ≤ d ∨ 1 ≤ r ) with hd | hr
      · omega
      · have : 35 ≤ r * (θ ^ 2 - 1) := by
          calc 35 = 1 * 35 := by omega
          _ ≤ r * (θ ^ 2 - 1) := Nat.mul_le_mul hr (by omega)
        omega
    have hs_div : s * θ ^ 2 / 2 = s * (θ ^ 2 / 2) := by
      rcases heven with ⟨k, hk⟩
      have hsq : θ ^ 2 = 2 * (2 * k * k) := by rw [hk]; ring
      rw [hsq, ← mul_assoc, mul_comm s 2, mul_assoc,
        Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)]
    have hm_ge_half : θ ^ 2 / 2 ≤ m := by
      rw [← hm_eq, hs_div]
      exact Nat.le_mul_of_pos_left _ hs_pos
    -- Replace `A₁` and `A₂` by `range (first ∘ P)` and `range (last ∘ P)`.
    let A₁₀ : Set α := Set.range fun i ↦ (P i).first
    let A₂₀ : Set α := Set.range fun i ↦ (P i).last
    have hA₁₀_sub : A₁₀ ⊆ A₁ := by rintro _ ⟨i, rfl⟩; exact (hP_fam.1 i).2.1
    have hA₂₀_sub : A₂₀ ⊆ A₂ := by rintro _ ⟨i, rfl⟩; exact (hP_fam.1 i).2.2
    have hA₁₀_G : A₁₀ ⊆ G.verts := hA₁₀_sub.trans hA₁
    have hA₂₀_G : A₂₀ ⊆ G.verts := hA₂₀_sub.trans hA₂
    have hP_fam₀ : IsDisjointPathFamily G A₁₀ A₂₀ P :=
      ⟨fun i ↦ ⟨(hP_fam.1 i).1, ⟨i, rfl⟩, ⟨i, rfl⟩⟩, hP_fam.2⟩
    have hB_sep₀ : ∀ j, Separates G (X ∪ (B j).verts) A₁₀ A₂₀ :=
      fun j ↦ (hB_sep j).mono_endpoints hA₁₀_sub hA₂₀_sub
    -- "If some edge of `G` is in both some `Pᵢ` and some `Bⱼ`, we may contract it..."
    have hno_shared_edge :
        ∀ (P' : Fin m → Path α), IsDisjointPathFamily G A₁₀ A₂₀ P' →
          (∀ i, (P' i).Avoids X) →
          ∀ i j, Disjoint (P' i).edgeSet (B j).edgeSet := by
      intro P' hP'_fam hP'_avoids i j
      rw [Set.disjoint_left]
      intro e heP heB
      rcases contract_shared_path_subgraph_edge hfin hG hA₁₀_G hA₂₀_G hX P' hP'_fam hP'_avoids
        B hB_le hB_disj hB_sep₀ heP heB with
        ⟨G', A₁', A₂', P'', B', hG'_fin, hG'_mem, hV_lt, hE_le, hA₁'_G, hA₂'_G, hX_G',
          hP''_fam, hP''_avoids, hB'_le, _, hB'_comp, hB'_disj, hB'_sep⟩
      have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
      rcases ih _ hlt hG'_fin hG'_mem hA₁'_G hA₂'_G hX_G' hX_card P'' hP''_fam hP''_avoids
        B' hB'_le (fun k ↦ (hB'_comp k).trans (hB_comp k)) hB'_disj hB'_sep rfl with h1 | h2
      · exact hm_ge h1
      · exact hn_ge h2
    -- "...and if some edge is neither in some `Pᵢ` nor in some `Bⱼ`, we may delete it, in either
    -- case producing a smaller counterexample."
    have hedge_cover : G.edgeSet ⊆ (⋃ i, (P i).edgeSet) ∪ ⋃ j, (B j).edgeSet := by
      intro e heG
      by_contra hnot_mem
      rw [mem_union, mem_iUnion, mem_iUnion, not_or, not_exists, not_exists] at hnot_mem
      rcases hnot_mem with ⟨hnot_P, hnot_B⟩
      let G' := G.deleteEdges {e}
      have hG'_le : G' ≤ G := G.deleteEdges_le {e}
      have hG'_fin : G'.verts.Finite := hfin
      have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
      have hE_fin : G.edgeSet.Finite := finite_edgeSet_of_finite_verts hfin
      have hG'_edgeSet : G'.edgeSet = G.edgeSet \ {e} := by
        ext x
        induction x using Sym2.ind with
        | _ a b => simp [G', Subgraph.deleteEdges_adj]
      have hE_lt : G'.edgeSet.ncard < G.edgeSet.ncard := by
        rw [hG'_edgeSet]
        exact Set.ncard_sdiff_singleton_lt_of_mem heG hE_fin
      have hV_eq : G'.verts.ncard = G.verts.ncard := rfl
      have hP_fam' : IsDisjointPathFamily G' A₁₀ A₂₀ P := by
        refine ⟨fun i ↦ ⟨?_, (hP_fam₀.1 i).2.1, (hP_fam₀.1 i).2.2⟩, hP_fam₀.2⟩
        refine ⟨(hP_fam₀.1 i).1.1, fun x y hxy ↦ ?_⟩
        rw [Subgraph.deleteEdges_adj]
        exact ⟨(hP_fam₀.1 i).1.2 hxy, fun heq ↦ hnot_P i (heq ▸ hxy)⟩
      have hB_le' : ∀ j, B j ≤ G' := by
        intro j
        refine ⟨(hB_le j).1, fun x y hxy ↦ ?_⟩
        rw [Subgraph.deleteEdges_adj]
        exact ⟨(hB_le j).2 hxy, fun heq ↦ hnot_B j (heq ▸ hxy)⟩
      have hB_sep' : ∀ j, Separates G' (X ∪ (B j).verts) A₁₀ A₂₀ :=
        fun j ↦ (hB_sep₀ j).of_le hG'_le
      have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
      rcases ih _ hlt hG'_fin hG'_mem hA₁₀_G hA₂₀_G hX hX_card P hP_fam' hP_avoids B hB_le'
        hB_comp hB_disj hB_sep' rfl with h1 | h2
      · exact hm_ge h1
      · exact hn_ge h2
    -- "It follows that `E(P₁) ∪ … ∪ E(Pₘ) = E(G) - (E(B₁) ∪ … ∪ E(Bₙ))`, and so `{P₁, …, Pₘ}` is
    -- the unique set of `m` disjoint paths of `G` from `A₁` to `A₂` avoiding `X`."
    have hP_fam_delX : IsDisjointPathFamily (G.deleteVerts X) A₁₀ A₂₀ P := by
      refine ⟨fun i ↦ ⟨?_, (hP_fam₀.1 i).2.1, (hP_fam₀.1 i).2.2⟩, hP_fam₀.2⟩
      exact toSubgraph_le_deleteVerts_iff.2 ⟨(hP_fam₀.1 i).1, hP_avoids i⟩
    have hP_unique_delX : IsUniqueDisjointPathFamily (G.deleteVerts X) A₁₀ A₂₀ P := by
      refine isUniqueDisjointPathFamily_of_edgeSet_subset P hP_fam_delX (fun P' hP'_fam e he ↦ ?_)
      rcases mem_iUnion.1 he with ⟨k, he_P'k⟩
      have hP'_fam_G : IsDisjointPathFamily G A₁₀ A₂₀ P' :=
        ⟨fun i ↦ ⟨(hP'_fam.1 i).1.trans G.deleteVerts_le, (hP'_fam.1 i).2⟩, hP'_fam.2⟩
      have hP'_avoids : ∀ i, (P' i).Avoids X :=
        fun i ↦ (toSubgraph_le_deleteVerts_iff.1 (hP'_fam.1 i).1).2
      have he_G : e ∈ G.edgeSet := Subgraph.edgeSet_mono (hP'_fam_G.1 k).1 he_P'k
      rcases hedge_cover he_G with he_P | he_B
      · exact he_P
      · rcases mem_iUnion.1 he_B with ⟨j, he_Bj⟩
        exact ((hno_shared_edge P' hP'_fam_G hP'_avoids k j).notMem_of_mem_left he_P'k he_Bj).elim
    -- "Every vertex `v` of `V(G) - X` is in one of `P₁, …, Pₘ`; for if not, and `v` is isolated, we
    -- can delete it, and if `v` is not isolated, we can contract some edge incident with it, in
    -- either case producing a smaller counterexample."
    have hP_span_delX : (G.deleteVerts X).verts ⊆ ⋃ i, (P i).verts := by
      intro v₀ ⟨hv₀G, hv₀_not_X⟩
      by_contra hv₀_not_P
      rw [mem_iUnion, not_exists] at hv₀_not_P
      by_cases hex_adj : ∃ u₀, G.Adj u₀ v₀
      · rcases hex_adj with ⟨u₀, hadj_G⟩
        have he_G : s(u₀, v₀) ∈ G.edgeSet := hadj_G
        have he_B : s(u₀, v₀) ∈ ⋃ j, (B j).edgeSet := by
          rcases hedge_cover he_G with he_P | he_B
          · rcases mem_iUnion.1 he_P with ⟨i, hi_adj⟩
            change (P i).toSubgraph.Adj u₀ v₀ at hi_adj
            exact (hv₀_not_P i hi_adj.snd_mem).elim
          · exact he_B
        rcases mem_iUnion.1 he_B with ⟨j₀, hadj_B⟩
        change (B j₀).Adj u₀ v₀ at hadj_B
        have hA₁₀_P : A₁₀ ⊆ ⋃ i, (P i).verts := by
          rintro _ ⟨i, rfl⟩; exact mem_iUnion.2 ⟨i, (P i).first_mem_verts⟩
        have hA₂₀_P : A₂₀ ⊆ ⋃ i, (P i).verts := by
          rintro _ ⟨i, rfl⟩; exact mem_iUnion.2 ⟨i, (P i).last_mem_verts⟩
        rcases contract_outside_vertex_edge hfin hG P hA₁₀_P hA₂₀_P hX hP_fam₀ B hB_le hB_disj
          hB_sep₀ hadj_B hv₀_not_X hv₀_not_P with
          ⟨G', B', hG'_fin, hG'_mem, hV_lt, hE_le, hX_G', hP_fam', hB'_le, _, hB'_comp, hB'_disj,
            hB'_sep⟩
        have hA₁₀_G' : A₁₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩; exact (hP_fam'.1 i).1.1 (P i).first_mem_verts
        have hA₂₀_G' : A₂₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩; exact (hP_fam'.1 i).1.1 (P i).last_mem_verts
        have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
        rcases ih _ hlt hG'_fin hG'_mem hA₁₀_G' hA₂₀_G' hX_G' hX_card P hP_fam' hP_avoids B' hB'_le
          (fun j ↦ (hB'_comp j).trans (hB_comp j)) hB'_disj hB'_sep rfl with h1 | h2
        · exact hm_ge h1
        · exact hn_ge h2
      · -- `v₀` is isolated in `G`; delete `v₀`.
        let G' := G.deleteVerts {v₀}
        let B' (j : Fin n) := (B j).deleteVerts {v₀}
        have hG'_le : G' ≤ G := G.deleteVerts_le
        have hG'_fin : G'.verts.Finite := hfin.subset hG'_le.1
        have hG'_mem : G' ∈ 𝓕 θ := mem_𝓕_of_le hG'_le hG
        have hV_lt : G'.verts.ncard < G.verts.ncard := by
          rw [Subgraph.deleteVerts_verts]
          exact Set.ncard_sdiff_singleton_lt_of_mem hv₀G hfin
        have hE_le : G'.edgeSet.ncard ≤ G.edgeSet.ncard :=
          Set.ncard_le_ncard (Subgraph.edgeSet_mono hG'_le) (finite_edgeSet_of_finite_verts hfin)
        have hP_fam' : IsDisjointPathFamily G' A₁₀ A₂₀ P := by
          refine ⟨fun i ↦ ⟨?_, (hP_fam₀.1 i).2.1, (hP_fam₀.1 i).2.2⟩, hP_fam₀.2⟩
          exact toSubgraph_le_deleteVerts_iff.2
            ⟨(hP_fam₀.1 i).1, Set.disjoint_singleton_right.2 (hv₀_not_P i)⟩
        have hA₁₀_G' : A₁₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩; exact (hP_fam'.1 i).1.1 (P i).first_mem_verts
        have hA₂₀_G' : A₂₀ ⊆ G'.verts := by
          rintro _ ⟨i, rfl⟩; exact (hP_fam'.1 i).1.1 (P i).last_mem_verts
        have hX_G' : X ⊆ G'.verts := by
          intro x hx
          exact ⟨hX hx, fun heq ↦ hv₀_not_X (mem_singleton_iff.1 heq ▸ hx)⟩
        have hB'_le : ∀ j, B' j ≤ G' := fun j ↦ Subgraph.deleteVerts_mono (hB_le j)
        have hB'_comp : ∀ j, numComponents (B' j) ≤ d := fun j ↦
          (numComponents_deleteVerts_singleton_le_of_isolated (hfin.subset (hB_le j).1) (hB_le j)
            hex_adj).trans (hB_comp j)
        have hB'_disj : Pairwise fun j₁ j₂ ↦ Disjoint (B' j₁).verts (B' j₂).verts :=
          fun j₁ j₂ hne ↦ (hB_disj hne).mono sdiff_subset sdiff_subset
        have hB'_sep : ∀ j, Separates G' (X ∪ (B' j).verts) A₁₀ A₂₀ := by
          intro j Q ⟨hQ_le, hQ_first, hQ_last⟩ hQ_avoids
          have hQ_not_v₀ : v₀ ∉ Q.verts :=
            (toSubgraph_le_deleteVerts_iff.1 hQ_le).2.notMem_of_mem_right (mem_singleton v₀)
          refine hB_sep₀ j Q ⟨hQ_le.trans hG'_le, hQ_first, hQ_last⟩ ?_
          rw [Path.Avoids, Set.disjoint_left] at hQ_avoids ⊢
          intro x hxQ hx_union
          apply hQ_avoids hxQ
          rcases hx_union with hxX | hxB
          · exact Or.inl hxX
          · exact Or.inr ⟨hxB, fun heq ↦ hQ_not_v₀ (mem_singleton_iff.1 heq ▸ hxQ)⟩
        have hlt : G'.verts.ncard + G'.edgeSet.ncard + m < N := by omega
        rcases ih _ hlt hG'_fin hG'_mem hA₁₀_G' hA₂₀_G' hX_G' hX_card P hP_fam' hP_avoids B' hB'_le
          hB'_comp hB'_disj hB'_sep rfl with h1 | h2
        · exact hm_ge h1
        · exact hn_ge h2
    -- "Let `J₁ ⊆ {1, …, n}` be defined by `j ∈ J₁` if and only if some component of `Bⱼ \ X` meets
    -- at least `½ θ²` of the paths `P₁, …, Pₘ`. By setting `A₁' = A₁ - X`, `A₂' = A₂ - X`, and
    -- applying (2.6) to `G \ X`, we deduce that `|J₁| < 2 m θ^{2θ - 2} 2^m`."
    let J₁ : Set (Fin n) :=
      {j : Fin n | ∃ c : ((B j).deleteVerts X).coe.ConnectedComponent,
        θ ^ 2 / 2 ≤ {i : Fin m |
          ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty}.ncard}
    have hJ₁_bound : J₁.ncard < 2 * m * θ ^ (2 * θ - 2) * 2 ^ m := by
      let eJ₁ := (Set.toFinite J₁).equivFin.symm
      let C₁ (k : Fin J₁.ncard) : (⊤ : SimpleGraph α).Subgraph :=
        let j := (eJ₁ k).1
        let c := Classical.choose (eJ₁ k).2
        compSubgraph ((B j).deleteVerts X) c
      have hC₁_le : ∀ k, C₁ k ≤ G.deleteVerts X := by
        intro k
        exact (compSubgraph_le _ _).trans (Subgraph.deleteVerts_mono (hB_le (eJ₁ k).1))
      have hC₁_conn : ∀ k, (C₁ k).Connected := fun k ↦ compSubgraph_connected _ _
      have hC₁_disj : Pairwise fun k₁ k₂ ↦ Disjoint (C₁ k₁).verts (C₁ k₂).verts := by
        intro k₁ k₂ hne
        have hj_ne : (eJ₁ k₁).1 ≠ (eJ₁ k₂).1 :=
          fun h ↦ hne (eJ₁.injective (Subtype.ext h))
        exact (hB_disj hj_ne).mono
          ((compSubgraph_le _ _).trans Subgraph.deleteVerts_le).1
          ((compSubgraph_le _ _).trans Subgraph.deleteVerts_le).1
      have hC₁_meet : ∀ k, θ ^ 2 / 2 ≤ {i : Fin m | ((P i).verts ∩ (C₁ k).verts).Nonempty}.ncard :=
        fun k ↦ Classical.choose_spec (eJ₁ k).2
      have hdel_fin : (G.deleteVerts X).verts.Finite := hfin.subset G.deleteVerts_le.1
      have hdel_mem : G.deleteVerts X ∈ 𝓕 θ := mem_𝓕_of_le G.deleteVerts_le hG
      have hlt_2_6 := theorem_2_6_simple hθ heven hm_ge_half hdel_fin hdel_mem P hP_unique_delX
        hP_span_delX C₁ hC₁_le hC₁_conn hC₁_disj hC₁_meet
      calc
        J₁.ncard < 2 * m * θ ^ (2 * θ - 2) * m.choose (θ ^ 2 / 2) := hlt_2_6
        _ ≤ 2 * m * θ ^ (2 * θ - 2) * 2 ^ m :=
          Nat.mul_le_mul_left _ (Nat.choose_le_two_pow m (θ ^ 2 / 2))
    -- "Now let `J₂ ⊆ {1, …, n}` be defined by `j ∈ J₂` if and only if `|X ∩ V(Bⱼ)| > 2 r`."
    let J₂ : Set (Fin n) := {j : Fin n | 2 * r < (X ∩ (B j).verts).ncard}
    have h2J₂_le_n : 2 * J₂.ncard ≤ n := by
      have hX_fin : X.Finite := hfin.subset hX
      have hsum_le : ∀ (S : Finset (Fin n)), (↑S : Set (Fin n)) ⊆ J₂ →
          (2 * r + 1) * S.card ≤ (⋃ j ∈ S, (X ∩ (B j).verts)).ncard := by
        intro S hS
        induction S using Finset.induction with
        | empty => simp
        | @insert j S hj_not_mem ih =>
          have hS_sub : (↑S : Set (Fin n)) ⊆ J₂ :=
            (Finset.coe_subset.2 (Finset.subset_insert j S)).trans hS
          have hj_J₂ : 2 * r + 1 ≤ (X ∩ (B j).verts).ncard := hS (Finset.mem_insert_self j S)
          have hdisj_union : Disjoint (X ∩ (B j).verts) (⋃ j' ∈ S, (X ∩ (B j').verts)) := by
            rw [Set.disjoint_iUnion₂_right]
            intro j' hj'S
            have hj_ne : j ≠ j' := fun heq ↦ hj_not_mem (heq ▸ hj'S)
            exact (hB_disj hj_ne).mono inter_subset_right inter_subset_right
          have hunion_eq : (⋃ j' ∈ insert j S, (X ∩ (B j').verts)) =
              (X ∩ (B j).verts) ∪ (⋃ j' ∈ S, (X ∩ (B j').verts)) := by
            ext x; simp
          rw [hunion_eq,
            Set.ncard_union_eq hdisj_union (hX_fin.subset inter_subset_left)
              (hX_fin.subset (iUnion₂_subset fun _ _ ↦ inter_subset_left)),
            Finset.card_insert_of_notMem hj_not_mem, mul_add, mul_one, add_comm ((2 * r + 1) * _)]
          exact Nat.add_le_add hj_J₂ (ih hS_sub)
      have hJ₂_card : J₂.toFinset.card = J₂.ncard := (Set.ncard_eq_toFinset_card' J₂).symm
      have hle_X : (2 * r + 1) * J₂.ncard ≤ X.ncard := by
        rw [← hJ₂_card]
        exact (hsum_le J₂.toFinset (by simp)).trans
          (Set.ncard_le_ncard (iUnion₂_subset fun _ _ ↦ inter_subset_left) hX_fin)
      have hle_rn : (2 * r + 1) * J₂.ncard ≤ r * n := hle_X.trans hX_card
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · simp only [mul_zero, zero_add, one_mul, zero_mul, nonpos_iff_eq_zero] at hle_rn
        omega
      · have : r * (2 * J₂.ncard) ≤ r * n := by
          calc r * (2 * J₂.ncard) = 2 * r * J₂.ncard := by ring
          _ ≤ (2 * r + 1) * J₂.ncard := Nat.mul_le_mul_right _ (by omega)
          _ ≤ r * n := hle_rn
        exact Nat.le_of_mul_le_mul_left this hr_pos
    -- Define `J₃ = {1, …, n} \ (J₁ ∪ J₂)`.
    let J₃ : Set (Fin n) := Set.univ \ (J₁ ∪ J₂)
    have hn_le_J₃ : n ≤ 2 * J₃.ncard + 2 * J₁.ncard := by
      have huniv : (Set.univ : Set (Fin n)) ⊆ (J₃ ∪ J₁) ∪ J₂ := by
        intro j _
        by_cases hj₁ : j ∈ J₁
        · exact Or.inl (Or.inr hj₁)
        · by_cases hj₂ : j ∈ J₂
          · exact Or.inr hj₂
          · exact Or.inl (Or.inl ⟨ trivial, fun h ↦ h.elim hj₁ hj₂ ⟩)
      have hcard_univ : n ≤ J₃.ncard + J₁.ncard + J₂.ncard := by
        calc
          n = (Set.univ : Set (Fin n)).ncard := by rw [Set.ncard_univ, Nat.card_fin]
          _ ≤ ((J₃ ∪ J₁) ∪ J₂).ncard := Set.ncard_le_ncard huniv (Set.toFinite _)
          _ ≤ (J₃ ∪ J₁).ncard + J₂.ncard := Set.ncard_union_le _ _
          _ ≤ J₃.ncard + J₁.ncard + J₂.ncard :=
            Nat.add_le_add_right (Set.ncard_union_le _ _) _
      omega
    -- Every path `P i` meets some component of `(B j).deleteVerts X`.
    have hP_meets_Bj_delX : ∀ j i, ∃ c : ((B j).deleteVerts X).coe.ConnectedComponent,
        ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty := by
      intro j i
      have hnot_avoids := hB_sep₀ j (P i) (hP_fam₀.1 i)
      rw [Path.Avoids, Set.not_disjoint_iff] at hnot_avoids
      rcases hnot_avoids with ⟨w, hwP, hw_union⟩
      have hw_not_X : w ∉ X := (hP_avoids i).notMem_of_mem_left hwP
      rcases hw_union with hwX | hwB
      · exact (hw_not_X hwX).elim
      · let u : ((B j).deleteVerts X).verts := ⟨w, hwB, hw_not_X⟩
        refine ⟨((B j).deleteVerts X).coe.connectedComponentMk u, w, hwP, ?_⟩
        exact mem_compSubgraph_verts _ u
    -- Helper: bound on the number of paths meeting a finite set of components of `(B j).deleteVerts X`
    -- for `j ∉ J₁`.
    have h_paths_of_comp_set_le : ∀ {j : Fin n}, j ∉ J₁ →
        ∀ (S : Set ((B j).deleteVerts X).coe.ConnectedComponent),
          {i : Fin m | ∃ c ∈ S,
            ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty}.ncard ≤
            S.ncard * (θ ^ 2 / 2 - 1) := by
      intro j hj₁ S
      have hH_fin : ((B j).deleteVerts X).verts.Finite :=
        hfin.subset (Subgraph.deleteVerts_le.trans (hB_le j)).1
      have : Finite ((B j).deleteVerts X).verts := hH_fin.to_subtype
      let : Fintype ((B j).deleteVerts X).verts := Fintype.ofFinite _
      have : Finite ((B j).deleteVerts X).coe.ConnectedComponent := Quot.finite _
      let : Fintype ((B j).deleteVerts X).coe.ConnectedComponent := Fintype.ofFinite _
      have h_finset : ∀ (T : Finset ((B j).deleteVerts X).coe.ConnectedComponent),
          {i : Fin m | ∃ c ∈ (↑T : Set _),
            ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty}.ncard ≤
            T.card * (θ ^ 2 / 2 - 1) := by
        intro T
        induction T using Finset.induction with
        | empty =>
          have hempty : {i : Fin m | ∃ c ∈ ((∅ : Finset ((B j).deleteVerts X).coe.ConnectedComponent) : Set _),
              ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty} = ∅ := by
            ext i; simp
          rw [hempty, Set.ncard_empty, Finset.card_empty, zero_mul]
        | @insert c T hc_not_mem ih =>
          have hunion : {i : Fin m | ∃ d ∈ (↑(insert c T) : Set _),
              ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) d).verts).Nonempty} =
              {i : Fin m |
                ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty} ∪
              {i : Fin m | ∃ d ∈ (↑T : Set _),
                ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) d).verts).Nonempty} := by
            ext i
            simp only [Finset.coe_insert, mem_insert_iff, mem_ofPred_eq, mem_union]
            constructor
            · rintro ⟨d, rfl | hd, h⟩
              · exact Or.inl h
              · exact Or.inr ⟨d, hd, h⟩
            · rintro (h | ⟨d, hd, h⟩)
              · exact ⟨c, Or.inl rfl, h⟩
              · exact ⟨d, Or.inr hd, h⟩
          have hc_le : {i : Fin m |
              ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty}.ncard ≤
              θ ^ 2 / 2 - 1 := by
            have hnot_ge : ¬ θ ^ 2 / 2 ≤ {i : Fin m |
                ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty}.ncard :=
              fun hge ↦ hj₁ ⟨c, hge⟩
            omega
          calc
            {i : Fin m | ∃ d ∈ (↑(insert c T) : Set _),
                ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) d).verts).Nonempty}.ncard
              ≤ {i : Fin m |
                  ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty}.ncard +
                {i : Fin m | ∃ d ∈ (↑T : Set _),
                  ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) d).verts).Nonempty}.ncard := by
                rw [hunion]; exact Set.ncard_union_le _ _
            _ ≤ (θ ^ 2 / 2 - 1) + T.card * (θ ^ 2 / 2 - 1) := Nat.add_le_add hc_le ih
            _ = (insert c T).card * (θ ^ 2 / 2 - 1) := by
              rw [Finset.card_insert_of_notMem hc_not_mem, add_mul, one_mul, add_comm]
      have hcard_eq : S.toFinset.card = S.ncard := (Set.ncard_eq_toFinset_card' S).symm
      simpa [hcard_eq] using h_finset S.toFinset
    -- Show `J₃.ncard < 2 ^ m * (θ ^ 2 / 2)`.
    have hs_def : s = d + r * (θ ^ 2 - 1) := rfl
    have hJ₃_lt : J₃.ncard < 2 ^ m * (θ ^ 2 / 2) := by
      rcases Nat.eq_zero_or_pos r with rfl | hr_pos
      · -- Case `r = 0`: then `X = ∅` and `1 ≤ d`, so no `j` can belong to `J₃`.
        have hd_pos : 1 ≤ d := by omega
        have hX_empty : X = ∅ :=
          (Set.ncard_eq_zero (hs := hfin.subset hX)).1 (by omega)
        have hJ₃_empty : J₃ = ∅ := by
          ext j
          simp only [mem_empty_iff_false, iff_false]
          rintro ⟨_, hj₁₂⟩
          have hj₁ : j ∉ J₁ := fun h ↦ hj₁₂ (Or.inl h)
          let C_no := {c : ((B j).deleteVerts X).coe.ConnectedComponent |
            ∀ y ∈ X ∩ (B j).verts,
              ∀ u ∈ (compSubgraph ((B j).deleteVerts X) c).verts, ¬ G.Adj y u}
          have hC_no_univ : C_no = Set.univ := by
            ext c; simp [C_no, hX_empty]
          have hC_no_card : C_no.ncard ≤ d :=
            (ncard_components_avoiding_neighbors_le (hfin.subset (hB_le j).1) (hB_le j) X).trans
              (hB_comp j)
          have hpaths_univ : {i : Fin m | ∃ c ∈ C_no,
              ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty} =
              Set.univ := by
            ext i
            simp only [hC_no_univ, mem_univ, true_and, mem_ofPred_eq, iff_true]
            exact hP_meets_Bj_delX j i
          have hm_le : m ≤ d * (θ ^ 2 / 2 - 1) := by
            calc
              m = (Set.univ : Set (Fin m)).ncard := by rw [Set.ncard_univ, Nat.card_fin]
              _ = {i : Fin m | ∃ c ∈ C_no,
                    ((P i).verts ∩ (compSubgraph ((B j).deleteVerts X) c).verts).Nonempty}.ncard := by
                rw [hpaths_univ]
              _ ≤ C_no.ncard * (θ ^ 2 / 2 - 1) := h_paths_of_comp_set_le hj₁ C_no
              _ ≤ d * (θ ^ 2 / 2 - 1) := Nat.mul_le_mul_right _ hC_no_card
          have hm_val : m = d * (θ ^ 2 / 2) := by
            rw [← hm_eq, hs_div, hs_def, zero_mul, add_zero]
          have hhalf_pos : 1 ≤ θ ^ 2 / 2 := by omega
          have hlt_m : d * (θ ^ 2 / 2 - 1) < d * (θ ^ 2 / 2) :=
            Nat.mul_lt_mul_of_pos_left (by omega) hd_pos
          omega
        rw [hJ₃_empty, Set.ncard_empty]
        have : 0 < 2 ^ m := Nat.two_pow_pos m
        have : 0 < θ ^ 2 / 2 := by omega
        exact Nat.mul_pos (Nat.two_pow_pos m) (by omega)
      · -- Case `1 ≤ r` (page 49):
        let K := (θ ^ 2 / 2) * (θ ^ 2 - 1) / 2
        have hK_gt : (θ ^ 2 / 2 - 1) * (θ ^ 2 / 2 - 1) < K := by
          rcases heven with ⟨k, hk⟩
          have hk_ge : 3 ≤ k := by omega
          have hhalf : θ ^ 2 / 2 = 2 * (k * k) := by
            have hsq : θ ^ 2 = 2 * (2 * (k * k)) := by rw [hk]; ring
            rw [hsq, Nat.mul_div_cancel_left _ (by omega)]
          have hK_eq : K = k * k * (4 * (k * k) - 1) := by
            dsimp [K]
            have hθ2 : θ ^ 2 = 4 * (k * k) := by rw [hk]; ring
            have hmul : (2 * (k * k)) * (4 * (k * k) - 1) = 2 * (k * k * (4 * (k * k) - 1)) := by
              ring
            rw [hhalf, hθ2, hmul, Nat.mul_div_cancel_left _ (by omega)]
          rw [hhalf, hK_eq]
          have hk2_ge : 9 ≤ k * k := by
            calc 9 = 3 * 3 := rfl
            _ ≤ k * k := Nat.mul_le_mul hk_ge hk_ge
          obtain ⟨a, ha⟩ : ∃ a, k * k = a + 9 := ⟨k * k - 9, by omega⟩
          have h1 : 2 * (k * k) - 1 = 2 * a + 17 := by omega
          have h2 : 4 * (k * k) - 1 = 4 * a + 35 := by omega
          rw [h1, h2, ha]
          nlinarith
        -- For every `j : J₃`, construct `v_j ∈ X ∩ (B j).verts`, `I_j ⊆ Fin m` of size `θ ^ 2 / 2`,
        -- and components `D_j i` of `(B j).deleteVerts X`.
        have hex_vj_Ij : ∀ j : J₃,
            ∃ (v_j : α) (I_j : Set (Fin m))
              (D_j : Fin m → ((B j.1).deleteVerts X).coe.ConnectedComponent),
              v_j ∈ X ∩ (B j.1).verts ∧
              I_j.ncard = θ ^ 2 / 2 ∧
              (∀ i ∈ I_j, ∃ u ∈ (compSubgraph ((B j.1).deleteVerts X) (D_j i)).verts,
                G.Adj v_j u) ∧
              (∀ i ∈ I_j,
                ((P i).verts ∩ (compSubgraph ((B j.1).deleteVerts X) (D_j i)).verts).Nonempty) ∧
              (∀ i ∈ I_j, ∀ i' ∈ I_j, i' ≠ i →
                Disjoint (P i').verts (compSubgraph ((B j.1).deleteVerts X) (D_j i)).verts) := by
          rintro ⟨j, _, hj₁₂⟩
          have hj₁ : j ∉ J₁ := fun h ↦ hj₁₂ (Or.inl h)
          have hj₂ : (X ∩ (B j).verts).ncard ≤ 2 * r := not_lt.1 (fun h ↦ hj₁₂ (Or.inr h))
          let H_j := (B j).deleteVerts X
          let Y_j := X ∩ (B j).verts
          let C_no := {c : H_j.coe.ConnectedComponent |
            ∀ y ∈ Y_j, ∀ u ∈ (compSubgraph H_j c).verts, ¬ G.Adj y u}
          let C_yes := {c : H_j.coe.ConnectedComponent |
            ∃ y ∈ Y_j, ∃ u ∈ (compSubgraph H_j c).verts, G.Adj y u}
          have hC_no_card : C_no.ncard ≤ d :=
            (ncard_components_avoiding_neighbors_le (hfin.subset (hB_le j).1) (hB_le j) X).trans
              (hB_comp j)
          have hno_paths_le :
              {i : Fin m | ∃ c ∈ C_no, ((P i).verts ∩ (compSubgraph H_j c).verts).Nonempty}.ncard ≤
                d * (θ ^ 2 / 2 - 1) :=
            (h_paths_of_comp_set_le hj₁ C_no).trans (Nat.mul_le_mul_right _ hC_no_card)
          let M_j := {i : Fin m | ∃ c ∈ C_yes, ((P i).verts ∩ (compSubgraph H_j c).verts).Nonempty}
          have huniv_sub : (Set.univ : Set (Fin m)) ⊆
              {i : Fin m | ∃ c ∈ C_no, ((P i).verts ∩ (compSubgraph H_j c).verts).Nonempty} ∪ M_j := by
            intro i _
            rcases hP_meets_Bj_delX j i with ⟨c, hmeet⟩
            by_cases hc : ∃ y ∈ Y_j, ∃ u ∈ (compSubgraph H_j c).verts, G.Adj y u
            · exact Or.inr ⟨c, hc, hmeet⟩
            · push Not at hc
              exact Or.inl ⟨c, hc, hmeet⟩
          have hm_le_sum : m ≤ d * (θ ^ 2 / 2 - 1) + M_j.ncard := by
            calc
              m = (Set.univ : Set (Fin m)).ncard := by rw [Set.ncard_univ, Nat.card_fin]
              _ ≤ ({i : Fin m | ∃ c ∈ C_no,
                    ((P i).verts ∩ (compSubgraph H_j c).verts).Nonempty} ∪ M_j).ncard :=
                Set.ncard_le_ncard huniv_sub (Set.toFinite _)
              _ ≤ {i : Fin m | ∃ c ∈ C_no,
                    ((P i).verts ∩ (compSubgraph H_j c).verts).Nonempty}.ncard + M_j.ncard :=
                Set.ncard_union_le _ _
              _ ≤ d * (θ ^ 2 / 2 - 1) + M_j.ncard := Nat.add_le_add_right hno_paths_le _
          have hM_j_ge : 2 * r * K ≤ M_j.ncard := by
            rcases heven with ⟨k, hk⟩
            have hhalf : θ ^ 2 / 2 = 2 * k * k := by
              have hsq : θ ^ 2 = 2 * (2 * k * k) := by rw [hk]; ring
              rw [hsq, Nat.mul_div_cancel_left _ (by omega)]
            have h2K : 2 * K = (θ ^ 2 / 2) * (θ ^ 2 - 1) := by
              dsimp [K]
              have hmul : (2 * k * k) * (θ ^ 2 - 1) = 2 * (k * k * (θ ^ 2 - 1)) := by ring
              rw [hhalf, hmul, Nat.mul_div_cancel_left _ (by omega)]
            have h2rK : 2 * r * K = r * (θ ^ 2 - 1) * (θ ^ 2 / 2) := by
              calc 2 * r * K = r * (2 * K) := by ring
              _ = r * ((θ ^ 2 / 2) * (θ ^ 2 - 1)) := by rw [h2K]
              _ = r * (θ ^ 2 - 1) * (θ ^ 2 / 2) := by ring
            have hm_val : m = d * (θ ^ 2 / 2) + r * (θ ^ 2 - 1) * (θ ^ 2 / 2) := by
              rw [← hm_eq, hs_div, add_mul]
            have hd_le : d * (θ ^ 2 / 2 - 1) ≤ d * (θ ^ 2 / 2) :=
              Nat.mul_le_mul_left d (by omega)
            omega
          -- By pigeonhole over `y ∈ Y_j`, find `v_j ∈ Y_j` with `K ≤ (Paths(j, v_j)).ncard`.
          let CompY (y : α) : Set H_j.coe.ConnectedComponent :=
            {c : H_j.coe.ConnectedComponent | ∃ u ∈ (compSubgraph H_j c).verts, G.Adj y u}
          let PathsY (y : α) : Set (Fin m) :=
            {i : Fin m | ∃ c ∈ CompY y, ((P i).verts ∩ (compSubgraph H_j c).verts).Nonempty}
          have hY_j_fin : Y_j.Finite := (hfin.subset hX).subset inter_subset_left
          have hex_vj : ∃ v_j ∈ Y_j, K ≤ (PathsY v_j).ncard := by
            by_contra hnot_vj
            push Not at hnot_vj
            have hM_sub : M_j ⊆ ⋃ y ∈ hY_j_fin.toFinset, PathsY y := by
              intro i ⟨c, ⟨y, hy, u, hu, hadj_yu⟩, hmeet⟩
              exact mem_biUnion (hY_j_fin.mem_toFinset.2 hy) ⟨c, ⟨u, hu, hadj_yu⟩, hmeet⟩
            have hsum_Y : ∀ (T : Finset α), (∀ y ∈ T, y ∈ Y_j) →
                (⋃ y ∈ T, PathsY y).ncard ≤ T.card * (K - 1) := by
              intro T hT
              induction T using Finset.induction with
              | empty => simp
              | @insert y T hy_not_mem ih =>
                have hT_sub : ∀ y' ∈ T, y' ∈ Y_j :=
                  fun y' hy' ↦ hT y' (Finset.mem_insert_of_mem hy')
                have hy_Y : y ∈ Y_j := hT y (Finset.mem_insert_self y T)
                have hy_le : (PathsY y).ncard ≤ K - 1 := by
                  have := hnot_vj y hy_Y
                  omega
                have hunion : (⋃ y' ∈ insert y T, PathsY y') =
                    PathsY y ∪ ⋃ y' ∈ T, PathsY y' := by
                  ext i; simp
                calc
                  (⋃ y' ∈ insert y T, PathsY y').ncard
                    ≤ (PathsY y).ncard + (⋃ y' ∈ T, PathsY y').ncard := by
                      rw [hunion]; exact Set.ncard_union_le _ _
                  _ ≤ (K - 1) + T.card * (K - 1) := Nat.add_le_add hy_le (ih hT_sub)
                  _ = (insert y T).card * (K - 1) := by
                    rw [Finset.card_insert_of_notMem hy_not_mem, add_mul, one_mul, add_comm]
            have hcard_Yj : hY_j_fin.toFinset.card = Y_j.ncard :=
              (Set.ncard_eq_toFinset_card Y_j hY_j_fin).symm
            have hM_le : M_j.ncard ≤ 2 * r * (K - 1) := by
              calc
                M_j.ncard ≤ (⋃ y ∈ hY_j_fin.toFinset, PathsY y).ncard :=
                  Set.ncard_le_ncard hM_sub (Set.toFinite _)
                _ ≤ hY_j_fin.toFinset.card * (K - 1) :=
                  hsum_Y hY_j_fin.toFinset (fun y hy ↦ hY_j_fin.mem_toFinset.1 hy)
                _ = Y_j.ncard * (K - 1) := by rw [hcard_Yj]
                _ ≤ (2 * r) * (K - 1) := Nat.mul_le_mul_right _ hj₂
            have hK_pos : 1 ≤ K := by omega
            have hlt_2rK : 2 * r * (K - 1) < 2 * r * K :=
              Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
            omega
          rcases hex_vj with ⟨v_j, hv_j_Y, hv_j_K⟩
          have h_each_c : ∀ c ∈ CompY v_j,
              {i : Fin m | ((P i).verts ∩ (compSubgraph H_j c).verts).Nonempty}.ncard <
                θ ^ 2 / 2 := by
            intro c _
            by_contra hge
            exact hj₁ ⟨c, not_lt.1 hge⟩
          rcases exists_private_paths_of_minimal_components
            (hfin.subset (Subgraph.deleteVerts_le.trans (hB_le j)).1) P (CompY v_j)
            (by omega) hK_gt h_each_c hv_j_K with
            ⟨I_j, D_j, hI_j_card, hD_j_comp, hD_j_meet, hD_j_disj⟩
          refine ⟨v_j, I_j, D_j, hv_j_Y, hI_j_card, hD_j_comp, hD_j_meet, hD_j_disj⟩
        choose v_fn I_fn D_fn hv_fn hI_card hD_adj hD_meet hD_disj using hex_vj_Ij
        -- By pigeonhole on `I_fn : J₃ → Set (Fin m)`, if `2 ^ m * (θ ^ 2 / 2) ≤ J₃.ncard`,
        -- some fiber `J₄` has size `≥ θ ^ 2 / 2`.
        by_contra hJ₃_ge
        have hJ₃_ge' : 2 ^ m * (θ ^ 2 / 2) ≤ J₃.ncard := not_lt.1 hJ₃_ge
        have hJ₃_univ_card : (Set.univ : Set J₃).ncard = J₃.ncard := by
          rw [← Set.ncard_image_of_injective Set.univ Subtype.val_injective]
          have himg : Subtype.val '' (Set.univ : Set J₃) = J₃ := by ext x; simp
          rw [himg]
        have hex_I₀ : ∃ I₀ : Set (Fin m),
            θ ^ 2 / 2 ≤ {j : J₃ | I_fn j = I₀}.ncard := by
          by_contra hnot_I₀
          push Not at hnot_I₀
          have hJ₃_sub : (Set.univ : Set J₃) ⊆ ⋃ I₀ ∈ (Finset.univ : Finset (Set (Fin m))),
              {j : J₃ | I_fn j = I₀} := by
            intro j _
            exact mem_biUnion (Finset.mem_univ (I_fn j)) rfl
          have hsum_I₀ : ∀ (T : Finset (Set (Fin m))),
              (⋃ I₀ ∈ T, {j : J₃ | I_fn j = I₀}).ncard ≤ T.card * (θ ^ 2 / 2 - 1) := by
            intro T
            induction T using Finset.induction with
            | empty => simp
            | @insert I₀ T hI₀_not_mem ih =>
              have hI₀_le : {j : J₃ | I_fn j = I₀}.ncard ≤ θ ^ 2 / 2 - 1 := by
                have := hnot_I₀ I₀
                omega
              have hunion : (⋃ I' ∈ insert I₀ T, {j : J₃ | I_fn j = I'}) =
                  {j : J₃ | I_fn j = I₀} ∪ ⋃ I' ∈ T, {j : J₃ | I_fn j = I'} := by
                ext j; simp
              calc
                (⋃ I' ∈ insert I₀ T, {j : J₃ | I_fn j = I'}).ncard
                  ≤ {j : J₃ | I_fn j = I₀}.ncard +
                      (⋃ I' ∈ T, {j : J₃ | I_fn j = I'}).ncard := by
                    rw [hunion]; exact Set.ncard_union_le _ _
                _ ≤ (θ ^ 2 / 2 - 1) + T.card * (θ ^ 2 / 2 - 1) := Nat.add_le_add hI₀_le ih
                _ = (insert I₀ T).card * (θ ^ 2 / 2 - 1) := by
                  rw [Finset.card_insert_of_notMem hI₀_not_mem, add_mul, one_mul, add_comm]
          have hcard_pow : (Finset.univ : Finset (Set (Fin m))).card = 2 ^ m := by
            rw [Finset.card_univ, Fintype.card_set, Fintype.card_fin]
          have hJ₃_le : J₃.ncard ≤ 2 ^ m * (θ ^ 2 / 2 - 1) := by
            rw [← hJ₃_univ_card]
            calc
              (Set.univ : Set J₃).ncard ≤ (⋃ I₀ ∈ (Finset.univ : Finset (Set (Fin m))),
                  {j : J₃ | I_fn j = I₀}).ncard :=
                Set.ncard_le_ncard hJ₃_sub (Set.toFinite _)
              _ ≤ (Finset.univ : Finset (Set (Fin m))).card * (θ ^ 2 / 2 - 1) := hsum_I₀ _
              _ = 2 ^ m * (θ ^ 2 / 2 - 1) := by rw [hcard_pow]
          have hlt_pow : 2 ^ m * (θ ^ 2 / 2 - 1) < 2 ^ m * (θ ^ 2 / 2) :=
            Nat.mul_lt_mul_of_pos_left (by omega) (Nat.two_pow_pos m)
          omega
        rcases hex_I₀ with ⟨I₀, hJ₄_card⟩
        let J₄ : Set J₃ := {j : J₃ | I_fn j = I₀}
        rcases Set.exists_subset_card_eq (s := J₄) hJ₄_card with ⟨J₄', hJ₄'_sub, hJ₄'_card⟩
        have hJ₄'_nonempty : J₄'.Nonempty :=
          Set.nonempty_of_ncard_ne_zero (by omega)
        rcases hJ₄'_nonempty with ⟨j₀, hj₀_J₄'⟩
        have hI₀_card : I₀.ncard = θ ^ 2 / 2 := by
          have hj₀_eq : I_fn j₀ = I₀ := hJ₄'_sub hj₀_J₄'
          rw [← hj₀_eq]
          exact hI_card j₀
        let eI : Fin (θ ^ 2 / 2) ≃ I₀ :=
          ((Set.toFinite I₀).equivFin.trans (finCongr hI₀_card)).symm
        let eJ : Fin (θ ^ 2 / 2) ≃ J₄' :=
          ((Set.toFinite J₄').equivFin.trans (finCongr hJ₄'_card)).symm
        -- Construct the connected subgraphs `Q₁, …, Q_{θ²/2}` and vertices `v'₁, …, v'_{θ²/2}`.
        let D_sub (b a : Fin (θ ^ 2 / 2)) : (⊤ : SimpleGraph α).Subgraph :=
          let j : J₃ := (eJ b).1
          compSubgraph ((B j.1).deleteVerts X) (D_fn j (eI a).1)
        let Q (a : Fin (θ ^ 2 / 2)) : (⊤ : SimpleGraph α).Subgraph :=
          (P (eI a).1).toSubgraph ⊔ ⨆ b ∈ (Set.univ : Set (Fin (θ ^ 2 / 2))), D_sub b a
        let v' (b : Fin (θ ^ 2 / 2)) : α := v_fn (eJ b).1
        have hD_sub_le_G : ∀ b a, D_sub b a ≤ G := fun b a ↦
          ((compSubgraph_le _ _).trans Subgraph.deleteVerts_le).trans (hB_le (eJ b).1.1)
        have hQ_le : ∀ a, Q a ≤ G := by
          intro a
          exact sup_le (hP_fam₀.1 (eI a).1).1 (iSup₂_le fun b _ ↦ hD_sub_le_G b a)
        have hQ_conn : ∀ a, (Q a).Connected := by
          intro a
          refine connected_path_sup_biUnion (P (eI a).1) Set.univ (fun b ↦ D_sub b a)
            (fun b _ ↦ compSubgraph_connected _ _) (fun b _ ↦ ?_)
          have hIj_eq : I_fn (eJ b).1 = I₀ := hJ₄'_sub (eJ b).2
          have hi_Ij : (eI a).1 ∈ I_fn (eJ b).1 := hIj_eq.symm ▸ (eI a).2
          exact hD_meet (eJ b).1 (eI a).1 hi_Ij
        have hQ_disj_X : ∀ a, Disjoint (Q a).verts X := by
          intro a
          simp only [Q, Subgraph.verts_sup, Subgraph.verts_iSup, Set.disjoint_union_left,
            Set.disjoint_iUnion_left]
          refine ⟨hP_avoids (eI a).1, fun b _ ↦ ?_⟩
          exact (toSubgraph_le_deleteVerts_iff.1 (compSubgraph_le _ _)).2
        have hQ_disj : Pairwise fun a₁ a₂ ↦ Disjoint (Q a₁).verts (Q a₂).verts := by
          intro a₁ a₂ hne
          have hi_ne : (eI a₁).1 ≠ (eI a₂).1 :=
            fun h ↦ hne (eI.injective (Subtype.ext h))
          simp only [Q, Subgraph.verts_sup, Subgraph.verts_iSup]
          rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
          refine ⟨⟨hP_fam₀.2 hi_ne, ?_⟩, ⟨?_, ?_⟩⟩
          · rw [Set.disjoint_iUnion₂_right]
            intro b₂ _
            have hIj₂_eq : I_fn (eJ b₂).1 = I₀ := hJ₄'_sub (eJ b₂).2
            have hi₁ : (eI a₁).1 ∈ I_fn (eJ b₂).1 := hIj₂_eq.symm ▸ (eI a₁).2
            have hi₂ : (eI a₂).1 ∈ I_fn (eJ b₂).1 := hIj₂_eq.symm ▸ (eI a₂).2
            exact hD_disj (eJ b₂).1 (eI a₂).1 hi₂ (eI a₁).1 hi₁ hi_ne
          · rw [Set.disjoint_iUnion₂_left]
            intro b₁ _
            have hIj₁_eq : I_fn (eJ b₁).1 = I₀ := hJ₄'_sub (eJ b₁).2
            have hi₁ : (eI a₁).1 ∈ I_fn (eJ b₁).1 := hIj₁_eq.symm ▸ (eI a₁).2
            have hi₂ : (eI a₂).1 ∈ I_fn (eJ b₁).1 := hIj₁_eq.symm ▸ (eI a₂).2
            exact (hD_disj (eJ b₁).1 (eI a₁).1 hi₁ (eI a₂).1 hi₂ hi_ne.symm).symm
          · rw [Set.disjoint_iUnion₂_left]
            intro b₁ _
            rw [Set.disjoint_iUnion₂_right]
            intro b₂ _
            by_cases hb : b₁ = b₂
            · subst hb
              have hIj₁_eq : I_fn (eJ b₁).1 = I₀ := hJ₄'_sub (eJ b₁).2
              have hi₁ : (eI a₁).1 ∈ I_fn (eJ b₁).1 := hIj₁_eq.symm ▸ (eI a₁).2
              have hi₂ : (eI a₂).1 ∈ I_fn (eJ b₁).1 := hIj₁_eq.symm ▸ (eI a₂).2
              have hcomp_ne : D_fn (eJ b₁).1 (eI a₁).1 ≠ D_fn (eJ b₁).1 (eI a₂).1 := by
                intro heq_c
                rcases hD_meet (eJ b₁).1 (eI a₁).1 hi₁ with ⟨x, hxP, hxC⟩
                have hdisj₁ := hD_disj (eJ b₁).1 (eI a₂).1 hi₂ (eI a₁).1 hi₁ hi_ne
                rw [← heq_c] at hdisj₁
                exact hdisj₁.notMem_of_mem_left hxP hxC
              exact compSubgraph_disjoint _ hcomp_ne
            · have hj_ne : (eJ b₁).1.1 ≠ (eJ b₂).1.1 :=
                fun h ↦ hb (eJ.injective (Subtype.ext (Subtype.ext h)))
              exact (hB_disj hj_ne).mono
                ((compSubgraph_le _ _).trans Subgraph.deleteVerts_le).1
                ((compSubgraph_le _ _).trans Subgraph.deleteVerts_le).1
        have hv'_inj : Function.Injective v' := by
          intro b₁ b₂ heq
          by_contra hne
          have hj_ne : (eJ b₁).1.1 ≠ (eJ b₂).1.1 :=
            fun h ↦ hne (eJ.injective (Subtype.ext (Subtype.ext h)))
          have hv₁_B : v' b₁ ∈ (B (eJ b₁).1.1).verts :=
            (hv_fn (eJ b₁).1).2
          have hv₂_B : v' b₁ ∈ (B (eJ b₂).1.1).verts := by
            rw [heq]
            exact (hv_fn (eJ b₂).1).2
          exact (hB_disj hj_ne).notMem_of_mem_left hv₁_B hv₂_B
        have hv'_X : ∀ b, v' b ∈ X :=
          fun b ↦ (hv_fn (eJ b).1).1
        have hv'_G : ∀ b, v' b ∈ G.verts := fun b ↦ hX (hv'_X b)
        have hadj_Q : ∀ a b, ∃ u ∈ (Q a).verts, G.Adj (v' b) u := by
          intro a b
          have hIj_eq : I_fn (eJ b).1 = I₀ := hJ₄'_sub (eJ b).2
          have hi : (eI a).1 ∈ I_fn (eJ b).1 := hIj_eq.symm ▸ (eI a).2
          rcases hD_adj (eJ b).1 (eI a).1 hi with ⟨u, hu_D, hadj_u⟩
          have hu_Q : u ∈ (Q a).verts := by
            have hle_Q : D_sub b a ≤ Q a :=
              (le_biSup (fun b' ↦ D_sub b' a) (mem_univ b)).trans le_sup_right
            exact hle_Q.1 hu_D
          exact ⟨u, hu_Q, hadj_u⟩
        have hiso := isIsoMinor_gridGraph_of_bipartite_subgraphs heven hfin Q hQ_le hQ_conn hQ_disj
          hQ_disj_X v' hv'_inj hv'_X hv'_G hadj_Q
        exact hG hiso
    -- Final arithmetic:
    -- `n ≤ 2 * J₃.ncard + 2 * J₁.ncard < 2 ^ m * (θ ^ 2 + 4 * m * θ ^ (2 * θ - 2))`
    -- `  = 2 ^ (s * θ ^ 2 / 2) * (θ ^ 2 + 2 * s * θ ^ (2 * θ))`.
    have h2_half : 2 * (θ ^ 2 / 2) = θ ^ 2 := by
      rcases heven with ⟨k, hk⟩
      have hsq : θ ^ 2 = 2 * (2 * k * k) := by rw [hk]; ring
      rw [hsq, Nat.mul_div_cancel_left _ (by omega)]
    have h4m : 4 * m * θ ^ (2 * θ - 2) = 2 * s * θ ^ (2 * θ) := by
      have h2m : 2 * m = s * θ ^ 2 := by
        rw [← hm_eq, hs_div, ← mul_assoc, mul_comm 2 s, mul_assoc, h2_half]
      calc
        4 * m * θ ^ (2 * θ - 2) = 2 * (2 * m) * θ ^ (2 * θ - 2) := by ring
        _ = 2 * (s * θ ^ 2) * θ ^ (2 * θ - 2) := by rw [h2m]
        _ = 2 * s * (θ ^ 2 * θ ^ (2 * θ - 2)) := by ring
        _ = 2 * s * θ ^ (2 + (2 * θ - 2)) := by rw [← pow_add]
        _ = 2 * s * θ ^ (2 * θ) := by
          congr 2
          omega
    have hn_lt : n < 2 ^ (s * θ ^ 2 / 2) * (θ ^ 2 + 2 * s * θ ^ (2 * θ)) := by
      have h1 : 2 * J₃.ncard < 2 ^ m * θ ^ 2 := by
        calc
          2 * J₃.ncard < 2 * (2 ^ m * (θ ^ 2 / 2)) :=
            Nat.mul_lt_mul_of_pos_left hJ₃_lt (by omega)
          _ = 2 ^ m * (2 * (θ ^ 2 / 2)) := by ring
          _ = 2 ^ m * θ ^ 2 := by rw [h2_half]
      have h2 : 2 * J₁.ncard < 2 ^ m * (2 * s * θ ^ (2 * θ)) := by
        calc
          2 * J₁.ncard < 2 * (2 * m * θ ^ (2 * θ - 2) * 2 ^ m) :=
            Nat.mul_lt_mul_of_pos_left hJ₁_bound (by omega)
          _ = 2 ^ m * (4 * m * θ ^ (2 * θ - 2)) := by ring
          _ = 2 ^ m * (2 * s * θ ^ (2 * θ)) := by rw [h4m]
      rw [hm_eq, mul_add]
      omega
    exact hn_ge hn_lt

end GraphMinor.GM01
end
