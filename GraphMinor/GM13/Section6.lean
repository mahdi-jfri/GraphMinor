module

public import GraphMinor.GM13.Section6a

/-!
# Graph Minors XIII, Section 6: Clique Minors and Edge Sparsification ((6.3)–(6.5))

This file completes the formalization of Section 6 of N. Robertson and P. D. Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 85–87):

- `algorithm_6_3_correct` and `theorem_6_3` ((6.3), pages 85–86)
- `algorithm_6_4_correct` and `theorem_6_4` ((6.4), pages 86–87)
- `algorithm_6_5_correct` and `theorem_6_5` ((6.5), page 87)
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v}

namespace Digraph

/-- For a digraph `G` and `X ⊆ V(G)`, `N(X)` is the set of vertices in `V(G) \ X` with a neighbour
in `X` in the underlying undirected graph `G.toGraph` (Graph Minors XIII, Section 6, page 85:
"If $G$ is a graph and $X \subseteq V(G)$, we denote by $N(X)$ the set of vertices in $V(G) - X$
with a neighbour in $X$."). -/
def extNeighbors (G : Digraph α β) (X : Set α) : Set α :=
  {v ∈ G.vertexSet \ X | ∃ x ∈ X, G.toGraph.Adj v x}

/-- The set of edges of `G` with at least one end in `X` (Graph Minors XIII, Section 6, page 85:
"$X_i$ meets at most $|N(X_i)| + k(i - 1)$ edges"). -/
def edgesMeeting (G : Digraph α β) (X : Set α) : Set β :=
  {e ∈ G.edgeSet | G.head e ∈ X ∨ G.tail e ∈ X}

lemma induce_insert_isConnected {G : Digraph α β} {X : Set α} {v : α}
    (hX : X ⊆ G.vertexSet) (hconn : (G.induce X).IsConnected)
    (hv : v ∈ G.extNeighbors X) :
    (G.induce (insert v X)).IsConnected := by
  have hvG : v ∈ G.vertexSet := hv.1.1
  rcases hv.2 with ⟨x₀, hx₀X, e₀, he₀G, hlink₀⟩
  have hX_sub_ins : (G.induce X).IsSubdigraph (G.induce (insert v X)) := {
    vertexSet_subset := inter_subset_inter_right _ (subset_insert v X)
    edgeSet_subset := fun _ ⟨he, hh, ht⟩ => ⟨he, mem_insert_of_mem v hh, mem_insert_of_mem v ht⟩
    head_eq := fun _ _ => rfl
    tail_eq := fun _ _ => rfl
  }
  have hv_mem : v ∈ (G.induce (insert v X)).vertexSet := ⟨hvG, mem_insert v X⟩
  have hx₀_mem_X : x₀ ∈ (G.induce X).vertexSet := ⟨hX hx₀X, hx₀X⟩
  have hx₀_mem : x₀ ∈ (G.induce (insert v X)).vertexSet := hX_sub_ins.vertexSet_subset hx₀_mem_X
  have he₀_ins : e₀ ∈ (G.induce (insert v X)).edgeSet := by
    refine ⟨he₀G, ?_⟩
    rcases hlink₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ mem_insert v X, h2 ▸ mem_insert_of_mem v hx₀X⟩
    · exact ⟨h1 ▸ mem_insert_of_mem v hx₀X, h2 ▸ mem_insert v X⟩
  have hlink_ins : (G.induce (insert v X)).toGraph.IsLink e₀ v x₀ := ⟨he₀_ins, hlink₀⟩
  have hwalk_to_x₀ : ∀ u ∈ (G.induce (insert v X)).vertexSet,
      Nonempty (GraphWalk (G.induce (insert v X)).toGraph u x₀) := by
    rintro u ⟨huG, rfl | huX⟩
    · exact ⟨.cons hlink_ins (.nil hx₀_mem)⟩
    · rcases hconn.2 u ⟨huG, huX⟩ x₀ hx₀_mem_X with ⟨W⟩
      exact ⟨hX_sub_ins.mapWalk W⟩
  refine ⟨⟨v, hv_mem⟩, fun u₁ hu₁ u₂ hu₂ => ?_⟩
  rcases hwalk_to_x₀ u₁ hu₁ with ⟨W₁⟩
  rcases hwalk_to_x₀ u₂ hu₂ with ⟨W₂⟩
  exact ⟨GraphWalk.append W₁ (GraphWalk.reverse W₂)⟩

/-- Helper for `(6.3)`: if `G.toGraph` is a simple graph, `X ⊆ G.vertexSet`, and `v ∈ G.vertexSet \ X`,
the number of edges in `G.edgesMeeting (insert v X) \ G.edgesMeeting X` is at most the number of
neighbors of `v` in `G.vertexSet \ X`. -/
lemma ncard_edgesMeeting_insert_sdiff_le {G : Digraph α β} {X : Set α} {v : α}
    (hfin : G.IsFinite) (hsimple : IsSimpleGraph G.toGraph) :
    (G.edgesMeeting (insert v X) \ G.edgesMeeting X).ncard ≤
      ({u ∈ G.vertexSet \ X | G.toGraph.Adj v u}).ncard := by
  let E_new : Set β := G.edgesMeeting (insert v X) \ G.edgesMeeting X
  let N_v : Set α := {u ∈ G.vertexSet \ X | G.toGraph.Adj v u}
  let other (e : β) : α := if G.head e = v then G.tail e else G.head e
  have hlink_other : ∀ e ∈ E_new, G.toGraph.IsLink e v (other e) ∧ other e ∈ N_v := by
    rintro e ⟨⟨heG, hh_ins | ht_ins⟩, hnotX⟩
    · have hh_v : G.head e = v := hh_ins.resolve_right (fun hhX => hnotX ⟨heG, Or.inl hhX⟩)
      have htNotX : G.tail e ∉ X := fun htX => hnotX ⟨heG, Or.inr htX⟩
      have hlink : G.toGraph.IsLink e v (G.tail e) := ⟨heG, Or.inl ⟨hh_v, rfl⟩⟩
      have htv : G.tail e ≠ v := fun h => hsimple.1 e heG v (h ▸ hlink)
      have hother_eq : other e = G.tail e := by simp [other, hh_v]
      rw [hother_eq]
      exact ⟨hlink, ⟨G.tail_mem heG, htNotX⟩, hlink.adj⟩
    · have ht_v : G.tail e = v := ht_ins.resolve_right (fun htX => hnotX ⟨heG, Or.inr htX⟩)
      have hhNotX : G.head e ∉ X := fun hhX => hnotX ⟨heG, Or.inl hhX⟩
      have hlink : G.toGraph.IsLink e v (G.head e) := ⟨heG, Or.inr ⟨rfl, ht_v⟩⟩
      have hhv : G.head e ≠ v := fun h => hsimple.1 e heG v (h ▸ hlink)
      have hother_eq : other e = G.head e := by simp [other, hhv]
      rw [hother_eq]
      exact ⟨hlink, ⟨G.head_mem heG, hhNotX⟩, hlink.adj⟩
  have hinj : Set.InjOn other E_new := by
    intro e₁ he₁ e₂ he₂ heq
    have hl₁ := (hlink_other e₁ he₁).1
    have hl₂ := heq ▸ (hlink_other e₂ he₂).1
    exact hsimple.2 e₁ he₁.1.1 e₂ he₂.1.1 v (other e₁) hl₁ hl₂
  have himg_sub : other '' E_new ⊆ N_v := by
    rintro _ ⟨e, he, rfl⟩
    exact (hlink_other e he).2
  have h1 : (other '' E_new).ncard ≤ N_v.ncard :=
    ncard_le_ncard himg_sub (hfin.finite_V.subset (fun u hu => hu.1.1))
  rw [hinj.ncard_image] at h1
  exact h1

end Digraph

/-- **Graph Minors XIII, Algorithm (6.3)** (pages 85–86):
"(6.3) Algorithm.
*Input:* An integer $k > 0$ and a non-null simple graph $G$ with $|E(G)| \ge k |V(G)|$.
*Output:* A subset $X \subseteq V(G)$ such that
(i) the restriction of $G$ to $X$ is non-null and connected
(ii) $N(X)$ is non-null, and
(iii) every vertex of $N(X)$ has $\ge k$ neighbours in $N(X)$.
*Running time:* $O(\nu\varepsilon)$."

This is the correctness of the method. The RAM program, a greedy vertex-addition recursion in a
component `H` with `|E(H)| ≥ k |V(H)|`, and its `O(ν ε)` time bound are `GM13.algorithm_6_3` in
`Results.lean`. -/
theorem algorithm_6_3_correct {G : Digraph α β} {k : ℕ}
    (hk : 0 < k) (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty)
    (hsimple : IsSimpleGraph G.toGraph)
    (hedges : k * G.vertexSet.ncard ≤ G.edgeSet.ncard) :
    ∃ X ⊆ G.vertexSet,
      (G.induce X).IsConnected ∧
      (G.extNeighbors X).Nonempty ∧
      ∀ v ∈ G.extNeighbors X, k ≤ ({u ∈ G.extNeighbors X | G.toGraph.Adj v u}).ncard := by
  suffices hmain : ∀ (n : ℕ) (G : Digraph α β),
      G.vertexSet.ncard = n → G.IsFinite → G.vertexSet.Nonempty →
      IsSimpleGraph G.toGraph → k * G.vertexSet.ncard ≤ G.edgeSet.ncard →
      ∃ X ⊆ G.vertexSet,
        (G.induce X).IsConnected ∧
        (G.extNeighbors X).Nonempty ∧
        ∀ v ∈ G.extNeighbors X, k ≤ ({u ∈ G.extNeighbors X | G.toGraph.Adj v u}).ncard from
    hmain G.vertexSet.ncard G rfl hfin hne hsimple hedges
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih_outer =>
    intro G hn hfin hne hsimple hedges
    -- Step (2)-(3): inner recursion growing `X ⊆ G.vertexSet` with `rem = G.vertexSet.ncard - X.ncard`
    have hinner : ∀ (rem : ℕ) (X : Set α),
        G.vertexSet.ncard - X.ncard = rem →
        X ⊆ G.vertexSet →
        (G.induce X).IsConnected →
        (G.edgesMeeting X).ncard ≤ (G.extNeighbors X).ncard + k * (X.ncard - 1) →
        ∃ X' ⊆ G.vertexSet,
          (G.induce X').IsConnected ∧
          (G.edgesMeeting X').ncard ≤ (G.extNeighbors X').ncard + k * (X'.ncard - 1) ∧
          (∀ v ∈ G.extNeighbors X', k ≤ ({u ∈ G.extNeighbors X' | G.toGraph.Adj v u}).ncard) := by
      intro rem
      induction rem using Nat.strongRecOn with
      | ind rem ih_in =>
        intro X hrem hX hconn hmeet
        by_cases hall : ∀ v ∈ G.extNeighbors X, k ≤ ({u ∈ G.extNeighbors X | G.toGraph.Adj v u}).ncard
        · exact ⟨X, hX, hconn, hmeet, hall⟩
        · push Not at hall
          rcases hall with ⟨v, hvNX, hd₁_lt⟩
          have hvG : v ∈ G.vertexSet := hvNX.1.1
          have hvNotX : v ∉ X := hvNX.1.2
          let X' : Set α := insert v X
          have hX'_sub : X' ⊆ G.vertexSet := insert_subset hvG hX
          have hX'_conn : (G.induce X').IsConnected :=
            G.induce_insert_isConnected hX hconn hvNX
          have hX_fin : X.Finite := hfin.finite_V.subset hX
          have hX_card_pos : 0 < X.ncard := by
            rcases hconn.1 with ⟨x₀, _, hx₀X⟩
            exact (ncard_pos hX_fin).mpr ⟨x₀, hx₀X⟩
          have hX'_card : X'.ncard = X.ncard + 1 := ncard_insert_of_notMem hvNotX hX_fin
          have hX_lt_G : X.ncard < G.vertexSet.ncard := by
            exact ncard_lt_ncard ⟨hX, fun h => hvNotX (h hvG)⟩ hfin.finite_V
          -- Verify the step (3) inequality:
          -- `|N(X_{i+1})| = |N(X_i)| - 1 + d_2` and `|edgesMeeting X'| ≤ |N(X')| + k * (|X'| - 1)`
          let N₁ : Set α := {u ∈ G.extNeighbors X | G.toGraph.Adj v u}
          let N₂ : Set α := {u ∈ G.vertexSet \ (X ∪ G.extNeighbors X) | G.toGraph.Adj v u}
          have hNX'_eq : G.extNeighbors X' = (G.extNeighbors X \ {v}) ∪ N₂ := by
            ext u
            simp only [Digraph.extNeighbors, X', N₂, mem_ofPred_eq, mem_sdiff, mem_insert_iff,
              mem_union]
            constructor
            · rintro ⟨⟨huG, huNotIns⟩, x, rfl | hxX, hadj⟩
              · have huv : u ≠ x := fun h => huNotIns (Or.inl h)
                have huNotX : u ∉ X := fun h => huNotIns (Or.inr h)
                by_cases huNX : ∃ x' ∈ X, G.toGraph.Adj u x'
                · exact Or.inl ⟨⟨⟨huG, huNotX⟩, huNX⟩, huv⟩
                · exact Or.inr ⟨⟨huG, fun h => h.elim huNotX (fun h2 => huNX h2.2)⟩, hadj.symm⟩
              · have huv : u ≠ v := fun h => huNotIns (Or.inl h)
                have huNotX : u ∉ X := fun h => huNotIns (Or.inr h)
                exact Or.inl ⟨⟨⟨huG, huNotX⟩, x, hxX, hadj⟩, huv⟩
            · rintro (⟨⟨⟨huG, huNotX⟩, x, hxX, hadj⟩, huv⟩ | ⟨⟨huG, hnot⟩, hadj⟩)
              · exact ⟨⟨huG, fun h => h.elim huv huNotX⟩, x, Or.inr hxX, hadj⟩
              · have huNotX : u ∉ X := fun h => hnot (Or.inl h)
                have huv : u ≠ v := by
                  rintro rfl
                  exact hnot (Or.inr hvNX)
                exact ⟨⟨huG, fun h => h.elim huv huNotX⟩, v, Or.inl rfl, hadj.symm⟩
          have hdisj_NX' : Disjoint (G.extNeighbors X \ {v}) N₂ := by
            rw [Set.disjoint_iff]
            rintro u ⟨⟨huNX, _⟩, ⟨_, hnot⟩, _⟩
            exact hnot (Or.inr huNX)
          have hNX_fin : (G.extNeighbors X).Finite :=
            hfin.finite_V.subset (fun u hu => hu.1.1)
          have hN₁_fin : N₁.Finite := hNX_fin.subset (sep_subset _ _)
          have hN₂_fin : N₂.Finite :=
            hfin.finite_V.subset (fun u hu => hu.1.1)
          have hNX'_card : (G.extNeighbors X').ncard + 1 = (G.extNeighbors X).ncard + N₂.ncard := by
            rw [hNX'_eq, ncard_union_eq hdisj_NX' hNX_fin.sdiff hN₂_fin,
              ncard_sdiff_singleton_of_mem hvNX]
            have hpos : 0 < (G.extNeighbors X).ncard := (ncard_pos hNX_fin).mpr ⟨v, hvNX⟩
            omega
          have hNv_sub : {u ∈ G.vertexSet \ X | G.toGraph.Adj v u} ⊆ N₁ ∪ N₂ := by
            rintro u ⟨⟨huG, huNotX⟩, hadj⟩
            by_cases huNX : u ∈ G.extNeighbors X
            · exact Or.inl ⟨huNX, hadj⟩
            · exact Or.inr ⟨⟨huG, fun h => h.elim huNotX huNX⟩, hadj⟩
          have hnew_edges_le :
              (G.edgesMeeting X' \ G.edgesMeeting X).ncard ≤ N₁.ncard + N₂.ncard := by
            have h1 : (G.edgesMeeting X' \ G.edgesMeeting X).ncard ≤
                ({u ∈ G.vertexSet \ X | G.toGraph.Adj v u}).ncard :=
              G.ncard_edgesMeeting_insert_sdiff_le hfin hsimple
            have h2 := ncard_le_ncard hNv_sub (hN₁_fin.union hN₂_fin)
            have h3 := ncard_union_le N₁ N₂
            omega
          have hmeet_sub : G.edgesMeeting X ⊆ G.edgesMeeting X' := by
            rintro e ⟨heG, hh | ht⟩
            · exact ⟨heG, Or.inl (mem_insert_of_mem v hh)⟩
            · exact ⟨heG, Or.inr (mem_insert_of_mem v ht)⟩
          have hmeet_X'_eq :
              (G.edgesMeeting X').ncard =
                (G.edgesMeeting X' \ G.edgesMeeting X).ncard + (G.edgesMeeting X).ncard :=
            (ncard_sdiff_add_ncard_of_subset hmeet_sub
              (hfin.finite_E.subset (fun e he => he.1))).symm
          have hmeet' : (G.edgesMeeting X').ncard ≤ (G.extNeighbors X').ncard + k * (X'.ncard - 1) := by
            have hd₁ : N₁.ncard < k := hd₁_lt
            have hmul : k * (X'.ncard - 1) = k * (X.ncard - 1) + k := by
              rw [hX'_card, Nat.add_sub_cancel]
              have hsub1 : X.ncard = (X.ncard - 1) + 1 := by omega
              conv_lhs => rw [hsub1, Nat.mul_add, Nat.mul_one]
            omega
          have hrem_lt : G.vertexSet.ncard - X'.ncard < rem := by omega
          exact ih_in _ hrem_lt X' rfl hX'_sub hX'_conn hmeet'
    -- Start the inner recursion from `X₁ = {v₁}` for some `v₁ ∈ G.vertexSet`
    rcases hne with ⟨v₁, hv₁⟩
    have hX₁_sub : ({v₁} : Set α) ⊆ G.vertexSet := singleton_subset_iff.mpr hv₁
    have hX₁_conn : (G.induce {v₁}).IsConnected :=
      ⟨⟨v₁, hv₁, rfl⟩, fun u ⟨_, hu⟩ w ⟨_, hw⟩ => by
        subst hu hw; exact ⟨.nil ⟨hv₁, rfl⟩⟩⟩
    have hX₁_meet :
        (G.edgesMeeting {v₁}).ncard ≤ (G.extNeighbors {v₁}).ncard + k * (({v₁} : Set α).ncard - 1) := by
      have h1 := G.ncard_edgesMeeting_insert_sdiff_le (X := ∅) (v := v₁) hfin hsimple
      have hemp : G.edgesMeeting ∅ = ∅ := by
        ext e; simp [Digraph.edgesMeeting]
      have hN_eq : {u ∈ G.vertexSet \ ∅ | G.toGraph.Adj v₁ u} = G.extNeighbors {v₁} := by
        ext u
        simp only [Digraph.extNeighbors, mem_ofPred_eq, mem_sdiff, mem_empty_iff_false, not_false_eq_true,
          and_true, mem_singleton_iff, exists_eq_left]
        refine ⟨fun ⟨huG, hadj⟩ => ⟨⟨huG, ?_⟩, hadj.symm⟩, fun ⟨⟨huG, _⟩, hadj⟩ => ⟨huG, hadj.symm⟩⟩
        rintro rfl
        rcases hadj with ⟨e, heG, hlink⟩
        exact hsimple.1 e heG u ⟨heG, hlink⟩
      rw [insert_empty_eq, hemp, sdiff_empty, hN_eq] at h1
      rw [ncard_singleton]
      omega
    obtain ⟨X, hX_sub, hX_conn, hX_meet, hX_deg⟩ :=
      hinner (G.vertexSet.ncard - ({v₁} : Set α).ncard) {v₁} rfl hX₁_sub hX₁_conn hX₁_meet
    -- Step (4): if `G.extNeighbors X` is nonempty, we are done; otherwise `X` is disconnected from
    -- `G.vertexSet \ X` and has `< k * X.ncard` edges, so `G.deleteVertices X` satisfies the
    -- hypotheses of `(6.3)` with strictly fewer vertices.
    by_cases hNX_ne : (G.extNeighbors X).Nonempty
    · exact ⟨X, hX_sub, hX_conn, hNX_ne, hX_deg⟩
    · rw [not_nonempty_iff_eq_empty] at hNX_ne
      have hX_fin : X.Finite := hfin.finite_V.subset hX_sub
      have hX_pos : 0 < X.ncard := by
        rcases hX_conn.1 with ⟨x₀, _, hx₀X⟩
        exact (ncard_pos hX_fin).mpr ⟨x₀, hx₀X⟩
      have hmeet_lt : (G.edgesMeeting X).ncard < k * X.ncard := by
        rw [hNX_ne, ncard_empty, zero_add] at hX_meet
        have hsub1 : k * (X.ncard - 1) + k = k * X.ncard := by
          have hx1 : X.ncard = (X.ncard - 1) + 1 := by omega
          conv_rhs => rw [hx1, Nat.mul_add, Nat.mul_one]
        omega
      let G' : Digraph α β := G.deleteVertices X
      have hG'V : G'.vertexSet = G.vertexSet \ X := inter_eq_self_of_subset_right sdiff_subset
      have hG'E : G'.edgeSet = G.edgeSet \ G.edgesMeeting X := by
        ext e
        simp only [G', Digraph.deleteVertices, Digraph.induce, Digraph.edgesMeeting,
          mem_ofPred_eq, mem_sdiff]
        refine ⟨fun ⟨heG, ⟨_, hhNotX⟩, ⟨_, htNotX⟩⟩ => ⟨heG, fun ⟨_, h⟩ => h.elim hhNotX htNotX⟩,
          fun ⟨heG, hnot⟩ => ⟨heG, ⟨G.head_mem heG, fun hh => hnot ⟨heG, Or.inl hh⟩⟩,
            ⟨G.tail_mem heG, fun ht => hnot ⟨heG, Or.inr ht⟩⟩⟩⟩
      have hG'V_card : G'.vertexSet.ncard + X.ncard = G.vertexSet.ncard := by
        rw [hG'V]
        exact ncard_sdiff_add_ncard_of_subset hX_sub hfin.finite_V
      have hG'E_card : G'.edgeSet.ncard + (G.edgesMeeting X).ncard = G.edgeSet.ncard := by
        rw [hG'E]
        exact ncard_sdiff_add_ncard_of_subset (fun e he => he.1) hfin.finite_E
      have hG'_edges : k * G'.vertexSet.ncard < G'.edgeSet.ncard := by
        have hmul : k * G.vertexSet.ncard = k * G'.vertexSet.ncard + k * X.ncard := by
          rw [← hG'V_card, Nat.mul_add]
        have h1 := hedges
        have h2 := hG'E_card
        have h3 := hmeet_lt
        omega
      have hG'_fin : G'.IsFinite :=
        ⟨hfin.finite_V.subset (G.deleteVertices_isSubdigraph X).vertexSet_subset,
         hfin.finite_E.subset (G.deleteVertices_isSubdigraph X).edgeSet_subset⟩
      have hG'E_pos : 0 < G'.edgeSet.ncard := by omega
      have hG'E_ne : G'.edgeSet.Nonempty := (ncard_pos hG'_fin.finite_E).mp hG'E_pos
      have hG'V_ne : G'.vertexSet.Nonempty := by
        rcases hG'E_ne with ⟨e₀, he₀⟩
        exact ⟨G'.head e₀, G'.head_mem he₀⟩
      have hG'_lt : G'.vertexSet.ncard < n := by omega
      have hG'_simple : IsSimpleGraph G'.toGraph := by
        have hle : G'.toGraph ≤ G.toGraph := (G.deleteVertices_isSubdigraph X).toGraph_le
        refine ⟨fun e he v hlink => hsimple.1 e (hle.edgeSet_mono he) v (hlink.mono hle),
          fun e₁ he₁ e₂ he₂ u v hl₁ hl₂ =>
            hsimple.2 e₁ (hle.edgeSet_mono he₁) e₂ (hle.edgeSet_mono he₂) u v
              (hl₁.mono hle) (hl₂.mono hle)⟩
      obtain ⟨Y, hY_sub, hY_conn, hY_NX, hY_deg⟩ :=
        ih_outer G'.vertexSet.ncard hG'_lt G' rfl hG'_fin hG'V_ne hG'_simple (le_of_lt hG'_edges)
      have hY_sub_G : Y ⊆ G.vertexSet :=
        hY_sub.trans (G.deleteVertices_isSubdigraph X).vertexSet_subset
      -- Any edge incident with `u ∈ G.vertexSet \ X` cannot meet `X` since `G.extNeighbors X = ∅`
      have hno_cross (e : β) (heG : e ∈ G.edgeSet) :
          (G.head e ∈ G.vertexSet \ X → G.tail e ∈ G.vertexSet \ X) ∧
          (G.tail e ∈ G.vertexSet \ X → G.head e ∈ G.vertexSet \ X) := by
        refine ⟨fun hh => ⟨G.tail_mem heG, fun htX => ?_⟩,
          fun ht => ⟨G.head_mem heG, fun hhX => ?_⟩⟩
        · have hm : G.head e ∈ G.extNeighbors X :=
            ⟨hh, G.tail e, htX, e, heG, Or.inl ⟨rfl, rfl⟩⟩
          rw [hNX_ne] at hm; exact hm
        · have hm : G.tail e ∈ G.extNeighbors X :=
            ⟨ht, G.head e, hhX, e, heG, Or.inr ⟨rfl, rfl⟩⟩
          rw [hNX_ne] at hm; exact hm
      have hadj_iff (u : α) (hu : u ∈ G.vertexSet \ X) (w : α) :
          G'.toGraph.Adj u w ↔ G.toGraph.Adj u w ∧ w ∈ G.vertexSet \ X := by
        constructor
        · rintro ⟨e, heG', hlink⟩
          have heG : e ∈ G.edgeSet := (G.deleteVertices_isSubdigraph X).edgeSet_subset heG'
          have hw : w ∈ G.vertexSet \ X := by
            rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact (hno_cross e heG).1 hu
            · exact (hno_cross e heG).2 hu
          exact ⟨⟨e, heG, hlink⟩, hw⟩
        · rintro ⟨⟨e, heG, hlink⟩, hw⟩
          have heG' : e ∈ G'.edgeSet := by
            rw [hG'E]
            refine ⟨heG, fun ⟨_, h⟩ => ?_⟩
            rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact h.elim hu.2 hw.2
            · exact h.elim hw.2 hu.2
          exact ⟨e, heG', hlink⟩
      have hNY_eq : G'.extNeighbors Y = G.extNeighbors Y := by
        ext u
        simp only [Digraph.extNeighbors, mem_ofPred_eq, mem_sdiff]
        constructor
        · rintro ⟨⟨huG', huNotY⟩, y, hyY, hadj⟩
          have hyG' : y ∈ G.vertexSet \ X := hG'V ▸ hY_sub hyY
          have hadjG := (hadj_iff y hyG' u).mp hadj.symm
          exact ⟨⟨hadjG.2.1, huNotY⟩, y, hyY, hadjG.1.symm⟩
        · rintro ⟨⟨huG, huNotY⟩, y, hyY, hadj⟩
          have hyG' : y ∈ G.vertexSet \ X := hG'V ▸ hY_sub hyY
          have hadjG' := (hadj_iff y hyG' u).mpr ⟨hadj.symm, ?_⟩
          · exact ⟨⟨hG'V.symm ▸ (hadj_iff y hyG' u).mp hadjG' |>.2, huNotY⟩, y, hyY, hadjG'.symm⟩
          · rcases hadj with ⟨e, heG, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
            · exact (hno_cross e heG).2 hyG'
            · exact (hno_cross e heG).1 hyG'
      have hind_sub : (G'.induce Y).IsSubdigraph (G.induce Y) := {
        vertexSet_subset := inter_subset_inter_left _ (G.deleteVertices_isSubdigraph X).vertexSet_subset
        edgeSet_subset := fun _ ⟨he, hh, ht⟩ =>
          ⟨(G.deleteVertices_isSubdigraph X).edgeSet_subset he, hh, ht⟩
        head_eq := fun _ _ => rfl
        tail_eq := fun _ _ => rfl
      }
      have hind_V : (G'.induce Y).vertexSet = (G.induce Y).vertexSet := by
        change G'.vertexSet ∩ Y = G.vertexSet ∩ Y
        rw [inter_eq_self_of_subset_right hY_sub, inter_eq_self_of_subset_right hY_sub_G]
      have hGY_conn : (G.induce Y).IsConnected := by
        refine ⟨hind_V ▸ hY_conn.1, fun u hu w hw => ?_⟩
        rw [← hind_V] at hu hw
        rcases hY_conn.2 u hu w hw with ⟨W⟩
        exact ⟨hind_sub.mapWalk W⟩
      refine ⟨Y, hY_sub_G, hGY_conn, hNY_eq ▸ hY_NX, fun v hv => ?_⟩
      rw [← hNY_eq] at hv
      have hvG' : v ∈ G.vertexSet \ X := hG'V ▸ hv.1.1
      have hset_eq : {u ∈ G'.extNeighbors Y | G'.toGraph.Adj v u} =
          {u ∈ G.extNeighbors Y | G.toGraph.Adj v u} := by
        ext u
        simp only [mem_ofPred_eq, hNY_eq]
        refine ⟨fun ⟨huNY, hadj'⟩ => ⟨huNY, ((hadj_iff v hvG' u).mp hadj').1⟩,
          fun ⟨huNY, hadj⟩ => ⟨huNY, (hadj_iff v hvG' u).mpr ⟨hadj, ?_⟩⟩⟩
        have huNY' : u ∈ G'.extNeighbors Y := hNY_eq.symm ▸ huNY
        exact hG'V ▸ huNY'.1.1
      rw [← hset_eq]
      exact hY_deg v hv

/-- **Graph Minors XIII, (6.3)** (pages 85–86): mathematical statement of Algorithm (6.3). -/
theorem theorem_6_3_proof {G : Digraph α β} {k : ℕ}
    (hk : 0 < k) (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty)
    (hsimple : IsSimpleGraph G.toGraph)
    (hedges : k * G.vertexSet.ncard ≤ G.edgeSet.ncard) :
    ∃ X ⊆ G.vertexSet,
      (G.induce X).IsConnected ∧
      (G.extNeighbors X).Nonempty ∧
      ∀ v ∈ G.extNeighbors X, k ≤ ({u ∈ G.extNeighbors X | G.toGraph.Adj v u}).ncard := by
  have hk_pos : 0 < k := hk
  have hne_V : G.vertexSet.Nonempty := hne
  exact algorithm_6_3_correct hk_pos hfin hne_V hsimple hedges

/-- Helper: if `S` is a finite set and `F : α → Set γ` assigns to each `v ∈ S` a subset `F v ⊆ Dom`
of a finite set `Dom` with `d ≤ (F v).ncard`, and `F v₁` is disjoint from `F v₂` for `v₁ ≠ v₂`,
then `d * S.ncard ≤ Dom.ncard`. -/
lemma mul_ncard_le_of_pairwiseDisjoint {γ : Type*} {S : Set α} {Dom : Set γ} {F : α → Set γ} {d : ℕ}
    (hS_fin : S.Finite) (hDom_fin : Dom.Finite)
    (hsub : ∀ v ∈ S, F v ⊆ Dom)
    (hdisj : S.PairwiseDisjoint F)
    (hcard : ∀ v ∈ S, d ≤ (F v).ncard) :
    d * S.ncard ≤ Dom.ncard := by
  have hbiUnion_sub : (⋃ v ∈ S, F v) ⊆ Dom := iUnion₂_subset hsub
  suffices h : ∀ (n : ℕ) (T : Set α), T.ncard = n → T ⊆ S →
      d * T.ncard ≤ (⋃ v ∈ T, F v).ncard by
    exact le_trans (h S.ncard S rfl Subset.rfl) (ncard_le_ncard hbiUnion_sub hDom_fin)
  intro n
  induction n with
  | zero =>
    intro T hT0 _
    rw [hT0, Nat.mul_zero]
    exact Nat.zero_le _
  | succ m ih =>
    intro T hTm hTS
    have hT_fin : T.Finite := hS_fin.subset hTS
    have hT_ne : T.Nonempty := (ncard_pos hT_fin).mp (by omega)
    rcases hT_ne with ⟨v₀, hv₀T⟩
    let T' : Set α := T \ {v₀}
    have hT'_sub_T : T' ⊆ T := sdiff_subset
    have hT'_sub_S : T' ⊆ S := hT'_sub_T.trans hTS
    have hT'_card : T'.ncard = m := by
      have h1 : T'.ncard = T.ncard - 1 := ncard_sdiff_singleton_of_mem hv₀T
      omega
    have ih' := ih T' hT'_card hT'_sub_S
    have hT_eq : T = insert v₀ T' := by
      change T = insert v₀ (T \ {v₀})
      rw [insert_sdiff_singleton, insert_eq_of_mem hv₀T]
    have hu_eq : (⋃ v ∈ T, F v) = F v₀ ∪ (⋃ v ∈ T', F v) := by
      conv_lhs => rw [hT_eq]
      exact biUnion_insert v₀ T' F
    have hdisj_v₀ : Disjoint (F v₀) (⋃ v ∈ T', F v) := by
      rw [disjoint_iUnion₂_right]
      intro v hvT'
      exact hdisj (hTS hv₀T) (hT'_sub_S hvT') (Ne.symm hvT'.2)
    have hFv₀_fin : (F v₀).Finite := hDom_fin.subset (hsub v₀ (hTS hv₀T))
    have hUT'_fin : (⋃ v ∈ T', F v).Finite :=
      hDom_fin.subset (iUnion₂_subset (fun v hv => hsub v (hT'_sub_S hv)))
    rw [hu_eq, ncard_union_eq hdisj_v₀ hFv₀_fin hUT'_fin, hTm, Nat.mul_succ, ← hT'_card]
    have hd_le : d ≤ (F v₀).ncard := hcard v₀ (hTS hv₀T)
    omega

/-- Handshaking inequality for a finite digraph `H`: if every vertex `v ∈ H.vertexSet` has at least
`d` neighbors in `H.vertexSet` in `H.toGraph`, then `d * H.vertexSet.ncard ≤ 2 * H.edgeSet.ncard`. -/
lemma mul_ncard_vertexSet_le_two_mul_ncard_edgeSet {H : Digraph α β} {d : ℕ}
    (hfin : H.IsFinite)
    (hdeg : ∀ v ∈ H.vertexSet, d ≤ ({u ∈ H.vertexSet | H.toGraph.Adj v u}).ncard) :
    d * H.vertexSet.ncard ≤ 2 * H.edgeSet.ncard := by
  let Dom : Set (β × Bool) :=
    (fun e => (e, true)) '' H.edgeSet ∪ (fun e => (e, false)) '' H.edgeSet
  have hDom_fin : Dom.Finite := (hfin.finite_E.image _).union (hfin.finite_E.image _)
  have hDom_card : Dom.ncard ≤ 2 * H.edgeSet.ncard := by
    have h1 : Dom.ncard ≤
        ((fun e => (e, true)) '' H.edgeSet).ncard + ((fun e => (e, false)) '' H.edgeSet).ncard :=
      ncard_union_le _ _
    have h2 := ncard_image_le (f := fun e => (e, true)) hfin.finite_E
    have h3 := ncard_image_le (f := fun e => (e, false)) hfin.finite_E
    omega
  let endAt (p : β × Bool) : α := if p.2 then H.head p.1 else H.tail p.1
  let otherAt (p : β × Bool) : α := if p.2 then H.tail p.1 else H.head p.1
  let F (v : α) : Set (β × Bool) := {p ∈ Dom | endAt p = v}
  have hF_sub (v : α) (_ : v ∈ H.vertexSet) : F v ⊆ Dom := sep_subset _ _
  have hF_disj : H.vertexSet.PairwiseDisjoint F := by
    intro v₁ _ v₂ _ hne
    change Disjoint (F v₁) (F v₂)
    rw [Set.disjoint_iff]
    rintro p ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    exact hne (h1.symm.trans h2)
  have hF_card (v : α) (hv : v ∈ H.vertexSet) : d ≤ (F v).ncard := by
    let Nv : Set α := {u ∈ H.vertexSet | H.toGraph.Adj v u}
    have hNv_sub : Nv ⊆ otherAt '' F v := by
      rintro u ⟨_, e, heH, ⟨hh, ht⟩ | ⟨hh, ht⟩⟩
      · refine ⟨(e, true), ⟨Or.inl ⟨e, heH, rfl⟩, ?_⟩, ?_⟩
        · simp [endAt, hh]
        · simp [otherAt, ht]
      · refine ⟨(e, false), ⟨Or.inr ⟨e, heH, rfl⟩, ?_⟩, ?_⟩
        · simp [endAt, ht]
        · simp [otherAt, hh]
    have hFv_fin : (F v).Finite := hDom_fin.subset (sep_subset _ _)
    have h1 : Nv.ncard ≤ (otherAt '' F v).ncard := ncard_le_ncard hNv_sub (hFv_fin.image _)
    have h2 : (otherAt '' F v).ncard ≤ (F v).ncard := ncard_image_le hFv_fin
    have h3 : d ≤ Nv.ncard := hdeg v hv
    omega
  have h4 := mul_ncard_le_of_pairwiseDisjoint hfin.finite_V hDom_fin hF_sub hF_disj hF_card
  omega

/-- Helper for `(6.4)`: `p` mutually vertex-disjoint connected subdigraphs `G₁, …, G_p` of `G` with
an edge of `G` between `G_i` and `G_j` for `1 ≤ i < j ≤ p` yield a model of `K_p` in `G.toGraph`. -/
lemma hasGraphModel_completeGraph_of_connected_subgraphs [Nonempty β]
    {G : Digraph α β} {p : ℕ} {sub : Fin p → Digraph α β}
    (hsub : ∀ i : Fin p, (sub i).IsSubdigraph G)
    (hconn : ∀ i : Fin p, (sub i).IsConnected)
    (hdisj : Pairwise (fun i j : Fin p => Disjoint (sub i).vertexSet (sub j).vertexSet))
    (hadj : ∀ i j : Fin p, i < j → G.HasEdgeBetween (sub i).vertexSet (sub j).vertexSet) :
    HasGraphModel (GM16.completeGraph p) G.toGraph := by
  let vMap (i : Fin p) : Graph α β := (sub i).toGraph
  have hex_edge (q : Sym2 (Fin p)) :
      q ∈ E(GM16.completeGraph p) →
      ∃ e ∈ G.edgeSet, ∀ i j : Fin p, q = s(i, j) → i ≠ j →
        ∃ x ∈ (sub i).vertexSet, ∃ y ∈ (sub j).vertexSet, G.toGraph.IsLink e x y := by
    rintro ⟨i₀, j₀, hne₀, rfl⟩
    have hlt_or_gt : i₀ < j₀ ∨ j₀ < i₀ := lt_or_gt_of_ne hne₀
    have hEdge₀ : G.HasEdgeBetween (sub i₀).vertexSet (sub j₀).vertexSet := by
      rcases hlt_or_gt with hlt | hgt
      · exact hadj i₀ j₀ hlt
      · rcases hadj j₀ i₀ hgt with ⟨e, heG, h⟩
        exact ⟨e, heG, h.symm⟩
    rcases hEdge₀ with ⟨e, heG, hlink₀⟩
    refine ⟨e, heG, fun i j heq _ => ?_⟩
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hlink₀ with ⟨hx, hy⟩ | ⟨hy, hx⟩
      · exact ⟨G.head e, hx, G.tail e, hy, heG, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨G.tail e, hx, G.head e, hy, heG, Or.inr ⟨rfl, rfl⟩⟩
    · rcases hlink₀ with ⟨hy, hx⟩ | ⟨hx, hy⟩
      · exact ⟨G.tail e, hx, G.head e, hy, heG, Or.inr ⟨rfl, rfl⟩⟩
      · exact ⟨G.head e, hx, G.tail e, hy, heG, Or.inl ⟨rfl, rfl⟩⟩
  let eMap (q : Sym2 (Fin p)) : β :=
    if hq : q ∈ E(GM16.completeGraph p) then Classical.choose (hex_edge q hq)
    else Classical.arbitrary β
  have heMap_spec (q : Sym2 (Fin p)) (hq : q ∈ E(GM16.completeGraph p)) :
      eMap q ∈ G.edgeSet ∧ ∀ i j : Fin p, q = s(i, j) → i ≠ j →
        ∃ x ∈ (sub i).vertexSet, ∃ y ∈ (sub j).vertexSet, G.toGraph.IsLink (eMap q) x y := by
    dsimp [eMap]
    simp only [hq, ↓reduceDIte]
    exact Classical.choose_spec (hex_edge q hq)
  apply hasGraphModel_of_exists_isGraphModel
  refine ⟨vMap, eMap, {
    sub_of_mem := fun i _ => (hsub i).toGraph_le
    nonempty_of_mem := fun i _ => (hconn i).1
    connected_of_mem := fun i _ => (hconn i).2
    disjoint_of_ne := fun i j _ _ hne => hdisj hne
    edge_mem := fun q hq => (heMap_spec q hq).1
    link_ends_of_ne := fun {q i j} hlink hne =>
      (heMap_spec q hlink.edge_mem).2 i j hlink.2 hne
    loop_ends := fun {q i} hlink => False.elim (hlink.1 rfl)
    eMap_injOn := by
      intro q₁ hq₁ q₂ hq₂ heq
      rcases hq₁ with ⟨i₁, j₁, hne₁, rfl⟩
      rcases hq₂ with ⟨i₂, j₂, hne₂, rfl⟩
      rcases (heMap_spec s(i₁, j₁) ⟨i₁, j₁, hne₁, rfl⟩).2 i₁ j₁ rfl hne₁ with
        ⟨x₁, hx₁, y₁, hy₁, hlink₁⟩
      rcases (heMap_spec s(i₂, j₂) ⟨i₂, j₂, hne₂, rfl⟩).2 i₂ j₂ rfl hne₂ with
        ⟨x₂, hx₂, y₂, hy₂, hlink₂⟩
      rw [← heq] at hlink₂
      rcases G.toGraph.eq_or_eq_of_isLink_of_isLink hlink₁ hlink₂ with rfl | rfl
      · have hy_eq : y₁ = y₂ := hlink₁.right_unique hlink₂
        subst hy_eq
        have hi_eq : i₁ = i₂ := by
          by_contra hne
          exact Set.disjoint_left.mp (hdisj hne) hx₁ hx₂
        have hj_eq : j₁ = j₂ := by
          by_contra hne
          exact Set.disjoint_left.mp (hdisj hne) hy₁ hy₂
        rw [hi_eq, hj_eq]
      · have hy_eq : y₁ = x₂ := hlink₁.right_unique hlink₂.symm
        subst hy_eq
        have hi_eq : i₁ = j₂ := by
          by_contra hne
          exact Set.disjoint_left.mp (hdisj hne) hx₁ hy₂
        have hj_eq : j₁ = i₂ := by
          by_contra hne
          exact Set.disjoint_left.mp (hdisj hne) hy₁ hx₂
        rw [hi_eq, hj_eq, Sym2.eq_swap]
  }⟩

/-- Iterative step of **Graph Minors XIII, Algorithm (6.4)** (pages 86–87):
if `p ≥ 1` and `G` is a finite non-null simple graph with `2^{p-2} |V(G)| ≤ 2 |E(G)|` (when `p ≥ 2`),
there are `p` disjoint non-null connected subgraphs `G₁, …, G_p` of `G` such that for `1 ≤ i < j ≤ p`
every vertex of `G_j` has a neighbour in `G_i`. -/
lemma exists_subgraphs_algorithm_6_4 {G : Digraph α β} {p : ℕ}
    (hp : 1 ≤ p) (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty)
    (hsimple : IsSimpleGraph G.toGraph)
    (hedges : p ≥ 2 → 2 ^ (p - 2) * G.vertexSet.ncard ≤ 2 * G.edgeSet.ncard) :
    ∃ sub : Fin p → Digraph α β,
      (∀ i : Fin p, (sub i).IsSubdigraph G) ∧
      (∀ i : Fin p, (sub i).IsConnected) ∧
      Pairwise (fun i j : Fin p => Disjoint (sub i).vertexSet (sub j).vertexSet) ∧
      (∀ i j : Fin p, i < j → ∀ v ∈ (sub j).vertexSet,
        ∃ u ∈ (sub i).vertexSet, G.toGraph.Adj v u) := by
  induction p generalizing G with
  | zero => omega
  | succ m ih =>
    by_cases hm0 : m = 0
    · subst hm0
      rcases hne with ⟨v₀, hv₀⟩
      refine ⟨fun _ => G.induce {v₀}, fun _ => G.induce_isSubdigraph {v₀},
        fun _ => ⟨⟨v₀, hv₀, rfl⟩, fun u ⟨_, hu⟩ w ⟨_, hw⟩ => by
          subst hu hw; exact ⟨.nil ⟨hv₀, rfl⟩⟩⟩,
        fun i j hne' => False.elim (hne' (Fin.ext (by omega))),
        fun i j hlt => False.elim (by omega)⟩
    · by_cases hm1 : m = 1
      · subst hm1
        -- `p = 2`: `1 * G.vertexSet.ncard ≤ 2 * G.edgeSet.ncard` and `G.vertexSet.ncard ≥ 1`
        have hV_pos : 0 < G.vertexSet.ncard := (ncard_pos hfin.finite_V).mpr hne
        have hE_pos : 0 < G.edgeSet.ncard := by
          have h2 := hedges (le_refl 2)
          change 1 * G.vertexSet.ncard ≤ 2 * G.edgeSet.ncard at h2
          omega
        rcases (ncard_pos hfin.finite_E).mp hE_pos with ⟨e₀, he₀⟩
        let u₀ := G.head e₀
        let v₀ := G.tail e₀
        have hu₀ : u₀ ∈ G.vertexSet := G.head_mem he₀
        have hv₀ : v₀ ∈ G.vertexSet := G.tail_mem he₀
        have hlink₀ : G.toGraph.IsLink e₀ u₀ v₀ := ⟨he₀, Or.inl ⟨rfl, rfl⟩⟩
        have huv_ne : u₀ ≠ v₀ := fun h => hsimple.1 e₀ he₀ u₀ (h ▸ hlink₀)
        let sub (i : Fin 2) : Digraph α β :=
          if i.1 = 0 then G.induce {u₀} else G.induce {v₀}
        refine ⟨sub, fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i j hlt v hv => ?_⟩
        · dsimp [sub]; split_ifs <;> exact G.induce_isSubdigraph _
        · dsimp [sub]
          split_ifs
          · exact ⟨⟨u₀, hu₀, rfl⟩, fun x ⟨_, hx⟩ y ⟨_, hy⟩ => by
              subst hx hy; exact ⟨.nil ⟨hu₀, rfl⟩⟩⟩
          · exact ⟨⟨v₀, hv₀, rfl⟩, fun x ⟨_, hx⟩ y ⟨_, hy⟩ => by
              subst hx hy; exact ⟨.nil ⟨hv₀, rfl⟩⟩⟩
        · dsimp [sub]
          have hij_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
          split_ifs with h1 h2 h2
          · omega
          · rw [Set.disjoint_iff]
            rintro x ⟨⟨_, rfl⟩, ⟨_, hxv⟩⟩
            exact huv_ne hxv
          · rw [Set.disjoint_iff]
            rintro x ⟨⟨_, hxv⟩, ⟨_, rfl⟩⟩
            exact huv_ne hxv
          · omega
        · have hi0 : i.1 = 0 := by omega
          have hj1 : j.1 = 1 := by omega
          dsimp [sub] at hv ⊢
          simp only [hi0, hj1, ↓reduceIte, one_ne_zero] at hv ⊢
          rcases hv with ⟨_, rfl⟩
          exact ⟨u₀, ⟨hu₀, rfl⟩, hlink₀.symm.adj⟩
      · -- `m ≥ 2`, so `p = m + 1 ≥ 3`: apply `algorithm_6_3_correct` with `k = 2 ^ (m - 2)`
        have hm2 : 2 ≤ m := by omega
        let k : ℕ := 2 ^ (m - 2)
        have hk_pos : 0 < k := Nat.pos_of_ne_zero (by positivity)
        have hedges_k : k * G.vertexSet.ncard ≤ G.edgeSet.ncard := by
          have h1 := hedges (by omega)
          have hpow : 2 ^ (m + 1 - 2) = 2 * k := by
            dsimp [k]
            have heq : m + 1 - 2 = (m - 2) + 1 := by omega
            rw [heq, Nat.pow_succ, Nat.mul_comm]
          rw [hpow, Nat.mul_assoc] at h1
          omega
        obtain ⟨X, hX_sub, hX_conn, hNX_ne, hNX_deg⟩ :=
          algorithm_6_3_correct hk_pos hfin hne hsimple hedges_k
        let Y : Set α := G.extNeighbors X
        have hY_sub : Y ⊆ G.vertexSet := fun u hu => hu.1.1
        let G_Y : Digraph α β := G.induce Y
        have hGY_sub : G_Y.IsSubdigraph G := G.induce_isSubdigraph Y
        have hGY_V : G_Y.vertexSet = Y := inter_eq_self_of_subset_right hY_sub
        have hGY_fin : G_Y.IsFinite :=
          ⟨hfin.finite_V.subset hGY_sub.vertexSet_subset,
           hfin.finite_E.subset hGY_sub.edgeSet_subset⟩
        have hGY_simple : IsSimpleGraph G_Y.toGraph := by
          have hle : G_Y.toGraph ≤ G.toGraph := hGY_sub.toGraph_le
          refine ⟨fun e he v hlink => hsimple.1 e (hle.edgeSet_mono he) v (hlink.mono hle),
            fun e₁ he₁ e₂ he₂ u v hl₁ hl₂ =>
              hsimple.2 e₁ (hle.edgeSet_mono he₁) e₂ (hle.edgeSet_mono he₂) u v
                (hl₁.mono hle) (hl₂.mono hle)⟩
        have hGY_deg : ∀ v ∈ G_Y.vertexSet,
            k ≤ ({u ∈ G_Y.vertexSet | G_Y.toGraph.Adj v u}).ncard := by
          intro v hv
          rw [hGY_V] at hv ⊢
          have hset_eq : {u ∈ Y | G_Y.toGraph.Adj v u} = {u ∈ Y | G.toGraph.Adj v u} := by
            ext u
            simp only [mem_ofPred_eq, and_congr_right_iff]
            intro huY
            refine ⟨fun ⟨e, heGY, hlink⟩ => ⟨e, heGY.1, hlink⟩,
              fun ⟨e, heG, hlink⟩ => ⟨e, ⟨heG, ?_⟩, hlink⟩⟩
            rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨hv, huY⟩
            · exact ⟨huY, hv⟩
          rw [hset_eq]
          exact hNX_deg v hv
        have hGY_handshake := mul_ncard_vertexSet_le_two_mul_ncard_edgeSet hGY_fin hGY_deg
        obtain ⟨sub_Y, hsub_Y, hconn_Y, hdisj_Y, hadj_Y⟩ :=
          ih (by omega) hGY_fin (hGY_V.symm ▸ hNX_ne) hGY_simple (fun _ => hGY_handshake)
        let sub (i : Fin (m + 1)) : Digraph α β :=
          if hi : i.1 = 0 then G.induce X else sub_Y ⟨i.1 - 1, by omega⟩
        refine ⟨sub, fun i => ?_, fun i => ?_, fun i j hij => ?_, fun i j hlt v hv => ?_⟩
        · dsimp [sub]
          split_ifs with hi
          · exact G.induce_isSubdigraph X
          · exact (hsub_Y _).trans hGY_sub
        · dsimp [sub]
          split_ifs with hi
          · exact hX_conn
          · exact hconn_Y _
        · dsimp [sub]
          have hij_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
          split_ifs with h1 h2 h2
          · omega
          · rw [Set.disjoint_iff]
            rintro x ⟨⟨_, hxX⟩, hxj⟩
            have hxY : x ∈ Y := hGY_V ▸ (hsub_Y _).vertexSet_subset hxj
            exact hxY.1.2 hxX
          · rw [Set.disjoint_iff]
            rintro x ⟨hxi, ⟨_, hxX⟩⟩
            have hxY : x ∈ Y := hGY_V ▸ (hsub_Y _).vertexSet_subset hxi
            exact hxY.1.2 hxX
          · exact hdisj_Y (fun h => by
              have hval := congrArg Fin.val h
              dsimp at hval; omega)
        · dsimp [sub] at hv ⊢
          have hj_ne0 : ¬ j.1 = 0 := by omega
          simp only [hj_ne0] at hv
          split_ifs with hi0
          · -- `i = 0`: `v ∈ (sub_Y ⟨j.1 - 1, _⟩).vertexSet ⊆ Y = G.extNeighbors X`
            have hvY : v ∈ Y := hGY_V ▸ (hsub_Y _).vertexSet_subset hv
            rcases hvY.2 with ⟨x, hxX, hadj_vx⟩
            exact ⟨x, ⟨hX_sub hxX, hxX⟩, hadj_vx⟩
          · -- `0 < i < j`
            have hlt' : (⟨i.1 - 1, by omega⟩ : Fin m) < ⟨j.1 - 1, by omega⟩ := by
              change i.1 - 1 < j.1 - 1; omega
            rcases hadj_Y _ _ hlt' v hv with ⟨u, hu, e, heGY, hlink⟩
            exact ⟨u, hu, e, hGY_sub.edgeSet_subset heGY, hlink⟩

/-- **Graph Minors XIII, Algorithm (6.4)** (pages 86–87):
"(6.4) Algorithm.
*Input:* A non-null simple graph $G$ with $|E(G)| \ge 2^{p-3} |V(G)|$.
*Output:* A model of $K_p$ in $G$.
*Running time:* $O(v^2)$."

This is the correctness of the method. The RAM program, which restricts `G` to a subgraph `H`
with `|E(H)| = 2^{p-3} |V(H)|` and runs `p - 2` iterations of Algorithm (6.3), and its `O(ν²)` time
bound are `GM13.algorithm_6_4` in `Results.lean`. -/
theorem algorithm_6_4_correct [Nonempty β] {G : Digraph α β} {p : ℕ}
    (hp : 1 ≤ p) (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty)
    (hsimple : IsSimpleGraph G.toGraph)
    (hedges : 2 ^ (p - 3) * G.vertexSet.ncard ≤ G.edgeSet.ncard) :
    HasGraphModel (GM16.completeGraph p) G.toGraph := by
  have hedges' : p ≥ 2 → 2 ^ (p - 2) * G.vertexSet.ncard ≤ 2 * G.edgeSet.ncard := by
    intro hp2
    by_cases hp2_eq : p = 2
    · subst hp2_eq
      change 1 * G.vertexSet.ncard ≤ G.edgeSet.ncard at hedges
      change 1 * G.vertexSet.ncard ≤ 2 * G.edgeSet.ncard
      omega
    · have hp3 : 3 ≤ p := by omega
      have hpow : 2 ^ (p - 2) = 2 * 2 ^ (p - 3) := by
        have heq : p - 2 = (p - 3) + 1 := by omega
        rw [heq, Nat.pow_succ, Nat.mul_comm]
      rw [hpow, Nat.mul_assoc]
      omega
  obtain ⟨sub, hsub, hconn, hdisj, hadj_all⟩ :=
    exists_subgraphs_algorithm_6_4 hp hfin hne hsimple hedges'
  refine hasGraphModel_completeGraph_of_connected_subgraphs hsub hconn hdisj (fun i j hlt => ?_)
  rcases (hconn j).1 with ⟨v, hvj⟩
  rcases hadj_all i j hlt v hvj with ⟨u, hui, e, heG, hlink⟩
  refine ⟨e, heG, ?_⟩
  rcases hlink with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨hvj, hui⟩
  · exact Or.inl ⟨hui, hvj⟩

/-- **Graph Minors XIII, (6.4)** (pages 86–87): mathematical statement of Algorithm (6.4). -/
theorem theorem_6_4_proof [Nonempty β] {G : Digraph α β} {p : ℕ}
    (hp : 1 ≤ p) (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty)
    (hsimple : IsSimpleGraph G.toGraph)
    (hedges : 2 ^ (p - 3) * G.vertexSet.ncard ≤ G.edgeSet.ncard) :
    HasGraphModel (GM16.completeGraph p) G.toGraph := by
  have hp_pos : 1 ≤ p := hp
  have hne_V : G.vertexSet.Nonempty := hne
  exact algorithm_6_4_correct hp_pos hfin hne_V hsimple hedges
/-- If every edge of `S` not in `S'` has head `u` and tail `v`, and `S'` contains an edge `e_conn`
with head `u` and tail `v`, then any walk in `S.toGraph` can be rerouted in `S'.toGraph`. -/
lemma GraphWalk.of_replace_parallel {S S' : Digraph α β} {u v : α} {e_conn : β}
    (hV : S.vertexSet ⊆ S'.vertexSet)
    (hhead : ∀ e ∈ S.edgeSet, e ∈ S'.edgeSet → S'.head e = S.head e)
    (htail : ∀ e ∈ S.edgeSet, e ∈ S'.edgeSet → S'.tail e = S.tail e)
    (he_conn : e_conn ∈ S'.edgeSet ∧ S'.head e_conn = u ∧ S'.tail e_conn = v)
    (hpar : ∀ e ∈ S.edgeSet, e ∉ S'.edgeSet → S.head e = u ∧ S.tail e = v)
    {x y : α} (W : GraphWalk S.toGraph x y) :
    Nonempty (GraphWalk S'.toGraph x y) := by
  induction W with
  | nil hx => exact ⟨.nil (hV hx)⟩
  | @cons x y z e hlink rest ih =>
    rcases ih with ⟨W'⟩
    have heS : e ∈ S.edgeSet := hlink.1
    by_cases heS' : e ∈ S'.edgeSet
    · have hlink' : S'.toGraph.IsLink e x y := by
        refine ⟨heS', ?_⟩
        rw [hhead e heS heS', htail e heS heS']
        exact hlink.2
      exact ⟨.cons hlink' W'⟩
    · have hht := hpar e heS heS'
      have hlink' : S'.toGraph.IsLink e_conn x y := by
        refine ⟨he_conn.1, ?_⟩
        rw [he_conn.2.1, he_conn.2.2, ← hht.1, ← hht.2]
        exact hlink.2
      exact ⟨.cons hlink' W'⟩

/-- If `U.ncard < P.ncard` for finite sets `P` and `U`, there exists an element of `P` not in `U`. -/
lemma exists_mem_sdiff_of_ncard_lt {P U : Set β} (hP_fin : P.Finite) (hU_fin : U.Finite)
    (hlt : U.ncard < P.ncard) : ∃ e ∈ P, e ∉ U := by
  have hPU_lt : (P ∩ U).ncard < P.ncard :=
    lt_of_le_of_lt (ncard_le_ncard inter_subset_right hU_fin) hlt
  have hne : (P \ U).Nonempty := by
    rw [nonempty_iff_ne_empty]
    intro hemp
    have hsub : P ⊆ P ∩ U := fun e he => ⟨he, by_contra (fun h => hemp.subset ⟨he, h⟩)⟩
    have hle := ncard_le_ncard hsub (hP_fin.inter_of_left _)
    omega
  rcases hne with ⟨e, heP, heNotU⟩
  exact ⟨e, heP, heNotU⟩

/-- Deleting a loop `e₀` at `u` when `G` has `> δ` loops at `u` preserves the `δ`-folio of `G`
relative to any `Z ⊆ V(G)` (Graph Minors XIII, Section 6, Step (1) of (6.5), page 87). -/
lemma hasSameDeltaFolioRel_delete_redundant_loop {G : Digraph α β} {Z : Set α} {δ : ℕ}
    {u : α} {e₀ : β}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet)
    (_he₀ : e₀ ∈ G.edgeSet) (hloop₀ : G.head e₀ = u ∧ G.tail e₀ = u)
    (hmany : δ < ({e ∈ G.edgeSet | G.head e = u ∧ G.tail e = u}).ncard) :
    HasSameDeltaFolioRel G (G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})) δ Z := by
  let G' : Digraph α β := G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})
  have hG'_sub : G'.IsSubdigraph G := G.subdigraphOf_isSubdigraph _ _
  have hG'V : G'.vertexSet = G.vertexSet := inter_self _
  have hG'E : G'.edgeSet = G.edgeSet \ {e₀} := by
    ext e
    simp only [G', Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
    exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, G.head_mem he, G.tail_mem he⟩⟩
  refine ⟨hZ, hG'V.symm ▸ hZ, fun k v hvG hvG' hinj hrange => ?_⟩
  ext H
  simp only [RootedDigraph.deltaFolio, mem_ofPred_eq, RootedDigraph.InDeltaFolio,
    RootedDigraph.InFolio]
  refine ⟨fun ⟨⟨hHfin, vMap, eMap, hMod⟩, hHdet⟩ => ⟨⟨hHfin, ?_⟩, hHdet⟩,
    fun ⟨⟨hHfin, vMap, eMap, hMod⟩, hHdet⟩ => ⟨⟨hHfin, vMap, eMap, {
      sub_of_mem := fun x hx => (hMod.sub_of_mem hx).trans hG'_sub
      connected_of_mem := fun x hx => hMod.connected_of_mem hx
      disjoint_of_ne := fun x y hx hy hne => hMod.disjoint_of_ne hx hy hne
      edge_mem := fun e he => hG'_sub.edgeSet_subset (hMod.edge_mem he)
      head_tail_mem := fun e he => hMod.head_tail_mem he
      loop_not_mem := fun e he hloop => hMod.loop_not_mem he hloop
      eMap_injOn := hMod.eMap_injOn
      root_mem := hMod.root_mem
    }⟩, hHdet⟩⟩
  -- Forward direction: convert model `(vMap, eMap)` in `G` to a model in `G'`
  let L_u : Set β := {e ∈ G.edgeSet | G.head e = u ∧ G.tail e = u}
  have hLu_fin : L_u.Finite := hfin.finite_E.subset (sep_subset _ _)
  have hmany' : δ < L_u.ncard := hmany
  let U : Set β := eMap '' H.digraph.edgeSet
  have hU_fin : U.Finite := hHfin.finite_E.image _
  have hHE_le : H.digraph.edgeSet.ncard ≤ δ := le_trans (le_max_left _ _) hHdet
  have hU_le : U.ncard ≤ δ := le_trans (ncard_image_le hHfin.finite_E) hHE_le
  -- Choose a replacement loop `e₁ ∈ L_u \ U` if `e₀ ∈ U`
  have hex_e₁ : e₀ ∈ U → ∃ e₁ ∈ L_u, e₁ ≠ e₀ ∧ e₁ ∉ U := by
    intro he₀U
    rcases exists_mem_sdiff_of_ncard_lt hLu_fin hU_fin (lt_of_le_of_lt hU_le hmany') with
      ⟨e₁, he₁L, he₁NotU⟩
    exact ⟨e₁, he₁L, fun h => he₁NotU (h ▸ he₀U), he₁NotU⟩
  by_cases he₀U : e₀ ∈ U
  · rcases hex_e₁ he₀U with ⟨e₁, he₁L, he₁_ne, he₁NotU⟩
    let eMap' (f : ℕ) : β := if eMap f = e₀ then e₁ else eMap f
    let vMap₁ (x : ℕ) : Digraph α β :=
      (vMap x).subdigraphOf (vMap x).vertexSet ((vMap x).edgeSet \ {e₀})
    let vMap' (x : ℕ) : Digraph α β :=
      (vMap₁ x).subdigraphOf (vMap₁ x).vertexSet ((vMap₁ x).edgeSet \ {e₁})
    have hvMap₁_V (x : ℕ) : (vMap₁ x).vertexSet = (vMap x).vertexSet := inter_self _
    have hvMap₁_E (x : ℕ) : (vMap₁ x).edgeSet = (vMap x).edgeSet \ {e₀} := by
      ext e
      simp only [vMap₁, Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, (vMap x).head_mem he, (vMap x).tail_mem he⟩⟩
    have hvMap'_V (x : ℕ) : (vMap' x).vertexSet = (vMap x).vertexSet := by
      change (vMap₁ x).vertexSet ∩ (vMap₁ x).vertexSet = (vMap x).vertexSet
      rw [inter_self, hvMap₁_V]
    have hvMap'_E (x : ℕ) : (vMap' x).edgeSet = ((vMap x).edgeSet \ {e₀}) \ {e₁} := by
      ext e
      simp only [vMap', Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      refine ⟨fun h => ?_, fun ⟨⟨he, hne0⟩, hne1⟩ => ?_⟩
      · have he1 : e ∈ (vMap₁ x).edgeSet := h.1.1
        rw [hvMap₁_E] at he1
        exact ⟨he1, h.1.2.2⟩
      · have he1 : e ∈ (vMap₁ x).edgeSet := by rw [hvMap₁_E]; exact ⟨he, hne0⟩
        exact ⟨⟨he1, he1, hne1⟩, (vMap₁ x).head_mem he1, (vMap₁ x).tail_mem he1⟩
    refine ⟨vMap', eMap', {
      sub_of_mem := fun x hx => {
        vertexSet_subset := by
          rw [hvMap'_V, hG'V]; exact (hMod.sub_of_mem hx).vertexSet_subset
        edgeSet_subset := by
          rw [hvMap'_E, hG'E]
          rintro e ⟨⟨he, hne0⟩, _⟩
          exact ⟨(hMod.sub_of_mem hx).edgeSet_subset he, hne0⟩
        head_eq := fun e he => by
          rw [hvMap'_E] at he
          exact (hMod.sub_of_mem hx).head_eq he.1.1
        tail_eq := fun e he => by
          rw [hvMap'_E] at he
          exact (hMod.sub_of_mem hx).tail_eq he.1.1
      }
      connected_of_mem := fun x hx => by
        have hloop_e₀ : e₀ ∈ (vMap x).edgeSet → (vMap x).head e₀ = (vMap x).tail e₀ := by
          intro he
          rw [(hMod.sub_of_mem hx).head_eq he, (hMod.sub_of_mem hx).tail_eq he, hloop₀.1, hloop₀.2]
        have hloop_e₁ : e₁ ∈ (vMap₁ x).edgeSet → (vMap₁ x).head e₁ = (vMap₁ x).tail e₁ := by
          intro he
          rw [hvMap₁_E] at he
          change (vMap x).head e₁ = (vMap x).tail e₁
          rw [(hMod.sub_of_mem hx).head_eq he.1, (hMod.sub_of_mem hx).tail_eq he.1, he₁L.2.1, he₁L.2.2]
        rcases hMod.connected_of_mem hx with ⟨hne, hconn⟩
        refine ⟨hvMap'_V x ▸ hne, fun a ha b hb => ?_⟩
        rw [hvMap'_V x] at ha hb
        rcases hconn a ha b hb with ⟨W⟩
        rcases GraphWalk.of_delete_loop hloop_e₀ W with ⟨W₁⟩
        exact GraphWalk.of_delete_loop hloop_e₁ W₁
      disjoint_of_ne := fun x y hx hy hne => by
        rw [hvMap'_V, hvMap'_V]; exact hMod.disjoint_of_ne hx hy hne
      edge_mem := fun f hf => by
        rw [hG'E]
        dsimp [eMap']
        split_ifs with hfe₀
        · exact ⟨he₁L.1, he₁_ne⟩
        · exact ⟨hMod.edge_mem hf, hfe₀⟩
      head_tail_mem := fun f hf => by
        rw [hvMap'_V, hvMap'_V]
        change G.head (eMap' f) ∈ _ ∧ G.tail (eMap' f) ∈ _
        dsimp [eMap']
        split_ifs with hfe₀
        · have hht := hMod.head_tail_mem hf
          rw [hfe₀, hloop₀.1, hloop₀.2] at hht
          rw [he₁L.2.1, he₁L.2.2]
          exact hht
        · exact hMod.head_tail_mem hf
      loop_not_mem := fun f hf hloop he_in => by
        rw [hvMap'_E] at he_in
        dsimp [eMap'] at he_in
        split_ifs at he_in with hfe₀
        · exact he_in.2 rfl
        · exact hMod.loop_not_mem hf hloop he_in.1.1
      eMap_injOn := by
        intro f₁ hf₁ f₂ hf₂ heq
        dsimp [eMap'] at heq
        split_ifs at heq with h1 h2 h2
        · exact hMod.eMap_injOn hf₁ hf₂ (h1.trans h2.symm)
        · exact False.elim (he₁NotU ⟨f₂, hf₂, heq.symm⟩)
        · exact False.elim (he₁NotU ⟨f₁, hf₁, heq⟩)
        · exact hMod.eMap_injOn hf₁ hf₂ heq
      root_mem := fun i => by
        rw [hvMap'_V]; exact hMod.root_mem i
    }⟩
  · -- `e₀ ∉ U`: keep `eMap` unchanged and delete `e₀` from each `vMap x`
    let vMap' (x : ℕ) : Digraph α β :=
      (vMap x).subdigraphOf (vMap x).vertexSet ((vMap x).edgeSet \ {e₀})
    have hvMap'_V (x : ℕ) : (vMap' x).vertexSet = (vMap x).vertexSet := inter_self _
    have hvMap'_E (x : ℕ) : (vMap' x).edgeSet = (vMap x).edgeSet \ {e₀} := by
      ext e
      simp only [vMap', Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
      exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, (vMap x).head_mem he, (vMap x).tail_mem he⟩⟩
    refine ⟨vMap', eMap, {
      sub_of_mem := fun x hx => {
        vertexSet_subset := by rw [hvMap'_V, hG'V]; exact (hMod.sub_of_mem hx).vertexSet_subset
        edgeSet_subset := by
          rw [hvMap'_E, hG'E]
          rintro e ⟨he, hne0⟩
          exact ⟨(hMod.sub_of_mem hx).edgeSet_subset he, hne0⟩
        head_eq := fun e he => by rw [hvMap'_E] at he; exact (hMod.sub_of_mem hx).head_eq he.1
        tail_eq := fun e he => by rw [hvMap'_E] at he; exact (hMod.sub_of_mem hx).tail_eq he.1
      }
      connected_of_mem := fun x hx => by
        have hloop_e₀ : e₀ ∈ (vMap x).edgeSet → (vMap x).head e₀ = (vMap x).tail e₀ := by
          intro he
          rw [(hMod.sub_of_mem hx).head_eq he, (hMod.sub_of_mem hx).tail_eq he, hloop₀.1, hloop₀.2]
        rcases hMod.connected_of_mem hx with ⟨hne, hconn⟩
        refine ⟨hvMap'_V x ▸ hne, fun a ha b hb => ?_⟩
        rw [hvMap'_V x] at ha hb
        rcases hconn a ha b hb with ⟨W⟩
        exact GraphWalk.of_delete_loop hloop_e₀ W
      disjoint_of_ne := fun x y hx hy hne => by
        rw [hvMap'_V, hvMap'_V]; exact hMod.disjoint_of_ne hx hy hne
      edge_mem := fun f hf => by
        rw [hG'E]
        exact ⟨hMod.edge_mem hf, fun h => he₀U ⟨f, hf, h⟩⟩
      head_tail_mem := fun f hf => by
        rw [hvMap'_V, hvMap'_V]; exact hMod.head_tail_mem hf
      loop_not_mem := fun f hf hloop he_in => by
        rw [hvMap'_E] at he_in
        exact hMod.loop_not_mem hf hloop he_in.1
      eMap_injOn := hMod.eMap_injOn
      root_mem := fun i => by rw [hvMap'_V]; exact hMod.root_mem i
    }⟩

/-- Deleting a parallel edge `e₀` with head `u` and tail `v` (`u ≠ v`) when `G` has `> δ + 1`
edges with head `u` and tail `v` preserves the `δ`-folio of `G` relative to any `Z ⊆ V(G)`
(Graph Minors XIII, Section 6, Step (1) of (6.5), page 87). -/
lemma hasSameDeltaFolioRel_delete_redundant_parallel {G : Digraph α β} {Z : Set α} {δ : ℕ}
    {u v : α} {e₀ : β}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet)
    (_he₀ : e₀ ∈ G.edgeSet) (hpar₀ : G.head e₀ = u ∧ G.tail e₀ = v) (_hne_uv : u ≠ v)
    (hmany : δ + 1 < ({e ∈ G.edgeSet | G.head e = u ∧ G.tail e = v}).ncard) :
    HasSameDeltaFolioRel G (G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})) δ Z := by
  let G' : Digraph α β := G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})
  have hG'_sub : G'.IsSubdigraph G := G.subdigraphOf_isSubdigraph _ _
  have hG'V : G'.vertexSet = G.vertexSet := inter_self _
  have hG'E : G'.edgeSet = G.edgeSet \ {e₀} := by
    ext e
    simp only [G', Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
    exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, G.head_mem he, G.tail_mem he⟩⟩
  refine ⟨hZ, hG'V.symm ▸ hZ, fun k r hrG hrG' hinj hrange => ?_⟩
  ext H
  simp only [RootedDigraph.deltaFolio, mem_ofPred_eq, RootedDigraph.InDeltaFolio,
    RootedDigraph.InFolio]
  refine ⟨fun ⟨⟨hHfin, vMap, eMap, hMod⟩, hHdet⟩ => ⟨⟨hHfin, ?_⟩, hHdet⟩,
    fun ⟨⟨hHfin, vMap, eMap, hMod⟩, hHdet⟩ => ⟨⟨hHfin, vMap, eMap, {
      sub_of_mem := fun x hx => (hMod.sub_of_mem hx).trans hG'_sub
      connected_of_mem := fun x hx => hMod.connected_of_mem hx
      disjoint_of_ne := fun x y hx hy hne => hMod.disjoint_of_ne hx hy hne
      edge_mem := fun e he => hG'_sub.edgeSet_subset (hMod.edge_mem he)
      head_tail_mem := fun e he => hMod.head_tail_mem he
      loop_not_mem := fun e he hloop => hMod.loop_not_mem he hloop
      eMap_injOn := hMod.eMap_injOn
      root_mem := hMod.root_mem
    }⟩, hHdet⟩⟩
  let P_uv : Set β := {e ∈ G.edgeSet | G.head e = u ∧ G.tail e = v}
  have hP_fin : P_uv.Finite := hfin.finite_E.subset (sep_subset _ _)
  have hmany' : δ + 1 < P_uv.ncard := hmany
  let U : Set β := eMap '' H.digraph.edgeSet
  have hU_fin : U.Finite := hHfin.finite_E.image _
  have hHE_le : H.digraph.edgeSet.ncard ≤ δ := le_trans (le_max_left _ _) hHdet
  have hU_le : U.ncard ≤ δ := le_trans (ncard_image_le hHfin.finite_E) hHE_le
  have hinsU_lt : (insert e₀ U).ncard < P_uv.ncard := by
    have h1 : (insert e₀ U).ncard ≤ U.ncard + 1 := ncard_insert_le _ _
    omega
  rcases exists_mem_sdiff_of_ncard_lt hP_fin (hU_fin.insert _) hinsU_lt with
    ⟨e_mod, he_modP, he_modNotIns⟩
  have he_mod_ne₀ : e_mod ≠ e₀ := fun h => he_modNotIns (Or.inl h)
  have he_modNotU : e_mod ∉ U := fun h => he_modNotIns (Or.inr h)
  let eMap' (f : ℕ) : β := if eMap f = e₀ then e_mod else eMap f
  let U' : Set β := eMap' '' H.digraph.edgeSet
  have hU'_fin : U'.Finite := hHfin.finite_E.image _
  have hU'_le : U'.ncard ≤ δ := le_trans (ncard_image_le hHfin.finite_E) hHE_le
  have hinsU'_lt : (insert e₀ U').ncard < P_uv.ncard := by
    have h1 : (insert e₀ U').ncard ≤ U'.ncard + 1 := ncard_insert_le _ _
    omega
  rcases exists_mem_sdiff_of_ncard_lt hP_fin (hU'_fin.insert _) hinsU'_lt with
    ⟨e_conn, he_connP, he_connNotIns⟩
  have he_conn_ne₀ : e_conn ≠ e₀ := fun h => he_connNotIns (Or.inl h)
  have he_connNotU' : e_conn ∉ U' := fun h => he_connNotIns (Or.inr h)
  have he_connG' : e_conn ∈ G'.edgeSet := by
    rw [hG'E]; exact ⟨he_connP.1, he_conn_ne₀⟩
  let vMap' (x : ℕ) : Digraph α β :=
    if u ∈ (vMap x).vertexSet ∧ v ∈ (vMap x).vertexSet then
      G'.subdigraphOf (vMap x).vertexSet (insert e_conn (((vMap x).edgeSet \ {e₀}) \ {e_mod}))
    else
      G'.subdigraphOf (vMap x).vertexSet (((vMap x).edgeSet \ {e₀}) \ {e_mod})
  have hvMap'_sub (x : ℕ) : (vMap' x).IsSubdigraph G' := by
    dsimp [vMap']
    split_ifs <;> exact G'.subdigraphOf_isSubdigraph _ _
  have hvMap'_V {x : ℕ} (hx : x ∈ H.digraph.vertexSet) :
      (vMap' x).vertexSet = (vMap x).vertexSet := by
    have hsubV : (vMap x).vertexSet ⊆ G'.vertexSet := by
      rw [hG'V]; exact (hMod.sub_of_mem hx).vertexSet_subset
    dsimp [vMap']
    split_ifs <;> exact inter_eq_self_of_subset_right hsubV
  have hvMap'_E_pos {x : ℕ} (hx : x ∈ H.digraph.vertexSet)
      (huv : u ∈ (vMap x).vertexSet ∧ v ∈ (vMap x).vertexSet) :
      (vMap' x).edgeSet = insert e_conn (((vMap x).edgeSet \ {e₀}) \ {e_mod}) := by
    dsimp [vMap']
    simp only [huv, and_self, ↓reduceIte]
    ext e
    simp only [Digraph.subdigraphOf, mem_inter_iff, mem_insert_iff, mem_sdiff,
      mem_singleton_iff, mem_ofPred_eq]
    refine ⟨fun h => h.1.2, ?_⟩
    rintro (rfl | ⟨⟨he, hne0⟩, hnemod⟩)
    · refine ⟨⟨he_connG', Or.inl rfl⟩, ?_, ?_⟩
      · rw [hG'_sub.head_eq he_connG', he_connP.2.1]; exact huv.1
      · rw [hG'_sub.tail_eq he_connG', he_connP.2.2]; exact huv.2
    · have heG' : e ∈ G'.edgeSet := by
        rw [hG'E]; exact ⟨(hMod.sub_of_mem hx).edgeSet_subset he, hne0⟩
      refine ⟨⟨heG', Or.inr ⟨⟨he, hne0⟩, hnemod⟩⟩, ?_, ?_⟩
      · rw [hG'_sub.head_eq heG', ← (hMod.sub_of_mem hx).head_eq he]
        exact (vMap x).head_mem he
      · rw [hG'_sub.tail_eq heG', ← (hMod.sub_of_mem hx).tail_eq he]
        exact (vMap x).tail_mem he
  have hvMap'_E_neg {x : ℕ} (hx : x ∈ H.digraph.vertexSet)
      (huv : ¬ (u ∈ (vMap x).vertexSet ∧ v ∈ (vMap x).vertexSet)) :
      (vMap' x).edgeSet = (vMap x).edgeSet := by
    dsimp [vMap']
    simp only [huv, ↓reduceIte]
    ext e
    simp only [Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
    refine ⟨fun h => h.1.2.1.1, fun he => ?_⟩
    have hnot_uv : ∀ e' ∈ (vMap x).edgeSet, ¬ (G.head e' = u ∧ G.tail e' = v) := by
      rintro e' he' ⟨hhu, htv⟩
      apply huv
      rw [← hhu, ← htv, ← (hMod.sub_of_mem hx).head_eq he', ← (hMod.sub_of_mem hx).tail_eq he']
      exact ⟨(vMap x).head_mem he', (vMap x).tail_mem he'⟩
    have hne0 : e ≠ e₀ := fun h => hnot_uv e he (h ▸ hpar₀)
    have hnemod : e ≠ e_mod := fun h => hnot_uv e he (h ▸ he_modP.2)
    have heG' : e ∈ G'.edgeSet := by
      rw [hG'E]; exact ⟨(hMod.sub_of_mem hx).edgeSet_subset he, hne0⟩
    refine ⟨⟨heG', ⟨he, hne0⟩, hnemod⟩, ?_, ?_⟩
    · rw [hG'_sub.head_eq heG', ← (hMod.sub_of_mem hx).head_eq he]
      exact (vMap x).head_mem he
    · rw [hG'_sub.tail_eq heG', ← (hMod.sub_of_mem hx).tail_eq he]
      exact (vMap x).tail_mem he
  refine ⟨vMap', eMap', {
    sub_of_mem := fun x _ => hvMap'_sub x
    connected_of_mem := fun x hx => by
      rcases hMod.connected_of_mem hx with ⟨hne, hconn⟩
      refine ⟨(hvMap'_V hx).symm ▸ hne, fun a ha b hb => ?_⟩
      rw [hvMap'_V hx] at ha hb
      rcases hconn a ha b hb with ⟨W⟩
      have hhead_eq : ∀ e ∈ (vMap x).edgeSet, e ∈ (vMap' x).edgeSet →
          (vMap' x).head e = (vMap x).head e := by
        intro e he he'
        rw [((hvMap'_sub x).trans hG'_sub).head_eq he', (hMod.sub_of_mem hx).head_eq he]
      have htail_eq : ∀ e ∈ (vMap x).edgeSet, e ∈ (vMap' x).edgeSet →
          (vMap' x).tail e = (vMap x).tail e := by
        intro e he he'
        rw [((hvMap'_sub x).trans hG'_sub).tail_eq he', (hMod.sub_of_mem hx).tail_eq he]
      by_cases huv : u ∈ (vMap x).vertexSet ∧ v ∈ (vMap x).vertexSet
      · have he_conn_in : e_conn ∈ (vMap' x).edgeSet := by
          rw [hvMap'_E_pos hx huv]; exact Or.inl rfl
        have he_conn_ht : e_conn ∈ (vMap' x).edgeSet ∧
            (vMap' x).head e_conn = u ∧ (vMap' x).tail e_conn = v := by
          refine ⟨he_conn_in, ?_, ?_⟩
          · rw [((hvMap'_sub x).trans hG'_sub).head_eq he_conn_in, he_connP.2.1]
          · rw [((hvMap'_sub x).trans hG'_sub).tail_eq he_conn_in, he_connP.2.2]
        have hpar : ∀ e ∈ (vMap x).edgeSet, e ∉ (vMap' x).edgeSet →
            (vMap x).head e = u ∧ (vMap x).tail e = v := by
          intro e he heNot
          rw [hvMap'_E_pos hx huv] at heNot
          have h0mod : e = e₀ ∨ e = e_mod := by
            by_contra hne_both
            have hne0 : e ≠ e₀ := fun h => hne_both (Or.inl h)
            have hnemod : e ≠ e_mod := fun h => hne_both (Or.inr h)
            exact heNot (Or.inr ⟨⟨he, hne0⟩, hnemod⟩)
          rw [(hMod.sub_of_mem hx).head_eq he, (hMod.sub_of_mem hx).tail_eq he]
          rcases h0mod with rfl | rfl
          · exact hpar₀
          · exact he_modP.2
        exact GraphWalk.of_replace_parallel (hvMap'_V hx).symm.subset hhead_eq htail_eq he_conn_ht hpar W
      · have hsub_xx' : (vMap x).IsSubdigraph (vMap' x) := {
          vertexSet_subset := (hvMap'_V hx).symm.subset
          edgeSet_subset := (hvMap'_E_neg hx huv).symm.subset
          head_eq := fun e he => (hhead_eq e he ((hvMap'_E_neg hx huv).symm ▸ he)).symm
          tail_eq := fun e he => (htail_eq e he ((hvMap'_E_neg hx huv).symm ▸ he)).symm
        }
        exact ⟨hsub_xx'.mapWalk W⟩
    disjoint_of_ne := fun x y hx hy hne => by
      rw [hvMap'_V hx, hvMap'_V hy]; exact hMod.disjoint_of_ne hx hy hne
    edge_mem := fun f hf => by
      rw [hG'E]
      dsimp [eMap']
      split_ifs with hfe₀
      · exact ⟨he_modP.1, he_mod_ne₀⟩
      · exact ⟨hMod.edge_mem hf, hfe₀⟩
    head_tail_mem := fun f hf => by
      have hhh : H.digraph.head f ∈ H.digraph.vertexSet := H.digraph.head_mem hf
      have hht : H.digraph.tail f ∈ H.digraph.vertexSet := H.digraph.tail_mem hf
      rw [hvMap'_V hhh, hvMap'_V hht]
      have heG' : eMap' f ∈ G'.edgeSet := by
        rw [hG'E]; dsimp [eMap']; split_ifs with hfe₀
        · exact ⟨he_modP.1, he_mod_ne₀⟩
        · exact ⟨hMod.edge_mem hf, hfe₀⟩
      rw [hG'_sub.head_eq heG', hG'_sub.tail_eq heG']
      dsimp [eMap']
      split_ifs with hfe₀
      · have hht_mod := hMod.head_tail_mem hf
        rw [hfe₀, hpar₀.1, hpar₀.2] at hht_mod
        rw [he_modP.2.1, he_modP.2.2]
        exact hht_mod
      · exact hMod.head_tail_mem hf
    loop_not_mem := fun f hf hloop he_in => by
      have hhh : H.digraph.head f ∈ H.digraph.vertexSet := H.digraph.head_mem hf
      have heU' : eMap' f ∈ U' := ⟨f, hf, rfl⟩
      have hne_conn : eMap' f ≠ e_conn := fun h => he_connNotU' (h ▸ heU')
      have he_in_sdiff : eMap' f ∈ ((vMap (H.digraph.head f)).edgeSet \ {e₀}) \ {e_mod} := by
        by_cases huv : u ∈ (vMap (H.digraph.head f)).vertexSet ∧ v ∈ (vMap (H.digraph.head f)).vertexSet
        · rw [hvMap'_E_pos hhh huv] at he_in
          rcases he_in with heq | hmem
          · exact False.elim (hne_conn heq)
          · exact hmem
        · rw [hvMap'_E_neg hhh huv] at he_in
          have hnot_uv : ¬ (G.head (eMap' f) = u ∧ G.tail (eMap' f) = v) := by
            rintro ⟨hhu, htv⟩
            apply huv
            rw [← hhu, ← htv, ← (hMod.sub_of_mem hhh).head_eq he_in, ← (hMod.sub_of_mem hhh).tail_eq he_in]
            exact ⟨(vMap (H.digraph.head f)).head_mem he_in, (vMap (H.digraph.head f)).tail_mem he_in⟩
          exact ⟨⟨he_in, fun h => hnot_uv (h ▸ hpar₀)⟩, fun h => hnot_uv (h ▸ he_modP.2)⟩
      dsimp [eMap'] at he_in_sdiff
      split_ifs at he_in_sdiff with hfe₀
      · exact he_in_sdiff.2 rfl
      · exact hMod.loop_not_mem hf hloop he_in_sdiff.1.1
    eMap_injOn := by
      intro f₁ hf₁ f₂ hf₂ heq
      dsimp [eMap'] at heq
      split_ifs at heq with h1 h2 h2
      · exact hMod.eMap_injOn hf₁ hf₂ (h1.trans h2.symm)
      · exact False.elim (he_modNotU ⟨f₂, hf₂, heq.symm⟩)
      · exact False.elim (he_modNotU ⟨f₁, hf₁, heq⟩)
      · exact hMod.eMap_injOn hf₁ hf₂ heq
    root_mem := fun i => by
      rw [hvMap'_V (H.roots_mem i)]; exact hMod.root_mem i
  }⟩

/-- A digraph `H` has bounded multiplicity for `δ`-folios if it has at most `δ` loops at each
vertex and at most `δ + 1` edges with head `u` and tail `v` for all distinct `u, v ∈ V(H)`
(Graph Minors XIII, Section 6, Step (1) of (6.5), page 87). -/
def Digraph.HasBoundedMultiplicity (H : Digraph α β) (δ : ℕ) : Prop :=
  (∀ u ∈ H.vertexSet, ({e ∈ H.edgeSet | H.head e = u ∧ H.tail e = u}).ncard ≤ δ) ∧
  (∀ u ∈ H.vertexSet, ∀ v ∈ H.vertexSet, u ≠ v →
    ({e ∈ H.edgeSet | H.head e = u ∧ H.tail e = v}).ncard ≤ δ + 1)

/-- `HasBoundedMultiplicity` is inherited by subdigraphs of a finite digraph. -/
lemma Digraph.HasBoundedMultiplicity.mono {H H' : Digraph α β} {δ : ℕ}
    (hfin : H.IsFinite) (hbm : H.HasBoundedMultiplicity δ) (hsub : H'.IsSubdigraph H) :
    H'.HasBoundedMultiplicity δ := by
  have hfib_sub (u v : α) :
      {e ∈ H'.edgeSet | H'.head e = u ∧ H'.tail e = v} ⊆
        {e ∈ H.edgeSet | H.head e = u ∧ H.tail e = v} := by
    rintro e ⟨he, hhu, htv⟩
    exact ⟨hsub.edgeSet_subset he, (hsub.head_eq he).symm.trans hhu, (hsub.tail_eq he).symm.trans htv⟩
  refine ⟨fun u hu => ?_, fun u hu v hv hne => ?_⟩
  · exact le_trans (ncard_le_ncard (hfib_sub u u) (hfin.finite_E.subset (sep_subset _ _)))
      (hbm.1 u (hsub.vertexSet_subset hu))
  · exact le_trans (ncard_le_ncard (hfib_sub u v) (hfin.finite_E.subset (sep_subset _ _)))
      (hbm.2 u (hsub.vertexSet_subset hu) v (hsub.vertexSet_subset hv) hne)

/-- Step (1) of Algorithm (6.5) (Graph Minors XIII, page 87): every finite digraph `G` has a
spanning subdigraph `H` with `HasBoundedMultiplicity δ` and the same `δ`-folio relative to `Z`. -/
lemma exists_boundedMultiplicity_subdigraph {G : Digraph α β} {Z : Set α} {δ : ℕ}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) :
    ∃ H : Digraph α β, H.IsSubdigraph G ∧ H.vertexSet = G.vertexSet ∧
      HasSameDeltaFolioRel G H δ Z ∧ H.HasBoundedMultiplicity δ := by
  suffices h : ∀ m, ∀ G : Digraph α β, G.IsFinite → G.edgeSet.ncard ≤ m → Z ⊆ G.vertexSet →
      ∃ H : Digraph α β, H.IsSubdigraph G ∧ H.vertexSet = G.vertexSet ∧
        HasSameDeltaFolioRel G H δ Z ∧ H.HasBoundedMultiplicity δ from
    h G.edgeSet.ncard G hfin le_rfl hZ
  intro m
  induction m with
  | zero =>
    intro G hGfin hle hZG
    refine ⟨G, Digraph.IsSubdigraph.refl G, rfl, HasSameDeltaFolioRel.refl G δ hZG, ?_⟩
    have hsub : ∀ u v, {e ∈ G.edgeSet | G.head e = u ∧ G.tail e = v} ⊆ G.edgeSet :=
      fun _ _ => sep_subset _ _
    refine ⟨fun u _ => ?_, fun u _ v _ _ => ?_⟩
    · have h0 := ncard_le_ncard (hsub u u) hGfin.finite_E; omega
    · have h0 := ncard_le_ncard (hsub u v) hGfin.finite_E; omega
  | succ m ih =>
    intro G hGfin hle hZG
    by_cases hbm : G.HasBoundedMultiplicity δ
    · exact ⟨G, Digraph.IsSubdigraph.refl G, rfl, HasSameDeltaFolioRel.refl G δ hZG, hbm⟩
    · have hnot : (∃ u ∈ G.vertexSet, δ < ({e ∈ G.edgeSet | G.head e = u ∧ G.tail e = u}).ncard) ∨
          (∃ u ∈ G.vertexSet, ∃ v ∈ G.vertexSet, u ≠ v ∧
            δ + 1 < ({e ∈ G.edgeSet | G.head e = u ∧ G.tail e = v}).ncard) := by
        by_contra hneither
        apply hbm
        refine ⟨fun u hu => not_lt.mp (fun hlt => hneither (Or.inl ⟨u, hu, hlt⟩)),
          fun u hu v hv hne => not_lt.mp (fun hlt => hneither (Or.inr ⟨u, hu, v, hv, hne, hlt⟩))⟩
      have hex_step : ∃ e₀ ∈ G.edgeSet,
          HasSameDeltaFolioRel G (G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})) δ Z := by
        rcases hnot with ⟨u, _, hlt⟩ | ⟨u, _, v, _, hne, hlt⟩
        · have hne_set : ({e ∈ G.edgeSet | G.head e = u ∧ G.tail e = u}).Nonempty :=
            nonempty_of_ncard_ne_zero (by omega)
          rcases hne_set with ⟨e₀, he₀G, hloop₀⟩
          exact ⟨e₀, he₀G, hasSameDeltaFolioRel_delete_redundant_loop hGfin hZG he₀G hloop₀ hlt⟩
        · have hne_set : ({e ∈ G.edgeSet | G.head e = u ∧ G.tail e = v}).Nonempty :=
            nonempty_of_ncard_ne_zero (by omega)
          rcases hne_set with ⟨e₀, he₀G, hpar₀⟩
          exact ⟨e₀, he₀G, hasSameDeltaFolioRel_delete_redundant_parallel hGfin hZG he₀G hpar₀ hne hlt⟩
      rcases hex_step with ⟨e₀, he₀G, hsame₀⟩
      let G₁ := G.subdigraphOf G.vertexSet (G.edgeSet \ {e₀})
      have hG₁_sub : G₁.IsSubdigraph G := G.subdigraphOf_isSubdigraph _ _
      have hG₁_V : G₁.vertexSet = G.vertexSet := inter_self _
      have hG₁_E : G₁.edgeSet = G.edgeSet \ {e₀} := by
        ext e
        simp only [G₁, Digraph.subdigraphOf, mem_inter_iff, mem_sdiff, mem_singleton_iff, mem_ofPred_eq]
        exact ⟨fun h => h.1.2, fun ⟨he, hne⟩ => ⟨⟨he, he, hne⟩, G.head_mem he, G.tail_mem he⟩⟩
      have hG₁_fin : G₁.IsFinite :=
        ⟨hGfin.finite_V.subset hG₁_sub.vertexSet_subset, hGfin.finite_E.subset hG₁_sub.edgeSet_subset⟩
      have hG₁_le : G₁.edgeSet.ncard ≤ m := by
        rw [hG₁_E, ncard_sdiff_singleton_of_mem he₀G]
        have hpos : 0 < G.edgeSet.ncard := (ncard_pos hGfin.finite_E).mpr ⟨e₀, he₀G⟩
        omega
      rcases ih G₁ hG₁_fin hG₁_le (hG₁_V.symm ▸ hZG) with ⟨H, hH_sub, hH_V, hsame₁, hH_bm⟩
      exact ⟨H, hH_sub.trans hG₁_sub, hH_V.trans hG₁_V, hsame₀.trans hsame₁, hH_bm⟩

/-- Upper bound on the cardinality of a finite set covered by a finite union of fibers of bounded
intersection cardinality. -/
lemma ncard_le_mul_ncard_of_subset_biUnion {γ : Type*} {I : Set γ} {F : γ → Set β} {S : Set β}
    {c : ℕ} (hI_fin : I.Finite) (hS_fin : S.Finite)
    (hF_le : ∀ i ∈ I, (S ∩ F i).ncard ≤ c)
    (hsub : S ⊆ ⋃ i ∈ I, F i) :
    S.ncard ≤ c * I.ncard := by
  suffices h : ∀ m, ∀ T : Set γ, T.Finite → T.ncard = m → ∀ S : Set β, S.Finite →
      (∀ i ∈ T, (S ∩ F i).ncard ≤ c) → S ⊆ ⋃ i ∈ T, F i → S.ncard ≤ c * T.ncard from
    h I.ncard I hI_fin rfl S hS_fin hF_le hsub
  intro m
  induction m with
  | zero =>
    intro T hT_fin hT0 S _ _ hsub_emp
    have hT_emp : T = ∅ := (ncard_eq_zero hT_fin).mp hT0
    subst hT_emp
    have hS_emp : S = ∅ := subset_eq_empty (by simpa using hsub_emp) rfl
    simp [hS_emp]
  | succ m ih =>
    intro T hT_fin hTm S hS_fin hF_le hsub_T
    have hT_ne : T.Nonempty := nonempty_of_ncard_ne_zero (by omega)
    rcases hT_ne with ⟨a, haT⟩
    let T' : Set γ := T \ {a}
    have hT'_fin : T'.Finite := hT_fin.sdiff
    have hT'_card : T'.ncard = m := by
      have h := ncard_sdiff_singleton_of_mem haT
      change T'.ncard = T.ncard - 1 at h
      omega
    have hsub' : S \ F a ⊆ ⋃ i ∈ T', F i := by
      intro x ⟨hxS, hxNotFa⟩
      rcases mem_iUnion₂.mp (hsub_T hxS) with ⟨i, hiT, hxi⟩
      by_cases hia : i = a
      · exact False.elim (hxNotFa (hia ▸ hxi))
      · exact mem_iUnion₂.mpr ⟨i, ⟨hiT, hia⟩, hxi⟩
    have hih := ih T' hT'_fin hT'_card (S \ F a) hS_fin.sdiff
      (fun i hiT' => le_trans (ncard_le_ncard (inter_subset_inter_left _ sdiff_subset) (hS_fin.inter_of_left _))
        (hF_le i hiT'.1))
      hsub'
    have hS_eq : S = (S ∩ F a) ∪ (S \ F a) := (inter_union_sdiff S (F a)).symm
    have hle_union : S.ncard ≤ (S ∩ F a).ncard + (S \ F a).ncard := by
      conv_lhs => rw [hS_eq]
      exact ncard_union_le _ _
    have hFa : (S ∩ F a).ncard ≤ c := hF_le a haT
    rw [hTm, Nat.mul_succ, ← hT'_card]
    omega

/-- Step (3) of Algorithm (6.5) (Graph Minors XIII, page 87): every finite digraph `G_i` with
`HasBoundedMultiplicity δ` has a spanning subdigraph `J_i` whose underlying undirected graph is
simple and satisfies `|E(G_i)| ≤ δ |V(J_i)| + 2(δ + 1) |E(J_i)|`. -/
lemma exists_simple_underlying_subdigraph {G_i : Digraph α β} {δ : ℕ}
    (hfin : G_i.IsFinite) (hbm : G_i.HasBoundedMultiplicity δ) :
    ∃ J_i : Digraph α β, J_i.IsSubdigraph G_i ∧ J_i.vertexSet = G_i.vertexSet ∧
      IsSimpleGraph J_i.toGraph ∧
      G_i.edgeSet.ncard ≤ δ * J_i.vertexSet.ncard + 2 * (δ + 1) * J_i.edgeSet.ncard := by
  let L : Set β := {e ∈ G_i.edgeSet | G_i.head e = G_i.tail e}
  let NL : Set β := {e ∈ G_i.edgeSet | G_i.head e ≠ G_i.tail e}
  have hL_fin : L.Finite := hfin.finite_E.subset (sep_subset _ _)
  have hNL_fin : NL.Finite := hfin.finite_E.subset (sep_subset _ _)
  let endsOf (e : β) : Sym2 α := s(G_i.head e, G_i.tail e)
  let E_simp : Set β := range (fun q : ↑(endsOf '' NL) => Classical.choose q.2)
  have hE_simp_sub : E_simp ⊆ NL := by
    rintro e ⟨q, rfl⟩
    exact (Classical.choose_spec q.2).1
  let J_i : Digraph α β := G_i.subdigraphOf G_i.vertexSet E_simp
  have hJi_sub : J_i.IsSubdigraph G_i := G_i.subdigraphOf_isSubdigraph _ _
  have hJi_V : J_i.vertexSet = G_i.vertexSet := inter_self _
  have hJi_E : J_i.edgeSet = E_simp := by
    ext e
    simp only [J_i, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
    refine ⟨fun h => h.1.2, fun he => ?_⟩
    have heG : e ∈ G_i.edgeSet := (hE_simp_sub he).1
    exact ⟨⟨heG, he⟩, G_i.head_mem heG, G_i.tail_mem heG⟩
  refine ⟨J_i, hJi_sub, hJi_V, ?_, ?_⟩
  · -- `IsSimpleGraph J_i.toGraph`
    refine ⟨fun e he v ⟨_, hloop⟩ => ?_, fun e₁ he₁ e₂ he₂ x y h1 h2 => ?_⟩
    · change e ∈ J_i.edgeSet at he
      rw [hJi_E] at he
      have heNL : e ∈ NL := hE_simp_sub he
      rcases hloop with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact heNL.2 (h1.trans h2.symm)
      · exact heNL.2 (h1.trans h2.symm)
    · have he1 : e₁ ∈ E_simp := hJi_E ▸ he₁
      have he2 : e₂ ∈ E_simp := hJi_E ▸ he₂
      rcases he1 with ⟨q₁, rfl⟩
      rcases he2 with ⟨q₂, rfl⟩
      have hq1 := (Classical.choose_spec q₁.2).2
      have hq2 := (Classical.choose_spec q₂.2).2
      have hends1 : endsOf (Classical.choose q₁.2) = s(x, y) := by
        dsimp [endsOf]
        rcases h1.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      have hends2 : endsOf (Classical.choose q₂.2) = s(x, y) := by
        dsimp [endsOf]
        rcases h2.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rfl
        · exact Sym2.eq_swap
      have hq_eq : q₁ = q₂ := Subtype.ext (hq1.symm.trans (hends1.trans (hends2.symm.trans hq2)))
      rw [hq_eq]
  · -- Cardinality bound: `|E(G_i)| ≤ δ |V(J_i)| + 2(δ + 1) |E(J_i)|`
    have hL_bound : L.ncard ≤ δ * G_i.vertexSet.ncard := by
      let F_L (u : α) : Set β := {e ∈ G_i.edgeSet | G_i.head e = u ∧ G_i.tail e = u}
      refine ncard_le_mul_ncard_of_subset_biUnion (F := F_L) hfin.finite_V hL_fin (fun u hu => ?_) (fun e he => ?_)
      · exact le_trans (ncard_le_ncard inter_subset_right (hfin.finite_E.subset (sep_subset _ _))) (hbm.1 u hu)
      · exact mem_iUnion₂.mpr ⟨G_i.head e, G_i.head_mem he.1, he.1, rfl, he.2.symm⟩
    have hNL_bound : NL.ncard ≤ 2 * (δ + 1) * E_simp.ncard := by
      let F_NL (e₀ : β) : Set β :=
        {e ∈ G_i.edgeSet | G_i.head e = G_i.head e₀ ∧ G_i.tail e = G_i.tail e₀} ∪
          {e ∈ G_i.edgeSet | G_i.head e = G_i.tail e₀ ∧ G_i.tail e = G_i.head e₀}
      have hE_simp_fin : E_simp.Finite := hNL_fin.subset hE_simp_sub
      refine ncard_le_mul_ncard_of_subset_biUnion (F := F_NL) hE_simp_fin hNL_fin (fun e₀ he₀ => ?_) (fun e he => ?_)
      · have he₀NL : e₀ ∈ NL := hE_simp_sub he₀
        have hu : G_i.head e₀ ∈ G_i.vertexSet := G_i.head_mem he₀NL.1
        have hv : G_i.tail e₀ ∈ G_i.vertexSet := G_i.tail_mem he₀NL.1
        have h1 : ({e ∈ G_i.edgeSet | G_i.head e = G_i.head e₀ ∧ G_i.tail e = G_i.tail e₀}).ncard ≤ δ + 1 :=
          hbm.2 _ hu _ hv he₀NL.2
        have h2 : ({e ∈ G_i.edgeSet | G_i.head e = G_i.tail e₀ ∧ G_i.tail e = G_i.head e₀}).ncard ≤ δ + 1 :=
          hbm.2 _ hv _ hu he₀NL.2.symm
        have hF_fin : (F_NL e₀).Finite :=
          (hfin.finite_E.subset (sep_subset _ _)).union (hfin.finite_E.subset (sep_subset _ _))
        have h_inter : (NL ∩ F_NL e₀).ncard ≤ (F_NL e₀).ncard := ncard_le_ncard inter_subset_right hF_fin
        have h_union : (F_NL e₀).ncard ≤
            ({e ∈ G_i.edgeSet | G_i.head e = G_i.head e₀ ∧ G_i.tail e = G_i.tail e₀}).ncard +
              ({e ∈ G_i.edgeSet | G_i.head e = G_i.tail e₀ ∧ G_i.tail e = G_i.head e₀}).ncard :=
          ncard_union_le _ _
        omega
      · let q : ↑(endsOf '' NL) := ⟨endsOf e, e, he, rfl⟩
        let e₀ : β := Classical.choose q.2
        have he₀_mem : e₀ ∈ E_simp := mem_range_self q
        have hq_spec : endsOf e₀ = endsOf e := (Classical.choose_spec q.2).2
        have hsym : (G_i.head e = G_i.head e₀ ∧ G_i.tail e = G_i.tail e₀) ∨
            (G_i.head e = G_i.tail e₀ ∧ G_i.tail e = G_i.head e₀) :=
          Sym2.eq_iff.mp hq_spec.symm
        refine mem_iUnion₂.mpr ⟨e₀, he₀_mem, ?_⟩
        rcases hsym with hdir | hrev
        · exact Or.inl ⟨he.1, hdir⟩
        · exact Or.inr ⟨he.1, hrev⟩
    have hE_eq : G_i.edgeSet = L ∪ NL := by
      ext e
      simp only [L, NL, mem_union, mem_sep_iff]
      exact ⟨fun he => (Classical.em (G_i.head e = G_i.tail e)).imp (fun h => ⟨he, h⟩) (fun h => ⟨he, h⟩),
        fun h => h.elim And.left And.left⟩
    have hE_le : G_i.edgeSet.ncard ≤ L.ncard + NL.ncard := by
      rw [hE_eq]; exact ncard_union_le L NL
    rw [hJi_V, hJi_E]
    omega

/-- If `J_i.IsSubdigraph G_i` and `J_i.toGraph` has a model of `K`, then `G_i.toGraph` has a model
of `K`. -/
lemma HasGraphModel.mono_isSubdigraph {γ δ' : Type*} {K : Graph γ δ'} {J_i G_i : Digraph α β}
    (hsub : J_i.IsSubdigraph G_i) (hmod : HasGraphModel K J_i.toGraph) :
    HasGraphModel K G_i.toGraph := by
  rcases hmod with ⟨vMap, eMap, hM⟩
  exact ⟨vMap, eMap, {
    sub_of_mem := fun u hu => (hM.sub_of_mem hu).trans hsub.toGraph_le
    nonempty_of_mem := hM.nonempty_of_mem
    connected_of_mem := hM.connected_of_mem
    disjoint_of_ne := hM.disjoint_of_ne
    edge_mem := fun e he => hsub.edgeSet_subset (hM.edge_mem he)
    link_ends_of_ne := fun e u v hlink hne => by
      rcases hM.link_ends_of_ne hlink hne with ⟨x, hx, y, hy, hlinkJ⟩
      exact ⟨x, hx, y, hy, hsub.toGraph_le.isLink_mono hlinkJ⟩
    loop_ends := fun e u hloop => by
      rcases hM.loop_ends hloop with ⟨hnot, x, hx, y, hy, hlinkJ⟩
      exact ⟨hnot, x, hx, y, hy, hsub.toGraph_le.isLink_mono hlinkJ⟩
    eMap_injOn := hM.eMap_injOn
  }⟩

/-- **Graph Minors XIII, (6.5) Algorithm** (page 87):
"*Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
*Output:* A subdigraph $G'$ of $G$ with $Z \subseteq V(G')$, such that $G$ and $G'$ have the same $\delta$-folio relative to $Z$, and such that $|E(G')| \le C|V(G')|$, where $C = \delta + 2(\delta+1)2^{p-3}$ and where $p = \lfloor\frac{5}{2}\xi\rfloor + 3\delta + 1$."

This is the correctness of the method. The RAM program, with the edge-multiplicity pruning of step
(1) and at most `ν(G)` iterations of Algorithms (6.4) and (6.2) in steps (2)–(4), and its `O(ν³)`
time bound are `GM13.algorithm_6_5` in `Results.lean`. -/
theorem algorithm_6_5_correct [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ : ℕ}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) (hZ_card : Z.ncard ≤ ξ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    ∃ G' : Digraph α β, G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
      HasSameDeltaFolioRel G G' δ Z ∧
      G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard := by
  intro p C
  obtain ⟨H, hH_sub, hH_V, hsame_GH, hH_bm⟩ := exists_boundedMultiplicity_subdigraph hfin hZ
  have hH_fin : H.IsFinite :=
    ⟨hfin.finite_V.subset hH_sub.vertexSet_subset, hfin.finite_E.subset hH_sub.edgeSet_subset⟩
  have hZ_H : Z ⊆ H.vertexSet := hH_V.symm ▸ hZ
  suffices hrec : ∀ n, ∀ G_i : Digraph α β, G_i.IsSubdigraph H → Z ⊆ G_i.vertexSet →
      HasSameDeltaFolioRel H G_i δ Z → G_i.vertexSet.ncard ≤ n →
      ∃ G' : Digraph α β, G'.IsSubdigraph G_i ∧ Z ⊆ G'.vertexSet ∧
        HasSameDeltaFolioRel H G' δ Z ∧ G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard by
    obtain ⟨G', hG'_sub, hZ_G', hsame_HG', hG'_bound⟩ :=
      hrec H.vertexSet.ncard H (Digraph.IsSubdigraph.refl H) hZ_H
        (HasSameDeltaFolioRel.refl H δ hZ_H) le_rfl
    exact ⟨G', hG'_sub.trans hH_sub, hZ_G', hsame_GH.trans hsame_HG', hG'_bound⟩
  intro n
  induction n with
  | zero =>
    intro G_i hGi_sub hZ_Gi hsame_HGi hGi_V0
    have hGi_fin : G_i.IsFinite :=
      ⟨hH_fin.finite_V.subset hGi_sub.vertexSet_subset, hH_fin.finite_E.subset hGi_sub.edgeSet_subset⟩
    have hV_emp : G_i.vertexSet = ∅ :=
      (ncard_eq_zero hGi_fin.finite_V).mp (Nat.eq_zero_of_le_zero hGi_V0)
    have hE_emp : G_i.edgeSet = ∅ := by
      rw [eq_empty_iff_forall_notMem]
      intro e he
      have hh : G_i.head e ∈ G_i.vertexSet := G_i.head_mem he
      rw [hV_emp] at hh
      exact hh
    refine ⟨G_i, Digraph.IsSubdigraph.refl G_i, hZ_Gi, hsame_HGi, ?_⟩
    rw [hE_emp, ncard_empty]
    exact Nat.zero_le _
  | succ m ih =>
    intro G_i hGi_sub hZ_Gi hsame_HGi hGi_Vle
    by_cases hstop : G_i.edgeSet.ncard ≤ C * G_i.vertexSet.ncard
    · exact ⟨G_i, Digraph.IsSubdigraph.refl G_i, hZ_Gi, hsame_HGi, hstop⟩
    · have hlt_C : C * G_i.vertexSet.ncard < G_i.edgeSet.ncard := not_le.mp hstop
      have hGi_fin : G_i.IsFinite :=
        ⟨hH_fin.finite_V.subset hGi_sub.vertexSet_subset, hH_fin.finite_E.subset hGi_sub.edgeSet_subset⟩
      have hGi_bm : G_i.HasBoundedMultiplicity δ := hH_bm.mono hH_fin hGi_sub
      obtain ⟨J_i, hJi_sub, hJi_V, hJi_simp, hGi_E_le⟩ :=
        exists_simple_underlying_subdigraph hGi_fin hGi_bm
      have hJi_fin : J_i.IsFinite :=
        ⟨hGi_fin.finite_V.subset hJi_sub.vertexSet_subset, hGi_fin.finite_E.subset hJi_sub.edgeSet_subset⟩
      have hJi_ne : J_i.vertexSet.Nonempty := by
        apply nonempty_of_ncard_ne_zero
        intro h0
        have hV_emp : G_i.vertexSet = ∅ :=
          (ncard_eq_zero hGi_fin.finite_V).mp (hJi_V ▸ h0)
        have hE_emp : G_i.edgeSet = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro e he
          have hh : G_i.head e ∈ G_i.vertexSet := G_i.head_mem he
          rw [hV_emp] at hh
          exact hh
        rw [hE_emp, ncard_empty] at hlt_C
        omega
      have hedges_Ji : 2 ^ (p - 3) * J_i.vertexSet.ncard ≤ J_i.edgeSet.ncard := by
        have hC_def : C = δ + 2 * (δ + 1) * 2 ^ (p - 3) := rfl
        rw [hC_def, ← hJi_V, Nat.add_mul, Nat.mul_assoc] at hlt_C
        have hlt2 : 2 * (δ + 1) * (2 ^ (p - 3) * J_i.vertexSet.ncard) <
            2 * (δ + 1) * J_i.edgeSet.ncard := by omega
        exact le_of_lt (Nat.lt_of_mul_lt_mul_left hlt2)
      have hp1 : 1 ≤ p := by omega
      have hKp_Ji : HasGraphModel (GM16.completeGraph p) J_i.toGraph :=
        algorithm_6_4_correct hp1 hJi_fin hJi_ne hJi_simp hedges_Ji
      have hKp_Gi : HasGraphModel (GM16.completeGraph p) G_i.toGraph :=
        hKp_Ji.mono_isSubdigraph hJi_sub
      obtain ⟨v, _, hv_irr⟩ :=
        exists_irrelevantVertex_of_completeGraph_minor hGi_fin hZ_Gi hZ_card rfl hKp_Gi
      let G_next := G_i.deleteVertex v
      have hGnext_sub_Gi : G_next.IsSubdigraph G_i := G_i.deleteVertex_isSubdigraph v
      have hGnext_sub_H : G_next.IsSubdigraph H := hGnext_sub_Gi.trans hGi_sub
      have hZ_Gnext : Z ⊆ G_next.vertexSet := hv_irr.2.2.1
      have hsame_Gi_Gnext : HasSameDeltaFolioRel G_i G_next δ Z := hv_irr.2.2.symm
      have hsame_H_Gnext : HasSameDeltaFolioRel H G_next δ Z := hsame_HGi.trans hsame_Gi_Gnext
      have hGnext_Vle : G_next.vertexSet.ncard ≤ m := by
        have hV_eq : G_next.vertexSet = G_i.vertexSet \ {v} :=
          inter_eq_self_of_subset_right sdiff_subset
        rw [hV_eq, ncard_sdiff_singleton_of_mem hv_irr.1]
        have hpos : 0 < G_i.vertexSet.ncard := (ncard_pos hGi_fin.finite_V).mpr ⟨v, hv_irr.1⟩
        omega
      obtain ⟨G', hG'_sub, hZ_G', hsame_HG', hG'_bound⟩ :=
        ih G_next hGnext_sub_H hZ_Gnext hsame_H_Gnext hGnext_Vle
      exact ⟨G', hG'_sub.trans hGnext_sub_Gi, hZ_G', hsame_HG', hG'_bound⟩

/-- **Graph Minors XIII, (6.5)** (page 87): mathematical statement of Algorithm (6.5). -/
theorem theorem_6_5_proof [Nonempty β] {G : Digraph α β} {Z : Set α} {ξ δ : ℕ}
    (hfin : G.IsFinite) (hZ : Z ⊆ G.vertexSet) (hZ_card : Z.ncard ≤ ξ) :
    let p := 5 * ξ / 2 + 3 * δ + 1
    let C := δ + 2 * (δ + 1) * 2 ^ (p - 3)
    ∃ G' : Digraph α β, G'.IsSubdigraph G ∧ Z ⊆ G'.vertexSet ∧
      HasSameDeltaFolioRel G G' δ Z ∧
      G'.edgeSet.ncard ≤ C * G'.vertexSet.ncard := by
  have hZ_sub : Z ⊆ G.vertexSet := hZ
  have hZ_le : Z.ncard ≤ ξ := hZ_card
  exact algorithm_6_5_correct hfin hZ_sub hZ_le

end GraphMinor.GM13
