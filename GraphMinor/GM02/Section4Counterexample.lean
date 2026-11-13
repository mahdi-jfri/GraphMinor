module

public import GraphMinor.GM02.Section4Feasible

/-!
# Two counterexamples to Graph Minors II, (4.5), as printed

Both examples satisfy the hypotheses printed before (4.4): `V(H) ⊆ V(G)` and no
loop of `G` is incident with a vertex of `H`. In both, `G` is the single edge
`0 1`, so no subgraph of `G` has a vertex with two edges, and no suppression is
possible. Thus `G` topologically contains `H` only if `H` is isomorphic to a
subgraph of `G` by an isomorphism that fixes every vertex.

* `H` is the vertex `0` with one loop. In `G'` the path `s₁, 1, t₁` joins the
  pair, so `(G', 𝒜)` is feasible. But `G` has no loop.
* `H` has two parallel edges between `0` and `1`. In `G'` the single edges
  `s₁t₁` and `s₂t₂` join the pairs, so `(G', 𝒜)` is feasible. But `G` has only
  one edge.

These show that the hypotheses added in `theorem_4_5` are needed.
-/

public section

namespace GraphMinor.GM02

open Graph Set Relation SimpleGraph Classical

/-- Without two edges no suppression is possible. -/
theorem eq_of_reflTransGen_of_edgeSet_subsingleton {α β : Type*} {K L : Graph α β}
    (hK : E(K).Subsingleton) (h : ReflTransGen IsSuppression K L) : L = K := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    subst ih
    obtain ⟨d, rfl⟩ := hstep
    exact (d.first_ne_second (hK d.first_link.edge_mem d.second_link.edge_mem)).elim

/-- Disjoint paths for the pairs `(sᵢ, tᵢ)` make `(G', 𝒜)` feasible. -/
theorem splitFeasible_of_paths {α β : Type*} {G H : Graph α β} {k : ℕ} (edge : Fin k ≃ E(H))
    (Q : ∀ i, PairPath (pathGraph (splitGraph G H edge)) s(splitS i, splitT i))
    (hQ : ∀ i j, i ≠ j → Disjoint (Q i).vertices (Q j).vertices) :
    (splitTermination G H edge).Feasible (splitGraph G H edge) := by
  refine ⟨fun p => (splitIndex_spec G H edge p) ▸ Q (splitIndex G H edge p), ?_⟩
  intro p q hpq
  have hverts : ∀ p, ((splitIndex_spec G H edge p) ▸ Q (splitIndex G H edge p)).vertices =
      (Q (splitIndex G H edge p)).vertices := by
    intro p
    generalize (splitIndex_spec G H edge p) = e
    generalize p.val = c at e
    subst e
    rfl
  rw [hverts p, hverts q]
  exact hQ _ _ fun h => hpq (splitIndex_injective G H edge h)

/-- The graph `G` of both examples: one edge `0` joining `0` and `1`. -/
def counterG : Graph ℕ ℕ := banana 0 1 {0}

theorem counterG_no_loop (e a : ℕ) : ¬ counterG.IsLoopAt e a := by
  intro h
  rcases h with ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;> omega

/-- If `counterG` topologically contains `H`, then `H` is isomorphic to a
subgraph of `counterG` by an isomorphism that fixes every vertex. -/
theorem counterG_topologicallyContains {H : Graph ℕ ℕ} (h : TopologicallyContains counterG H) :
    ∃ K ≤ counterG, IsoFix H K := by
  obtain ⟨K, hK, L, hs, hiso⟩ := topologicallyContains_iff_isoFix.1 h
  have hsub : E(K).Subsingleton := by
    intro a ha b hb
    have ha' : a ∈ ({0} : Set ℕ) := hK.edgeSet_mono ha
    have hb' : b ∈ ({0} : Set ℕ) := hK.edgeSet_mono hb
    rw [Set.mem_singleton_iff] at ha' hb'
    rw [ha', hb']
  rw [eq_of_reflTransGen_of_edgeSet_subsingleton hsub hs] at hiso
  exact ⟨K, hK, hiso⟩

/-! ### A loop of `H` -/

/-- The graph `H` of the first example: the vertex `0` with the loop `0`. -/
def counterLoopH : Graph ℕ ℕ := banana 0 0 {0}

/-- The enumeration of the one edge of `counterLoopH`. -/
def counterLoopEdge : Fin 1 ≃ E(counterLoopH) where
  toFun _ := ⟨0, rfl⟩
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv e := Subtype.ext (e.2).symm

/-- Graph Minors II, (4.5), page 319, fails for a loop of `H`. -/
theorem counterexample_4_5_loop :
    V(counterLoopH) ⊆ V(counterG) ∧
      (∀ e a, a ∈ V(counterLoopH) → ¬ counterG.IsLoopAt e a) ∧
      (splitTermination counterG counterLoopH counterLoopEdge).Feasible
        (splitGraph counterG counterLoopH counterLoopEdge) ∧
      ¬ TopologicallyContains counterG counterLoopH := by
  refine ⟨?_, fun e a _ => counterG_no_loop e a, ?_, ?_⟩
  · rintro a (rfl | rfl) <;> exact Or.inl rfl
  · have hends : ∀ i, (splitEnds counterLoopH counterLoopEdge i).1 = 0 ∧
        (splitEnds counterLoopH counterLoopEdge i).2 = 0 := by
      intro i
      obtain ⟨-, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ := splitEnds_isLink counterLoopH counterLoopEdge i
      · exact ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
    have h1 : (1 : ℕ) ∈ V(counterG) \ V(counterLoopH) := by
      refine ⟨Or.inr rfl, ?_⟩
      rintro (h | h) <;> exact absurd h (by decide)
    have hpath : ∀ i, ∃ P : PairPath (pathGraph (splitGraph counterG counterLoopH
        counterLoopEdge)) s(splitS i, splitT i), True := by
      intro i
      have hn := splitList_nodup i (List.nodup_singleton 1)
      have hV : ∀ c ∈ splitList i [1], c ∈ splitVertexSet counterG counterLoopH 1 := by
        intro c hc
        rcases mem_splitList.1 hc with rfl | ⟨y, hy, rfl⟩ | rfl
        · exact Or.inr ⟨_, rfl⟩
        · rw [List.mem_singleton.1 hy]
          exact Or.inl ⟨1, h1, rfl⟩
        · exact Or.inr ⟨_, rfl⟩
      have hadj01 : counterG.Adj 0 1 := ⟨0, rfl, Or.inl ⟨rfl, rfl⟩⟩
      have hc : (splitList i [1]).IsChain (pathGraph (splitGraph counterG counterLoopH
          counterLoopEdge)).Adj := by
        simp only [splitList, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
          List.isChain_cons_cons, List.IsChain.singleton, and_true]
        refine ⟨⟨(splitGraph_adj_iff _ _ _ _ _).2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩,
          ⟨(splitGraph_adj_iff _ _ _ _ _).2 ⟨?_, ?_, ?_, ?_⟩, ?_⟩⟩
        · exact Or.inr ⟨_, rfl⟩
        · exact Or.inl ⟨1, h1, rfl⟩
        · simp [splitS]
        · change counterG.Adj (splitEnds counterLoopH counterLoopEdge i).1 1
          rw [(hends i).1]
          exact hadj01
        · simp [splitS]
        · exact Or.inl ⟨1, h1, rfl⟩
        · exact Or.inr ⟨_, rfl⟩
        · simp [splitT]
        · change counterG.Adj 1 (splitEnds counterLoopH counterLoopEdge i).2
          rw [(hends i).2]
          exact hadj01.symm
        · simp [splitT]
      obtain ⟨P, -⟩ := exists_pairPath_of_splitList i hn hc
      exact ⟨P, trivial⟩
    choose Q _ using hpath
    exact splitFeasible_of_paths counterLoopEdge Q fun i j hij => (hij (Subsingleton.elim i j)).elim
  · intro h
    obtain ⟨K, hK, σ, -, hbij, hlink⟩ := counterG_topologicallyContains h
    have hl : counterLoopH.IsLink 0 0 0 := ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    have hK0 := ((hlink 0 rfl 0 0).1 hl).mono hK
    rcases hK0 with ⟨-, ⟨-, h⟩ | ⟨h, -⟩⟩ <;> exact absurd h (by decide)

/-! ### Two parallel edges of `H` -/

/-- The graph `H` of the second example: edges `0` and `1`, both joining `0`
and `1`. -/
def counterParH : Graph ℕ ℕ := banana 0 1 {0, 1}

theorem counterParH_mem (i : Fin 2) : (i.val : ℕ) ∈ E(counterParH) := by
  rcases i with ⟨_ | _ | n, hn⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · omega

/-- The enumeration of the two edges of `counterParH`. -/
def counterParEdge : Fin 2 ≃ E(counterParH) where
  toFun i := ⟨i.val, counterParH_mem i⟩
  invFun e := if e.val = 0 then 0 else 1
  left_inv i := by
    rcases i with ⟨_ | _ | n, hn⟩
    · rfl
    · rfl
    · omega
  right_inv e := by
    rcases e with ⟨e, he⟩
    rcases he with rfl | rfl
    · rfl
    · rfl

/-- Graph Minors II, (4.5), page 319, fails for two edges of `H` with the same
ends. -/
theorem counterexample_4_5_parallel :
    V(counterParH) ⊆ V(counterG) ∧
      (∀ e a, a ∈ V(counterParH) → ¬ counterG.IsLoopAt e a) ∧
      (splitTermination counterG counterParH counterParEdge).Feasible
        (splitGraph counterG counterParH counterParEdge) ∧
      ¬ TopologicallyContains counterG counterParH := by
  refine ⟨fun a ha => ha, fun e a _ => counterG_no_loop e a, ?_, ?_⟩
  · have hadj : ∀ i, counterG.Adj (splitEnds counterParH counterParEdge i).1
        (splitEnds counterParH counterParEdge i).2 := by
      intro i
      obtain ⟨-, h⟩ := splitEnds_isLink counterParH counterParEdge i
      exact ⟨0, rfl, h⟩
    have hpath : ∀ i, ∃ P : PairPath (pathGraph (splitGraph counterG counterParH
        counterParEdge)) s(splitS i, splitT i),
        ∀ a, a ∈ P.vertices ↔ a ∈ splitList i [] := by
      intro i
      have hn := splitList_nodup (α := ℕ) i List.nodup_nil
      have hc : (splitList i ([] : List ℕ)).IsChain (pathGraph (splitGraph counterG counterParH
          counterParEdge)).Adj := by
        simp only [splitList, List.map_nil, List.nil_append, List.isChain_pair]
        refine ⟨(splitGraph_adj_iff _ _ _ _ _).2 ⟨Or.inr ⟨_, rfl⟩, Or.inr ⟨_, rfl⟩,
          by simp [splitS, splitT], hadj i⟩, by simp [splitS, splitT]⟩
      exact exists_pairPath_of_splitList i hn hc
    choose Q hQ using hpath
    refine splitFeasible_of_paths counterParEdge Q fun i j hij => ?_
    rw [Set.disjoint_left]
    intro a ha hb
    rw [hQ] at ha hb
    rcases mem_splitList.1 ha with rfl | ⟨y, hy, rfl⟩ | rfl
    · rcases mem_splitList.1 hb with h | ⟨y, hy, h⟩ | h
      · simp only [splitS, Sum.inr.injEq, Prod.mk.injEq, and_true] at h
        exact hij h
      · exact (List.not_mem_nil hy).elim
      · simp [splitS, splitT] at h
    · exact (List.not_mem_nil hy).elim
    · rcases mem_splitList.1 hb with h | ⟨y, hy, h⟩ | h
      · simp [splitS, splitT] at h
      · exact (List.not_mem_nil hy).elim
      · simp only [splitT, Sum.inr.injEq, Prod.mk.injEq, and_true] at h
        exact hij h
  · intro h
    obtain ⟨K, hK, σ, -, hbij, -⟩ := counterG_topologicallyContains h
    have h0 : σ 0 = 0 := hK.edgeSet_mono (hbij.mapsTo (Or.inl rfl))
    have h1 : σ 1 = 0 := hK.edgeSet_mono (hbij.mapsTo (Or.inr rfl))
    have := hbij.injOn (Or.inl rfl) (Or.inr rfl) (h0.trans h1.symm)
    omega

end GraphMinor.GM02
