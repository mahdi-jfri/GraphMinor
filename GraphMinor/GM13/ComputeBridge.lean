module

public import GraphMinor.GM13.Section6
public import GraphMinor.Compute.Algorithm63
public import GraphMinor.Compute.Algorithm64

/-!
# Bridge Between Graph Minors XIII (6.3)–(6.4) and the Word RAM Programs

This file connects the mathematical formalization of Algorithms (6.3) and (6.4) over `GM13.Digraph`
in `GraphMinor/GM13/Section6.lean` with the Word RAM programs `Compute.alg63EndToEndProg` and
`Compute.alg64EndToEndProg` over `SimpleGraph (Fin n)` in `GraphMinor/Compute/Algorithm63.lean` and
`GraphMinor/Compute/Algorithm64.lean`:

1. `digraphOfSimpleGraph`: embeds any `G : SimpleGraph (Fin n)` as a `GM13.Digraph (Fin n) (Fin n × Fin n)`
   whose underlying undirected graph `(digraphOfSimpleGraph G).toGraph` is simple (`IsSimpleGraph`),
   has the same vertices (`|V| = n`) and edges (`|E| = G.edgeFinset.card`), and the same adjacency
   relation (`(digraphOfSimpleGraph G).toGraph.Adj u v ↔ G.Adj u v`).
2. `isAlg63Output_implies_gm13` and `algorithm_6_3_end_to_end`: proves that any `X` satisfying
   `Compute.IsAlg63Output x X` satisfies the output conditions of `algorithm_6_3_correct` on
   `digraphOfSimpleGraph x.G`, and joins `Compute.gm13_algorithm_6_3` with the `GM13` output statement.
3. `hasGraphModel_of_isCliqueModel`, `algorithm_6_4_correct_faithful`, `algorithm_6_4_end_to_end`,
   and `algorithm_6_4_faithful_end_to_end`: proves that `Compute.IsCliqueModel G p sets` gives
   `HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph G).toGraph`, proves the faithful edge
   bound `2 ^ p * |V| ≤ 8 * |E|` for all `p ≥ 1` (handling `p ≤ 2` directly and using
   `algorithm_6_4_correct` for `p ≥ 3`), and states and proves the end-to-end Word RAM theorems.
-/

@[expose] public section

namespace GraphMinor.GM13

open Set Function Classical
open Graph SimpleGraph
open GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM16 GraphMinor.Compute

/-! ## Part 1: `digraphOfSimpleGraph` and Basic Properties -/

/-- The `GM13.Digraph` associated to a simple graph `G : SimpleGraph (Fin n)`, with vertex set
`Set.univ : Set (Fin n)` and edge set `{e : Fin n × Fin n | e.1 < e.2 ∧ G.Adj e.1 e.2}` oriented
from `e.1` to `e.2`. -/
def digraphOfSimpleGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Digraph (Fin n) (Fin n × Fin n) where
  vertexSet := Set.univ
  edgeSet := {e : Fin n × Fin n | e.1 < e.2 ∧ G.Adj e.1 e.2}
  head := Prod.fst
  tail := Prod.snd
  head_mem _ _ := Set.mem_univ _
  tail_mem _ _ := Set.mem_univ _

@[simp]
theorem digraphOfSimpleGraph_vertexSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    (digraphOfSimpleGraph G).vertexSet = Set.univ := rfl

@[simp]
theorem digraphOfSimpleGraph_toGraph_vertexSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    V((digraphOfSimpleGraph G).toGraph) = Set.univ := rfl

theorem digraphOfSimpleGraph_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    (digraphOfSimpleGraph G).edgeSet = {e : Fin n × Fin n | e.1 < e.2 ∧ G.Adj e.1 e.2} := rfl

@[simp]
theorem digraphOfSimpleGraph_head {n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin n × Fin n) :
    (digraphOfSimpleGraph G).head e = e.1 := rfl

@[simp]
theorem digraphOfSimpleGraph_tail {n : ℕ} (G : SimpleGraph (Fin n)) (e : Fin n × Fin n) :
    (digraphOfSimpleGraph G).tail e = e.2 := rfl

/-- `digraphOfSimpleGraph G` is a finite digraph. -/
theorem digraphOfSimpleGraph_isFinite {n : ℕ} (G : SimpleGraph (Fin n)) :
    (digraphOfSimpleGraph G).IsFinite :=
  ⟨Set.toFinite _, Set.toFinite _⟩

/-- If `0 < n`, `digraphOfSimpleGraph G` has a non-empty vertex set. -/
theorem digraphOfSimpleGraph_vertexSet_nonempty {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n) :
    (digraphOfSimpleGraph G).vertexSet.Nonempty :=
  ⟨⟨0, hn⟩, Set.mem_univ _⟩

/-- The number of vertices of `digraphOfSimpleGraph G` is `n`. -/
@[simp]
theorem digraphOfSimpleGraph_vertexSet_ncard {n : ℕ} (G : SimpleGraph (Fin n)) :
    (digraphOfSimpleGraph G).vertexSet.ncard = n := by
  rw [digraphOfSimpleGraph_vertexSet, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- Bijection from `(digraphOfSimpleGraph G).edgeSet` to `G.edgeSet` sending `(u, v)` to `s(u, v)`. -/
theorem digraphOfSimpleGraph_bijOn_edgeSet {n : ℕ} (G : SimpleGraph (Fin n)) :
    Set.BijOn (fun e : Fin n × Fin n => s(e.1, e.2))
      (digraphOfSimpleGraph G).edgeSet G.edgeSet := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    simpa [SimpleGraph.mem_edgeSet] using he.2
  · intro e₁ he₁ e₂ he₂ heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · exfalso
      have hlt₁ : e₁.1 < e₁.2 := he₁.1
      have hlt₂ : e₂.1 < e₂.2 := he₂.1
      rw [h1, h2] at hlt₁
      exact lt_asymm hlt₁ hlt₂
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have hadj : G.Adj u v := by simpa [SimpleGraph.mem_edgeSet] using he
      rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
      · exact ⟨(u, v), ⟨hlt, hadj⟩, rfl⟩
      · exact ⟨(v, u), ⟨hgt, hadj.symm⟩, Sym2.eq_swap⟩

/-- The number of edges of `digraphOfSimpleGraph G` equals `G.edgeFinset.card`. -/
@[simp]
theorem digraphOfSimpleGraph_edgeSet_ncard {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (digraphOfSimpleGraph G).edgeSet.ncard = G.edgeFinset.card := by
  rw [(digraphOfSimpleGraph_bijOn_edgeSet G).ncard_eq, ← SimpleGraph.coe_edgeFinset G,
    Set.ncard_coe_finset]

@[simp]
theorem digraphOfSimpleGraph_toGraph_edgeSet_ncard {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    E((digraphOfSimpleGraph G).toGraph).ncard = G.edgeFinset.card :=
  digraphOfSimpleGraph_edgeSet_ncard G

/-- Link characterization in `(digraphOfSimpleGraph G).toGraph`. -/
theorem digraphOfSimpleGraph_toGraph_isLink {n : ℕ} (G : SimpleGraph (Fin n))
    (e : Fin n × Fin n) (u v : Fin n) :
    (digraphOfSimpleGraph G).toGraph.IsLink e u v ↔
      (e.1 < e.2 ∧ G.Adj e.1 e.2) ∧ ((e.1 = u ∧ e.2 = v) ∨ (e.1 = v ∧ e.2 = u)) :=
  Iff.rfl

/-- Adjacency in `(digraphOfSimpleGraph G).toGraph` coincides with adjacency in `G`. -/
@[simp]
theorem digraphOfSimpleGraph_toGraph_adj {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    (digraphOfSimpleGraph G).toGraph.Adj u v ↔ G.Adj u v := by
  constructor
  · rintro ⟨e, ⟨_, hadj⟩, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact hadj
    · exact hadj.symm
  · intro hadj
    rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
    · exact ⟨(u, v), ⟨hlt, hadj⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨(v, u), ⟨hgt, hadj.symm⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- The underlying graph `(digraphOfSimpleGraph G).toGraph` is a simple graph (`IsSimpleGraph`). -/
theorem digraphOfSimpleGraph_isSimpleGraph {n : ℕ} (G : SimpleGraph (Fin n)) :
    IsSimpleGraph (digraphOfSimpleGraph G).toGraph := by
  refine ⟨fun e _ v hlink => ?_, fun e₁ _ e₂ _ u v hlink₁ hlink₂ => ?_⟩
  · rcases hlink with ⟨⟨hlt, _⟩, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · change e.1 = v at h1; change e.2 = v at h2
      rw [h1, h2] at hlt; exact lt_irrefl _ hlt
    · change e.1 = v at h1; change e.2 = v at h2
      rw [h1, h2] at hlt; exact lt_irrefl _ hlt
  · rcases hlink₁ with ⟨⟨hlt₁, _⟩, ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩⟩ <;>
    rcases hlink₂ with ⟨⟨hlt₂, _⟩, ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩⟩
    · exact Prod.ext (h1a.trans h2a.symm) (h1b.trans h2b.symm)
    · exfalso
      have ha : e₁.1 = e₂.2 := h1a.trans h2b.symm
      have hb : e₁.2 = e₂.1 := h1b.trans h2a.symm
      rw [ha, hb] at hlt₁
      exact lt_asymm hlt₁ hlt₂
    · exfalso
      have ha : e₁.1 = e₂.2 := h1a.trans h2b.symm
      have hb : e₁.2 = e₂.1 := h1b.trans h2a.symm
      rw [ha, hb] at hlt₁
      exact lt_asymm hlt₁ hlt₂
    · exact Prod.ext (h1a.trans h2a.symm) (h1b.trans h2b.symm)

/-! ## Part 2: Induced Connectedness, External Neighborhoods, and Degrees -/

@[simp]
theorem digraphOfSimpleGraph_induce_vertexSet {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Fin n)) :
    ((digraphOfSimpleGraph G).induce S).vertexSet = S := by
  change Set.univ ∩ S = S
  exact Set.univ_inter S

theorem digraphOfSimpleGraph_induce_isLink_of_adj {n : ℕ} (G : SimpleGraph (Fin n))
    {S : Set (Fin n)} {u v : Fin n} (hu : u ∈ S) (hv : v ∈ S) (hadj : G.Adj u v) :
    ∃ e, ((digraphOfSimpleGraph G).induce S).toGraph.IsLink e u v := by
  rcases lt_or_gt_of_ne (G.ne_of_adj hadj) with hlt | hgt
  · exact ⟨(u, v), ⟨⟨hlt, hadj⟩, hu, hv⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨(v, u), ⟨⟨hgt, hadj.symm⟩, hv, hu⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- Any walk in `G.induce S` lifts to a `GraphWalk` in `((digraphOfSimpleGraph G).induce S).toGraph`. -/
theorem graphWalk_induce_of_simpleGraph_walk {n : ℕ} (G : SimpleGraph (Fin n))
    {S : Set (Fin n)} {u v : S} (w : (G.induce S).Walk u v) :
    Nonempty (GraphWalk ((digraphOfSimpleGraph G).induce S).toGraph u.1 v.1) := by
  induction w with
  | @nil a =>
    exact ⟨GraphWalk.nil ⟨Set.mem_univ a.1, a.2⟩⟩
  | @cons a b c hadj _ ih =>
    rcases digraphOfSimpleGraph_induce_isLink_of_adj G a.2 b.2 hadj with ⟨e, hlink⟩
    rcases ih with ⟨W⟩
    exact ⟨GraphWalk.cons hlink W⟩

/-- Connectedness of `G.induce S` implies `IsConnected` of `(digraphOfSimpleGraph G).induce S`. -/
theorem digraphOfSimpleGraph_induce_isConnected {n : ℕ} (G : SimpleGraph (Fin n))
    {S : Set (Fin n)} (hconn : (G.induce S).Connected) :
    ((digraphOfSimpleGraph G).induce S).IsConnected := by
  rcases hconn.nonempty with ⟨x₀, hx₀⟩
  refine ⟨⟨x₀, Set.mem_univ x₀, hx₀⟩, fun u hu v hv => ?_⟩
  rcases hconn.preconnected ⟨u, hu.2⟩ ⟨v, hv.2⟩ with ⟨w⟩
  exact graphWalk_induce_of_simpleGraph_walk G w

/-- The external neighborhood `Compute.extNeighborhood G X` coincides with
`(digraphOfSimpleGraph G).extNeighbors (X : Set (Fin n))`. -/
@[simp]
theorem digraphOfSimpleGraph_extNeighbors_eq {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) :
    (digraphOfSimpleGraph G).extNeighbors (X : Set (Fin n)) =
      (Compute.extNeighborhood G X : Set (Fin n)) := by
  ext v
  rw [Finset.mem_coe, Compute.mem_extNeighborhood]
  simp only [Digraph.extNeighbors, digraphOfSimpleGraph_vertexSet, digraphOfSimpleGraph_toGraph_adj,
    Set.mem_sdiff, Set.mem_univ, true_and, Finset.mem_coe]
  refine ⟨fun ⟨hv, u, hu, hadj⟩ => ⟨hv, u, hu, hadj.symm⟩,
    fun ⟨hv, u, hu, hadj⟩ => ⟨hv, u, hu, hadj.symm⟩⟩

/-- For any `S : Finset (Fin n)` and `v : Fin n`, the number of neighbors of `v` in `S` in
`(digraphOfSimpleGraph G).toGraph` equals `Compute.degInto G S v`. -/
theorem digraphOfSimpleGraph_ncard_neighbors_in_eq_degInto {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (v : Fin n) :
    ({u ∈ (S : Set (Fin n)) | (digraphOfSimpleGraph G).toGraph.Adj v u}).ncard =
      Compute.degInto G S v := by
  classical
  have hset :
      {u ∈ (S : Set (Fin n)) | (digraphOfSimpleGraph G).toGraph.Adj v u} =
        ((Finset.univ.filter (fun u : Fin n => u ∈ S ∧ G.Adj v u) : Finset (Fin n)) :
          Set (Fin n)) := by
    ext u
    simp [digraphOfSimpleGraph_toGraph_adj]
  rw [hset, Set.ncard_coe_finset]
  rfl

/-! ## Part 3: Bridge and End-to-End Theorem for Algorithm (6.3) -/

/-- If `X : Finset (Fin x.n)` satisfies the Word RAM output specification `Compute.IsAlg63Output x X`,
then `(X : Set (Fin x.n))` satisfies the `GM13` output conditions of Algorithm (6.3) on
`digraphOfSimpleGraph x.G`. -/
theorem isAlg63Output_implies_gm13 (x : Compute.Alg63Input) (X : Finset (Fin x.n))
    (hout : Compute.IsAlg63Output x X) :
    let D := digraphOfSimpleGraph x.G
    let X_set : Set (Fin x.n) := (X : Set (Fin x.n))
    X_set ⊆ D.vertexSet ∧
    (D.induce X_set).IsConnected ∧
    (D.extNeighbors X_set).Nonempty ∧
    ∀ v ∈ D.extNeighbors X_set,
      x.k ≤ ({u ∈ D.extNeighbors X_set | D.toGraph.Adj v u}).ncard := by
  rcases hout with ⟨_, hconn, hN_ne, hN_deg⟩
  dsimp only
  refine ⟨Set.subset_univ _, digraphOfSimpleGraph_induce_isConnected x.G hconn, ?_, ?_⟩
  · rw [digraphOfSimpleGraph_extNeighbors_eq]
    exact Finset.coe_nonempty.mpr hN_ne
  · intro v hv
    rw [digraphOfSimpleGraph_extNeighbors_eq] at hv ⊢
    rw [digraphOfSimpleGraph_ncard_neighbors_in_eq_degInto]
    exact hN_deg v hv

/-- End-to-end Word RAM theorem for **Graph Minors XIII, Algorithm (6.3)** (pages 85–86):
on any valid input `x : Compute.Alg63Input` (a non-null simple graph `x.G` with `x.k > 0` and
`x.k * x.n ≤ x.G.edgeFinset.card`), the Word RAM program `Compute.alg63EndToEndProg` runs in time
`O(vε)` (`alg63Size x = x.n * x.G.edgeFinset.card`) and its decoded output
`X = (Compute.decAlg63Out x.n out : Set (Fin x.n))` satisfies the `GM13` output specification of
Algorithm (6.3) on `D = digraphOfSimpleGraph x.G`. -/
theorem algorithm_6_3_end_to_end :
    ComputesArrRelInTime Compute.alg63Size Compute.encAlg63In
      (fun x out =>
        let D := digraphOfSimpleGraph x.G
        let X : Set (Fin x.n) := (Compute.decAlg63Out x.n out : Set (Fin x.n))
        X ⊆ D.vertexSet ∧
        (D.induce X).IsConnected ∧
        (D.extNeighbors X).Nonempty ∧
        ∀ v ∈ D.extNeighbors X,
          x.k ≤ ({u ∈ D.extNeighbors X | D.toGraph.Adj v u}).ncard)
      Compute.alg63EndToEndProg (fun s => s + 1) := by
  rcases Compute.gm13_algorithm_6_3 with ⟨C, c, hc, hC, hexec⟩
  refine ⟨C, c, hc, hC, fun x s₀ hs₀ => ?_⟩
  rcases hexec x s₀ hs₀ with ⟨s', t, hex, ht, hout⟩
  exact ⟨s', t, hex, ht, isAlg63Output_implies_gm13 x (Compute.decAlg63Out x.n (s'.arrs outArr)) hout⟩

/-! ## Part 4: Bridge, Faithful Edge Bound, and End-to-End Theorems for Algorithm (6.4) -/

/-- If `sets : Fin p → Finset (Fin n)` is a clique minor model `Compute.IsCliqueModel G p sets`,
then `(digraphOfSimpleGraph G).toGraph` has a graph model of `GM16.completeGraph p`
(`HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph G).toGraph`). -/
theorem hasGraphModel_of_isCliqueModel {n p : ℕ} (G : SimpleGraph (Fin n))
    (sets : Fin p → Finset (Fin n)) (hmodel : Compute.IsCliqueModel G p sets) :
    HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph G).toGraph := by
  cases p with
  | zero =>
    let eMap : Sym2 (Fin 0) → Fin n × Fin n :=
      Quot.lift (fun p : Fin 0 × Fin 0 => Fin.elim0 p.1) (fun a _ _ => Fin.elim0 a.1)
    apply hasGraphModel_of_exists_isGraphModel
    refine ⟨Fin.elim0, eMap, {
      sub_of_mem := fun v _ => Fin.elim0 v
      nonempty_of_mem := fun v _ => Fin.elim0 v
      connected_of_mem := fun v _ => Fin.elim0 v
      disjoint_of_ne := fun u _ _ _ _ => Fin.elim0 u
      edge_mem := fun _ ⟨x, _, _, _⟩ => Fin.elim0 x
      link_ends_of_ne := fun {_ u _} _ _ => Fin.elim0 u
      loop_ends := fun {_ u} _ => Fin.elim0 u
      eMap_injOn := fun _ ⟨x, _, _, _⟩ _ _ _ => Fin.elim0 x
    }⟩
  | succ p' =>
    rcases (hmodel.1 ⟨0, Nat.zero_lt_succ p'⟩).1 with ⟨v₀, _⟩
    have : Nonempty (Fin n × Fin n) := ⟨(v₀, v₀)⟩
    let D := digraphOfSimpleGraph G
    let sub (i : Fin (p' + 1)) : Digraph (Fin n) (Fin n × Fin n) :=
      D.induce (sets i : Set (Fin n))
    apply hasGraphModel_completeGraph_of_connected_subgraphs (sub := sub)
    · intro i
      exact D.induce_isSubdigraph (sets i : Set (Fin n))
    · intro i
      exact digraphOfSimpleGraph_induce_isConnected G (hmodel.1 i).2
    · intro i j hij
      dsimp [sub]
      rw [digraphOfSimpleGraph_induce_vertexSet, digraphOfSimpleGraph_induce_vertexSet]
      exact Finset.disjoint_coe.mpr (hmodel.2.1 i j hij)
    · intro i j hij
      rcases hmodel.2.2 i j (ne_of_lt hij) with ⟨u, hu, v, hv, hadj⟩
      have hadjD : D.toGraph.Adj u v := (digraphOfSimpleGraph_toGraph_adj G u v).mpr hadj
      rcases hadjD with ⟨e, heD, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ⟨e, heD, Or.inl ⟨⟨Set.mem_univ _, hu⟩, ⟨Set.mem_univ _, hv⟩⟩⟩
      · exact ⟨e, heD, Or.inr ⟨⟨Set.mem_univ _, hv⟩, ⟨Set.mem_univ _, hu⟩⟩⟩

/-- **Graph Minors XIII, Algorithm (6.4)** (pages 86–87) with the faithful rational edge bound
`2 ^ p * |V(G)| ≤ 8 * |E(G)|` (`|E(G)| ≥ 2^{p-3} |V(G)|`):
for `p ≤ 2`, we construct the `K_p` model directly (`p = 1` from a single vertex, `p = 2` from a
single edge since `4 |V(G)| ≤ 8 |E(G)|` and `|V(G)| ≥ 1` force `|E(G)| ≥ 1`); for `p ≥ 3`,
`2 ^ p = 8 * 2 ^ (p - 3)` and we apply `algorithm_6_4_correct`. -/
theorem algorithm_6_4_correct_faithful {α : Type*} {β : Type*} [Nonempty β]
    {G : Digraph α β} {p : ℕ}
    (hp : 1 ≤ p) (hfin : G.IsFinite) (hne : G.vertexSet.Nonempty)
    (hsimple : IsSimpleGraph G.toGraph)
    (hedges : 2 ^ p * G.vertexSet.ncard ≤ 8 * G.edgeSet.ncard) :
    HasGraphModel (GM16.completeGraph p) G.toGraph := by
  by_cases hp1 : p = 1
  · subst hp1
    rcases hne with ⟨v₀, hv₀⟩
    let sub : Fin 1 → Digraph α β := fun _ => G.induce {v₀}
    apply hasGraphModel_completeGraph_of_connected_subgraphs (sub := sub)
    · intro _; exact G.induce_isSubdigraph {v₀}
    · intro _
      exact ⟨⟨v₀, hv₀, rfl⟩, fun u ⟨_, hu⟩ w ⟨_, hw⟩ => by
        subst hu hw; exact ⟨.nil ⟨hv₀, rfl⟩⟩⟩
    · intro i j hij
      exact False.elim (hij (Fin.ext (by omega)))
    · intro i j hlt
      exact False.elim (by omega)
  · by_cases hp2 : p = 2
    · subst hp2
      have hV_pos : 0 < G.vertexSet.ncard := (Set.ncard_pos hfin.finite_V).mpr hne
      have hE_pos : 0 < G.edgeSet.ncard := by
        change 4 * G.vertexSet.ncard ≤ 8 * G.edgeSet.ncard at hedges
        omega
      rcases (Set.ncard_pos hfin.finite_E).mp hE_pos with ⟨e₀, he₀⟩
      let u₀ := G.head e₀
      let v₀ := G.tail e₀
      have hu₀ : u₀ ∈ G.vertexSet := G.head_mem he₀
      have hv₀ : v₀ ∈ G.vertexSet := G.tail_mem he₀
      have hlink₀ : G.toGraph.IsLink e₀ u₀ v₀ := ⟨he₀, Or.inl ⟨rfl, rfl⟩⟩
      have huv_ne : u₀ ≠ v₀ := fun h => hsimple.1 e₀ he₀ u₀ (h ▸ hlink₀)
      let sub (i : Fin 2) : Digraph α β :=
        if i.1 = 0 then G.induce {u₀} else G.induce {v₀}
      apply hasGraphModel_completeGraph_of_connected_subgraphs (sub := sub)
      · intro i; dsimp [sub]; split_ifs <;> exact G.induce_isSubdigraph _
      · intro i; dsimp [sub]; split_ifs
        · exact ⟨⟨u₀, hu₀, rfl⟩, fun x ⟨_, hx⟩ y ⟨_, hy⟩ => by
            subst hx hy; exact ⟨.nil ⟨hu₀, rfl⟩⟩⟩
        · exact ⟨⟨v₀, hv₀, rfl⟩, fun x ⟨_, hx⟩ y ⟨_, hy⟩ => by
            subst hx hy; exact ⟨.nil ⟨hv₀, rfl⟩⟩⟩
      · intro i j hij
        dsimp [sub]
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
      · intro i j hlt
        have hi0 : i.1 = 0 := by omega
        have hj1 : j.1 = 1 := by omega
        dsimp [sub]
        simp only [hi0, hj1, ↓reduceIte, one_ne_zero]
        exact ⟨e₀, he₀, Or.inl ⟨⟨hu₀, rfl⟩, ⟨hv₀, rfl⟩⟩⟩
    · have hp3 : 3 ≤ p := by omega
      have hpow : 2 ^ p = 8 * 2 ^ (p - 3) := by
        have heq : p = (p - 3) + 3 := by omega
        conv_lhs => rw [heq, Nat.pow_add, Nat.mul_comm]
      have hedges3 : 2 ^ (p - 3) * G.vertexSet.ncard ≤ G.edgeSet.ncard := by
        rw [hpow, Nat.mul_assoc] at hedges
        omega
      exact algorithm_6_4_correct hp hfin hne hsimple hedges3

/-- Corollary of `algorithm_6_4_correct_faithful` for `digraphOfSimpleGraph G`. -/
theorem digraphOfSimpleGraph_hasGraphModel_of_faithful_bound {n p : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hp : 1 ≤ p) (hn : 0 < n) (hedges : 2 ^ p * n ≤ 8 * G.edgeFinset.card) :
    HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph G).toGraph := by
  have : Nonempty (Fin n × Fin n) := ⟨(⟨0, hn⟩, ⟨0, hn⟩)⟩
  apply algorithm_6_4_correct_faithful hp (digraphOfSimpleGraph_isFinite G)
    (digraphOfSimpleGraph_vertexSet_nonempty G hn) (digraphOfSimpleGraph_isSimpleGraph G)
  rw [digraphOfSimpleGraph_vertexSet_ncard, digraphOfSimpleGraph_edgeSet_ncard]
  exact hedges

/-- End-to-end Word RAM theorem for **Graph Minors XIII, Algorithm (6.4)** (pages 86–87) over
`Compute.Alg64Input p`: for any fixed `p : ℕ`, `Compute.alg64EndToEndProg p` runs in time
`O((v + 1)²)` (`alg64Size p x = x.n`) and its decoded output `Compute.decAlg64Out p x.n out`
is a clique model in `x.G` (`Compute.IsCliqueModel`) witnessing
`HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph x.G).toGraph`. -/
theorem algorithm_6_4_end_to_end (p : ℕ) :
    ComputesArrRelInTime (Compute.alg64Size p) (Compute.encAlg64In p)
      (fun x out =>
        Compute.IsCliqueModel x.G p (Compute.decAlg64Out p x.n out) ∧
        HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph x.G).toGraph)
      (Compute.alg64EndToEndProg p) (fun v => (v + 1) ^ 2) := by
  rcases Compute.gm13_algorithm_6_4 p with ⟨C, c, hc, hC, hexec⟩
  refine ⟨C, c, hc, hC, fun x s₀ hs₀ => ?_⟩
  rcases hexec x s₀ hs₀ with ⟨s', t, hex, ht, hmodel⟩
  exact ⟨s', t, hex, ht, hmodel, hasGraphModel_of_isCliqueModel x.G _ hmodel⟩

/-- Faithful problem input for GM XIII (6.4) with the paper's exact edge bound
`2 ^ p * n ≤ 8 * G.edgeFinset.card` (`|E(G)| ≥ 2^{p-3} |V(G)|`). -/
structure Alg64FaithfulInput (p : ℕ) where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- The input simple graph on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidability of adjacency in `G`. -/
  [decAdj : DecidableRel G.Adj]
  /-- `G` is non-null (`n > 0`). -/
  hn : 0 < n
  /-- Paper's edge-density hypothesis `|E(G)| ≥ 2^{p-3} |V(G)|`, written `2 ^ p * n ≤ 8 * |E(G)|`. -/
  hedges : 2 ^ p * n ≤ 8 * G.edgeFinset.card

attribute [instance] Alg64FaithfulInput.decAdj

/-- Problem size `v = |V(G)| = x.n` for `Alg64FaithfulInput p`. -/
def alg64FaithfulSize (p : ℕ) (x : Alg64FaithfulInput p) : ℕ :=
  x.n

/-- Flat input encoding `encGraph x.G` for `Alg64FaithfulInput p`. -/
def encAlg64FaithfulIn (p : ℕ) (x : Alg64FaithfulInput p) : List ℕ :=
  Compute.encGraph x.G

/-- For `p ≥ 3`, `Alg64FaithfulInput p` embeds directly into `Compute.Alg64Input p`. -/
def Alg64FaithfulInput.toAlg64Input {p : ℕ} (_hp : 3 ≤ p) (x : Alg64FaithfulInput p) :
    Compute.Alg64Input p where
  n := x.n
  G := x.G
  hn := x.hn
  hedges := x.hedges

/-- End-to-end Word RAM theorem for `Compute.alg64EndToEndProg p` under the paper's exact edge bound
`2 ^ p * x.n ≤ 8 * x.G.edgeFinset.card` when `3 ≤ p`. -/
theorem algorithm_6_4_faithful_of_three_le (p : ℕ) (hp : 3 ≤ p) :
    ComputesArrRelInTime (alg64FaithfulSize p) (encAlg64FaithfulIn p)
      (fun x out =>
        Compute.IsCliqueModel x.G p (Compute.decAlg64Out p x.n out) ∧
        HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph x.G).toGraph)
      (Compute.alg64EndToEndProg p) (fun v => (v + 1) ^ 2) := by
  rcases algorithm_6_4_end_to_end p with ⟨C, c, hc, hC, hexec⟩
  refine ⟨C, c, hc, hC, fun x s₀ hs₀ => ?_⟩
  exact hexec (x.toAlg64Input hp) s₀ hs₀

/-- Word RAM program for GM XIII Algorithm (6.4) over `Alg64FaithfulInput p` for all `p : ℕ`:
coincides with `Compute.alg64EndToEndProg p` for `p ≠ 2`, and for `p = 2` reads `n := inArr[0]`
and the first edge `(u₀, v₀) = (inArr[2], inArr[3])` (which exists since `4 * n ≤ 8 * |E|` and
`n > 0` imply `|E| ≥ 1`), sets arrays `18` and `19` to `{u₀}` and `{v₀}`, and packs the `2`
bitsets into `outArr`. -/
def alg64FaithfulProg (p : ℕ) : Compute.Cmd :=
  match p with
  | 2 =>
    .seq (.assign 0 (.read inArr (.const 0)))
      (.seq (.assign 4 (.read inArr (.const 2)))
        (.seq (.assign 5 (.read inArr (.const 3)))
          (.seq (setSingletonBitSetProg 18 0 4)
            (.seq (setSingletonBitSetProg 19 0 5)
              (packBitSetsUpTo 2 2)))))
  | p => Compute.alg64EndToEndProg p

/-- End-to-end Word RAM theorem for **Graph Minors XIII, Algorithm (6.4)** (pages 86–87) under the
paper's faithful edge bound `2 ^ p * x.n ≤ 8 * x.G.edgeFinset.card` (`|E(G)| ≥ 2^{p-3} |V(G)|`)
for every `p : ℕ`. -/
theorem algorithm_6_4_faithful_end_to_end (p : ℕ) :
    ComputesArrRelInTime (alg64FaithfulSize p) (encAlg64FaithfulIn p)
      (fun x out =>
        Compute.IsCliqueModel x.G p (Compute.decAlg64Out p x.n out) ∧
        HasGraphModel (GM16.completeGraph p) (digraphOfSimpleGraph x.G).toGraph)
      (alg64FaithfulProg p) (fun v => (v + 1) ^ 2) := by
  cases p with
  | zero =>
    unfold ComputesArrRelInTime ComputesRelInTime alg64FaithfulProg Compute.alg64EndToEndProg
    refine ⟨2, 1, by omega, by omega, fun x s₀ _ => ?_⟩
    let w := wordSize 1 (alg64FaithfulSize 0 x)
    have h0_w : 0 < 2 ^ w := Nat.two_pow_pos w
    let s₁ := s₀.setArr outArr (List.replicate 0 0)
    have hex₁ : Exec w (.alloc outArr (.const 0)) s₀ s₁ (1 + 0) :=
      .alloc (by simp [Expr.eval, checkWord, h0_w])
    have hpos : 1 ≤ (alg64FaithfulSize 0 x + 1) ^ 2 :=
      Nat.le_trans (by omega : 1 ≤ alg64FaithfulSize 0 x + 1)
        (Nat.le_self_pow (by decide : 2 ≠ 0) _)
    have hmodel : Compute.IsCliqueModel x.G 0 (Compute.decAlg64Out 0 x.n (s₁.arrs outArr)) :=
      ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
    exact ⟨s₁, 1 + 0, hex₁, by dsimp only; omega,
      hmodel, hasGraphModel_of_isCliqueModel x.G _ hmodel⟩
  | succ p₁ =>
    cases p₁ with
    | zero =>
      -- `p = 1`
      unfold ComputesArrRelInTime ComputesRelInTime alg64FaithfulProg Compute.alg64EndToEndProg
      refine ⟨40, 2, by omega, by omega, fun x s₀ hs₀ => ?_⟩
      let w := wordSize 2 (alg64FaithfulSize 1 x)
      have hw_bound : 2 * (alg64FaithfulSize 1 x + 2) < 2 ^ w :=
        two_mul_lt_two_pow_wordSize (c := 2) (n := alg64FaithfulSize 1 x) (by omega)
      have hsize_eq : alg64FaithfulSize 1 x = x.n := rfl
      have hw : 1 < 2 ^ w := by omega
      have h0_w : 0 < 2 ^ w := by omega
      have hn_w : x.n < 2 ^ w := by omega
      have h0_len : 0 < (s₀.arrs inArr).length := by simp [hs₀, encAlg64FaithfulIn, encGraph]
      have h0_val : (s₀.arrs inArr)[0]'h0_len = x.n := by simp [hs₀, encAlg64FaithfulIn, encGraph]
      let s₁ := s₀.setReg 0 x.n
      have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
      let s₂ := s₁.setReg 4 0
      have hex₂ : Exec w (.assign 4 (.const 0)) s₁ s₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let v₀ : Fin x.n := ⟨0, x.hn⟩
      rcases setSingletonBitSetProg_exec v₀ 18 0 4 hw hn_w (s := s₂) rfl rfl with
        ⟨s₃, t₃, hex₃, ht₃, hbit₃, _, hreg₃⟩
      let sets : ℕ → Finset (Fin x.n) := fun _ => {v₀}
      rcases packBitSetsUpTo_exec 1 sets hw hn_w hw (by simpa using hn_w) 1 le_rfl
          (s := s₃) (by rw [hreg₃ 0]; rfl)
          (fun j' hj' => by simpa [show j' = 0 by omega] using hbit₃) with
        ⟨s₄, t₄, hex₄, ht₄, _, hout_len₄, hpack₄, _⟩
      have hsq : x.n + 1 ≤ (x.n + 1) ^ 2 := Nat.le_self_pow (by omega) (x.n + 1)
      have htime₁ : 3 + (2 + (t₃ + t₄)) ≤ 40 * (alg64FaithfulSize 1 x + 1) ^ 2 := by
        change 3 + (2 + (t₃ + t₄)) ≤ 40 * (x.n + 1) ^ 2
        omega
      have hmodel : Compute.IsCliqueModel x.G 1 (Compute.decAlg64Out 1 x.n (s₄.arrs outArr)) := by
        refine ⟨?_, ?_, ?_⟩
        · intro i
          have hi : i = ⟨0, by omega⟩ := Fin.ext (by omega)
          subst hi
          rw [decAlg64Out_eq_of_packed sets (s₄.arrs outArr) hout_len₄ hpack₄]
          exact ⟨Finset.singleton_nonempty v₀, connected_induce_singleton x.G v₀⟩
        · intro i j hij
          exact absurd (Fin.ext (by omega : i.1 = j.1)) hij
        · intro i j hij
          exact absurd (Fin.ext (by omega : i.1 = j.1)) hij
      exact ⟨s₄, 3 + (2 + (t₃ + t₄)),
        .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
        htime₁, hmodel, hasGraphModel_of_isCliqueModel x.G _ hmodel⟩
    | succ p₂ =>
      cases p₂ with
      | zero =>
        -- `p = 2`: `4 * x.n ≤ 8 * x.G.edgeFinset.card` and `0 < x.n` give `1 ≤ |E|`
        unfold ComputesArrRelInTime ComputesRelInTime alg64FaithfulProg
        refine ⟨80, 2, by omega, by omega, fun x s₀ hs₀ => ?_⟩
        let edges := edgeListOf x.G
        have hm_eq : edges.length = x.G.edgeFinset.card :=
          length_edgeListOf_eq_card_edgeFinset x.G
        have hm_pos : 0 < edges.length := by
          have h1 := x.hedges
          have h2 := x.hn
          change 4 * x.n ≤ 8 * x.G.edgeFinset.card at h1
          omega
        let u₀ : Fin x.n := (edges[0]'hm_pos).1
        let v₀ : Fin x.n := (edges[0]'hm_pos).2
        have hmem₀ : edges[0]'hm_pos ∈ edgeListOf x.G := List.getElem_mem hm_pos
        obtain ⟨huv_lt, hadj_uv⟩ := (mem_edgeListOf x.G _).mp hmem₀
        have huv_ne : u₀ ≠ v₀ := fun h => by
          have hval : u₀.1 = v₀.1 := congrArg Fin.val h
          omega
        let w := wordSize 2 (alg64FaithfulSize 2 x)
        have hw_bound : 2 * (alg64FaithfulSize 2 x + 2) < 2 ^ w :=
          two_mul_lt_two_pow_wordSize (c := 2) (n := alg64FaithfulSize 2 x) (by omega)
        have hsize_eq : alg64FaithfulSize 2 x = x.n := rfl
        have hw3 : 3 < 2 ^ w := by omega
        have hw2 : 2 < 2 ^ w := by omega
        have hw : 1 < 2 ^ w := by omega
        have h0_w : 0 < 2 ^ w := by omega
        have hn_w : x.n < 2 ^ w := by omega
        have h2n_w : 2 * x.n < 2 ^ w := by omega
        have hu₀_w : u₀.1 < 2 ^ w := Nat.lt_trans u₀.2 hn_w
        have hv₀_w : v₀.1 < 2 ^ w := Nat.lt_trans v₀.2 hn_w
        have hin_len : (s₀.arrs inArr).length = 2 + 2 * edges.length := by
          simp [hs₀, encAlg64FaithfulIn, encGraph, edges]; omega
        have h0_len : 0 < (s₀.arrs inArr).length := by omega
        have h2_len : 2 < (s₀.arrs inArr).length := by omega
        have h3_len : 3 < (s₀.arrs inArr).length := by omega
        have h0_val : (s₀.arrs inArr)[0]'h0_len = x.n := by
          simp [hs₀, encAlg64FaithfulIn, encGraph]
        have h2_val : (s₀.arrs inArr)[2]'h2_len = u₀.1 := by
          have h := getElem_flatEdges_even edges hm_pos
          simpa [hs₀, encAlg64FaithfulIn, encGraph, edges, u₀] using h
        have h3_val : (s₀.arrs inArr)[3]'h3_len = v₀.1 := by
          have h := getElem_flatEdges_odd edges hm_pos
          simpa [hs₀, encAlg64FaithfulIn, encGraph, edges, v₀] using h
        let s₁ := s₀.setReg 0 x.n
        have hex₁ : Exec w (.assign 0 (.read inArr (.const 0))) s₀ s₁ 3 :=
          .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
        let s₂ := s₁.setReg 4 u₀.1
        have hex₂ : Exec w (.assign 4 (.read inArr (.const 2))) s₁ s₂ 3 :=
          .assign (by simp [s₁, Expr.eval, checkWord, hw2, h2_len, h2_val, hu₀_w])
        let s₃ := s₂.setReg 5 v₀.1
        have hex₃ : Exec w (.assign 5 (.read inArr (.const 3))) s₂ s₃ 3 :=
          .assign (by simp [s₂, s₁, Expr.eval, checkWord, hw3, h3_len, h3_val, hv₀_w])
        rcases setSingletonBitSetProg_exec u₀ 18 0 4 hw hn_w (s := s₃) rfl rfl with
          ⟨s₄, t₄, hex₄, ht₄, hbit₄, _, hreg₄⟩
        rcases setSingletonBitSetProg_exec v₀ 19 0 5 hw hn_w
            (s := s₄) (by rw [hreg₄ 0]; rfl) (by rw [hreg₄ 5]; rfl) with
          ⟨s₅, t₅, hex₅, ht₅, hbit₅, harr₅, hreg₅⟩
        let sets : ℕ → Finset (Fin x.n) := fun j => if j = 0 then {u₀} else {v₀}
        have hbits₅ : ∀ j < 2, IsBitSet (sets j) (18 + j) s₅ := by
          intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            dsimp [sets]
            exact hbit₄.of_arr_eq (harr₅ 18 (by decide))
          · have hj1 : j = 1 := by omega
            subst hj1
            dsimp [sets]
            exact hbit₅
        rcases packBitSetsUpTo_exec 2 sets hw hn_w hw2 h2n_w 2 le_rfl
            (s := s₅) (by rw [hreg₅ 0, hreg₄ 0]; rfl) hbits₅ with
          ⟨s₆, t₆, hex₆, ht₆, _, hout_len₆, hpack₆, _⟩
        have hsq : (x.n + 1) * (x.n + 1) = (x.n + 1) ^ 2 := (Nat.pow_two (x.n + 1)).symm
        have hn_le_sq : x.n + 1 ≤ (x.n + 1) ^ 2 := Nat.le_self_pow (by omega) (x.n + 1)
        have htime₂ :
            3 + (3 + (3 + (t₄ + (t₅ + t₆)))) ≤ 80 * (alg64FaithfulSize 2 x + 1) ^ 2 := by
          change 3 + (3 + (3 + (t₄ + (t₅ + t₆)))) ≤ 80 * (x.n + 1) ^ 2
          omega
        have hmodel : Compute.IsCliqueModel x.G 2 (Compute.decAlg64Out 2 x.n (s₆.arrs outArr)) := by
          have hdec : ∀ i : Fin 2, Compute.decAlg64Out 2 x.n (s₆.arrs outArr) i = sets i.1 :=
            fun i => decAlg64Out_eq_of_packed sets (s₆.arrs outArr) hout_len₆ hpack₆ i
          refine ⟨?_, ?_, ?_⟩
          · intro i
            rw [hdec i]
            by_cases hi0 : i.1 = 0
            · have hif : sets i.1 = {u₀} := by simp [sets, hi0]
              rw [hif]
              exact ⟨Finset.singleton_nonempty u₀, connected_induce_singleton x.G u₀⟩
            · have hif : sets i.1 = {v₀} := by simp [sets, hi0]
              rw [hif]
              exact ⟨Finset.singleton_nonempty v₀, connected_induce_singleton x.G v₀⟩
          · intro i j hij
            rw [hdec i, hdec j]
            have hij_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
            dsimp [sets]
            split_ifs with h1 h2 h2
            · omega
            · exact Finset.disjoint_singleton.mpr huv_ne
            · exact Finset.disjoint_singleton.mpr huv_ne.symm
            · omega
          · intro i j hij
            rw [hdec i, hdec j]
            have hij_val : i.1 ≠ j.1 := fun h => hij (Fin.ext h)
            dsimp [sets]
            split_ifs with h1 h2 h2
            · omega
            · exact ⟨u₀, Finset.mem_singleton_self u₀, v₀, Finset.mem_singleton_self v₀, hadj_uv⟩
            · exact ⟨v₀, Finset.mem_singleton_self v₀, u₀, Finset.mem_singleton_self u₀,
                hadj_uv.symm⟩
            · omega
        exact ⟨s₆, 3 + (3 + (3 + (t₄ + (t₅ + t₆)))),
          .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
          htime₂, hmodel, hasGraphModel_of_isCliqueModel x.G _ hmodel⟩
      | succ p₃ =>
        exact algorithm_6_4_faithful_of_three_le (p₃ + 3) (by omega)

end GraphMinor.GM13
