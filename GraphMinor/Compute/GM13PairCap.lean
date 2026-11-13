module

public import GraphMinor.Compute.MultiDigraph

/-!
# The multiplicity cap of Graph Minors XIII, (4.3), Step (1)

Step (1) of (4.3), page 77, keeps a maximal subgraph $G_1$ of $G$ "with at most $\delta$ loops at
each vertex and with no $\delta + 1$ edges mutually parallel". That cutoff is too small (see
the correction to (4.3), Step (1), in `corrections/GM13.md`), and we keep at most $\delta + 1$
edges between each pair of distinct
vertices instead, counting both directions together. This file defines that subgraph,
`MultiDigraph.capPair`, and a Word RAM program that writes its encoding in time linear in the
number of active pairs.

A `MultiDigraph` counts directed edges, and its encoding lists the active ordered pairs so that
`(u, v)` comes right before `(v, u)` when `u < v` and both are active. For a pair `(u, v)` with
`v < u`, the program therefore finds the number of edges from `v` to `u` in the triple just
before, and keeps at most `δ + 1` edges between `u` and `v` in all.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace MultiDigraph

/-- The subgraph of Step (1) of Graph Minors XIII, (4.3), page 77, with the corrected cutoff
(see the correction to (4.3), Step (1), in `corrections/GM13.md`): at most `δ` loops at each
vertex, and at most `δ + 1` edges between two
distinct vertices `u` and `v`, counting both directions. For `u < v` the edges from `u` to `v` are
kept first. -/
def capPair {n : ℕ} (δ : ℕ) (G : MultiDigraph n) : MultiDigraph n where
  edgeMult u v :=
    if u = v then Nat.min (G.edgeMult u v) δ
    else Nat.min (G.edgeMult u v)
      (δ + 1 - if v.1 < u.1 then Nat.min (G.edgeMult v u) (δ + 1) else 0)

theorem capPair_edgeMult {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (u v : Fin n) :
    (G.capPair δ).edgeMult u v =
      if u = v then Nat.min (G.edgeMult u v) δ
      else Nat.min (G.edgeMult u v)
        (δ + 1 - if v.1 < u.1 then Nat.min (G.edgeMult v u) (δ + 1) else 0) :=
  rfl

theorem capPair_loop {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (u : Fin n) :
    (G.capPair δ).edgeMult u u = Nat.min (G.edgeMult u u) δ := by
  simp [capPair_edgeMult]

theorem capPair_le_cap {n : ℕ} (δ : ℕ) (G : MultiDigraph n) : G.capPair δ ≤ G.cap δ := by
  intro u v
  rw [capPair_edgeMult, cap_edgeMult]
  split_ifs <;> simp only [Nat.min_def] <;> split_ifs <;> omega

theorem capPair_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) : G.capPair δ ≤ G :=
  le_trans (G.capPair_le_cap δ) (G.cap_le δ)

theorem capPair_edgeMult_le_succ {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (u v : Fin n) :
    (G.capPair δ).edgeMult u v ≤ δ + 1 :=
  le_trans (G.capPair_le_cap δ u v) (G.cap_edgeMult_le_succ δ u v)

theorem numEdges_capPair_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) :
    (G.capPair δ).numEdges ≤ (G.cap δ).numEdges :=
  numEdges_mono (G.capPair_le_cap δ)

/-- Between two distinct vertices `u < v`, the subgraph keeps `min (m(u, v) + m(v, u)) (δ + 1)`
edges in all. -/
theorem capPair_add {n : ℕ} (δ : ℕ) (G : MultiDigraph n) {u v : Fin n} (huv : u.1 < v.1) :
    (G.capPair δ).edgeMult u v + (G.capPair δ).edgeMult v u =
      Nat.min (G.edgeMult u v + G.edgeMult v u) (δ + 1) := by
  have hne : u ≠ v := fun h => by rw [h] at huv; exact Nat.lt_irrefl _ huv
  have hne' : v ≠ u := Ne.symm hne
  have hnlt : ¬ v.1 < u.1 := by omega
  rw [capPair_edgeMult, capPair_edgeMult]
  simp only [hne, hne', hnlt, huv, ↓reduceIte, Nat.min_def]
  split_ifs <;> omega

/-- Edges from `u` to `v` are kept first: if `u < v`, then the subgraph keeps
`min (m(u, v)) (δ + 1)` of them. -/
theorem capPair_of_lt {n : ℕ} (δ : ℕ) (G : MultiDigraph n) {u v : Fin n} (huv : u.1 < v.1) :
    (G.capPair δ).edgeMult u v = Nat.min (G.edgeMult u v) (δ + 1) := by
  have hne : u ≠ v := fun h => by rw [h] at huv; exact Nat.lt_irrefl _ huv
  have hnlt : ¬ v.1 < u.1 := by omega
  simp [capPair_edgeMult, hne, hnlt]

theorem activePairsList_capPair {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    (G.capPair δ).activePairsList =
      G.activePairsList.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) := by
  unfold activePairsList
  rw [List.filter_filter]
  refine List.filter_congr fun p _ => ?_
  symm
  rw [Bool.and_eq_left_iff_imp]
  intro h
  have h' : 0 < (G.capPair δ).edgeMult p.1 p.2 := of_decide_eq_true h
  exact decide_eq_true (Nat.lt_of_lt_of_le h' (G.capPair_le δ p.1 p.2))

/-- The triples of `G.capPair δ` written along a list of active directed pairs of `G`. -/
def capPairTriplesAux {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    List (Fin n × Fin n) → List ℕ
  | [] => []
  | (u, v) :: ps =>
    let m := (G.capPair δ).edgeMult u v
    if 0 < m then
      [u.1, v.1, m] ++ capPairTriplesAux G δ ps
    else
      capPairTriplesAux G δ ps

theorem capPairTriplesAux_eq_flatTriples_filter {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    ∀ (ps : List (Fin n × Fin n)),
      capPairTriplesAux G δ ps =
        flatTriples (G.capPair δ)
          (ps.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)))
  | [] => rfl
  | (u, v) :: ps => by
    simp only [capPairTriplesAux, List.filter_cons]
    by_cases hm : 0 < (G.capPair δ).edgeMult u v
    · simp only [hm, ↓reduceIte, decide_true, flatTriples,
        capPairTriplesAux_eq_flatTriples_filter G δ ps, List.cons_append, List.nil_append]
    · simp only [hm, ↓reduceIte, decide_false, Bool.false_eq_true,
        capPairTriplesAux_eq_flatTriples_filter G δ ps]

theorem flatTriples_capPair {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    flatTriples (G.capPair δ) (G.capPair δ).activePairsList =
      capPairTriplesAux G δ G.activePairsList := by
  rw [activePairsList_capPair, capPairTriplesAux_eq_flatTriples_filter]

theorem sumEdgeMult_capPair_activePairsList {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    sumEdgeMult (G.capPair δ) G.activePairsList = (G.capPair δ).numEdges := by
  rw [← sumEdgeMult_activePairsList (G.capPair δ), activePairsList_capPair,
    sumEdgeMult_filter_pos]

/-- In the canonical order, if `v < u` and both `(v, u)` and `(u, v)` are active, then `(v, u)`
comes right before `(u, v)`. -/
theorem activePairsList_getElem_pred {n : ℕ} (G : MultiDigraph n) {k : ℕ}
    (hk : k < G.activePairsList.length) {u v : Fin n}
    (hget : G.activePairsList[k] = (u, v)) (hvu : v.1 < u.1) (hpos : 0 < G.edgeMult v u) :
    ∃ hk1 : 1 ≤ k, G.activePairsList[k - 1]'(by omega) = (v, u) := by
  have hmem : (v, u) ∈ upperPairs n := (mem_upperPairs _).mpr (Nat.le_of_lt hvu)
  obtain ⟨P₁, P₂, hsplit⟩ := List.append_of_mem hmem
  have hne : v ≠ u := fun h => by rw [h] at hvu; exact Nat.lt_irrefl _ hvu
  have huv_pos : 0 < G.edgeMult u v := by
    have hm : (u, v) ∈ G.activePairsList := hget ▸ List.getElem_mem hk
    exact (G.mem_activePairsList _).mp hm
  have hblock : activeBlock G (v, u) = [(v, u), (u, v)] := by
    simp [activeBlock, hne, hpos, huv_pos]
  have hlist : G.activePairsList =
      P₁.flatMap (activeBlock G) ++ ((v, u) :: (u, v) :: P₂.flatMap (activeBlock G)) := by
    rw [activePairsList_eq_flatMap_upperPairs, hsplit, List.flatMap_append, List.flatMap_cons,
      hblock]
    simp
  set L := P₁.flatMap (activeBlock G) with hL
  have hlen : L.length + 1 < G.activePairsList.length := by
    rw [hlist]; simp
  have hget' : G.activePairsList[L.length + 1]'hlen = (u, v) := by
    simp only [hlist]
    rw [List.getElem_append_right (by omega)]
    simp
  have hkeq : k = L.length + 1 := by
    have hnd := G.nodup_activePairsList
    exact (hnd.getElem_inj_iff).mp (hget.trans hget'.symm)
  subst hkeq
  refine ⟨by omega, ?_⟩
  simp only [hlist, Nat.add_sub_cancel]
  rw [List.getElem_append_right (by omega)]
  simp

end MultiDigraph

end GraphMinor.Compute
