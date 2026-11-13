module

public import GraphMinor.HP25.Defs

/-!
# The edges of the frame are safe

Humeau and Pous, arXiv:2505.16431v2, Section 5.1 (page 15): "the edges $x_ix_{i+1}$
($1\le i\le k-1$) and $x_kx_1$ are all safe for $T$ since they cannot be used in a crossing. Hence
we assume that $T$ induces a cycle $C$ in $G$."

This file proves the sentence (`isCrossed_sup_edge_iff`): adding an edge between two consecutive
entries of the tuple changes nothing. A `T`-path that uses an edge between two entries of `T` has
these two entries as its ends, since its inner vertices avoid `T`. The two ends of a path of a
crossing are not consecutive in the tuple, because an entry of the other path lies between them on
each side. So no path of a crossing uses the new edge, and the crossing lies in `G`.

The file also proves that crossings survive adding edges (`IsCrossed.mono`).
-/

public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} {G H : SimpleGraph V}

/-- `Walk.mapLe` keeps the support. -/
theorem support_mapLe {u v : V} (p : G.Walk u v) (h : G ≤ H) : (p.mapLe h).support = p.support := by
  simp [Walk.mapLe, Walk.support_map]

/-- A `T`-path of `G` is a `T`-path of every larger graph. -/
theorem IsTPath.mapLe {T : List V} {u v : V} {p : G.Walk u v} (hp : IsTPath G T p) (h : G ≤ H) :
    IsTPath H T (p.mapLe h) := by
  refine ⟨hp.1.mapLe h, hp.2.1, hp.2.2.1, fun x hx => ?_⟩
  rw [support_mapLe] at hx
  exact hp.2.2.2 x hx

/-- Crossings survive adding edges: if `G ≤ H` and `T` is crossed in `G`, it is crossed in `H`. -/
theorem IsCrossed.mono {T : List V} (hc : IsCrossed G T) (h : G ≤ H) : IsCrossed H T := by
  obtain ⟨a, b, c, d, Q, R, hidx, hQ, hR, hdisj⟩ := hc
  refine ⟨a, b, c, d, Q.mapLe h, R.mapLe h, hidx, hQ.mapLe h, hR.mapLe h, ?_⟩
  simpa [support_mapLe] using hdisj

/-- A `T`-path of `H` whose edges avoid `s(u, v)` is a `T`-path of `G` when `H ≤ G ⊔ edge u v`. -/
theorem IsTPath.transfer {T : List V} {u v a b : V} {p : (G ⊔ edge u v).Walk a b}
    (hp : IsTPath (G ⊔ edge u v) T p) (he : s(u, v) ∉ p.edges) :
    ∃ q : G.Walk a b, IsTPath G T q ∧ q.support = p.support := by
  have hsub : ∀ e, e ∈ p.edges → e ∈ G.edgeSet := by
    intro e hep
    induction e using Sym2.ind with
    | _ x y =>
      have hadj := p.adj_of_mem_edges hep
      rcases (sup_adj _ _ _ _).1 hadj with h | h
      · exact h
      · exfalso
        rw [edge_adj] at h
        rcases h.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact he hep
        · exact he (by rwa [Sym2.eq_swap])
  refine ⟨p.transfer G hsub, ⟨hp.1.transfer hsub, hp.2.1, hp.2.2.1, ?_⟩, Walk.support_transfer _ _⟩
  intro x hx
  rw [Walk.support_transfer] at hx
  exact hp.2.2.2 x hx

/-- A `T`-path that uses an edge between two distinct entries `u`, `v` of `T` has ends `u` and
`v`: all its vertices in `T` are ends. -/
theorem ends_of_mem_edges {T : List V} {u v a b : V} {p : H.Walk a b}
    (hp : IsTPath H T p) (he : s(u, v) ∈ p.edges) (hu : u ∈ T) (hv : v ∈ T) (huv : u ≠ v) :
    (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
  have hu' : u = a ∨ u = b := by
    by_contra h
    push Not at h
    exact (hp.2.2.2 u (p.fst_mem_support_of_mem_edges he) h.1 h.2).1 hu
  have hv' : v = a ∨ v = b := by
    by_contra h
    push Not at h
    exact (hp.2.2.2 v (p.snd_mem_support_of_mem_edges he) h.1 h.2).1 hv
  rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
  · exact absurd rfl huv
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl huv

/-- The edges of the frame are safe (Humeau and Pous, Section 5.1, page 15): for a tuple `T` of at
least three distinct vertices and two entries `u = T[i]`, `v = T[j]` that are consecutive on the
cycle (`j = i + 1`, or `i` and `j` are the first and last positions), adding the edge `uv` does not
change whether `T` is crossed. -/
theorem isCrossed_sup_edge_iff {T : List V} (hT : T.Nodup) (hk : 3 ≤ T.length) {i j : ℕ} {u v : V}
    (hu : T[i]? = some u) (hv : T[j]? = some v)
    (hij : j = i + 1 ∨ (i = 0 ∧ j + 1 = T.length)) :
    IsCrossed (G ⊔ edge u v) T ↔ IsCrossed G T := by
  refine ⟨fun hc => ?_, fun hc => hc.mono le_sup_left⟩
  obtain ⟨a, b, c, d, Q, R, ⟨i', r, j', s, h1, h2, h3, hi', hr, hj', hs⟩, hQ, hR, hdisj⟩ := hc
  have hilt : i < T.length := (List.getElem?_eq_some_iff.1 hu).1
  have hjlt : j < T.length := (List.getElem?_eq_some_iff.1 hv).1
  have hslt : s < T.length := (List.getElem?_eq_some_iff.1 hs).1
  have huv : u ≠ v := by
    intro h
    have : i = j := (hT.getElem?_inj hilt).1 (by rw [hu, hv, h])
    omega
  have huT : u ∈ T := List.mem_of_getElem? hu
  have hvT : v ∈ T := List.mem_of_getElem? hv
  -- equal entries have equal positions
  have pos : ∀ {k l : ℕ} {x : V}, T[k]? = some x → T[l]? = some x → k = l := by
    intro k l x hk hl
    exact (hT.getElem?_inj (List.getElem?_eq_some_iff.1 hk).1).1 (by rw [hk, hl])
  by_cases hQe : s(u, v) ∈ Q.edges
  · exfalso
    rcases ends_of_mem_edges hQ hQe huT hvT huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := pos hu hi'; have := pos hv hj'; omega
    · have := pos hu hj'; have := pos hv hi'; omega
  by_cases hRe : s(u, v) ∈ R.edges
  · exfalso
    rcases ends_of_mem_edges hR hRe huT hvT huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := pos hu hr; have := pos hv hs; omega
    · have := pos hu hs; have := pos hv hr; omega
  obtain ⟨Q', hQ', hQs⟩ := hQ.transfer hQe
  obtain ⟨R', hR', hRs⟩ := hR.transfer hRe
  exact ⟨a, b, c, d, Q', R', ⟨i', r, j', s, h1, h2, h3, hi', hr, hj', hs⟩, hQ', hR',
    by rw [hQs, hRs]; exact hdisj⟩

end GraphMinor.HP25
