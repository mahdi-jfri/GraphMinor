module

public import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Enumerating each original edge once

Section 7.2 permits any prescribed number of original edges. We scan vertices in
numerical order and retain only neighbours with larger indices. This lists each
undirected edge once, so a prefix gives a set of exactly the requested size.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- The oriented edges in one row, with their smaller endpoint first. -/
def edgeRow {N : ℕ} (lists : Fin N → List ℕ) (u : Fin N) : List (Fin N × Fin N) :=
  ((toFin N (lists u)).filter (fun v => u.val < v.val)).map (fun v => (u, v))

/-- Enumerate the edges once by increasing smaller endpoint and the old neighbour order. -/
def edgeStream {N : ℕ} (lists : Fin N → List ℕ) : List (Fin N × Fin N) :=
  (List.finRange N).flatMap (edgeRow lists)

/-- Membership in a row records its first endpoint and the strict endpoint order. -/
theorem mem_edgeRow {N : ℕ} (lists : Fin N → List ℕ) (u a b : Fin N) :
    (a, b) ∈ edgeRow lists u ↔ a = u ∧ b.val ∈ lists u ∧ u.val < b.val := by
  simp only [edgeRow, List.mem_map, List.mem_filter, decide_eq_true_eq, mem_toFin,
    Prod.mk.injEq]
  constructor
  · rintro ⟨v, ⟨hv, hlt⟩, rfl, rfl⟩
    exact ⟨rfl, hv, hlt⟩
  · rintro ⟨rfl, hb, hlt⟩
    exact ⟨b, ⟨hb, hlt⟩, rfl, rfl⟩

/-- The stream contains precisely the increasing orientations of the graph edges. -/
theorem mem_edgeStream {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (a b : Fin N) :
    (a, b) ∈ edgeStream lists ↔ G.Adj a b ∧ a.val < b.val := by
  simp only [edgeStream, List.mem_flatMap, List.mem_finRange, true_and, mem_edgeRow]
  constructor
  · rintro ⟨u, rfl, hb, hlt⟩
    exact ⟨((h a).2.2.2 b).mp hb, hlt⟩
  · rintro ⟨ha, hlt⟩
    exact ⟨a, rfl, ((h a).2.2.2 b).mpr ha, hlt⟩

/-- No oriented edge appears twice in the stream. -/
theorem edgeStream_nodup {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) : (edgeStream lists).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun u _ => ((nodup_toFin (h u).2.1 (h u).1).filter _).map
    (fun a b he => congrArg Prod.snd he), ?_⟩
  apply (List.nodup_finRange N).imp
  intro u v huv p hpu hpv
  obtain ⟨a, b⟩ := p
  exact huv (((mem_edgeRow lists u a b).mp hpu).1.symm.trans
    ((mem_edgeRow lists v a b).mp hpv).1)

/-- Forgetting edge orientation still leaves a duplicate-free list. -/
theorem edgeStream_keys_nodup {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) : ((edgeStream lists).map (fun p => s(p.1, p.2))).Nodup := by
  apply (edgeStream_nodup h).map_on
  intro a ha b hb he
  have hla := ((mem_edgeStream h a.1 a.2).mp ha).2
  have hlb := ((mem_edgeStream h b.1 b.2).mp hb).2
  rcases Sym2.eq_iff.mp he with hh | hh
  · exact Prod.ext hh.1 hh.2
  · have h1 := congrArg Fin.val hh.1
    have h2 := congrArg Fin.val hh.2
    omega

/-- The undirected keys in the stream are exactly the graph's edge set. -/
theorem mem_edgeStream_keys {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (e : Sym2 (Fin N)) :
    e ∈ (edgeStream lists).map (fun p => s(p.1, p.2)) ↔ e ∈ G.edgeSet := by
  induction e using Sym2.ind with
  | _ a b =>
    constructor
    · intro he
      obtain ⟨⟨u, v⟩, huv, heq⟩ := List.mem_map.mp he
      have ha := ((mem_edgeStream h u v).mp huv).1
      rw [← heq]
      exact ha
    · intro he
      have hab : G.Adj a b := he
      by_cases hlt : a.val < b.val
      · exact List.mem_map.mpr ⟨(a, b), (mem_edgeStream h a b).mpr ⟨hab, hlt⟩, rfl⟩
      · have hne : a.val ≠ b.val := fun hh => hab.ne (Fin.ext hh)
        exact List.mem_map.mpr ⟨(b, a), (mem_edgeStream h b a).mpr ⟨hab.symm, by omega⟩,
          Sym2.eq_swap⟩

/-- The stream length is the number of original edges. -/
theorem edgeStream_length {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) : (edgeStream lists).length = G.edgeSet.ncard := by
  classical
  have heq : (↑((edgeStream lists).map (fun p => s(p.1, p.2))).toFinset : Set (Sym2 (Fin N))) =
      G.edgeSet := by
    ext e
    simpa only [Finset.mem_coe, List.mem_toFinset] using mem_edgeStream_keys h e
  rw [← heq, Set.ncard_coe_finset, List.toFinset_card_of_nodup (edgeStream_keys_nodup h), List.length_map]

/-- The undirected edges in the requested prefix of the stream. -/
def edgePrefixSet {N : ℕ} (lists : Fin N → List ℕ) (k : ℕ) : Set (Sym2 (Fin N)) :=
  ↑(((edgeStream lists).map (fun p => s(p.1, p.2))).take k).toFinset

/-- An edge prefix is a finite subset of the old edges with the requested size, when
that many old edges exist. -/
theorem edgePrefixSet_spec {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    (h : IsAdjListFamily G lists) (k : ℕ) (hk : k ≤ G.edgeSet.ncard) :
    edgePrefixSet lists k ⊆ G.edgeSet ∧ (edgePrefixSet lists k).Finite ∧
      (edgePrefixSet lists k).ncard = k := by
  classical
  refine ⟨fun e he => (mem_edgeStream_keys h e).mp (List.mem_of_mem_take
    (List.mem_toFinset.mp he)), Set.toFinite _, ?_⟩
  rw [edgePrefixSet, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (show (((edgeStream lists).map (fun p => s(p.1, p.2))).take k).Nodup from
      (edgeStream_keys_nodup h).take), List.length_take, List.length_map, edgeStream_length h,
    Nat.min_eq_left hk]

end GraphMinor.Compute.Crossing
