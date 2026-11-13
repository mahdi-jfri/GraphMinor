module

public import GraphMinor.HP25.Lemma43ClaimB
import GraphMinor.HP25.Lemma43Reroute
import GraphMinor.HP25.Lemma43Tools
import GraphMinor.HP25.Lemma41Tools
import GraphMinor.HP25.Lemma43ClaimA

/-!
# The gap of Lemma 4.3: the graph of a core

This file holds the graph part of the proof of `Lemma43Gap` (the cycle `P L` is crossless in
`G[𝒞 ∪ P]`). Graph Minors XIII, Section 8, attaches to a society `(G, Ω)` its *core*: a set `Z` of
vertices, with `Ω̄ ⊆ Z`, such that every vertex outside `Z` reaches at most three vertices of `Z` by
paths with no other vertex in `Z`. Two vertices of `Z` are adjacent in the core when a path of `G`
joins them with no inner vertex in `Z`. Here we only use these two properties of `Z`, stated for a
simple graph, and we do not need the core to be 4-linked.

* `coreGraph G Z`: the graph on `V` in which distinct `u, w ∈ Z` are adjacent when a walk of `G`
  joins them with no inner vertex in `Z`.
* `exists_coreWalk`: a walk of `G` with both ends in `Z` gives a walk of `coreGraph G Z` with the
  same ends, on the vertices of the walk that lie in `Z`.
* `adj_of_coreGraph_adj`: if `G` is maximally crossless on `S` for a cycle `C ⊆ Z`, then two vertices
  of `S` that are adjacent in the core are adjacent in `G`. Otherwise `G + uw` has a crossing, and
  the path of the crossing that uses `uw` can go around through the walk of `G` from `u` to `w`. The
  other path of the crossing does not meet that walk: a vertex outside `Z` on both would reach `u`,
  `w` and two more vertices of `Z`, four in all.
* `Case2.mem_core`: in the second case of Lemma 4.3 every vertex of `P` lies in `Z`. Otherwise the
  last vertex of `Z` before it and the first one after it on `P` are adjacent in the core, so
  adjacent in `G`, against "P is induced".
-/

public section

namespace GraphMinor.HP25

open SimpleGraph Set

variable {V : Type*} {G : SimpleGraph V}

/-- The graph of the core with vertex set `Z`: distinct `u, w ∈ Z` are adjacent when some walk of
`G` from `u` to `w` has no inner vertex in `Z` (Graph Minors XIII, Section 8, pages 93–94: "distinct
$u, v \in Z$ are adjacent if and only if there is a ... path in $G$ between $u$ and $v$ with no
internal vertex in $Z$"). -/
@[expose] def coreGraph (G : SimpleGraph V) (Z : Set V) : SimpleGraph V where
  Adj u w := u ≠ w ∧ u ∈ Z ∧ w ∈ Z ∧
    ∃ p : G.Walk u w, ∀ t ∈ p.support, t ≠ u → t ≠ w → t ∉ Z
  symm := ⟨fun u w ⟨hne, hu, hw, p, hp⟩ => ⟨hne.symm, hw, hu, p.reverse, fun t ht h1 h2 =>
    hp t (by rwa [Walk.support_reverse, List.mem_reverse] at ht) h2 h1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `w ∈ Z` is reached from `v` by a walk of `G` with no vertex in `Z` other than `w`. -/
@[expose] def ReachOut (G : SimpleGraph V) (Z : Set V) (v w : V) : Prop :=
  w ∈ Z ∧ ∃ p : G.Walk v w, ∀ t ∈ p.support, t ≠ w → t ∉ Z

/-- A walk ending in `Z` splits at its first vertex in `Z`. -/
theorem exists_first_split {Z : Set V} : ∀ {a v : V} (p : G.Walk a v), v ∈ Z →
    ∃ w ∈ Z, ∃ (q₀ : G.Walk a w) (q₁ : G.Walk w v), p = q₀.append q₁ ∧
      ∀ t ∈ q₀.support, t ≠ w → t ∉ Z
  | _, _, .nil, hv => ⟨_, hv, .nil, .nil, rfl, fun t ht h => by simp_all⟩
  | a, _, .cons h p', hv => by
    by_cases ha : a ∈ Z
    · exact ⟨a, ha, .nil, .cons h p', rfl, fun t ht h' => by simp_all⟩
    · obtain ⟨w, hw, q₀, q₁, rfl, hq⟩ := exists_first_split p' hv
      refine ⟨w, hw, .cons h q₀, q₁, rfl, fun t ht htw => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ha
      · exact hq t ht htw

/-- **Walks of `G` give walks of the core.** A walk of `G` with both ends in `Z` gives a walk of
`coreGraph G Z` with the same ends, whose vertices are vertices of the walk in `Z`: consecutive
vertices of the walk in `Z` are joined in the core by the piece of the walk between them. -/
theorem exists_coreWalk {Z : Set V} : ∀ (n : ℕ) {u v : V} (p : G.Walk u v), p.length ≤ n →
    u ∈ Z → v ∈ Z → ∃ q : (coreGraph G Z).Walk u v, ∀ t ∈ q.support, t ∈ p.support ∧ t ∈ Z
  | _, _, _, .nil, _, hu, _ => ⟨.nil, fun t ht => by simp_all⟩
  | 0, _, _, .cons _ _, hn, _, _ => by simp at hn
  | n + 1, u, v, .cons (v := a) h p', hn, hu, hv => by
    obtain ⟨w, hw, q₀, q₁, rfl, hq⟩ := exists_first_split p' hv
    have hlen : q₁.length ≤ n := by
      rw [Walk.length_cons, Walk.length_append] at hn
      omega
    obtain ⟨r, hr⟩ := exists_coreWalk n q₁ hlen hw hv
    by_cases huw : u = w
    · subst huw
      exact ⟨r, fun t ht => ⟨by
        have := (hr t ht).1
        rw [Walk.support_cons, Walk.support_append]
        rw [← Walk.cons_tail_support q₁, List.mem_cons] at this
        rcases this with rfl | h'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ h'), (hr t ht).2⟩⟩
    · have hadj : (coreGraph G Z).Adj u w := by
        refine ⟨huw, hu, hw, .cons h q₀, fun t ht htu htw => ?_⟩
        rw [Walk.support_cons, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact absurd rfl htu
        · exact hq t ht htw
      refine ⟨.cons hadj r, fun t ht => ?_⟩
      rw [Walk.support_cons, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact ⟨List.mem_cons_self, hu⟩
      · have := (hr t ht).1
        refine ⟨?_, (hr t ht).2⟩
        rw [Walk.support_cons, Walk.support_append]
        rw [← Walk.cons_tail_support q₁, List.mem_cons] at this
        rcases this with rfl | h'
        · exact List.mem_cons_of_mem _ (List.mem_append_left _ q₀.end_mem_support)
        · exact List.mem_cons_of_mem _ (List.mem_append_right _ h')

/-- The two parts of a path cut at one of its vertices meet only at that vertex. -/
theorem eq_of_mem_takeUntil_dropUntil [DecidableEq V] {u w x t : V} {p : G.Walk u w}
    (hp : p.IsPath) (hx : x ∈ p.support) (h1 : t ∈ (p.takeUntil x hx).support)
    (h2 : t ∈ (p.dropUntil x hx).support) : t = x := by
  have hnd := hp.support_nodup
  rw [← p.take_spec hx, Walk.support_append] at hnd
  rw [← Walk.cons_tail_support (p.dropUntil x hx), List.mem_cons] at h2
  rcases h2 with h2 | h2
  · exact h2
  · exact absurd h2 (List.disjoint_of_nodup_append hnd h1)

/-- A vertex outside `Z` on a path between two vertices of `Z`, with no other vertex of the path in
`Z`, reaches both ends. -/
theorem reachOut_of_path [DecidableEq V] {Z : Set V} {u w x : V} {p : G.Walk u w} (hp : p.IsPath)
    (hu : u ∈ Z) (hw : w ∈ Z) (hin : ∀ t ∈ p.support, t ≠ u → t ≠ w → t ∉ Z) (hx : x ∈ p.support)
    (hxZ : x ∉ Z) : ReachOut G Z x u ∧ ReachOut G Z x w := by
  refine ⟨⟨hu, (p.takeUntil x hx).reverse, fun t ht htu => hin t ?_ htu ?_⟩,
    ⟨hw, p.dropUntil x hx, fun t ht htw => hin t ?_ ?_ htw⟩⟩
  · rw [Walk.support_reverse, List.mem_reverse] at ht
    exact p.support_takeUntil_subset_support hx ht
  · rintro rfl
    rw [Walk.support_reverse, List.mem_reverse] at ht
    exact hxZ (eq_of_mem_takeUntil_dropUntil hp hx ht (p.dropUntil x hx).end_mem_support ▸ hw)
  · exact p.support_dropUntil_subset_support hx ht
  · rintro rfl
    exact hxZ (eq_of_mem_takeUntil_dropUntil hp hx (p.takeUntil x hx).start_mem_support ht ▸ hu)

/-- A vertex outside `Z` on a path with both ends in `Z` reaches two different vertices of `Z` on
the path. -/
theorem exists_two_reachOut [DecidableEq V] {Z : Set V} {c d x : V} {p : G.Walk c d}
    (hp : p.IsPath) (hc : c ∈ Z) (hd : d ∈ Z) (hx : x ∈ p.support) (hxZ : x ∉ Z) :
    ∃ b₁ b₂, b₁ ≠ b₂ ∧ b₁ ∈ p.support ∧ b₂ ∈ p.support ∧ ReachOut G Z x b₁ ∧
      ReachOut G Z x b₂ := by
  obtain ⟨b₁, hb₁, q₁, r₁, he₁, hq₁⟩ := exists_first_split (p.takeUntil x hx).reverse hc
  obtain ⟨b₂, hb₂, q₂, r₂, he₂, hq₂⟩ := exists_first_split (p.dropUntil x hx) hd
  have hm₁ : b₁ ∈ (p.takeUntil x hx).support := by
    have : b₁ ∈ (q₁.append r₁).support := (Walk.mem_support_append_iff q₁ r₁).mpr (Or.inl q₁.end_mem_support)
    rw [← he₁, Walk.support_reverse, List.mem_reverse] at this
    exact this
  have hm₂ : b₂ ∈ (p.dropUntil x hx).support := by
    have : b₂ ∈ (q₂.append r₂).support := (Walk.mem_support_append_iff q₂ r₂).mpr (Or.inl q₂.end_mem_support)
    rw [← he₂] at this
    exact this
  refine ⟨b₁, b₂, fun h => ?_, p.support_takeUntil_subset_support hx hm₁,
    p.support_dropUntil_subset_support hx hm₂, ⟨hb₁, q₁, hq₁⟩, ⟨hb₂, q₂, hq₂⟩⟩
  subst h
  exact hxZ (eq_of_mem_takeUntil_dropUntil hp hx hm₁ hm₂ ▸ hb₁)

/-- Four different vertices of `Z` reached from one vertex outside `Z` contradict the bound three. -/
theorem not_four_reachOut [Finite V] {Z : Set V}
    (hatt : ∀ v, v ∉ Z → {w | ReachOut G Z v w}.ncard ≤ 3) {x a b c d : V} (hx : x ∉ Z)
    (ha : ReachOut G Z x a) (hb : ReachOut G Z x b) (hc : ReachOut G Z x c)
    (hd : ReachOut G Z x d) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) : False := by
  have h4 : ({a, b, c, d} : Set V).ncard = 4 := by
    rw [Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]), Set.ncard_pair hcd]
  have hle : ({a, b, c, d} : Set V).ncard ≤ {w | ReachOut G Z x w}.ncard := by
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro t (rfl | rfl | rfl | rfl) <;> assumption
  have := hatt x hx
  omega

/-- **Core edges between vertices of `S` are edges.** Let `G` be maximally crossless on `S` for `C`,
let `C ⊆ Z`, and let every vertex outside `Z` reach at most three vertices of `Z`. If `u, w ∈ S` are
adjacent in `coreGraph G Z`, they are adjacent in `G`. -/
theorem adj_of_coreGraph_adj [Finite V] {S Z : Set V} {C : List V} (hmax : IsMaxCrosslessOn G S C)
    (hCZ : ∀ c ∈ C, c ∈ Z) (hatt : ∀ v, v ∉ Z → {w | ReachOut G Z v w}.ncard ≤ 3) {u w : V}
    (hu : u ∈ S) (hw : w ∈ S) (h : (coreGraph G Z).Adj u w) : G.Adj u w := by
  classical
  by_contra hn
  obtain ⟨hne, huZ, hwZ, p, hp⟩ := h
  rcases isCrossed_sup_edge_cases' (hmax.2.2 u hu w hw hne hn) with h |
    ⟨a, b, c, d, Q, R, halt, hQ, hQe, hR, hdisj⟩
  · exact hmax.2.1 h
  have hp' := p.bypass_isPath
  have hin : ∀ t ∈ p.bypass.support, t ≠ u → t ≠ w → t ∉ Z := fun t ht =>
    hp t (p.support_bypass_subset_support ht)
  have huQ : u ∈ Q.support := Q.fst_mem_support_of_mem_edges hQe
  have hwQ : w ∈ Q.support := Q.snd_mem_support_of_mem_edges hQe
  refine hmax.2.1 (reroute_edge Q R halt hQ hQe hR hdisj (Z := p.bypass.support)
    p.bypass.isChain_adj_support (Walk.support_head? _) (Walk.support_getLast? _) ?_ ?_)
  · intro t ht htC
    by_contra h'
    push Not at h'
    exact hin t ht h'.1 h'.2 (hCZ t htC)
  · intro t ht htR
    by_cases htu : t = u
    · exact hdisj (htu ▸ huQ) htR
    by_cases htw : t = w
    · exact hdisj (htw ▸ hwQ) htR
    have htZ := hin t ht htu htw
    obtain ⟨r₁, r₂⟩ := reachOut_of_path hp' huZ hwZ hin ht htZ
    obtain ⟨b₁, b₂, hb, hb₁, hb₂, s₁, s₂⟩ := exists_two_reachOut hR.1 (hCZ _ hR.2.1)
      (hCZ _ hR.2.2.1) htR htZ
    have hnQ : ∀ {y}, y ∈ R.support → y ∈ Q.support → False := fun h1 h2 => hdisj h2 h1
    exact not_four_reachOut hatt htZ r₁ r₂ s₁ s₂ hne (fun e => hnQ hb₁ (e ▸ huQ))
      (fun e => hnQ hb₂ (e ▸ huQ)) (fun e => hnQ hb₁ (e ▸ hwQ)) (fun e => hnQ hb₂ (e ▸ hwQ)) hb

/-- Two entries `P[a]`, `P[b]` of `Z` on a chain without repetition, with no entry of `Z` strictly
between them, are adjacent in the core. -/
theorem coreGraph_adj_of_stretch {Z : Set V} {P : List V} (hch : P.IsChain G.Adj) (hnd : P.Nodup)
    {a b : ℕ} (hab : a < b) (hb : b < P.length) (ha : P[a] ∈ Z) (hbZ : P[b] ∈ Z)
    (hin : ∀ (j : ℕ) (hj : j < P.length), a < j → j < b → P[j] ∉ Z) :
    (coreGraph G Z).Adj P[a] P[b] := by
  obtain ⟨hh, hl, hmem⟩ := stretch_facts (P := P) hab.le hb
  obtain ⟨p, hp⟩ := exists_walk_of_chain _ ((hch.drop a).take _) hh hl
  refine ⟨fun e => by have := (hnd.getElem_inj_iff).mp e; omega, ha, hbZ, p, fun t ht h1 h2 => ?_⟩
  rw [hp] at ht
  obtain ⟨j, hj, h1j, h2j, rfl⟩ := hmem t ht
  refine hin j hj (lt_of_le_of_ne h1j fun e => h1 (by subst e; rfl))
    (lt_of_le_of_ne h2j fun e => h2 (by subst e; rfl))

namespace Case2

variable {S Z : Set V} {x y z ℓ : V} {L P : List V}

/-- **Core edges along `P`.** In the second case of Lemma 4.3, two vertices of `P` adjacent in the
core are consecutive on `P`: they are adjacent in `G` (`adj_of_coreGraph_adj`), and `P` is
induced (`IsMuMin.induced`). -/
theorem core_adj_P [Finite V] (hc : Case2 G S x y z ℓ L P)
    (hCZ : ∀ c ∈ x :: y :: z :: L, c ∈ Z)
    (hatt : ∀ v, v ∉ Z → {w | ReachOut G Z v w}.ncard ≤ 3) {i j : ℕ} (hij : i < j)
    (hj : j < P.length) (h : (coreGraph G Z).Adj P[i] P[j]) : j = i + 1 := by
  have hadj := adj_of_coreGraph_adj hc.max hCZ hatt (hc.P_sub _ (List.getElem_mem _))
    (hc.P_sub _ (List.getElem_mem _)) h
  by_contra hne
  exact hc.mu.induced hc.ℓ_mem_S hc.ℓ_not_mem (i := i) (j := j) (by omega) hj hadj

/-- **The vertices of `P` lie in the core** (step 2 of the proof of the gap). If `P[i] ∉ Z`, the last
vertex of `Z` before it and the first after it on `P` are adjacent in the core, so consecutive on
`P` by `core_adj_P`, which is absurd. -/
theorem mem_core [Finite V] (hc : Case2 G S x y z ℓ L P) (hCZ : ∀ c ∈ x :: y :: z :: L, c ∈ Z)
    (hatt : ∀ v, v ∉ Z → {w | ReachOut G Z v w}.ncard ≤ 3) : ∀ v ∈ P, v ∈ Z := by
  intro v hv
  by_contra hvZ
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hv
  have h2 := hc.mu.1.two_le_length hc.cyc
  obtain ⟨a, b, hai, hib, hbn, ⟨ha, haZ⟩, ⟨hb, hbZ⟩, hmid⟩ := exists_gap
    (fun j => ∃ hj : j < P.length, P[j] ∈ Z) (i := i) (n := P.length - 1)
    ⟨by omega, by rw [hc.mu.1.getElem_zero (by omega)]; exact hCZ _ (by simp)⟩
    ⟨by omega, by rw [hc.mu.1.getElem_last (by omega)]; exact hCZ _ (by simp)⟩
    (fun ⟨_, h⟩ => hvZ h) (by omega)
  have hadj := coreGraph_adj_of_stretch (G := G) hc.mu.1.1 hc.mu.1.2.1 (by omega : a < b) hb haZ hbZ
    (fun j hj h1 h2 hjZ => hmid j h1 h2 ⟨hj, hjZ⟩)
  have := hc.core_adj_P hCZ hatt (by omega : a < b) hb hadj
  omega

end Case2

end GraphMinor.HP25
