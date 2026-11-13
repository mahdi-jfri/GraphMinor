module

public import GraphMinor.Compute.CrossingOpsBfsOrder

/-!
# Discovery edges are the scan-first parent edges

A fresh neighbour is discovered by the first scanned vertex adjacent to it. Earlier scanned
vertices have already discovered all their neighbours. Later queue entries cannot precede
its discovering vertex. Thus the recorded discovery edge uses precisely the scan parent.
-/

public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

universe u
variable {V : Type u} [DecidableEq V]

omit [DecidableEq V] in
/-- Every recorded discovery edge has both endpoints in the queue history and is a graph edge. -/
theorem BfsScanTrace.edge_endpoints {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges) :
    ∀ p c, (p, c) ∈ edges → p ∈ items ∧ c ∈ items ∧ G.Adj p c := by
  induction h with
  | nil => simp
  | root h empty r hr fresh ih =>
    intro p c he
    obtain ⟨hp, hc, hadj⟩ := ih p c he
    exact ⟨List.mem_append_left _ hp, List.mem_append_left _ hc, hadj⟩
  | @scan items head edges h pending fresh hnd hn ih =>
    intro p c he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨hp, hc, hadj⟩ := ih p c he
      exact ⟨List.mem_append_left _ hp, List.mem_append_left _ hc, hadj⟩
    · obtain ⟨v, hv, heq⟩ := List.mem_map.mp he
      have hp : items[head] = p := congrArg Prod.fst heq
      have hc : v = c := congrArg Prod.snd heq
      subst p
      subst v
      exact ⟨List.mem_append_left _ (List.getElem_mem pending), List.mem_append_right _ hv,
        ((hn c).mp hv).1⟩

private theorem isScanParent_append_iff {G : SimpleGraph V} {items fresh : List V} {c p : V}
    (hc : c ∈ items) :
    IsScanParent G (items ++ fresh) c p ↔ IsScanParent G items c p := by
  constructor
  · intro h
    have hp : p ∈ items := by
      by_contra hp
      have hlt := h.2.1
      rw [List.idxOf_append_of_notMem hp, List.idxOf_append_of_mem hc] at hlt
      have := List.idxOf_lt_length_of_mem hc
      omega
    refine ⟨h.1, ?_, fun y hy => ?_⟩
    · simpa only [List.idxOf_append_of_mem hp, List.idxOf_append_of_mem hc] using h.2.1
    · by_cases hym : y ∈ items
      · simpa only [List.idxOf_append_of_mem hp, List.idxOf_append_of_mem hym] using h.2.2 y hy
      · rw [List.idxOf_eq_length_iff.mpr hym]
        exact (List.idxOf_lt_length_of_mem hp).le
  · intro h
    have hp : p ∈ items := List.idxOf_lt_length_iff.mp
      (h.2.1.trans (List.idxOf_lt_length_of_mem hc))
    refine ⟨h.1, ?_, fun y hy => ?_⟩
    · simpa only [List.idxOf_append_of_mem hp, List.idxOf_append_of_mem hc] using h.2.1
    · rw [List.idxOf_append_of_mem hp]
      by_cases hym : y ∈ items
      · rw [List.idxOf_append_of_mem hym]; exact h.2.2 y hy
      · rw [List.idxOf_append_of_notMem hym]
        have := List.idxOf_lt_length_of_mem hp
        omega

private theorem scanParent_unique {G : SimpleGraph V} {items : List V} {c p q : V}
    (hc : c ∈ items) (hp : IsScanParent G items c p) (hq : IsScanParent G items c q) : p = q := by
  have hpm : p ∈ items := List.idxOf_lt_length_iff.mp
    (hp.2.1.trans (List.idxOf_lt_length_of_mem hc))
  have hqm : q ∈ items := List.idxOf_lt_length_iff.mp
    (hq.2.1.trans (List.idxOf_lt_length_of_mem hc))
  have heq : items.idxOf p = items.idxOf q := le_antisymm (hp.2.2 q hq.1) (hq.2.2 p hp.1)
  have hp' := List.getElem?_idxOf hpm
  have hq' := List.getElem?_idxOf hqm
  exact Option.some.inj (hp'.symm.trans (heq ▸ hq'))

/-- For every discovered vertex, its recorded discovery parent is exactly its scan parent
in the queue history. Roots have no discovery parent and no earlier neighbour. -/
theorem BfsScanTrace.parent_iff {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges) :
    ∀ c ∈ items, ∀ p, (p, c) ∈ edges ↔ IsScanParent G items c p := by
  induction h with
  | nil => simp
  | @root items head edges h empty r hr fresh ih =>
    intro c hc p
    rcases List.mem_append.mp hc with hc | hc
    · exact (ih c hc p).trans (isScanParent_append_iff hc).symm
    · have hcr : c = r := by simpa only [List.mem_singleton] using hc
      subst c
      constructor
      · intro he
        exact False.elim (fresh (h.edge_endpoints p r he).2.1)
      · intro hp
        have hpm : p ∈ items := by
          by_contra hpm
          have hlt := hp.2.1
          rw [List.idxOf_append_of_notMem hpm, List.idxOf_append_of_notMem fresh] at hlt
          simp only [List.idxOf_cons_self] at hlt
          omega
        have hpt : p ∈ items.take head := by simpa only [empty, List.take_length] using hpm
        exact False.elim (fresh (h.closed p hpt r hr hp.1.symm))
  | @scan items head edges h pending fresh hnd hn ih =>
    intro c hc p
    rcases List.mem_append.mp hc with hc | hc
    · have hnotfresh : c ∉ fresh := fun hf => ((hn c).mp hf).2.2 hc
      have hnew : (p, c) ∉ fresh.map (fun v => (items[head], v)) := by
        intro hm
        obtain ⟨v, hv, heq⟩ := List.mem_map.mp hm
        have he : v = c := congrArg Prod.snd heq
        exact hnotfresh (he ▸ hv)
      simp only [List.mem_append, hnew, or_false]
      exact (ih c hc p).trans (isScanParent_append_iff hc).symm
    · have hcdata := (hn c).mp hc
      have hu : items[head] ∈ items := List.getElem_mem pending
      have hparent : IsScanParent G (items ++ fresh) c items[head] := by
        refine ⟨hcdata.1.symm, ?_, fun y hy => ?_⟩
        · rw [List.idxOf_append_of_mem hu, List.idxOf_append_of_notMem hcdata.2.2,
            h.nodup.idxOf_getElem head pending]
          omega
        · rw [List.idxOf_append_of_mem hu, h.nodup.idxOf_getElem head pending]
          by_cases hym : y ∈ items
          · rw [List.idxOf_append_of_mem hym]
            by_contra hlt
            have hyt : y ∈ items.take head :=
              (List.mem_take_iff_idxOf_lt hym).mpr (by omega)
            exact hcdata.2.2 (h.closed y hyt c hcdata.2.1 hy.symm)
          · rw [List.idxOf_append_of_notMem hym]
            omega
      constructor
      · intro he
        rcases List.mem_append.mp he with he | he
        · exact False.elim (hcdata.2.2 (h.edge_endpoints p c he).2.1)
        · obtain ⟨v, hv, heq⟩ := List.mem_map.mp he
          have hp : items[head] = p := congrArg Prod.fst heq
          exact hp ▸ hparent
      · intro hp
        have hpu := scanParent_unique (List.mem_append_right items hc) hp hparent
        subst p
        exact List.mem_append_right _ (List.mem_map.mpr ⟨c, hc, rfl⟩)

/-- The undirected graph formed by the discovery edges of a BFS forest search. -/
@[expose] def bfsDiscoveryForest (edges : List (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel (fun p c => (p, c) ∈ edges)

/-- Once every input vertex is discovered, the discovery graph is the scan forest of the
queue history. The support hypothesis rules out graph edges to vertices outside the input. -/
theorem BfsScanTrace.discoveryForest_eq {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges)
    (hG : HP25.IsSupportedOn G T) (hcover : ∀ v ∈ T, v ∈ items) :
    bfsDiscoveryForest edges = scanForest G items := by
  ext a b
  change (a ≠ b ∧ ((a, b) ∈ edges ∨ (b, a) ∈ edges)) ↔
    IsScanParent G items a b ∨ IsScanParent G items b a
  constructor
  · rintro ⟨-, he | he⟩
    · exact Or.inr ((h.parent_iff b (h.edge_endpoints a b he).2.1 a).mp he)
    · exact Or.inl ((h.parent_iff a (h.edge_endpoints b a he).2.1 b).mp he)
  · rintro (hp | hp)
    · exact ⟨hp.1.ne, Or.inr ((h.parent_iff a (hcover a (hG hp.1)) b).mpr hp)⟩
    · exact ⟨Ne.symm hp.1.ne, Or.inl ((h.parent_iff b (hcover b (hG hp.1)) a).mpr hp)⟩

/-- The discovery graph of a covering BFS history satisfies the forest interface of
Section 7.1. -/
theorem BfsScanTrace.isScanFirstForest {G : SimpleGraph V} {T : Set V} {items : List V}
    {head : ℕ} {edges : List (V × V)} (h : BfsScanTrace G T items head edges)
    (hG : HP25.IsSupportedOn G T) (hcover : ∀ v ∈ T, v ∈ items) :
    IsScanFirstForest G T (bfsDiscoveryForest edges) :=
  ⟨items, h.isScanOrder hcover, h.discoveryForest_eq hG hcover⟩

end GraphMinor.Compute.Crossing
