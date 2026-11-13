module

public import GraphMinor.Compute.SpecsCrossing
public import GraphMinor.Crossing.BridgeCross

/-!
# Walk-based and list-based bridge crossings

This file links the walk-based crossing and bridge definitions of `GraphMinor.Crossing.BridgeDefs`
and `GraphMinor.Crossing.BridgeCross` (`HP25.IsCrossing`, `UsesDistinctBridges`, `bridgeCross`) to
the vertex-list predicates of `GraphMinor.Crossing.Defs` and `GraphMinor.Compute.SpecsCrossing`
(`IsPathList`, `IsDPathList`, `IsCrossingPair`, `InDistinctBridges`, `IsCrossingPairAt`).

It also generalizes `bridgeCross` to any bridge list `bridges : List (BridgeData V)` satisfying
`ValidBridgeList G verts D bridges` (`bridgeCrossWith`), showing that any duplicate-free list of
valid `D`-bridges covering all `D`-bridges of `G` produces a valid crossing when it returns `some`
and returns `some` whenever a crossing using distinct `D`-bridges exists.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

universe u
variable {V : Type u}

/-! ### 1. Converting between `IsTPath` walks and `IsDPathList` vertex lists -/

private lemma isPathList_reverse {G : SimpleGraph V} {L : List V} :
    Crossing.IsPathList G L.reverse ↔ Crossing.IsPathList G L := by
  unfold Crossing.IsPathList
  rw [List.reverse_ne_nil_iff, List.nodup_reverse, List.isChain_reverse]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor <;> (intro h; exact h.imp fun _ _ hab => hab.symm)

private lemma inner_append_cons_last (a : V) (mid : List V) (b : V) :
    Crossing.inner (a :: (mid ++ [b])) = mid := by
  simp [Crossing.inner]

private lemma inner_reverse (L : List V) :
    Crossing.inner L.reverse = (Crossing.inner L).reverse := by
  cases L with
  | nil => rfl
  | cons a rest =>
    cases rest using List.reverseRecOn with
    | nil => rfl
    | append_singleton mid b =>
      have h1 : (a :: (mid ++ [b])).reverse = b :: (mid.reverse ++ [a]) := by
        simp [List.reverse_append]
      rw [h1, inner_append_cons_last, inner_append_cons_last]

private lemma isDPathList_reverse {G : SimpleGraph V} {D L : List V} :
    IsDPathList G D L.reverse ↔ IsDPathList G D L := by
  unfold IsDPathList
  rw [isPathList_reverse, List.length_reverse, List.head?_reverse, List.getLast?_reverse,
    inner_reverse]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun y hy => h3 y (List.mem_reverse.mpr hy)⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun y hy => h3 y (List.mem_reverse.mp hy)⟩

private lemma hasEnds_reverse {L : List V} {a b : V} :
    HasEnds L.reverse a b ↔ HasEnds L b a := by
  unfold HasEnds
  rw [List.head?_reverse, List.getLast?_reverse, and_comm]

private lemma walk_support_head? {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.head? = some u := by
  cases p <;> simp

private lemma walk_support_getLast? {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.support.getLast? = some v := by
  induction p with
  | nil => simp
  | cons _ q ih =>
    rw [Walk.support_cons]
    cases hq : q.support with
    | nil => exact absurd hq q.support_ne_nil
    | cons b rest =>
      rw [List.getLast?_cons_cons, ← hq]
      exact ih

private lemma list_decomp_of_length_ge_two {L : List V} {u v : V}
    (hlen : 2 ≤ L.length) (hhead : L.head? = some u) (hlast : L.getLast? = some v) :
    L = u :: (Crossing.inner L ++ [v]) := by
  cases L with
  | nil => simp at hlen
  | cons a rest =>
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    cases rest using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton mid b =>
      have hlast' : (a :: (mid ++ [b])).getLast? = some b := by
        rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]
        simp
      rw [hlast'] at hlast
      simp only [Option.some.injEq] at hlast
      subst hlast
      rw [inner_append_cons_last]

private lemma mem_inner_iff_of_nodup {L : List V} {u v : V}
    (hlen : 2 ≤ L.length) (hnd : L.Nodup) (hhead : L.head? = some u) (hlast : L.getLast? = some v)
    (x : V) :
    x ∈ Crossing.inner L ↔ x ∈ L ∧ x ≠ u ∧ x ≠ v := by
  have hdec := list_decomp_of_length_ge_two hlen hhead hlast
  have hnd' : (u :: (Crossing.inner L ++ [v])).Nodup := hdec ▸ hnd
  rw [List.nodup_cons, List.mem_append, List.mem_singleton, not_or, List.nodup_append] at hnd'
  constructor
  · intro hx
    have hxu : x ≠ u := fun h => hnd'.1.1 (h ▸ hx)
    have hxv : x ≠ v := fun h => hnd'.2.2.2 x hx v (by simp) h
    have hxL : x ∈ L := by
      rw [hdec]
      exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
    exact ⟨hxL, hxu, hxv⟩
  · rintro ⟨hxL, hxu, hxv⟩
    rw [hdec, List.mem_cons, List.mem_append, List.mem_singleton] at hxL
    exact (hxL.resolve_left hxu).resolve_right hxv

/-- Every `D`-path `P : G.Walk u v` with `u ≠ v` has support satisfying `IsDPathList G D` and
`HasEnds P.support u v`. -/
theorem isDPathList_support_of_isTPath {G : SimpleGraph V} {D : List V} {u v : V}
    {P : G.Walk u v} (hP : HP25.IsTPath G D P) (huv : u ≠ v) :
    IsDPathList G D P.support ∧ HasEnds P.support u v := by
  have hhead := walk_support_head? P
  have hlast := walk_support_getLast? P
  have hnd := hP.1.support_nodup
  have hlen : 2 ≤ P.support.length := by
    cases P with
    | nil => exact absurd rfl huv
    | cons _ q =>
      rw [Walk.support_cons, List.length_cons]
      have := List.length_pos_iff.mpr q.support_ne_nil
      omega
  refine ⟨⟨⟨P.support_ne_nil, hnd, P.isChain_adj_support⟩, hlen, ?_, ?_, ?_⟩, ⟨hhead, hlast⟩⟩
  · intro a ha
    rw [hhead, Option.some.injEq] at ha
    exact ha ▸ hP.2.1
  · intro b hb
    rw [hlast, Option.some.injEq] at hb
    exact hb ▸ hP.2.2.1
  · intro y hy
    obtain ⟨hyP, hyu, hyv⟩ := (mem_inner_iff_of_nodup hlen hnd hhead hlast y).mp hy
    exact (hP.2.2.2 y hyP hyu hyv).1

private lemma exists_walk_of_isChain {G : SimpleGraph V} :
    ∀ (L : List V) {u v : V}, L ≠ [] → L.IsChain G.Adj →
      L.head? = some u → L.getLast? = some v →
      ∃ P : G.Walk u v, P.support = L
  | [], _, _, hne, _, _, _ => absurd rfl hne
  | [a], u, v, _, _, hhead, hlast => by
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hhead hlast
    subst hhead; subst hlast
    exact ⟨Walk.nil, rfl⟩
  | a :: b :: rest, u, v, _, hc, hhead, hlast => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rw [List.isChain_cons_cons] at hc
    rw [List.getLast?_cons_cons] at hlast
    obtain ⟨P', hP'⟩ := exists_walk_of_isChain (b :: rest) (by simp) hc.2 rfl hlast
    exact ⟨Walk.cons hc.1 P', by simp [hP']⟩

/-- Every list `L` with `IsDPathList G D L` and `HasEnds L u v` is the support of a `D`-path
`P : G.Walk u v`. -/
theorem exists_isTPath_of_isDPathList_hasEnds {G : SimpleGraph V} {D L : List V} {u v : V}
    (hL : IsDPathList G D L) (hends : HasEnds L u v) :
    ∃ P : G.Walk u v, P.support = L ∧ HP25.IsTPath G D P := by
  obtain ⟨⟨hne, hnd, hc⟩, hlen, hheadD, hlastD, hinner⟩ := hL
  obtain ⟨hhead, hlast⟩ := hends
  obtain ⟨P, hP_supp⟩ := exists_walk_of_isChain L hne hc hhead hlast
  have hpath : P.IsPath := Walk.IsPath.mk' (by rw [hP_supp]; exact hnd)
  refine ⟨P, hP_supp, ⟨hpath, hheadD u hhead, hlastD v hlast, ?_⟩⟩
  intro x hx hxu hxv
  rw [hP_supp] at hx
  have hx_in : x ∈ Crossing.inner L :=
    (mem_inner_iff_of_nodup hlen hnd hhead hlast x).mpr ⟨hx, hxu, hxv⟩
  exact ⟨hinner x hx_in, hinner x hx_in⟩

/-- Every list `L` with `IsDPathList G D L` and `HasEndsUnordered L u v` is (up to reversal) the
support of a `D`-path `P : G.Walk u v`, preserving the set of vertices and the set of inner
vertices. -/
theorem exists_isTPath_of_isDPathList_hasEndsUnordered {G : SimpleGraph V} {D L : List V}
    {u v : V} (hL : IsDPathList G D L) (hends : HasEndsUnordered L u v) :
    ∃ P : G.Walk u v,
      (∀ x, x ∈ P.support ↔ x ∈ L) ∧
      (∀ x, (x ∈ P.support ∧ x ≠ u ∧ x ≠ v) ↔ x ∈ Crossing.inner L) ∧
      HP25.IsTPath G D P := by
  rcases hends with h | h
  · obtain ⟨P, hsupp, hT⟩ := exists_isTPath_of_isDPathList_hasEnds hL h
    refine ⟨P, fun x => by rw [hsupp], fun x => ?_, hT⟩
    rw [hsupp]
    exact (mem_inner_iff_of_nodup hL.2.1 hL.1.2.1 h.1 h.2 x).symm
  · have hLr : IsDPathList G D L.reverse := isDPathList_reverse.mpr hL
    have hr : HasEnds L.reverse u v := hasEnds_reverse.mpr h
    obtain ⟨P, hsupp, hT⟩ := exists_isTPath_of_isDPathList_hasEnds hLr hr
    refine ⟨P, fun x => by rw [hsupp, List.mem_reverse], fun x => ?_, hT⟩
    rw [hsupp, ← mem_inner_iff_of_nodup hLr.2.1 hLr.1.2.1 hr.1 hr.2 x, inner_reverse,
      List.mem_reverse]

/-! ### 2. Linking `HP25.IsCrossing` / `UsesDistinctBridges` with `IsCrossingPair` / `InDistinctBridges` -/

/-- Any walk-based crossing `HP25.IsCrossing G D Q R` gives a list-based crossing pair
`IsCrossingPair G D Q.support R.support`. -/
theorem isCrossingPair_of_isCrossing {G : SimpleGraph V} {D : List V} (hD : D.Nodup)
    {u₁ v₁ u₂ v₂ : V} {Q : G.Walk u₁ v₁} {R : G.Walk u₂ v₂}
    (hcr : HP25.IsCrossing G D Q R) :
    IsCrossingPair G D Q.support R.support := by
  obtain ⟨hu₁v₁, hu₂v₂, -, -⟩ := IsCrossing.not_isCycleEdge_ends hD hcr
  obtain ⟨hQ_list, hQ_ends⟩ := isDPathList_support_of_isTPath hcr.2.1 hu₁v₁
  obtain ⟨hR_list, hR_ends⟩ := isDPathList_support_of_isTPath hcr.2.2.1 hu₂v₂
  obtain ⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩ := hcr.1
  exact ⟨hQ_list, hR_list, hcr.2.2.2, i, r, j, s, hir, hrj, hjs, u₁, u₂, v₁, v₂,
    hi, hr, hj, hs, Or.inl ⟨Or.inl hQ_ends, Or.inl hR_ends⟩⟩

private lemma offCycleGraph_reachable_iff_reachIn {G : SimpleGraph V} {D : List V}
    {x y : V} (hx : x ∉ D) :
    (offCycleGraph G D).Reachable x y ↔ ReachIn G {z | z ∉ D} x y := by
  constructor
  · rintro ⟨w⟩
    refine ⟨w.mapLe (offCycleGraph_le G D), ?_⟩
    intro z hz
    rw [walk_support_mapLe] at hz
    exact (walk_support_mem_offCycleComp w (mem_offCycleComp_self hx) z hz).1
  · rintro ⟨p, hp⟩
    induction p with
    | nil => exact Reachable.refl _
    | @cons a b c hadj q ih =>
      have ha : a ∉ D := hp a (by simp)
      have hb : b ∉ D := hp b (by simp)
      have hadj' : (offCycleGraph G D).Adj a b := ⟨hadj, ha, hb⟩
      exact hadj'.reachable.trans (ih hb (fun z hz => hp z (List.mem_cons_of_mem _ hz)))

/-- Any list-based crossing pair `IsCrossingPair G D L₁ L₂` satisfying `InDistinctBridges G D L₁ L₂`
gives a walk-based crossing `HP25.IsCrossing G D Q R` satisfying `UsesDistinctBridges G S D Q R`. -/
theorem exists_isCrossing_usesDistinctBridges_of_isCrossingPair {G : SimpleGraph V} {S : Set V}
    {D L₁ L₂ : List V} (hG : HP25.IsSupportedOn G S) (hD : D.Nodup)
    (hpair : IsCrossingPair G D L₁ L₂) (hdist : InDistinctBridges G D L₁ L₂) :
    ∃ (u₁ v₁ u₂ v₂ : V) (Q : G.Walk u₁ v₁) (R : G.Walk u₂ v₂),
      HP25.IsCrossing G D Q R ∧ UsesDistinctBridges G S D Q R := by
  obtain ⟨hL₁, hL₂, hdisj, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, hends⟩ := hpair
  rcases hends with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · obtain ⟨Q, hQ_mem, hQ_in, hQ_path⟩ := exists_isTPath_of_isDPathList_hasEndsUnordered hL₁ h₁
    obtain ⟨R, hR_mem, hR_in, hR_path⟩ := exists_isTPath_of_isDPathList_hasEndsUnordered hL₂ h₂
    have hQR_disj : Q.support.Disjoint R.support :=
      fun x hxQ hxR => hdisj ((hQ_mem x).mp hxQ) ((hR_mem x).mp hxR)
    have hcr : HP25.IsCrossing G D Q R :=
      ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ_path, hR_path, hQR_disj⟩
    refine ⟨a, b, c, d, Q, R, hcr, (IsCrossing.usesDistinctBridges_iff hG hD hcr).mpr ?_⟩
    rintro ⟨x, hxQ, hxa, hxb, y, hyR, hyc, hyd, hreach⟩
    have hx_in : x ∈ Crossing.inner L₁ := (hQ_in x).mp ⟨hxQ, hxa, hxb⟩
    have hy_in : y ∈ Crossing.inner L₂ := (hR_in y).mp ⟨hyR, hyc, hyd⟩
    have hxD : x ∉ D := hL₁.2.2.2.2 x hx_in
    exact hdist x hx_in y hy_in ((offCycleGraph_reachable_iff_reachIn hxD).mp hreach)
  · obtain ⟨R, hR_mem, hR_in, hR_path⟩ := exists_isTPath_of_isDPathList_hasEndsUnordered hL₁ h₁
    obtain ⟨Q, hQ_mem, hQ_in, hQ_path⟩ := exists_isTPath_of_isDPathList_hasEndsUnordered hL₂ h₂
    have hQR_disj : Q.support.Disjoint R.support :=
      fun x hxQ hxR => hdisj ((hR_mem x).mp hxR) ((hQ_mem x).mp hxQ)
    have hcr : HP25.IsCrossing G D Q R :=
      ⟨⟨i, r, j, s, hir, hrj, hjs, hi, hr, hj, hs⟩, hQ_path, hR_path, hQR_disj⟩
    refine ⟨a, b, c, d, Q, R, hcr, (IsCrossing.usesDistinctBridges_iff hG hD hcr).mpr ?_⟩
    rintro ⟨x, hxQ, hxa, hxb, y, hyR, hyc, hyd, hreach⟩
    have hx_in : x ∈ Crossing.inner L₂ := (hQ_in x).mp ⟨hxQ, hxa, hxb⟩
    have hy_in : y ∈ Crossing.inner L₁ := (hR_in y).mp ⟨hyR, hyc, hyd⟩
    have hyD : y ∉ D := hL₁.2.2.2.2 y hy_in
    exact hdist y hy_in x hx_in ((offCycleGraph_reachable_iff_reachIn hyD).mp hreach.symm)

/-! ### 3. `ValidBridgeList` and `bridgeCrossWith` -/

/-- A list `bridges : List (BridgeData V)` is a valid duplicate-free enumeration of all `D`-bridges
of `G` on `verts`. -/
structure ValidBridgeList [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (verts D : List V) (bridges : List (BridgeData V)) : Prop where
  /-- Distinct entries represent distinct bridges. -/
  pairwise_ne : bridges.Pairwise (fun b₁ b₂ => b₁.toBridge ≠ b₂.toBridge)
  /-- Every entry is a valid `D`-bridge, and component vertex lists avoid `D` and have no repeats. -/
  valid_mem : ∀ bd ∈ bridges, IsBridge G {x | x ∈ verts} D bd.toBridge ∧
    (∀ A, bd = BridgeData.comp A → A.Nodup ∧ ∀ x ∈ A, x ∉ D)
  /-- Every valid `D`-bridge of `G` on `verts` appears in `bridges`. -/
  complete : ∀ B, IsBridge G {x | x ∈ verts} D B →
    ∃ (γ : ℕ) (hγ : γ < bridges.length), (bridges[γ]'hγ).toBridge = B

theorem ValidBridgeList.toBridge_ne_of_ne [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {verts D : List V} {bridges : List (BridgeData V)}
    (hB : ValidBridgeList G verts D bridges) {γ₁ γ₂ : ℕ}
    (h₁ : γ₁ < bridges.length) (h₂ : γ₂ < bridges.length) (hne : γ₁ ≠ γ₂) :
    (bridges[γ₁]'h₁).toBridge ≠ (bridges[γ₂]'h₂).toBridge := by
  have hpw := List.pairwise_iff_getElem.mp hB.pairwise_ne
  rcases lt_trichotomy γ₁ γ₂ with hlt | rfl | hgt
  · exact hpw γ₁ γ₂ h₁ h₂ hlt
  · exact absurd rfl hne
  · exact (hpw γ₂ γ₁ h₂ h₁ hgt).symm

/-- Soundness of `BridgeData.findPath` for any bridge in a `ValidBridgeList`. -/
theorem BridgeData.findPath_sound_of_isBridge [DecidableEq V] [HP25.WalkSearch V]
    [HP25.LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Set V} {D : List V} {bd : BridgeData V}
    (hbd_bridge : IsBridge G S D bd.toBridge)
    (hbd_off : ∀ A, bd = BridgeData.comp A → ∀ x ∈ A, x ∉ D)
    {p q : V} (hpD : p ∈ D) (hqD : q ∈ D) (hpq : p ≠ q)
    (hp_att : bd.attaches G p = true) (hq_att : bd.attaches G q = true)
    {P : G.Walk p q} (hfind : bd.findPath G p q = some P) :
    HP25.IsTPath G D P ∧ UsesBridge G P bd.toBridge := by
  cases bd with
  | comp A =>
    simp only [BridgeData.findPath] at hfind
    cases hw : HP25.WalkSearch.find (G \ SimpleGraph.edge p q) A p q with
    | none => simp [hw] at hfind
    | some w =>
      rw [hw] at hfind
      simp only [Option.some.injEq] at hfind
      subst hfind
      have hws := HP25.LawfulWalkSearch.isWalkSearch (G \ SimpleGraph.edge p q)
      have hw_path : w.IsPath := hws.isPath hw
      have hw_supp := hws.support_subset hw
      have hP_path : (w.mapLe sdiff_le).IsPath := hw_path.mapLe sdiff_le
      have hA_not_D : ∀ x ∈ A, x ∉ D := hbd_off A rfl
      have hinner_A : ∀ x ∈ (w.mapLe sdiff_le).support, x ≠ p → x ≠ q → x ∈ A := by
        intro x hx hxp hxq
        rw [walk_support_mapLe] at hx
        exact (hw_supp x hx).resolve_left hxp |>.resolve_left hxq
      have hTPath : HP25.IsTPath G D (w.mapLe sdiff_le) := by
        refine ⟨hP_path, hpD, hqD, fun x hx hxp hxq => ?_⟩
        have hxA := hinner_A x hx hxp hxq
        exact ⟨hA_not_D x hxA, hA_not_D x hxA⟩
      have hex_inner : ∃ x ∈ (w.mapLe sdiff_le).support, x ≠ p ∧ x ≠ q := by
        rw [walk_support_mapLe]
        cases hw_eq : w with
        | nil => exact absurd rfl hpq
        | @cons _ mid _ hadj₁ w' =>
          cases hw'_eq : w' with
          | nil =>
            exfalso
            rw [sdiff_adj, edge_adj] at hadj₁
            exact hadj₁.2 ⟨Or.inl ⟨rfl, rfl⟩, hpq⟩
          | @cons _ mid₂ _ _ w'' =>
            have hmid_ne_p : mid ≠ p := ((G \ SimpleGraph.edge p q).ne_of_adj hadj₁).symm
            have hmid_ne_q : mid ≠ q := by
              intro hmq
              subst hmq
              rw [hw_eq, hw'_eq] at hw_path
              have hnd := hw_path.support_nodup
              simp only [Walk.support_cons, List.nodup_cons] at hnd
              exact hnd.2.1 w''.end_mem_support
            exact ⟨mid, by simp, hmid_ne_p, hmid_ne_q⟩
      exact ⟨hTPath, hex_inner, fun x hx hxp hxq => hinner_A x hx hxp hxq⟩
  | chord u v =>
    simp only [BridgeData.findPath] at hfind
    split_ifs at hfind with hadj
    simp only [Option.some.injEq] at hfind
    subst hfind
    have hp_uv : p = u ∨ p = v := of_decide_eq_true hp_att
    have hq_uv : q = u ∨ q = v := of_decide_eq_true hq_att
    have hsym : s(u, v) = s(p, q) := by
      rcases hp_uv with rfl | rfl <;> rcases hq_uv with rfl | rfl
      · exact absurd rfl hpq
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hpq
    refine ⟨⟨Walk.IsPath.of_adj hadj, hpD, hqD, fun x hx hxp hxq => ?_⟩,
      ⟨fun x hx => ?_, hsym⟩⟩
    · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      exact hx.elim (fun h => absurd h hxp) (fun h => absurd h hxq)
    · simp only [Walk.support_cons, Walk.support_nil, List.mem_cons, List.not_mem_nil,
        or_false] at hx
      exact hx

/-- Completeness of `BridgeData.findPath` for any bridge in a `ValidBridgeList`. -/
theorem BridgeData.findPath_isSome_of_isBridge [DecidableEq V] [HP25.WalkSearch V]
    [HP25.LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Set V} {D : List V} {bd : BridgeData V}
    (hbd_bridge : IsBridge G S D bd.toBridge)
    {p q : V} (hpD : p ∈ D) (hqD : q ∈ D) (hpq : p ≠ q)
    (hp_att : bd.attaches G p = true) (hq_att : bd.attaches G q = true) :
    (bd.findPath G p q).isSome = true := by
  cases bd with
  | comp A =>
    simp only [BridgeData.findPath]
    have hp_att' : IsBridgeAttachment G D (BridgeData.comp A).toBridge p :=
      ((BridgeData.comp A).attaches_iff G hpD).mp hp_att
    have hq_att' : IsBridgeAttachment G D (BridgeData.comp A).toBridge q :=
      ((BridgeData.comp A).attaches_iff G hqD).mp hq_att
    obtain ⟨a, haA, hadj_ap⟩ := hp_att'.2
    obtain ⟨b, hbA, hadj_bq⟩ := hq_att'.2
    obtain ⟨v₀, _, _, hcomp_eq⟩ := hbd_bridge
    have hA_eq : {x | x ∈ A} = offCycleComp G D v₀ := hcomp_eq
    have ha_comp : a ∈ offCycleComp G D v₀ := by rwa [← hA_eq]
    have hb_comp : b ∈ offCycleComp G D v₀ := by rwa [← hA_eq]
    obtain ⟨w₀⟩ := ha_comp.2.symm.trans hb_comp.2
    have hw₀_in : ∀ x ∈ w₀.support, x ∈ A := by
      intro x hx
      change x ∈ {z | z ∈ A}
      rw [hA_eq]
      exact walk_support_mem_offCycleComp w₀ ha_comp x hx
    have hadj_pa' : (G \ SimpleGraph.edge p q).Adj p a := by
      rw [sdiff_adj, edge_adj]
      refine ⟨hadj_ap.symm, ?_⟩
      rintro ⟨⟨_, h2⟩ | ⟨_, h2⟩, _⟩
      · exact ha_comp.1 (h2 ▸ hqD)
      · exact ha_comp.1 (h2 ▸ hpD)
    have hadj_bq' : (G \ SimpleGraph.edge p q).Adj b q := by
      rw [sdiff_adj, edge_adj]
      refine ⟨hadj_bq, ?_⟩
      rintro ⟨⟨h1, _⟩ | ⟨h1, _⟩, _⟩
      · exact hb_comp.1 (h1 ▸ hpD)
      · exact hb_comp.1 (h1 ▸ hqD)
    let W : (G \ SimpleGraph.edge p q).Walk p q :=
      (Walk.cons hadj_pa' (w₀.mapLe (offCycleGraph_le_sdiff_edge G hpD))).concat hadj_bq'
    have hW_inner : ∀ x ∈ W.support, x ≠ p → x ≠ q → x ∈ A := by
      intro x hx hxp hxq
      simp only [W, Walk.support_concat, Walk.support_cons, walk_support_mapLe,
        List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with (rfl | hx') | rfl
      · exact absurd rfl hxp
      · exact hw₀_in x hx'
      · exact absurd rfl hxq
    have hisSome :=
      (HP25.LawfulWalkSearch.isWalkSearch (G \ SimpleGraph.edge p q)).isSome_of_walk W hW_inner
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hisSome
    simp [hw]
  | chord u v =>
    obtain ⟨u', v', heq, _, _, hadj_u'v', _⟩ := hbd_bridge
    have hp_uv : p = u ∨ p = v := of_decide_eq_true hp_att
    have hq_uv : q = u ∨ q = v := of_decide_eq_true hq_att
    have hsym : s(p, q) = s(u, v) := by
      rcases hp_uv with rfl | rfl <;> rcases hq_uv with rfl | rfl
      · exact absurd rfl hpq
      · rfl
      · exact Sym2.eq_swap
      · exact absurd rfl hpq
    have hadj_pq : G.Adj p q := by
      have hsym' : s(p, q) = s(u', v') := hsym.trans heq
      rcases Sym2.eq_iff.mp hsym' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hadj_u'v'
      · exact hadj_u'v'.symm
    simp [BridgeData.findPath, hadj_pq]

/-- `bridgeCross` parameterized by an explicit bridge list `bridges : List (BridgeData V)`. -/
def bridgeCrossWith [DecidableEq V] [HP25.WalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : List V) (bridges : List (BridgeData V)) : Option (HP25.CrossingWalks G D) :=
  let cs := allBridgeCandidates G D bridges
  let sorted := sortCandidates D.length cs
  match sweepCandidates sorted with
  | none => none
  | some (I₁, I₂) =>
    if h₁ : I₁.l < D.length ∧ I₁.r < D.length then
      if h₂ : I₂.l < D.length ∧ I₂.r < D.length then
        match bridges[I₁.γ]?, bridges[I₂.γ]? with
        | some bd₁, some bd₂ =>
          let u₁ := D[I₁.l]'h₁.1
          let v₁ := D[I₁.r]'h₁.2
          let u₂ := D[I₂.l]'h₂.1
          let v₂ := D[I₂.r]'h₂.2
          match bd₁.findPath G u₁ v₁, bd₂.findPath G u₂ v₂ with
          | some Q, some R => some ⟨u₁, v₁, u₂, v₂, Q, R⟩
          | _, _ => none
        | _, _ => none
      else none
    else none

/-- An unsuccessful candidate sweep makes `bridgeCrossWith` return no pair. -/
theorem bridgeCrossWith_eq_none_of_sweep [DecidableEq V] [HP25.WalkSearch V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : List V)
    (bridges : List (BridgeData V))
    (h : sweepCandidates (sortCandidates D.length (allBridgeCandidates G D bridges)) = none) :
    bridgeCrossWith G D bridges = none := by
  simp only [bridgeCrossWith, h]

/-- Soundness of `bridgeCrossWith` on any `ValidBridgeList`. -/
theorem bridgeCrossWith_valid_and_usesDistinctBridges [DecidableEq V] [HP25.WalkSearch V]
    [HP25.LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hD : D.Nodup) {bridges : List (BridgeData V)}
    (hB : ValidBridgeList G verts D bridges)
    {cr : HP25.CrossingWalks G D} (heq : bridgeCrossWith G D bridges = some cr) :
    cr.Valid ∧ UsesDistinctBridges G {x | x ∈ verts} D cr.Q cr.R := by
  unfold bridgeCrossWith at heq
  dsimp only at heq
  set cs := allBridgeCandidates G D bridges
  set sorted := sortCandidates D.length cs
  have hcs_lt : ∀ I ∈ cs, I.l < D.length ∧ I.r < D.length := by
    intro I hI
    obtain ⟨_, hl_r, hr_lt, _, _⟩ := mem_allBridgeCandidates_spec G hI
    exact ⟨lt_trans hl_r hr_lt, hr_lt⟩
  have hperm : sorted.Perm cs := sortCandidates_perm hcs_lt
  have hpw : sorted.Pairwise CandidateOrder := sortCandidates_pairwise hcs_lt
  cases hsweep : sweepCandidates sorted with
  | none =>
    rw [hsweep] at heq
    simp at heq
  | some pair =>
    rcases pair with ⟨I₁, I₂⟩
    rw [hsweep] at heq
    obtain ⟨hI₁_sorted, hI₂_sorted, hinter⟩ := sweepCandidates_sound hpw hsweep
    have hI₁_cs : I₁ ∈ cs := hperm.subset hI₁_sorted
    have hI₂_cs : I₂ ∈ cs := hperm.subset hI₂_sorted
    obtain ⟨hγ₁, hI₁_lr, hI₁_r, hI₁_l_att, hI₁_r_att⟩ := mem_allBridgeCandidates_spec G hI₁_cs
    obtain ⟨hγ₂, hI₂_lr, hI₂_r, hI₂_l_att, hI₂_r_att⟩ := mem_allBridgeCandidates_spec G hI₂_cs
    have h₁ : I₁.l < D.length ∧ I₁.r < D.length := ⟨lt_trans hI₁_lr hI₁_r, hI₁_r⟩
    have h₂ : I₂.l < D.length ∧ I₂.r < D.length := ⟨lt_trans hI₂_lr hI₂_r, hI₂_r⟩
    simp only [h₁, h₂, and_self, ↓reduceDIte] at heq
    have hget₁ : bridges[I₁.γ]? = some (bridges[I₁.γ]'hγ₁) := List.getElem?_eq_getElem hγ₁
    have hget₂ : bridges[I₂.γ]? = some (bridges[I₂.γ]'hγ₂) := List.getElem?_eq_getElem hγ₂
    rw [hget₁, hget₂] at heq
    dsimp only at heq
    set bd₁ := bridges[I₁.γ]'hγ₁
    set bd₂ := bridges[I₂.γ]'hγ₂
    set u₁ := D[I₁.l]'h₁.1
    set v₁ := D[I₁.r]'h₁.2
    set u₂ := D[I₂.l]'h₂.1
    set v₂ := D[I₂.r]'h₂.2
    cases hfind₁ : bd₁.findPath G u₁ v₁ with
    | none =>
      rw [hfind₁] at heq
      simp at heq
    | some Q =>
      cases hfind₂ : bd₂.findPath G u₂ v₂ with
      | none =>
        rw [hfind₁, hfind₂] at heq
        simp at heq
      | some R =>
        rw [hfind₁, hfind₂] at heq
        simp only [Option.some.injEq] at heq
        subst heq
        rcases hinter with ⟨hγ_ne, hl₁_l₂, hl₂_r₁, hr₁_r₂⟩
        have hne_idx : ∀ {i j : ℕ} (hi : i < D.length) (hj : j < D.length),
            i ≠ j → D[i]'hi ≠ D[j]'hj :=
          fun _ _ hne h => hne (hD.getElem_inj_iff.mp h)
        have hu₁v₁ : u₁ ≠ v₁ := hne_idx h₁.1 h₁.2 (by omega)
        have hu₂v₂ : u₂ ≠ v₂ := hne_idx h₂.1 h₂.2 (by omega)
        have hu₁_att : bd₁.attaches G u₁ = true :=
          bd₁.attaches_of_mem_attachmentIndices G hI₁_l_att
        have hv₁_att : bd₁.attaches G v₁ = true :=
          bd₁.attaches_of_mem_attachmentIndices G hI₁_r_att
        have hu₂_att : bd₂.attaches G u₂ = true :=
          bd₂.attaches_of_mem_attachmentIndices G hI₂_l_att
        have hv₂_att : bd₂.attaches G v₂ = true :=
          bd₂.attaches_of_mem_attachmentIndices G hI₂_r_att
        have hbd₁_info := hB.valid_mem bd₁ (List.getElem_mem hγ₁)
        have hbd₂_info := hB.valid_mem bd₂ (List.getElem_mem hγ₂)
        have hQ_sound := BridgeData.findPath_sound_of_isBridge G hbd₁_info.1
          (fun A hA => (hbd₁_info.2 A hA).2)
          (List.getElem_mem h₁.1) (List.getElem_mem h₁.2) hu₁v₁ hu₁_att hv₁_att hfind₁
        have hR_sound := BridgeData.findPath_sound_of_isBridge G hbd₂_info.1
          (fun A hA => (hbd₂_info.2 A hA).2)
          (List.getElem_mem h₂.1) (List.getElem_mem h₂.2) hu₂v₂ hu₂_att hv₂_att hfind₂
        have hB_ne : bd₁.toBridge ≠ bd₂.toBridge :=
          hB.toBridge_ne_of_ne hγ₁ hγ₂ hγ_ne
        have hdist : UsesDistinctBridges G {x | x ∈ verts} D Q R :=
          ⟨bd₁.toBridge, bd₂.toBridge, hbd₁_info.1, hbd₂_info.1, hB_ne, hQ_sound.2, hR_sound.2⟩
        have hdisj : Q.support.Disjoint R.support := by
          refine disjoint_support_of_usesDistinctBridges hbd₁_info.1 hbd₂_info.1 hB_ne
            hQ_sound.2 hR_sound.2
            (List.getElem_mem h₁.1) (List.getElem_mem h₁.2)
            (List.getElem_mem h₂.1) (List.getElem_mem h₂.2) ?_
          intro x hx₁ hx₂
          rcases hx₁ with rfl | rfl <;> rcases hx₂ with h | h
          · exact hne_idx h₁.1 h₂.1 (by omega) h
          · exact hne_idx h₁.1 h₂.2 (by omega) h
          · exact hne_idx h₁.2 h₂.1 (by omega) h
          · exact hne_idx h₁.2 h₂.2 (by omega) h
        have hvalid : HP25.IsCrossing G D Q R := by
          refine ⟨⟨I₁.l, I₂.l, I₁.r, I₂.r, hl₁_l₂, hl₂_r₁, hr₁_r₂,
            List.getElem?_eq_getElem h₁.1, List.getElem?_eq_getElem h₂.1,
            List.getElem?_eq_getElem h₁.2, List.getElem?_eq_getElem h₂.2⟩,
            hQ_sound.1, hR_sound.1, hdisj⟩
        exact ⟨hvalid, hdist⟩

/-- Completeness of `bridgeCrossWith` on any `ValidBridgeList`. -/
theorem bridgeCrossWith_isSome_of_usesDistinctBridges [DecidableEq V] [HP25.WalkSearch V]
    [HP25.LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {verts D : List V} (hG : HP25.IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup)
    {bridges : List (BridgeData V)} (hB : ValidBridgeList G verts D bridges)
    {u₁ v₁ u₂ v₂ : V} {Q : G.Walk u₁ v₁} {R : G.Walk u₂ v₂}
    (hcr : HP25.IsCrossing G D Q R)
    (hdist : UsesDistinctBridges G {x | x ∈ verts} D Q R) :
    (bridgeCrossWith G D bridges).isSome = true := by
  unfold bridgeCrossWith
  dsimp only
  set cs := allBridgeCandidates G D bridges
  set sorted := sortCandidates D.length cs
  have hcs_lt : ∀ I ∈ cs, I.l < D.length ∧ I.r < D.length := by
    intro I hI
    obtain ⟨_, hl_r, hr_lt, _, _⟩ := mem_allBridgeCandidates_spec G hI
    exact ⟨lt_trans hl_r hr_lt, hr_lt⟩
  have hperm : sorted.Perm cs := sortCandidates_perm hcs_lt
  have hpw : sorted.Pairwise CandidateOrder := sortCandidates_pairwise hcs_lt
  obtain ⟨B₁, B₂, hB₁, hB₂, hB_ne, hQ_B₁, hR_B₂⟩ := hdist
  obtain ⟨γ₁, hγ₁, hB₁_eq⟩ := hB.complete B₁ hB₁
  obtain ⟨γ₂, hγ₂, hB₂_eq⟩ := hB.complete B₂ hB₂
  have hγ_ne : γ₁ ≠ γ₂ := fun h => hB_ne (by subst h; exact hB₁_eq.symm.trans hB₂_eq)
  set bd₁ := bridges[γ₁]'hγ₁
  set bd₂ := bridges[γ₂]'hγ₂
  have hQ_path : HP25.IsTPath G D Q := hcr.2.1
  have hR_path : HP25.IsTPath G D R := hcr.2.2.1
  obtain ⟨hu₁v₁, hu₂v₂, hnot₁, hnot₂⟩ := IsCrossing.not_isCycleEdge_ends hD hcr
  obtain ⟨B₁', hB₁', hQ_B₁', hu₁_att', hv₁_att'⟩ := IsTPath.exists_bridge hG hQ_path hu₁v₁ hnot₁
  obtain ⟨B₂', hB₂', hR_B₂', hu₂_att', hv₂_att'⟩ := IsTPath.exists_bridge hG hR_path hu₂v₂ hnot₂
  have hB₁'_eq : B₁' = B₁ := UsesBridge.unique hB₁' hB₁ hQ_B₁' hQ_B₁
  have hB₂'_eq : B₂' = B₂ := UsesBridge.unique hB₂' hB₂ hR_B₂' hR_B₂
  have hu₁_att : bd₁.attaches G u₁ = true := by
    rw [bd₁.attaches_iff G hQ_path.2.1, hB₁_eq, ← hB₁'_eq]
    exact hu₁_att'
  have hv₁_att : bd₁.attaches G v₁ = true := by
    rw [bd₁.attaches_iff G hQ_path.2.2.1, hB₁_eq, ← hB₁'_eq]
    exact hv₁_att'
  have hu₂_att : bd₂.attaches G u₂ = true := by
    rw [bd₂.attaches_iff G hR_path.2.1, hB₂_eq, ← hB₂'_eq]
    exact hu₂_att'
  have hv₂_att : bd₂.attaches G v₂ = true := by
    rw [bd₂.attaches_iff G hR_path.2.2.1, hB₂_eq, ← hB₂'_eq]
    exact hv₂_att'
  have halt : HP25.Alternate D u₁ v₁ u₂ v₂ := hcr.alternate
  obtain ⟨I₁, hI₁_cand, I₂, hI₂_cand, hinter⟩ :=
    lemma_3_candidatesOfIndices hD (bd₁.attaches G) (bd₂.attaches G) γ₁ γ₂
      hu₁_att hv₁_att hu₂_att hv₂_att halt
  rw [← bd₁.attachmentIndices_eq_map_idxOf G hD] at hI₁_cand
  rw [← bd₂.attachmentIndices_eq_map_idxOf G hD] at hI₂_cand
  have hI₁_cs : I₁ ∈ cs := (mem_allBridgeCandidates_iff G).mpr ⟨γ₁, hγ₁, hI₁_cand⟩
  have hI₂_cs : I₂ ∈ cs := (mem_allBridgeCandidates_iff G).mpr ⟨γ₂, hγ₂, hI₂_cand⟩
  have hI₁_sorted : I₁ ∈ sorted := hperm.symm.subset hI₁_cs
  have hI₂_sorted : I₂ ∈ sorted := hperm.symm.subset hI₂_cs
  have hI₁_γ : I₁.γ = γ₁ := by
    unfold candidatesOfIndices at hI₁_cand
    rw [List.mem_map] at hI₁_cand
    obtain ⟨_, _, rfl⟩ := hI₁_cand
    rfl
  have hI₂_γ : I₂.γ = γ₂ := by
    unfold candidatesOfIndices at hI₂_cand
    rw [List.mem_map] at hI₂_cand
    obtain ⟨_, _, rfl⟩ := hI₂_cand
    rfl
  have hsweep_some : (sweepCandidates sorted).isSome := by
    rcases hinter with h12 | h21
    · exact sweepCandidates_complete hpw hI₁_sorted hI₂_sorted
        ⟨by rw [hI₁_γ, hI₂_γ]; exact hγ_ne, h12⟩
    · exact sweepCandidates_complete hpw hI₂_sorted hI₁_sorted
        ⟨by rw [hI₁_γ, hI₂_γ]; exact hγ_ne.symm, h21⟩
  obtain ⟨⟨J, I⟩, hsweep_eq⟩ := Option.isSome_iff_exists.mp hsweep_some
  rw [hsweep_eq]
  obtain ⟨hJ_sorted, hI_sorted, _⟩ := sweepCandidates_sound hpw hsweep_eq
  have hJ_cs : J ∈ cs := hperm.subset hJ_sorted
  have hI_cs : I ∈ cs := hperm.subset hI_sorted
  obtain ⟨hγJ, hJ_lr, hJ_r, hJ_l_att, hJ_r_att⟩ := mem_allBridgeCandidates_spec G hJ_cs
  obtain ⟨hγI, hI_lr, hI_r, hI_l_att, hI_r_att⟩ := mem_allBridgeCandidates_spec G hI_cs
  have h₁ : J.l < D.length ∧ J.r < D.length := ⟨lt_trans hJ_lr hJ_r, hJ_r⟩
  have h₂ : I.l < D.length ∧ I.r < D.length := ⟨lt_trans hI_lr hI_r, hI_r⟩
  simp only [h₁, h₂, and_self, ↓reduceDIte]
  rw [List.getElem?_eq_getElem hγJ, List.getElem?_eq_getElem hγI]
  dsimp only
  have hne_J : D[J.l]'h₁.1 ≠ D[J.r]'h₁.2 :=
    fun h => (ne_of_lt hJ_lr) (hD.getElem_inj_iff.mp h)
  have hne_I : D[I.l]'h₂.1 ≠ D[I.r]'h₂.2 :=
    fun h => (ne_of_lt hI_lr) (hD.getElem_inj_iff.mp h)
  have hfindJ := BridgeData.findPath_isSome_of_isBridge G
    (hB.valid_mem (bridges[J.γ]'hγJ) (List.getElem_mem hγJ)).1
    (List.getElem_mem h₁.1) (List.getElem_mem h₁.2) hne_J
    ((bridges[J.γ]'hγJ).attaches_of_mem_attachmentIndices G hJ_l_att)
    ((bridges[J.γ]'hγJ).attaches_of_mem_attachmentIndices G hJ_r_att)
  have hfindI := BridgeData.findPath_isSome_of_isBridge G
    (hB.valid_mem (bridges[I.γ]'hγI) (List.getElem_mem hγI)).1
    (List.getElem_mem h₂.1) (List.getElem_mem h₂.2) hne_I
    ((bridges[I.γ]'hγI).attaches_of_mem_attachmentIndices G hI_l_att)
    ((bridges[I.γ]'hγI).attaches_of_mem_attachmentIndices G hI_r_att)
  obtain ⟨QJ, hQJ⟩ := Option.isSome_iff_exists.mp hfindJ
  obtain ⟨RI, hRI⟩ := Option.isSome_iff_exists.mp hfindI
  simp [hQJ, hRI]

/-- Total attachments across any `ValidBridgeList` is bounded by `(directedEdges G verts).length`. -/
theorem ValidBridgeList.totalAttachments_le_directedEdges [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {verts D : List V} {bridges : List (BridgeData V)}
    (hG : HP25.IsSupportedOn G {x | x ∈ verts}) (hD : D.Nodup)
    (hB : ValidBridgeList G verts D bridges) :
    totalAttachments G D bridges ≤ (directedEdges G verts).length := by
  classical
  rw [← length_attachmentPairs G D bridges]
  let f : V × V → ℕ × ℕ := fun ⟨u, v⟩ =>
    let B : Bridge V := if u ∈ D then Bridge.chord s(u, v) else Bridge.comp (offCycleComp G D u)
    let γ : ℕ := if h : ∃ (γ : ℕ) (hγ : γ < bridges.length), (bridges[γ]'hγ).toBridge = B
      then Classical.choose h else 0
    (γ, D.idxOf v)
  apply nodup_length_le_of_forall_exists_map (directedEdges G verts) f
    (nodup_attachmentPairs G D bridges)
  rintro ⟨γ₀, i₀⟩ hp
  obtain ⟨hγ₀, hi₀⟩ := mem_attachmentPairs_spec G hp
  have hi₀_lt : i₀ < D.length := (bridges[γ₀]'hγ₀).mem_attachmentIndices_lt G hi₀
  set bd₀ := bridges[γ₀]'hγ₀
  set v₀ := D[i₀]'hi₀_lt
  have hv₀_D : v₀ ∈ D := List.getElem_mem hi₀_lt
  have hatt₀ : IsBridgeAttachment G D bd₀.toBridge v₀ :=
    (bd₀.attaches_iff G hv₀_D).mp (bd₀.attaches_of_mem_attachmentIndices G hi₀)
  have hB₀ : IsBridge G {x | x ∈ verts} D bd₀.toBridge :=
    (hB.valid_mem bd₀ (List.getElem_mem hγ₀)).1
  obtain ⟨u₀, hdir, hB_eq⟩ := exists_directedEdge_of_isBridgeAttachment G hG hB₀ hatt₀
  refine ⟨(u₀, v₀), hdir, ?_⟩
  dsimp only [f]
  rw [hB_eq]
  have hex : ∃ (γ : ℕ) (hγ : γ < bridges.length), (bridges[γ]'hγ).toBridge = bd₀.toBridge :=
    ⟨γ₀, hγ₀, rfl⟩
  simp only [hex, ↓reduceDIte]
  have hchoose_spec := Classical.choose_spec hex
  obtain ⟨hγ_ch, hch_eq⟩ := hchoose_spec
  have hγ_eq : Classical.choose hex = γ₀ := by
    by_contra hne
    exact hB.toBridge_ne_of_ne hγ_ch hγ₀ hne hch_eq
  rw [hγ_eq, hD.idxOf_getElem i₀ hi₀_lt]

/-- If `bridgeCrossWith G D bridges = none` on a `ValidBridgeList`, then no crossing pair of `D`
in `G` uses distinct `D`-bridges (`InDistinctBridges`). -/
theorem not_inDistinctBridges_of_bridgeCrossWith_eq_none [DecidableEq V] [HP25.WalkSearch V]
    [HP25.LawfulWalkSearch V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {S : Set V} {verts D : List V} (hG_S : HP25.IsSupportedOn G S)
    (hG : HP25.IsSupportedOn G {x | x ∈ verts}) (hS_sub : S ⊆ {x | x ∈ verts}) (hD : D.Nodup)
    {bridges : List (BridgeData V)} (hB : ValidBridgeList G verts D bridges)
    (hnone : bridgeCrossWith G D bridges = none) :
    ∀ L₁ L₂ : List V, IsCrossingPair G D L₁ L₂ → ¬ InDistinctBridges G D L₁ L₂ := by
  intro L₁ L₂ hpair hdist
  obtain ⟨u₁, v₁, u₂, v₂, Q, R, hcr, hdist_S⟩ :=
    exists_isCrossing_usesDistinctBridges_of_isCrossingPair hG_S hD hpair hdist
  have hdist_verts : UsesDistinctBridges G {x | x ∈ verts} D Q R := by
    obtain ⟨B₁, B₂, hB₁, hB₂, hne, hQ, hR⟩ := hdist_S
    have hmono : ∀ B, IsBridge G S D B → IsBridge G {x | x ∈ verts} D B := by
      rintro (A | e) h
      · obtain ⟨v, hvS, hvD, rfl⟩ := h
        exact ⟨v, hS_sub hvS, hvD, rfl⟩
      · exact h
    exact ⟨B₁, B₂, hmono B₁ hB₁, hmono B₂ hB₂, hne, hQ, hR⟩
  have his := bridgeCrossWith_isSome_of_usesDistinctBridges G hG hD hB hcr hdist_verts
  rw [hnone] at his
  simp at his

end GraphMinor.Compute.Crossing
end
