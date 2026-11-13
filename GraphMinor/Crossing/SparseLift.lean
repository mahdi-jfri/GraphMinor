module

public import GraphMinor.Crossing.Statements

/-!
# Lifting contractions (Section 11 of the note)

This file proves the three contraction-lifting claims of Section 11 of
`docs/crossing/crossing_extractor.tex`:
* `lift11OffOff_proved` (`Lift11OffOffStatement`): lifting a crossing pair when both ends of the
  contracted edge `uv` are off the cycle `D`.
* `lift11OneOn_proved` (`Lift11OneOnStatement`): lifting a crossing pair when `u ∉ D` and `v ∈ D`.
* `lift11BothOn_proved` (`Lift11BothOnStatement`): lifting a crossing pair when `uv` is a cycle
  edge of `D`.
-/

public section

namespace GraphMinor.Crossing

open SimpleGraph

universe u

variable {V : Type u}

/-! ### General path-list and contraction helpers -/

private lemma not_mem_of_isChain_contractGraph {K : SimpleGraph V} {u v : V} {L : List V}
    (hlen : 2 ≤ L.length) (hc : L.IsChain (contractGraph K u v).Adj) : u ∉ L := by
  induction L with
  | nil => simp at hlen
  | cons x rest ih =>
    cases rest with
    | nil => simp at hlen
    | cons y rest' =>
      rw [List.isChain_cons_cons] at hc
      rw [List.mem_cons]
      rintro (rfl | hmem)
      · exact hc.1.2.1 rfl
      · cases rest' with
        | nil =>
          rw [List.mem_singleton] at hmem
          exact hc.1.2.2.1 hmem.symm
        | cons z rest'' =>
          exact ih (by simp) hc.2 hmem

private lemma isChain_of_isChain_contractGraph_of_notMem {K : SimpleGraph V} {u v : V}
    {L : List V} (hc : L.IsChain (contractGraph K u v).Adj) (hv : v ∉ L) :
    L.IsChain K.Adj := by
  induction L with
  | nil => exact List.IsChain.nil
  | cons a rest ih =>
    cases rest with
    | nil => exact List.IsChain.singleton a
    | cons b rest' =>
      rw [List.isChain_cons_cons] at hc ⊢
      have hav : a ≠ v := fun h => hv (h ▸ List.mem_cons_self)
      have hbv : b ≠ v := fun h => hv (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      have hab : K.Adj a b := by
        rcases hc.1.2.2.2 with h | ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact absurd h hav
        · exact absurd h hbv
      exact ⟨hab, ih hc.2 (fun h => hv (List.mem_cons_of_mem _ h))⟩

private lemma isPathList_reverse {G : SimpleGraph V} {L : List V} :
    IsPathList G L.reverse ↔ IsPathList G L := by
  unfold IsPathList
  rw [List.reverse_ne_nil_iff, List.nodup_reverse, List.isChain_reverse]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor <;> (intro h; exact h.imp fun _ _ hab => hab.symm)

private lemma inner_cons_cons (a b : V) (rest : List V) :
    inner (a :: b :: rest) = (b :: rest).dropLast := rfl

private lemma inner_append_cons_Last (a : V) (mid : List V) (b : V) :
    inner (a :: (mid ++ [b])) = mid := by
  simp [inner]

private lemma inner_reverse (L : List V) : inner L.reverse = (inner L).reverse := by
  cases L with
  | nil => rfl
  | cons a rest =>
    cases rest using List.reverseRecOn with
    | nil => rfl
    | append_singleton mid b =>
      have h1 : (a :: (mid ++ [b])).reverse = b :: (mid.reverse ++ [a]) := by
        simp [List.reverse_append]
      rw [h1, inner_append_cons_Last, inner_append_cons_Last]

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

private lemma hasEndsUnordered_reverse {L : List V} {a b : V} :
    HasEndsUnordered L.reverse a b ↔ HasEndsUnordered L a b := by
  unfold HasEndsUnordered
  rw [hasEnds_reverse, hasEnds_reverse, or_comm]

private lemma notMem_reverse_tail_of_head?_ne_of_notMem_inner {L : List V} {v : V}
    (hhead : L.head? ≠ some v) (hinner : v ∉ inner L) :
    v ∉ L.reverse.tail := by
  cases L with
  | nil => simp
  | cons a rest =>
    cases rest using List.reverseRecOn with
    | nil => simp
    | append_singleton mid b =>
      have h1 : (a :: (mid ++ [b])).reverse = b :: (mid.reverse ++ [a]) := by
        simp [List.reverse_append]
      rw [h1, List.tail_cons, List.mem_append, List.mem_reverse, List.mem_singleton]
      rw [inner_append_cons_Last] at hinner
      rintro (hmid | rfl)
      · exact hinner hmid
      · exact hhead rfl

private lemma getLast?_cons_append_singleton (a : V) (mid : List V) (b : V) :
    (a :: (mid ++ [b])).getLast? = some b := by
  have h : a :: (mid ++ [b]) = (a :: mid) ++ [b] := rfl
  rw [h, List.getLast?_append_of_ne_nil _ (by simp)]
  rfl

private lemma mem_or_mem_inner_of_mem {L : List V} {x : V} (hx : x ∈ L) :
    L.head? = some x ∨ L.getLast? = some x ∨ x ∈ inner L := by
  cases L with
  | nil => simp at hx
  | cons a rest =>
    rw [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Or.inl rfl
    · cases rest using List.reverseRecOn with
      | nil => simp at hx
      | append_singleton mid b =>
        rw [inner_append_cons_Last]
        rw [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | hxb
        · exact Or.inr (Or.inr hx)
        · subst hxb
          exact Or.inr (Or.inl (getLast?_cons_append_singleton a mid x))

private lemma mem_and_ne_ends_of_mem_inner {L : List V} (hnodup : L.Nodup) {y : V}
    (hy : y ∈ inner L) : y ∈ L ∧ L.head? ≠ some y ∧ L.getLast? ≠ some y := by
  cases L with
  | nil => simp [inner] at hy
  | cons a rest =>
    cases rest using List.reverseRecOn with
    | nil => simp [inner] at hy
    | append_singleton mid b =>
      rw [inner_append_cons_Last] at hy
      rw [List.nodup_cons] at hnodup
      obtain ⟨ha_not, hnodup_rest⟩ := hnodup
      rw [List.nodup_append] at hnodup_rest
      have hya : y ≠ a := fun h => ha_not (h ▸ List.mem_append_left _ hy)
      have hyb : y ≠ b := fun h => hnodup_rest.2.2 y hy b (List.mem_singleton.mpr rfl) h
      refine ⟨List.mem_cons_of_mem _ (List.mem_append_left _ hy), ?_, ?_⟩
      · simp [hya.symm]
      · rw [getLast?_cons_append_singleton]
        simp [hyb.symm]

variable [DecidableEq V]

/-! ### Section 11: Both ends off the cycle (`Lift11OffOffStatement`) -/

private lemma idxOf_pos_of_mem_of_head?_ne {L : List V} {v : V} (hv : v ∈ L)
    (hhead : L.head? ≠ some v) : 1 ≤ L.idxOf v := by
  cases L with
  | nil => simp at hv
  | cons x rest =>
    have hxv : x ≠ v := fun h => hhead (by simp [h])
    rw [List.idxOf_cons_ne _ hxv]
    omega

private lemma decomp_of_mem_of_head?_ne_of_getLast?_ne {L : List V} {v : V}
    (hv : v ∈ L) (hhead : L.head? ≠ some v) (hlast : L.getLast? ≠ some v) :
    ∃ (L₁' : List V) (a b : V) (L₂' : List V),
      L = (L₁' ++ [a]) ++ v :: b :: L₂' ∧
      L.take (L.idxOf v) = L₁' ++ [a] ∧
      L.drop (L.idxOf v + 1) = b :: L₂' ∧
      L.getD (L.idxOf v - 1) v = a ∧
      L.getD (L.idxOf v + 1) v = b := by
  induction L with
  | nil => simp at hv
  | cons x rest ih =>
    have hxv : x ≠ v := fun h => hhead (by simp [h])
    have hv_rest : v ∈ rest := by
      rcases List.mem_cons.mp hv with rfl | h
      · exact absurd rfl hxv
      · exact h
    have hlast_rest : rest.getLast? ≠ some v := by
      cases rest with
      | nil => simp at hv_rest
      | cons y rest' => simpa using hlast
    by_cases hrest_head : rest.head? = some v
    · cases rest with
      | nil => simp at hv_rest
      | cons y rest' =>
        simp only [List.head?_cons, Option.some.injEq] at hrest_head
        subst y
        cases rest' with
        | nil => simp at hlast_rest
        | cons b L₂' =>
          refine ⟨[], x, b, L₂', rfl, ?_, ?_, ?_, ?_⟩ <;>
            simp [List.idxOf_cons_ne _ hxv]
    · obtain ⟨L₁', a, b, L₂', hL, htake, hdrop, hget1, hget2⟩ :=
        ih hv_rest hrest_head hlast_rest
      have hj_pos : 1 ≤ rest.idxOf v := idxOf_pos_of_mem_of_head?_ne hv_rest hrest_head
      refine ⟨x :: L₁', a, b, L₂', ?_, ?_, ?_, ?_, ?_⟩
      · simp [hL]
      · rw [List.idxOf_cons_ne _ hxv, List.take_succ_cons, htake, List.cons_append]
      · rw [List.idxOf_cons_ne _ hxv, List.drop_succ_cons, hdrop]
      · rw [List.idxOf_cons_ne _ hxv]
        obtain ⟨k, hk⟩ : ∃ k, rest.idxOf v = k + 1 := Nat.exists_eq_add_one.mpr hj_pos
        rw [hk] at hget1 ⊢
        simpa [List.getD] using hget1
      · rw [List.idxOf_cons_ne _ hxv]
        simpa [List.getD] using hget2

private lemma isDPathList_liftOffOff {K : SimpleGraph V} [DecidableRel K.Adj]
    {D : List V} {u v : V} (huv : K.Adj u v) (huD : u ∉ D) (hvD : v ∉ D)
    {L : List V} (hL : IsDPathList (contractGraph K u v) D L) :
    IsDPathList K D (liftOffOff K u v L) ∧
      (∀ a b, HasEndsUnordered (liftOffOff K u v L) a b ↔ HasEndsUnordered L a b) ∧
      (∀ y ∈ liftOffOff K u v L, y ∈ L ∨ (v ∈ L ∧ y = u)) := by
  obtain ⟨⟨hne, hnodup, hchain⟩, hlen, hheadD, hlastD, hinnerD⟩ := hL
  have huL : u ∉ L := not_mem_of_isChain_contractGraph hlen hchain
  unfold liftOffOff
  split_ifs with hvL
  · have hhead_ne : L.head? ≠ some v := fun h => hvD (hheadD v h)
    have hlast_ne : L.getLast? ≠ some v := fun h => hvD (hlastD v h)
    obtain ⟨L₁', a, b, L₂', hL_eq, htake, hdrop, hget1, hget2⟩ :=
      decomp_of_mem_of_head?_ne_of_getLast?_ne hvL hhead_ne hlast_ne
    dsimp only
    rw [htake, hdrop, hget1, hget2]
    set ua := if K.Adj v a then v else u
    set ub := if K.Adj v b then v else u
    set mid := if ua = ub then [ua] else [ua, ub]
    let L' := (L₁' ++ [a]) ++ mid ++ (b :: L₂')
    have hnodup1 : (L₁' ++ [a]).Nodup := by
      rw [hL_eq, List.nodup_append'] at hnodup; exact hnodup.1
    have hnodup_vb : (v :: b :: L₂').Nodup := by
      rw [hL_eq, List.nodup_append'] at hnodup; exact hnodup.2.1
    have hdisj12 : (L₁' ++ [a]).Disjoint (v :: b :: L₂') := by
      rw [hL_eq, List.nodup_append'] at hnodup; exact hnodup.2.2
    have hv_not1 : v ∉ L₁' ++ [a] := fun h => hdisj12 h List.mem_cons_self
    have hv_not2 : v ∉ b :: L₂' := (List.nodup_cons.mp hnodup_vb).1
    have hnodup2 : (b :: L₂').Nodup := (List.nodup_cons.mp hnodup_vb).2
    have hu_not1 : u ∉ L₁' ++ [a] := fun h => huL (hL_eq ▸ List.mem_append_left _ h)
    have hu_not2 : u ∉ b :: L₂' :=
      fun h => huL (hL_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ h))
    have hchain1_c : (L₁' ++ [a]).IsChain (contractGraph K u v).Adj := by
      rw [hL_eq, List.isChain_append] at hchain; exact hchain.1
    have hchain_vb_c : (v :: b :: L₂').IsChain (contractGraph K u v).Adj := by
      rw [hL_eq, List.isChain_append] at hchain; exact hchain.2.1
    have hav_c : (contractGraph K u v).Adj a v := by
      rw [hL_eq, List.isChain_append] at hchain
      exact hchain.2.2 a (by simp) v rfl
    have hvb_c : (contractGraph K u v).Adj v b :=
      (List.isChain_cons_cons.mp hchain_vb_c).1
    have hchain2_c : (b :: L₂').IsChain (contractGraph K u v).Adj :=
      (List.isChain_cons_cons.mp hchain_vb_c).2
    have hchain1 : (L₁' ++ [a]).IsChain K.Adj :=
      isChain_of_isChain_contractGraph_of_notMem hchain1_c hv_not1
    have hchain2 : (b :: L₂').IsChain K.Adj :=
      isChain_of_isChain_contractGraph_of_notMem hchain2_c hv_not2
    have haua : K.Adj a ua := by
      dsimp only [ua]
      split_ifs with hva
      · exact hva.symm
      · rcases hav_c.2.2.2 with h | ⟨rfl, _⟩ | ⟨_, h⟩
        · exact absurd h.symm hva
        · exact absurd rfl hav_c.1
        · exact h.symm
    have hubb : K.Adj ub b := by
      dsimp only [ub]
      split_ifs with hvb
      · exact hvb
      · rcases hvb_c.2.2.2 with h | ⟨_, h⟩ | ⟨rfl, _⟩
        · exact absurd h hvb
        · exact h
        · exact absurd rfl hvb_c.1
    have hmid_mem : ∀ z ∈ mid, z = u ∨ z = v := by
      intro z hz
      have hua_uv : ua = u ∨ ua = v := by dsimp only [ua]; split_ifs <;> simp
      have hub_uv : ub = u ∨ ub = v := by dsimp only [ub]; split_ifs <;> simp
      dsimp only [mid] at hz
      split_ifs at hz <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      · rcases hz with rfl; exact hua_uv
      · rcases hz with rfl | rfl
        · exact hua_uv
        · exact hub_uv
    have hmid_nodup : mid.Nodup := by
      dsimp only [mid]
      split_ifs with heq
      · exact List.nodup_singleton _
      · simp [heq]
    have hnodup' : L'.Nodup := by
      dsimp only [L']
      rw [List.nodup_append', List.nodup_append']
      refine ⟨⟨hnodup1, hmid_nodup, ?_⟩, hnodup2, ?_⟩
      · intro z hz1 hzmid
        rcases hmid_mem z hzmid with rfl | rfl
        · exact hu_not1 hz1
        · exact hv_not1 hz1
      · intro z hz1mid hz2
        rcases List.mem_append.mp hz1mid with hz1 | hzmid
        · exact hdisj12 hz1 (List.mem_cons_of_mem _ hz2)
        · rcases hmid_mem z hzmid with rfl | rfl
          · exact hu_not2 hz2
          · exact hv_not2 hz2
    have hchain' : L'.IsChain K.Adj := by
      dsimp only [L']
      rw [List.append_assoc, List.isChain_append]
      refine ⟨hchain1, ?_, ?_⟩
      · dsimp only [mid]
        split_ifs with heq
        · rw [← heq] at hubb
          exact List.isChain_cons_cons.mpr ⟨hubb, hchain2⟩
        · have huab : K.Adj ua ub := by
            have hua_uv : ua = u ∨ ua = v := by dsimp only [ua]; split_ifs <;> simp
            have hub_uv : ub = u ∨ ub = v := by dsimp only [ub]; split_ifs <;> simp
            rcases hua_uv with h1 | h1 <;> rcases hub_uv with h2 | h2
            · exact absurd (h1.trans h2.symm) heq
            · exact h1 ▸ h2 ▸ huv
            · exact h1 ▸ h2 ▸ huv.symm
            · exact absurd (h1.trans h2.symm) heq
          exact List.isChain_cons_cons.mpr ⟨huab, List.isChain_cons_cons.mpr ⟨hubb, hchain2⟩⟩
      · intro x hx y hy
        have hxa : x = a := by simpa [eq_comm] using hx
        have hyua : y = ua := by
          dsimp only [mid] at hy
          split_ifs at hy <;> simpa [eq_comm] using hy
        exact hxa ▸ hyua ▸ haua
    have hhead_eq : L'.head? = L.head? := by
      dsimp only [L']
      cases L₁' <;> simp [hL_eq]
    have hlast_eq : L'.getLast? = L.getLast? := by
      dsimp only [L']
      rw [hL_eq, List.getLast?_append_of_ne_nil _ (by simp),
        List.getLast?_append_of_ne_nil _ (by simp)]
      simp [List.getLast?_cons]
    have hmem' : ∀ y ∈ L', y ∈ L ∨ (v ∈ L ∧ y = u) := by
      intro y hy
      dsimp only [L'] at hy
      rw [List.mem_append, List.mem_append] at hy
      rcases hy with (hy1 | hymid) | hy2
      · exact Or.inl (hL_eq ▸ List.mem_append_left _ hy1)
      · rcases hmid_mem y hymid with rfl | rfl
        · exact Or.inr ⟨hvL, rfl⟩
        · exact Or.inl hvL
      · exact Or.inl (hL_eq ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hy2))
    refine ⟨⟨⟨by simp, hnodup', hchain'⟩, ?_, ?_, ?_, ?_⟩, ?_, hmem'⟩
    · simp only [List.length_append, List.length_cons]
      omega
    · intro c hc; exact hheadD c (hhead_eq ▸ hc)
    · intro c hc; exact hlastD c (hlast_eq ▸ hc)
    · intro y hy
      obtain ⟨hyL', hy_head, hy_last⟩ := mem_and_ne_ends_of_mem_inner hnodup' hy
      rw [hhead_eq] at hy_head
      rw [hlast_eq] at hy_last
      rcases hmem' y hyL' with hyL | ⟨_, rfl⟩
      · rcases mem_or_mem_inner_of_mem hyL with h | h | h
        · exact absurd h hy_head
        · exact absurd h hy_last
        · exact hinnerD y h
      · exact huD
    · intro c d
      unfold HasEndsUnordered HasEnds
      rw [hhead_eq, hlast_eq]
  · have hchain' : L.IsChain K.Adj := isChain_of_isChain_contractGraph_of_notMem hchain hvL
    exact ⟨⟨⟨hne, hnodup, hchain'⟩, hlen, hheadD, hlastD, hinnerD⟩,
      fun _ _ => Iff.rfl, fun y hy => Or.inl hy⟩

/-- **The lift when both ends are off the cycle** (Section 11, "Both ends off the cycle"): "The
added vertices do not occur on the other path or elsewhere on this path." -/
theorem lift11OffOff_proved : Lift11OffOffStatement := by
  intro V _ K _ S D u v L₁ L₂ _ _ huv huD hvD hcross
  obtain ⟨hL₁, hL₂, hdisj, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, hends⟩ := hcross
  have huL₁ : u ∉ L₁ := not_mem_of_isChain_contractGraph hL₁.2.1 hL₁.1.2.2
  have huL₂ : u ∉ L₂ := not_mem_of_isChain_contractGraph hL₂.2.1 hL₂.1.2.2
  obtain ⟨hL₁', hends₁, hmem₁⟩ := isDPathList_liftOffOff huv huD hvD hL₁
  obtain ⟨hL₂', hends₂, hmem₂⟩ := isDPathList_liftOffOff huv huD hvD hL₂
  refine ⟨hL₁', hL₂', ?_, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, ?_⟩
  · intro y hy₁ hy₂
    rcases hmem₁ y hy₁ with hy₁ | ⟨hv₁, hyu₁⟩ <;> rcases hmem₂ y hy₂ with hy₂ | ⟨hv₂, hyu₂⟩
    · exact hdisj hy₁ hy₂
    · exact huL₁ (hyu₂ ▸ hy₁)
    · exact huL₂ (hyu₁ ▸ hy₂)
    · exact hdisj hv₁ hv₂
  · rw [hends₁, hends₁, hends₂, hends₂]
    exact hends

/-! ### Section 11: One end on the cycle (`Lift11OneOnStatement`) -/

private lemma liftStartOneOn_eq_self_of_head?_ne (K : SimpleGraph V) [DecidableRel K.Adj]
    (u v : V) {L : List V} (hhead : L.head? ≠ some v) :
    liftStartOneOn K u v L = L := by
  cases L with
  | nil => rfl
  | cons x rest =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      have hxv : x ≠ v := fun h => hhead (by simp [h])
      simp [liftStartOneOn, hxv]

private lemma liftOneOn_eq_liftStartOneOn_of_head?_eq (K : SimpleGraph V) [DecidableRel K.Adj]
    (u v : V) {L : List V} (hlen : 2 ≤ L.length) (hnodup : L.Nodup) (hhead : L.head? = some v) :
    liftOneOn K u v L = liftStartOneOn K u v L := by
  cases L with
  | nil => simp at hlen
  | cons x rest =>
    cases rest with
    | nil => simp at hlen
    | cons b rest' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst x
      have hv_not_rest : v ∉ b :: rest' := (List.nodup_cons.mp hnodup).1
      have hlast_ne : (liftStartOneOn K u v (v :: b :: rest')).reverse.head? ≠ some v := by
        rw [List.head?_reverse]
        have hlast_eq : (liftStartOneOn K u v (v :: b :: rest')).getLast? =
            (b :: rest').getLast? := by
          dsimp only [liftStartOneOn]
          split_ifs <;> simp
        rw [hlast_eq]
        intro hlast
        exact hv_not_rest (List.mem_of_getLast? hlast)
      unfold liftOneOn
      rw [liftStartOneOn_eq_self_of_head?_ne K u v hlast_ne, List.reverse_reverse]

private lemma liftOneOn_reverse_of_head?_ne (K : SimpleGraph V) [DecidableRel K.Adj]
    (u v : V) {L : List V} (hhead : L.head? ≠ some v) :
    liftOneOn K u v L = (liftStartOneOn K u v L.reverse).reverse := by
  unfold liftOneOn
  rw [liftStartOneOn_eq_self_of_head?_ne K u v hhead]

private lemma isDPathList_liftStartOneOn {K : SimpleGraph V} [DecidableRel K.Adj]
    {D : List V} {u v : V} (huv : K.Adj u v) (huD : u ∉ D)
    {L : List V} (hL : IsDPathList (contractGraph K u v) D L) (hv_tail : v ∉ L.tail) :
    IsDPathList K D (liftStartOneOn K u v L) ∧
      (∀ a b, HasEnds (liftStartOneOn K u v L) a b ↔ HasEnds L a b) ∧
      (∀ y ∈ liftStartOneOn K u v L, y ∈ L ∨ (v ∈ L ∧ y = u)) := by
  obtain ⟨⟨hne, hnodup, hchain⟩, hlen, hheadD, hlastD, hinnerD⟩ := hL
  have huL : u ∉ L := not_mem_of_isChain_contractGraph hlen hchain
  cases L with
  | nil => simp at hlen
  | cons x rest =>
    cases rest with
    | nil => simp at hlen
    | cons b rest' =>
      simp only [List.tail_cons] at hv_tail
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hxb, hchain_rest⟩ := hchain
      have hchain_K_rest : (b :: rest').IsChain K.Adj :=
        isChain_of_isChain_contractGraph_of_notMem hchain_rest hv_tail
      dsimp only [liftStartOneOn]
      split_ifs with hcond
      · obtain ⟨hx_eq_v, hnot_vb⟩ := hcond
        subst x
        have hub : K.Adj u b := by
          rcases hxb.2.2.2 with h | ⟨_, h⟩ | ⟨hbv, _⟩
          · exact absurd h hnot_vb
          · exact h
          · exact absurd hbv.symm hxb.1
        have hnodup' : (v :: u :: b :: rest').Nodup := by
          rw [List.nodup_cons] at hnodup ⊢
          refine ⟨?_, List.nodup_cons.mpr ⟨fun hu => huL (List.mem_cons_of_mem _ hu), hnodup.2⟩⟩
          rw [List.mem_cons]
          rintro (rfl | hmem)
          · exact K.loopless.irrefl _ huv
          · exact hv_tail hmem
        have hchain' : (v :: u :: b :: rest').IsChain K.Adj :=
          List.isChain_cons_cons.mpr ⟨huv.symm, List.isChain_cons_cons.mpr ⟨hub, hchain_K_rest⟩⟩
        have hends : ∀ a c, HasEnds (v :: u :: b :: rest') a c ↔ HasEnds (v :: b :: rest') a c := by
          intro a c
          unfold HasEnds
          simp
        refine ⟨⟨⟨by simp, hnodup', hchain'⟩, by simp, hheadD, ?_, ?_⟩, hends, ?_⟩
        · intro c hc
          apply hlastD c
          simpa using hc
        · intro y hy
          rw [inner_cons_cons, List.dropLast_cons_of_ne_nil (by simp), List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact huD
          · exact hinnerD y hy
        · intro y hy
          rw [List.mem_cons, List.mem_cons] at hy
          rcases hy with rfl | rfl | hy
          · exact Or.inl List.mem_cons_self
          · exact Or.inr ⟨List.mem_cons_self, rfl⟩
          · exact Or.inl (List.mem_cons_of_mem _ hy)
      · have hxb_K : K.Adj x b := by
          rcases hxb.2.2.2 with h | ⟨hxv, _⟩ | ⟨hbv, _⟩
          · exact h
          · exact Classical.byContradiction fun hnot => hcond ⟨hxv, hxv ▸ hnot⟩
          · exact absurd (hbv ▸ List.mem_cons_self) hv_tail
        have hchain' : (x :: b :: rest').IsChain K.Adj :=
          List.isChain_cons_cons.mpr ⟨hxb_K, hchain_K_rest⟩
        exact ⟨⟨⟨hne, hnodup, hchain'⟩, hlen, hheadD, hlastD, hinnerD⟩,
          fun _ _ => Iff.rfl, fun y hy => Or.inl hy⟩

private lemma isDPathList_liftOneOn {K : SimpleGraph V} [DecidableRel K.Adj]
    {D : List V} {u v : V} (huv : K.Adj u v) (huD : u ∉ D) (hvD : v ∈ D)
    {L : List V} (hL : IsDPathList (contractGraph K u v) D L) :
    IsDPathList K D (liftOneOn K u v L) ∧
      (∀ a b, HasEndsUnordered (liftOneOn K u v L) a b ↔ HasEndsUnordered L a b) ∧
      (∀ y ∈ liftOneOn K u v L, y ∈ L ∨ (v ∈ L ∧ y = u)) := by
  have hv_inner : v ∉ inner L := fun h => hL.2.2.2.2 v h hvD
  by_cases hhead : L.head? = some v
  · rw [liftOneOn_eq_liftStartOneOn_of_head?_eq K u v hL.2.1 hL.1.2.1 hhead]
    have hv_tail : v ∉ L.tail := by
      cases L with
      | nil => simp
      | cons x rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst x
        exact (List.nodup_cons.mp hL.1.2.1).1
    obtain ⟨h1, h2, h3⟩ := isDPathList_liftStartOneOn huv huD hL hv_tail
    refine ⟨h1, fun a b => ?_, h3⟩
    unfold HasEndsUnordered
    rw [h2, h2]
  · rw [liftOneOn_reverse_of_head?_ne K u v hhead]
    have hv_rtail : v ∉ L.reverse.tail :=
      notMem_reverse_tail_of_head?_ne_of_notMem_inner hhead hv_inner
    have hLr : IsDPathList (contractGraph K u v) D L.reverse := isDPathList_reverse.mpr hL
    obtain ⟨h1, h2, h3⟩ := isDPathList_liftStartOneOn huv huD hLr hv_rtail
    refine ⟨isDPathList_reverse.mpr h1, fun a b => ?_, ?_⟩
    · rw [hasEndsUnordered_reverse]
      unfold HasEndsUnordered
      rw [h2, h2, hasEnds_reverse, hasEnds_reverse, or_comm]
    · intro y hy
      rw [List.mem_reverse] at hy
      rcases h3 y hy with hyL | ⟨hvL, rfl⟩
      · exact Or.inl (List.mem_reverse.mp hyL)
      · exact Or.inr ⟨List.mem_reverse.mp hvL, rfl⟩

/-- **The lift when one end is on the cycle** (Section 11, "One end on the cycle"): "The algorithm
orients this case so that $u\notin V(D)$ and $v\in V(D)$, and keeps $w=v$." "The only vertex added
inside the path is $u$, which is off the cycle." -/
theorem lift11OneOn_proved : Lift11OneOnStatement := by
  intro V _ K _ S D u v L₁ L₂ _ _ huv huD hvD hcross
  obtain ⟨hL₁, hL₂, hdisj, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, hends⟩ := hcross
  have huL₁ : u ∉ L₁ := not_mem_of_isChain_contractGraph hL₁.2.1 hL₁.1.2.2
  have huL₂ : u ∉ L₂ := not_mem_of_isChain_contractGraph hL₂.2.1 hL₂.1.2.2
  obtain ⟨hL₁', hends₁, hmem₁⟩ := isDPathList_liftOneOn huv huD hvD hL₁
  obtain ⟨hL₂', hends₂, hmem₂⟩ := isDPathList_liftOneOn huv huD hvD hL₂
  refine ⟨hL₁', hL₂', ?_, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, ?_⟩
  · intro y hy₁ hy₂
    rcases hmem₁ y hy₁ with hy₁ | ⟨hv₁, hyu₁⟩ <;> rcases hmem₂ y hy₂ with hy₂ | ⟨hv₂, hyu₂⟩
    · exact hdisj hy₁ hy₂
    · exact huL₁ (hyu₂ ▸ hy₁)
    · exact huL₂ (hyu₁ ▸ hy₂)
    · exact hdisj hv₁ hv₂
  · rw [hends₁, hends₁, hends₂, hends₂]
    exact hends

/-! ### Section 11: Both ends on the cycle (`Lift11BothOnStatement`) -/

private def repV (v w x : V) : V :=
  if x = v then w else x

private lemma repV_self (v x : V) : repV v v x = x := by
  unfold repV; split_ifs with h <;> [exact h.symm; rfl]

private lemma repV_of_ne {v w x : V} (h : x ≠ v) : repV v w x = x := by
  unfold repV; simp [h]

private lemma liftStartBothOn_eq_self_of_head?_ne (K : SimpleGraph V) [DecidableRel K.Adj]
    (u v : V) {L : List V} (hhead : L.head? ≠ some v) :
    liftStartBothOn K u v L = L := by
  cases L with
  | nil => rfl
  | cons x rest =>
    cases rest with
    | nil => rfl
    | cons b rest' =>
      have hxv : x ≠ v := fun h => hhead (by simp [h])
      simp [liftStartBothOn, hxv]

private lemma liftBothOn_eq_liftStartBothOn_of_head?_eq (K : SimpleGraph V) [DecidableRel K.Adj]
    (u v : V) {L : List V} (hlen : 2 ≤ L.length) (hnodup : L.Nodup) (hhead : L.head? = some v) :
    liftBothOn K u v L = liftStartBothOn K u v L := by
  cases L with
  | nil => simp at hlen
  | cons x rest =>
    cases rest with
    | nil => simp at hlen
    | cons b rest' =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst x
      have hv_not_rest : v ∉ b :: rest' := (List.nodup_cons.mp hnodup).1
      have hlast_ne : (liftStartBothOn K u v (v :: b :: rest')).reverse.head? ≠ some v := by
        rw [List.head?_reverse]
        have hlast_eq : (liftStartBothOn K u v (v :: b :: rest')).getLast? =
            (b :: rest').getLast? := by
          dsimp only [liftStartBothOn]
          split_ifs <;> simp
        rw [hlast_eq]
        intro hlast
        exact hv_not_rest (List.mem_of_getLast? hlast)
      unfold liftBothOn
      rw [liftStartBothOn_eq_self_of_head?_ne K u v hlast_ne, List.reverse_reverse]

private lemma liftBothOn_reverse_of_head?_ne (K : SimpleGraph V) [DecidableRel K.Adj]
    (u v : V) {L : List V} (hhead : L.head? ≠ some v) :
    liftBothOn K u v L = (liftStartBothOn K u v L.reverse).reverse := by
  unfold liftBothOn
  rw [liftStartBothOn_eq_self_of_head?_ne K u v hhead]

private lemma isDPathList_liftStartBothOn {K : SimpleGraph V} [DecidableRel K.Adj]
    {D : List V} {u v : V} (huD : u ∈ D)
    {L : List V} (hL : IsDPathList (contractGraph K u v) (D.erase u) L) (hv_tail : v ∉ L.tail) :
    IsDPathList K D (liftStartBothOn K u v L) ∧
      (∃ w, (w = u ∨ w = v) ∧
        ∀ a b, HasEnds L a b → HasEnds (liftStartBothOn K u v L) (repV v w a) (repV v w b)) ∧
      (∀ y ∈ liftStartBothOn K u v L, y ∈ L ∨ (v ∈ L ∧ y = u)) := by
  obtain ⟨⟨hne, hnodup, hchain⟩, hlen, hheadD, hlastD, hinnerD⟩ := hL
  have huL : u ∉ L := not_mem_of_isChain_contractGraph hlen hchain
  have hheadD' : ∀ a, L.head? = some a → a ∈ D := fun a ha => List.mem_of_mem_erase (hheadD a ha)
  have hlastD' : ∀ b, L.getLast? = some b → b ∈ D :=
    fun b hb => List.mem_of_mem_erase (hlastD b hb)
  have hinnerD' : ∀ y ∈ inner L, y ∉ D := by
    intro y hy hyD
    have hyL : y ∈ L := (mem_and_ne_ends_of_mem_inner hnodup hy).1
    have hyu : y ≠ u := fun h => huL (h ▸ hyL)
    exact hinnerD y hy ((List.mem_erase_of_ne hyu).mpr hyD)
  cases L with
  | nil => simp at hlen
  | cons x rest =>
    cases rest with
    | nil => simp at hlen
    | cons b rest' =>
      simp only [List.tail_cons] at hv_tail
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hxb, hchain_rest⟩ := hchain
      have hchain_K_rest : (b :: rest').IsChain K.Adj :=
        isChain_of_isChain_contractGraph_of_notMem hchain_rest hv_tail
      dsimp only [liftStartBothOn]
      split_ifs with hcond
      · obtain ⟨hx_eq_v, hnot_vb⟩ := hcond
        subst x
        have hub : K.Adj u b := by
          rcases hxb.2.2.2 with h | ⟨_, h⟩ | ⟨hbv, _⟩
          · exact absurd h hnot_vb
          · exact h
          · exact absurd hbv.symm hxb.1
        have hnodup' : (u :: b :: rest').Nodup :=
          List.nodup_cons.mpr ⟨fun hu => huL (List.mem_cons_of_mem _ hu),
            (List.nodup_cons.mp hnodup).2⟩
        have hchain' : (u :: b :: rest').IsChain K.Adj :=
          List.isChain_cons_cons.mpr ⟨hub, hchain_K_rest⟩
        refine ⟨⟨⟨by simp, hnodup', hchain'⟩, by simp, ?_, ?_, hinnerD'⟩,
          ⟨u, Or.inl rfl, ?_⟩, ?_⟩
        · intro a ha
          simp only [List.head?_cons, Option.some.injEq] at ha
          exact ha ▸ huD
        · intro c hc
          apply hlastD' c
          simpa using hc
        · intro a c ⟨ha, hc⟩
          simp only [List.head?_cons, Option.some.injEq] at ha
          subst a
          have hcv : c ≠ v := fun h => hv_tail (h ▸ List.mem_of_getLast? (by simpa using hc))
          refine ⟨by simp [repV], ?_⟩
          rw [repV_of_ne hcv]
          simpa using hc
        · intro y hy
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact Or.inr ⟨List.mem_cons_self, rfl⟩
          · exact Or.inl (List.mem_cons_of_mem _ hy)
      · have hxb_K : K.Adj x b := by
          rcases hxb.2.2.2 with h | ⟨hxv, _⟩ | ⟨hbv, _⟩
          · exact h
          · exact Classical.byContradiction fun hnot => hcond ⟨hxv, hxv ▸ hnot⟩
          · exact absurd (hbv ▸ List.mem_cons_self) hv_tail
        have hchain' : (x :: b :: rest').IsChain K.Adj :=
          List.isChain_cons_cons.mpr ⟨hxb_K, hchain_K_rest⟩
        refine ⟨⟨⟨hne, hnodup, hchain'⟩, hlen, hheadD', hlastD', hinnerD'⟩,
          ⟨v, Or.inr rfl, ?_⟩, fun y hy => Or.inl hy⟩
        intro a c h
        rwa [repV_self, repV_self]

private lemma isDPathList_liftBothOn {K : SimpleGraph V} [DecidableRel K.Adj]
    {D : List V} {u v : V} (huv : K.Adj u v) (huD : u ∈ D) (hvD : v ∈ D)
    {L : List V} (hL : IsDPathList (contractGraph K u v) (D.erase u) L) :
    IsDPathList K D (liftBothOn K u v L) ∧
      (∃ w, (w = u ∨ w = v) ∧
        ∀ a b, HasEndsUnordered L a b →
          HasEndsUnordered (liftBothOn K u v L) (repV v w a) (repV v w b)) ∧
      (v ∉ L → ∀ w a b, HasEndsUnordered L a b →
        HasEndsUnordered (liftBothOn K u v L) (repV v w a) (repV v w b)) ∧
      (∀ y ∈ liftBothOn K u v L, y ∈ L ∨ (v ∈ L ∧ y = u)) := by
  have hv_erase : v ∈ D.erase u := (List.mem_erase_of_ne huv.ne.symm).mpr hvD
  have hv_inner : v ∉ inner L := fun h => hL.2.2.2.2 v h hv_erase
  have hnot_v_ends : v ∉ L → ∀ w a b, HasEndsUnordered L a b →
      HasEndsUnordered (liftBothOn K u v L) (repV v w a) (repV v w b) := by
    intro hvL w a b hends
    have hhead : L.head? ≠ some v := fun h => hvL (List.mem_of_head? h)
    have hlast : L.reverse.head? ≠ some v := by
      rw [List.head?_reverse]
      exact fun h => hvL (List.mem_of_getLast? h)
    have hlift_eq : liftBothOn K u v L = L := by
      unfold liftBothOn
      rw [liftStartBothOn_eq_self_of_head?_ne K u v hhead,
        liftStartBothOn_eq_self_of_head?_ne K u v hlast, List.reverse_reverse]
    rw [hlift_eq]
    have hav : a ≠ v := by
      rintro rfl
      rcases hends with ⟨ha, _⟩ | ⟨_, ha⟩
      · exact hvL (List.mem_of_head? ha)
      · exact hvL (List.mem_of_getLast? ha)
    have hbv : b ≠ v := by
      rintro rfl
      rcases hends with ⟨_, hb⟩ | ⟨hb, _⟩
      · exact hvL (List.mem_of_getLast? hb)
      · exact hvL (List.mem_of_head? hb)
    rwa [repV_of_ne hav, repV_of_ne hbv]
  by_cases hhead : L.head? = some v
  · rw [liftBothOn_eq_liftStartBothOn_of_head?_eq K u v hL.2.1 hL.1.2.1 hhead]
    have hv_tail : v ∉ L.tail := by
      cases L with
      | nil => simp
      | cons x rest =>
        simp only [List.head?_cons, Option.some.injEq] at hhead
        subst x
        exact (List.nodup_cons.mp hL.1.2.1).1
    obtain ⟨h1, ⟨w, hw, h2⟩, h3⟩ := isDPathList_liftStartBothOn huD hL hv_tail
    refine ⟨h1, ⟨w, hw, fun a b h => ?_⟩, ?_, h3⟩
    · rcases h with h | h
      · exact Or.inl (h2 a b h)
      · exact Or.inr (h2 b a h)
    · rw [← liftBothOn_eq_liftStartBothOn_of_head?_eq K u v hL.2.1 hL.1.2.1 hhead]
      exact hnot_v_ends
  · rw [liftBothOn_reverse_of_head?_ne K u v hhead]
    have hv_rtail : v ∉ L.reverse.tail :=
      notMem_reverse_tail_of_head?_ne_of_notMem_inner hhead hv_inner
    have hLr : IsDPathList (contractGraph K u v) (D.erase u) L.reverse :=
      isDPathList_reverse.mpr hL
    obtain ⟨h1, ⟨w, hw, h2⟩, h3⟩ := isDPathList_liftStartBothOn huD hLr hv_rtail
    refine ⟨isDPathList_reverse.mpr h1, ⟨w, hw, fun a b h => ?_⟩, ?_, ?_⟩
    · rw [hasEndsUnordered_reverse]
      rcases h with h | h
      · exact Or.inr (h2 b a (hasEnds_reverse.mpr h))
      · exact Or.inl (h2 a b (hasEnds_reverse.mpr h))
    · rw [← liftBothOn_reverse_of_head?_ne K u v hhead]
      exact hnot_v_ends
    · intro y hy
      rw [List.mem_reverse] at hy
      rcases h3 y hy with hyL | ⟨hvL, rfl⟩
      · exact Or.inl (List.mem_reverse.mp hyL)
      · exact Or.inr ⟨List.mem_reverse.mp hvL, rfl⟩

/-! ### Cycle indices when erasing one end of a cycle edge -/

private def embIdx (k idx : ℕ) : ℕ :=
  if idx < k then idx else idx + 1

private lemma embIdx_strictMono (k : ℕ) {i j : ℕ} (hij : i < j) :
    embIdx k i < embIdx k j := by
  unfold embIdx; split_ifs <;> omega

private lemma embIdx_ne (k idx : ℕ) : embIdx k idx ≠ k := by
  unfold embIdx; split_ifs <;> omega

private lemma getElem?_embIdx_erase {D : List V} {u : V} (hu : u ∈ D) (idx : ℕ) :
    D[embIdx (D.idxOf u) idx]? = (D.erase u)[idx]? := by
  induction D generalizing idx with
  | nil => simp at hu
  | cons x rest ih =>
    by_cases hxu : x = u
    · subst x
      simp [embIdx]
    · have hu_rest : u ∈ rest := by
        rcases List.mem_cons.mp hu with rfl | h
        · exact absurd rfl hxu
        · exact h
      rw [List.idxOf_cons_ne _ hxu, List.erase_cons_tail (by simpa [beq_iff_eq] using hxu)]
      cases idx with
      | zero => simp [embIdx]
      | succ m =>
        have hemb : embIdx (rest.idxOf u + 1) (m + 1) = embIdx (rest.idxOf u) m + 1 := by
          unfold embIdx; split_ifs <;> omega
        rw [hemb, List.getElem?_cons_succ, List.getElem?_cons_succ, ih hu_rest m]

private lemma idxOf_eq_of_getElem?_eq_some {D : List V} (hnodup : D.Nodup) {i : ℕ} {x : V}
    (h : D[i]? = some x) : D.idxOf x = i := by
  induction D generalizing i with
  | nil => simp at h
  | cons a rest ih =>
    rw [List.nodup_cons] at hnodup
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst a
      exact List.idxOf_cons_self
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      have hax : a ≠ x := fun hax => hnodup.1 (hax ▸ List.mem_of_getElem? h)
      rw [List.idxOf_cons_ne _ hax, ih hnodup.2 h]

omit [DecidableEq V] in
private lemma mem_zip_append_singleton {d₀ : V} {rest L : List V} {x y : V}
    (h : (x, y) ∈ L.zip (rest ++ [d₀])) (heq : L = d₀ :: rest) :
    (∃ m, (d₀ :: rest)[m]? = some x ∧ (d₀ :: rest)[m + 1]? = some y) ∨
      ((d₀ :: rest)[rest.length]? = some x ∧ (d₀ :: rest)[0]? = some y) := by
  subst heq
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp h
  rw [List.getElem?_zip_eq_some] at hm
  obtain ⟨hx, hy⟩ := hm
  have hm_len : m < rest.length + 1 := (List.getElem?_eq_some_iff.mp hx).1
  by_cases hm_lt : m < rest.length
  · left
    refine ⟨m, hx, ?_⟩
    rw [List.getElem?_cons_succ, ← List.getElem?_append_left hm_lt (l₂ := [d₀]), hy]
  · right
    have hm_eq : m = rest.length := by omega
    subst hm_eq
    refine ⟨hx, ?_⟩
    simp only [List.getElem?_append_right (le_refl rest.length), Nat.sub_self,
      List.getElem?_cons_zero] at hy ⊢
    exact hy

private lemma cycleEdge_idxOf_cases {D : List V} {u v : V} (hnodup : D.Nodup)
    (he : IsCycleEdge D u v) :
    u ∈ D ∧ v ∈ D ∧
      (D.idxOf v = D.idxOf u + 1 ∨ D.idxOf u = D.idxOf v + 1 ∨
        (D.idxOf u = D.length - 1 ∧ D.idxOf v = 0) ∨
        (D.idxOf v = D.length - 1 ∧ D.idxOf u = 0)) := by
  obtain ⟨p, hp, hp_eq⟩ := he
  cases D with
  | nil => simp at hp
  | cons d₀ rest =>
    have hrot : (d₀ :: rest).rotate 1 = rest ++ [d₀] := by
      rw [List.rotate_cons_succ, List.rotate_zero]
    rw [hrot] at hp
    rcases hp_eq with rfl | rfl
    · rcases mem_zip_append_singleton hp rfl with ⟨m, hu, hv⟩ | ⟨hu, hv⟩
      · exact ⟨List.mem_of_getElem? hu, List.mem_of_getElem? hv, Or.inl (by
          rw [idxOf_eq_of_getElem?_eq_some hnodup hu, idxOf_eq_of_getElem?_eq_some hnodup hv])⟩
      · exact ⟨List.mem_of_getElem? hu, List.mem_of_getElem? hv, Or.inr (Or.inr (Or.inl ⟨by
          rw [idxOf_eq_of_getElem?_eq_some hnodup hu]; simp,
          idxOf_eq_of_getElem?_eq_some hnodup hv⟩))⟩
    · rcases mem_zip_append_singleton hp rfl with ⟨m, hv, hu⟩ | ⟨hv, hu⟩
      · exact ⟨List.mem_of_getElem? hu, List.mem_of_getElem? hv, Or.inr (Or.inl (by
          rw [idxOf_eq_of_getElem?_eq_some hnodup hu, idxOf_eq_of_getElem?_eq_some hnodup hv]))⟩
      · exact ⟨List.mem_of_getElem? hu, List.mem_of_getElem? hv, Or.inr (Or.inr (Or.inr ⟨by
          rw [idxOf_eq_of_getElem?_eq_some hnodup hv]; simp,
          idxOf_eq_of_getElem?_eq_some hnodup hu⟩))⟩

private def repIdx (kv ku idx : ℕ) : ℕ :=
  if idx = kv then ku else idx

private lemma getElem?_repIdx {D : List V} {u v : V} (hnodup : D.Nodup) (hu : u ∈ D) (hv : v ∈ D)
    {idx : ℕ} {x : V} (hx : D[idx]? = some x) :
    D[repIdx (D.idxOf v) (D.idxOf u) idx]? = some (repV v u x) := by
  unfold repIdx repV
  by_cases hxv : x = v
  · subst x
    have hidx : idx = D.idxOf v := (idxOf_eq_of_getElem?_eq_some hnodup hx).symm
    simp only [hidx, ↓reduceIte]
    exact List.getElem?_idxOf hu
  · have hidx : idx ≠ D.idxOf v := by
      rintro rfl
      exact hxv (Option.some.inj (hx.symm.trans (List.getElem?_idxOf hv)))
    simp [hidx, hxv, hx]

private abbrev CrossEnds (L₁ L₂ : List V) (a c b d : V) : Prop :=
  (HasEndsUnordered L₁ a b ∧ HasEndsUnordered L₂ c d) ∨
    (HasEndsUnordered L₁ c d ∧ HasEndsUnordered L₂ a b)

omit [DecidableEq V] in
private lemma crossEnds_rotate_left {L₁ L₂ : List V} {a c b d : V}
    (h : CrossEnds L₁ L₂ a c b d) : CrossEnds L₁ L₂ c b d a := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨or_comm.mp h1, h2⟩
  · exact Or.inl ⟨h1, or_comm.mp h2⟩

omit [DecidableEq V] in
private lemma crossEnds_rotate_right {L₁ L₂ : List V} {a c b d : V}
    (h : CrossEnds L₁ L₂ a c b d) : CrossEnds L₁ L₂ d a c b :=
  crossEnds_rotate_left (crossEnds_rotate_left (crossEnds_rotate_left h))

/-- **The lift when both ends are on the cycle** (Section 11, "Both ends on the cycle"): "Replacing
one cycle position by one of two consecutive positions keeps the cyclic order of the four distinct
ends, since no other end lies between those two positions." -/
theorem lift11BothOn_proved : Lift11BothOnStatement := by
  intro V _ K _ S D u v L₁ L₂ _ hD huv hce hcross
  obtain ⟨hL₁, hL₂, hdisj, i, r, j, s, hir, hrj, hjs, a, c, b, d, hi, hr, hj, hs, hends⟩ := hcross
  obtain ⟨huD, hvD, hidx_cases⟩ := cycleEdge_idxOf_cases hD.2.1 hce
  have huL₁ : u ∉ L₁ := not_mem_of_isChain_contractGraph hL₁.2.1 hL₁.1.2.2
  have huL₂ : u ∉ L₂ := not_mem_of_isChain_contractGraph hL₂.2.1 hL₂.1.2.2
  obtain ⟨hL₁', ⟨w₁, hw₁, hends₁⟩, hnotv₁, hmem₁⟩ := isDPathList_liftBothOn huv huD hvD hL₁
  obtain ⟨hL₂', ⟨w₂, hw₂, hends₂⟩, hnotv₂, hmem₂⟩ := isDPathList_liftBothOn huv huD hvD hL₂
  have hdisj' : (liftBothOn K u v L₁).Disjoint (liftBothOn K u v L₂) := by
    intro y hy₁ hy₂
    rcases hmem₁ y hy₁ with hy₁ | ⟨hv₁, hyu₁⟩ <;> rcases hmem₂ y hy₂ with hy₂ | ⟨hv₂, hyu₂⟩
    · exact hdisj hy₁ hy₂
    · exact huL₁ (hyu₂ ▸ hy₁)
    · exact huL₂ (hyu₁ ▸ hy₂)
    · exact hdisj hv₁ hv₂
  have hex_w : ∃ w, (w = u ∨ w = v) ∧
      CrossEnds (liftBothOn K u v L₁) (liftBothOn K u v L₂)
        (repV v w a) (repV v w c) (repV v w b) (repV v w d) := by
    by_cases hvL₁ : v ∈ L₁
    · have hvL₂ : v ∉ L₂ := fun h => hdisj hvL₁ h
      refine ⟨w₁, hw₁, ?_⟩
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hends₁ a b h1, hnotv₂ hvL₂ w₁ c d h2⟩
      · exact Or.inr ⟨hends₁ c d h1, hnotv₂ hvL₂ w₁ a b h2⟩
    · refine ⟨w₂, hw₂, ?_⟩
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨hnotv₁ hvL₁ w₂ a b h1, hends₂ c d h2⟩
      · exact Or.inr ⟨hnotv₁ hvL₁ w₂ c d h1, hends₂ a b h2⟩
  obtain ⟨w, hw, hcross_w⟩ := hex_w
  let ku := D.idxOf u
  let kv := D.idxOf v
  let i₀ := embIdx ku i
  let r₀ := embIdx ku r
  let j₀ := embIdx ku j
  let s₀ := embIdx ku s
  have hi₀ : D[i₀]? = some a := (getElem?_embIdx_erase huD i).trans hi
  have hr₀ : D[r₀]? = some c := (getElem?_embIdx_erase huD r).trans hr
  have hj₀ : D[j₀]? = some b := (getElem?_embIdx_erase huD j).trans hj
  have hs₀ : D[s₀]? = some d := (getElem?_embIdx_erase huD s).trans hs
  have hir₀ : i₀ < r₀ := embIdx_strictMono ku hir
  have hrj₀ : r₀ < j₀ := embIdx_strictMono ku hrj
  have hjs₀ : j₀ < s₀ := embIdx_strictMono ku hjs
  refine ⟨hL₁', hL₂', hdisj', ?_⟩
  rcases hw with hwu | hwv
  · subst w
    have hi₁ : D[repIdx kv ku i₀]? = some (repV v u a) := getElem?_repIdx hD.2.1 huD hvD hi₀
    have hr₁ : D[repIdx kv ku r₀]? = some (repV v u c) := getElem?_repIdx hD.2.1 huD hvD hr₀
    have hj₁ : D[repIdx kv ku j₀]? = some (repV v u b) := getElem?_repIdx hD.2.1 huD hvD hj₀
    have hs₁ : D[repIdx kv ku s₀]? = some (repV v u d) := getElem?_repIdx hD.2.1 huD hvD hs₀
    have hi₀_ne : i₀ ≠ ku := embIdx_ne ku i
    have hr₀_ne : r₀ ≠ ku := embIdx_ne ku r
    have hj₀_ne : j₀ ≠ ku := embIdx_ne ku j
    have hs₀_ne : s₀ ≠ ku := embIdx_ne ku s
    have hs₀_lt : s₀ < D.length := (List.getElem?_eq_some_iff.mp hs₀).1
    rcases hidx_cases with hkv_ku | hku_kv | ⟨hku_last, hkv_zero⟩ | ⟨hkv_last, hku_zero⟩
    · refine ⟨repIdx kv ku i₀, repIdx kv ku r₀, repIdx kv ku j₀, repIdx kv ku s₀,
        ?_, ?_, ?_, _, _, _, _, hi₁, hr₁, hj₁, hs₁, hcross_w⟩ <;>
        (dsimp only [repIdx, ku, kv] at *; split_ifs <;> omega)
    · refine ⟨repIdx kv ku i₀, repIdx kv ku r₀, repIdx kv ku j₀, repIdx kv ku s₀,
        ?_, ?_, ?_, _, _, _, _, hi₁, hr₁, hj₁, hs₁, hcross_w⟩ <;>
        (dsimp only [repIdx, ku, kv] at *; split_ifs <;> omega)
    · by_cases hi₀_kv : i₀ = kv
      · have hr_eq : repIdx kv ku r₀ = r₀ := by unfold repIdx; simp [show r₀ ≠ kv by omega]
        have hj_eq : repIdx kv ku j₀ = j₀ := by unfold repIdx; simp [show j₀ ≠ kv by omega]
        have hs_eq : repIdx kv ku s₀ = s₀ := by unfold repIdx; simp [show s₀ ≠ kv by omega]
        have hi_eq : repIdx kv ku i₀ = ku := by unfold repIdx; simp [hi₀_kv]
        rw [hr_eq] at hr₁; rw [hj_eq] at hj₁; rw [hs_eq] at hs₁; rw [hi_eq] at hi₁
        refine ⟨r₀, j₀, s₀, ku, hrj₀, hjs₀, by omega, _, _, _, _,
          hr₁, hj₁, hs₁, hi₁, crossEnds_rotate_left hcross_w⟩
      · refine ⟨repIdx kv ku i₀, repIdx kv ku r₀, repIdx kv ku j₀, repIdx kv ku s₀,
          ?_, ?_, ?_, _, _, _, _, hi₁, hr₁, hj₁, hs₁, hcross_w⟩ <;>
          (dsimp only [repIdx, ku, kv] at *; split_ifs <;> omega)
    · by_cases hs₀_kv : s₀ = kv
      · have hi_eq : repIdx kv ku i₀ = i₀ := by unfold repIdx; simp [show i₀ ≠ kv by omega]
        have hr_eq : repIdx kv ku r₀ = r₀ := by unfold repIdx; simp [show r₀ ≠ kv by omega]
        have hj_eq : repIdx kv ku j₀ = j₀ := by unfold repIdx; simp [show j₀ ≠ kv by omega]
        have hs_eq : repIdx kv ku s₀ = ku := by unfold repIdx; simp [hs₀_kv]
        rw [hi_eq] at hi₁; rw [hr_eq] at hr₁; rw [hj_eq] at hj₁; rw [hs_eq] at hs₁
        refine ⟨ku, i₀, r₀, j₀, by omega, hir₀, hrj₀, _, _, _, _,
          hs₁, hi₁, hr₁, hj₁, crossEnds_rotate_right hcross_w⟩
      · refine ⟨repIdx kv ku i₀, repIdx kv ku r₀, repIdx kv ku j₀, repIdx kv ku s₀,
          ?_, ?_, ?_, _, _, _, _, hi₁, hr₁, hj₁, hs₁, hcross_w⟩ <;>
          (dsimp only [repIdx, ku, kv] at *; split_ifs <;> omega)
  · subst w
    simp only [repV_self] at hcross_w
    exact ⟨i₀, r₀, j₀, s₀, hir₀, hrj₀, hjs₀, a, c, b, d, hi₀, hr₀, hj₀, hs₀, hcross_w⟩

end GraphMinor.Crossing
