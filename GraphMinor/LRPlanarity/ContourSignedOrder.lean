module

public import GraphMinor.LRPlanarity.ContourFork
import GraphMinor.LRPlanarity.ContourTree
import GraphMinor.LRPlanarity.ForkOrder

/-!
# The signed contour order

This file proves the facts about `signedContourOrder` that Part IV, Sections 1 and 2 of
`docs/planarity/planarity_test.tex` state when they build the contour.

* The local orders form a valid contour order (`validContourOrder_signed`): "These rules give a
  rotation at every original vertex."
* The color that the contour gives to a back edge is its own color (`contourColor_signed`),
  since a target port of color `L` is placed before the child block and one of color `R` after.
* At a fork, events of distinct outgoing edges come in the signed order of the edges
  (`outEvent_lt_iff_signed`).
* "Inserting target ports does not change the order of the source ports, so the source ranks
  used to build the lists are exactly the order of the source ports in W." (`sourceRanks_eq`,
  `rank_lt_iff`).
* The block `L_e W(w) R_e` of a tree edge `e = (v, w)` is a contiguous subword of the word
  (`edgeBlockWord_infix`). Besides the ports below `w`, it holds only target ports at `v` of back
  edges from below `w` (`mem_edgeBlockWord`).
-/

public section

namespace GraphMinor.LRPlanarity.ContourWord

open SearchTree ForkOrder

variable {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)} {color : Coloring N}

open Classical in
/-- Part IV, Section 2: the block of an outgoing edge in the local order. A tree edge
`e = (v, w)` gives "target ports L_e ; child w ; target ports R_e", and an outgoing back edge
gives its source port. -/
@[expose] noncomputable def edgeBlock (T : Forest N) (G : SimpleGraph (Fin N))
    (color : Coloring N) (v : Fin N) (e : Arc N) : List (ContourEvent N) :=
  if T.TreeEdge e then targetList T G color v e.2 .left ++ [.child e.2] ++
    targetList T G color v e.2 .right
  else [.port ⟨e, true⟩]

theorem signedContourOrder_eq (v : Fin N) :
    signedContourOrder T G color v =
      (T.signedOutgoing G color v).flatMap (edgeBlock T G color v) := rfl

theorem edgeBlock_tree {v : Fin N} {e : Arc N} (he : T.TreeEdge e) :
    edgeBlock T G color v e = targetList T G color v e.2 .left ++ [.child e.2] ++
      targetList T G color v e.2 .right := by
  unfold edgeBlock
  simp only [he, ↓reduceIte]

theorem edgeBlock_back {v : Fin N} {e : Arc N} (he : ¬ T.TreeEdge e) :
    edgeBlock T G color v e = [.port ⟨e, true⟩] := by
  unfold edgeBlock
  simp only [he, ↓reduceIte]

/-! ### Target lists -/

theorem mem_targetList {v w : Fin N} {side : Color} {ev : ContourEvent N} :
    ev ∈ targetList T G color v w side ↔ ∃ b, T.BackEdge G b ∧ b.2 = v ∧ T.Ancestor w b.1 ∧
      color b = side ∧ ev = .port ⟨b, false⟩ := by
  unfold targetList
  simp only [List.mem_map, List.mem_mergeSort, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, ⟨h₁, h₂, h₃, h₄⟩, rfl⟩
    exact ⟨b, h₁, h₂, h₃, h₄, rfl⟩
  · rintro ⟨b, h₁, h₂, h₃, h₄, rfl⟩
    exact ⟨b, ⟨h₁, h₂, h₃, h₄⟩, rfl⟩

theorem port_mem_targetList {v w : Fin N} {side : Color} {b : Arc N} :
    ContourEvent.port ⟨b, false⟩ ∈ targetList T G color v w side ↔
      T.BackEdge G b ∧ b.2 = v ∧ T.Ancestor w b.1 ∧ color b = side := by
  rw [mem_targetList]
  constructor
  · rintro ⟨c, h₁, h₂, h₃, h₄, h⟩
    simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at h
    subst h
    exact ⟨h₁, h₂, h₃, h₄⟩
  · rintro ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨b, h₁, h₂, h₃, h₄, rfl⟩

theorem nodup_targetList (v w : Fin N) (side : Color) :
    (targetList T G color v w side).Nodup := by
  unfold targetList
  refine List.Nodup.map (fun b c h => ?_) (List.nodup_mergeSort.mpr (Finset.nodup_toList _))
  simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at h
  exact h

/-- Part IV, Section 2: "In each list, we order the edges by decreasing source rank." -/
theorem rank_le_of_targetList {v w : Fin N} {side : Color} {b c : Arc N}
    (hb : ContourEvent.port ⟨b, false⟩ ∈ targetList T G color v w side)
    (hc : ContourEvent.port ⟨c, false⟩ ∈ targetList T G color v w side)
    (hlt : (targetList T G color v w side).idxOf (.port ⟨b, false⟩) <
      (targetList T G color v w side).idxOf (.port ⟨c, false⟩)) :
    (sourceRanks T G color).idxOf c ≤ (sourceRanks T G color).idxOf b := by
  have hpw : (targetList T G color v w side).Pairwise (fun x y => ∀ b c : Arc N,
      x = .port ⟨b, false⟩ → y = .port ⟨c, false⟩ →
        (sourceRanks T G color).idxOf c ≤ (sourceRanks T G color).idxOf b) := by
    unfold targetList
    rw [List.pairwise_map]
    refine (List.pairwise_mergeSort (fun a b c hab hbc => ?_) (fun a b => ?_) _).imp ?_
    · simp only [decide_eq_true_eq] at hab hbc ⊢
      omega
    · simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    · intro a b h b' c' hb' hc'
      simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at hb' hc'
      subst hb' hc'
      simpa only [decide_eq_true_eq] using h
  exact rel_of_idxOf_lt hpw hb hc hlt b c rfl rfl

/-! ### Validity -/

theorem mem_edgeBlock_tree {v : Fin N} {e : Arc N} (he : T.TreeEdge e) {ev : ContourEvent N} :
    ev ∈ edgeBlock T G color v e ↔ ev = .child e.2 ∨
      ∃ b, T.BackEdge G b ∧ b.2 = v ∧ T.Ancestor e.2 b.1 ∧ ev = .port ⟨b, false⟩ := by
  rw [edgeBlock_tree he, List.mem_append, List.mem_append, List.mem_singleton, mem_targetList,
    mem_targetList]
  constructor
  · rintro ((⟨b, h₁, h₂, h₃, _, rfl⟩ | rfl) | ⟨b, h₁, h₂, h₃, _, rfl⟩)
    · exact Or.inr ⟨b, h₁, h₂, h₃, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨b, h₁, h₂, h₃, rfl⟩
  · rintro (rfl | ⟨b, h₁, h₂, h₃, rfl⟩)
    · exact Or.inl (Or.inr rfl)
    · cases hcol : color b
      · exact Or.inl (Or.inl ⟨b, h₁, h₂, h₃, hcol, rfl⟩)
      · exact Or.inr ⟨b, h₁, h₂, h₃, hcol, rfl⟩

theorem nodup_edgeBlock (v : Fin N) (e : Arc N) : (edgeBlock T G color v e).Nodup := by
  by_cases he : T.TreeEdge e
  · rw [edgeBlock_tree he, List.nodup_append, List.nodup_append]
    refine ⟨⟨nodup_targetList _ _ _, List.nodup_singleton _, fun a ha b hb => ?_⟩,
      nodup_targetList _ _ _, fun a ha b hb => ?_⟩
    · obtain ⟨c, -, -, -, -, rfl⟩ := mem_targetList.mp ha
      rw [List.mem_singleton] at hb
      subst hb
      simp
    · obtain ⟨c, -, -, -, hc, rfl⟩ := mem_targetList.mp hb
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨d, -, -, -, hd, rfl⟩ := mem_targetList.mp ha
        intro h
        simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at h
        subst h
        rw [hd] at hc
        cases hc
      · rw [List.mem_singleton] at ha
        subst ha
        simp
  · rw [edgeBlock_back he]
    exact List.nodup_singleton _

/-- Events of the blocks of distinct outgoing edges at `v` are distinct. -/
theorem edgeBlock_disjoint (hT : T.IsDFS G) {v : Fin N} {e e' : Arc N} (he : T.Outgoing G v e)
    (he' : T.Outgoing G v e') (hne : e ≠ e') :
    List.Disjoint (edgeBlock T G color v e) (edgeBlock T G color v e') := by
  intro ev h h'
  by_cases ht : T.TreeEdge e <;> by_cases ht' : T.TreeEdge e'
  · rcases (mem_edgeBlock_tree ht).mp h with rfl | ⟨b, -, -, hb, rfl⟩ <;>
      rcases (mem_edgeBlock_tree ht').mp h' with h' | ⟨b', -, -, hb', h'⟩
    · rw [ContourEvent.child.injEq] at h'
      exact hne (Prod.ext (he.1.trans he'.1.symm) h')
    · cases h'
    · cases h'
    · simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at h'
      subst h'
      have hc : T.parent e.2 = some v := he.1 ▸ ht
      have hc' : T.parent e'.2 = some v := he'.1 ▸ ht'
      exact hne (Prod.ext (he.1.trans he'.1.symm) (child_unique hT hc hc' hb hb'))
  · rw [edgeBlock_back ht', List.mem_singleton] at h'
    subst h'
    rcases (mem_edgeBlock_tree ht).mp h with h | ⟨b, -, -, -, h⟩
    · cases h
    · simp at h
  · rw [edgeBlock_back ht, List.mem_singleton] at h
    subst h
    rcases (mem_edgeBlock_tree ht').mp h' with h | ⟨b, -, -, -, h⟩
    · cases h
    · simp at h
  · rw [edgeBlock_back ht, List.mem_singleton] at h
    rw [edgeBlock_back ht', List.mem_singleton, h] at h'
    simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at h'
    exact hne h'

/-- Part IV, Section 2: "These rules give a rotation at every original vertex." -/
theorem validContourOrder_signed (hT : T.IsDFS G) (color : Coloring N) :
    ValidContourOrder T G (signedContourOrder T G color) := by
  intro v
  refine ⟨?_, fun event => ?_⟩
  · rw [signedContourOrder_eq, List.nodup_flatMap]
    refine ⟨fun e _ => nodup_edgeBlock v e,
      (nodup_signedOutgoing color v).pairwise_of_forall_ne fun e he e' he' hne => ?_⟩
    exact edgeBlock_disjoint hT ((mem_signedOutgoing color v e).mp he)
      ((mem_signedOutgoing color v e').mp he') hne
  rw [signedContourOrder_eq, List.mem_flatMap]
  simp only [mem_signedOutgoing]
  cases event with
  | child w =>
    constructor
    · rintro ⟨e, he, h⟩
      by_cases ht : T.TreeEdge e
      · rcases (mem_edgeBlock_tree ht).mp h with h | ⟨b, -, -, -, h⟩
        · rw [ContourEvent.child.injEq] at h
          rw [h, ← he.1]
          exact ht
        · cases h
      · rw [edgeBlock_back ht, List.mem_singleton] at h
        cases h
    · intro hw
      exact ⟨(v, w), ⟨rfl, Or.inl hw⟩, (mem_edgeBlock_tree (e := (v, w)) hw).mpr (Or.inl rfl)⟩
  | port p =>
    obtain ⟨b, source⟩ := p
    cases source with
    | true =>
      simp only [ite_true]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases ht : T.TreeEdge e
        · rcases (mem_edgeBlock_tree ht).mp h with h | ⟨c, -, -, -, h⟩
          · cases h
          · simp at h
        · rw [edgeBlock_back ht, List.mem_singleton] at h
          simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at h
          subst h
          exact ⟨he.2.resolve_left ht, he.1⟩
      · rintro ⟨hb, hbv⟩
        refine ⟨b, ⟨hbv, Or.inr hb⟩, ?_⟩
        rw [edgeBlock_back (not_treeEdge_of_backEdge hT hb)]
        exact List.mem_singleton_self _
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases ht : T.TreeEdge e
        · rcases (mem_edgeBlock_tree ht).mp h with h | ⟨c, hc, hcv, -, h⟩
          · cases h
          · simp only [ContourEvent.port.injEq, Port.mk.injEq, and_true] at h
            subst h
            exact ⟨hc, hcv⟩
        · rw [edgeBlock_back ht, List.mem_singleton] at h
          simp at h
      · rintro ⟨hb, hbv⟩
        have hvb : T.Ancestor v b.1 := hbv ▸ ancestor_of_backEdge hb
        have hne : v ≠ b.1 := hbv ▸ ne_of_backEdge hb
        obtain ⟨y, hy, hyb⟩ := exists_child_of_ancestor hvb hne
        exact ⟨(v, y), ⟨rfl, Or.inl hy⟩, (mem_edgeBlock_tree (e := (v, y)) hy).mpr (Or.inr ⟨b, hb, hbv, hyb, rfl⟩)⟩

/-! ### Colors and the order of fork edges -/

/-- The block of an outgoing edge is a contiguous part of the local order. -/
theorem edgeBlock_infix {v : Fin N} {e : Arc N} (he : T.Outgoing G v e) :
    edgeBlock T G color v e <:+: signedContourOrder T G color v := by
  rw [signedContourOrder_eq]
  exact List.infix_of_mem_flatten
    (List.mem_map_of_mem ((mem_signedOutgoing color v e).mpr he))

/-- Part IV, Section 2: the contour color of a back edge in the signed contour is its own
color, since `L_e` precedes `child w` and `R_e` follows it. -/
theorem contourColor_signed (hT : T.IsDFS G) (color : Coloring N) {b : Arc N}
    (hb : T.BackEdge G b) : contourColor T (signedContourOrder T G color) b = color b := by
  obtain ⟨w, hw, hwb⟩ := exists_child_of_ancestor (ancestor_of_backEdge hb) (ne_of_backEdge hb)
  have he : T.Outgoing G b.2 (b.2, w) := ⟨rfl, Or.inl hw⟩
  have hO := validContourOrder_signed hT color
  obtain ⟨off, hin, -⟩ := idxOf_of_infix (hO b.2).1 (edgeBlock_infix (color := color) he)
  have hblk : edgeBlock T G color b.2 (b.2, w) = targetList T G color b.2 w .left ++
      [.child w] ++ targetList T G color b.2 w .right := edgeBlock_tree (e := (b.2, w)) hw
  have hcB : ContourEvent.child w ∈ edgeBlock T G color b.2 (b.2, w) :=
    (mem_edgeBlock_tree (e := (b.2, w)) hw).mpr (Or.inl rfl)
  have htB : ContourEvent.port ⟨b, false⟩ ∈ edgeBlock T G color b.2 (b.2, w) :=
    (mem_edgeBlock_tree (e := (b.2, w)) hw).mpr (Or.inr ⟨b, hb, rfl, hwb, rfl⟩)
  refine color_eq_of_iff (contourColor_eq_left_iff hT hw hwb) ?_
  rw [hin _ hcB, hin _ htB, Nat.add_lt_add_iff_left, hblk]
  have hcL : ContourEvent.child w ∉ targetList T G color b.2 w .left := by
    intro h
    obtain ⟨c, -, -, -, -, h⟩ := mem_targetList.mp h
    cases h
  rw [List.append_assoc, List.singleton_append, List.idxOf_append_of_notMem hcL,
    List.idxOf_cons_self]
  cases hcol : color b
  · have htL : ContourEvent.port ⟨b, false⟩ ∈ targetList T G color b.2 w .left :=
      port_mem_targetList.mpr ⟨hb, rfl, hwb, hcol⟩
    rw [List.idxOf_append_of_mem htL]
    exact iff_of_true rfl (by simpa using List.idxOf_lt_length_of_mem htL)
  · have htL : ContourEvent.port ⟨b, false⟩ ∉ targetList T G color b.2 w .left := by
      intro h
      rw [(port_mem_targetList.mp h).2.2.2] at hcol
      cases hcol
    rw [List.idxOf_append_of_notMem htL, List.idxOf_cons_ne _ (by simp)]
    exact iff_of_false (by simp) (by omega)

theorem outEvent_mem_edgeBlock (v : Fin N) (e : Arc N) :
    outEvent T e ∈ edgeBlock T G color v e := by
  unfold outEvent
  split_ifs with ht
  · exact (mem_edgeBlock_tree ht).mpr (Or.inl rfl)
  · rw [edgeBlock_back ht]
    exact List.mem_singleton_self _

/-- At a fork, the events of distinct outgoing edges come in the signed order of the edges. -/
theorem outEvent_lt_iff_signed (hT : T.IsDFS G) {v : Fin N} {e f : Arc N}
    (he : T.Outgoing G v e) (hf : T.Outgoing G v f) (hef : e ≠ f) :
    (signedContourOrder T G color v).idxOf (outEvent T e) <
        (signedContourOrder T G color v).idxOf (outEvent T f) ↔
      (T.signedOutgoing G color v).idxOf e < (T.signedOutgoing G color v).idxOf f := by
  have hnd := ((validContourOrder_signed hT color) v).1
  rw [signedContourOrder_eq] at hnd ⊢
  have he' := (mem_signedOutgoing color v e).mpr he
  have hf' := (mem_signedOutgoing color v f).mpr hf
  constructor
  · intro h
    rcases idxOf_lt_or_gt he' hef with h' | h'
    · exact h'
    · exact absurd (idxOf_flatMap_lt hnd hf' he' h' (outEvent_mem_edgeBlock v f)
        (outEvent_mem_edgeBlock v e)) (Nat.lt_asymm h)
  · intro h
    exact idxOf_flatMap_lt hnd he' hf' h (outEvent_mem_edgeBlock v e)
      (outEvent_mem_edgeBlock v f)

/-! ### Source ranks -/

/-- The edge of a source port. -/
def sourceEdge (p : Port N) : Option (Arc N) := if p.source then some p.edge else none

theorem sourceEdge_inj (p q : Port N) (b : Arc N) (hp : sourceEdge p = some b)
    (hq : sourceEdge q = some b) : p = q := by
  obtain ⟨p, sp⟩ := p
  obtain ⟨q, sq⟩ := q
  cases sp <;> cases sq <;> simp_all [sourceEdge]

theorem sourceEnumeration_eq (color : Coloring N) : ∀ (k : ℕ) (v : Fin N),
    sourceEnumeration T G color k v =
      (vertexContour (signedContourOrder T G color) k v).filterMap sourceEdge
  | 0, v => by simp [sourceEnumeration, vertexContour]
  | k + 1, v => by
    rw [vertexContour_succ, signedContourOrder_eq, List.flatMap_assoc, List.filterMap_flatMap,
      sourceEnumeration]
    refine List.flatMap_congr fun e _ => ?_
    by_cases ht : T.TreeEdge e
    · have hnil : ∀ side, ((targetList T G color v e.2 side).flatMap
          (expand (vertexContour (signedContourOrder T G color) k))).filterMap sourceEdge = [] := by
        intro side
        refine List.filterMap_eq_nil_iff.mpr fun a ha => ?_
        obtain ⟨ev, hev, ha⟩ := List.mem_flatMap.mp ha
        obtain ⟨c, -, -, -, -, rfl⟩ := mem_targetList.mp hev
        rw [expand, List.mem_singleton] at ha
        subst ha
        rfl
      simp only [ht, ↓reduceIte]
      rw [edgeBlock_tree ht, List.flatMap_append, List.flatMap_append, List.filterMap_append,
        List.filterMap_append, hnil, hnil, List.flatMap_singleton, sourceEnumeration_eq color k e.2]
      simp [expand]
    · simp only [ht, ↓reduceIte]
      rw [edgeBlock_back ht]
      simp [expand, sourceEdge]

/-- Part IV, Section 2: "the source ranks used to build the lists are exactly the order of the
source ports in W." -/
theorem sourceRanks_eq (color : Coloring N) :
    sourceRanks T G color =
      (contourWord T (signedContourOrder T G color)).filterMap sourceEdge := by
  unfold sourceRanks contourWord
  rw [List.filterMap_flatMap]
  exact List.flatMap_congr fun r _ => sourceEnumeration_eq color (N + 1) r

theorem rank_lt_iff (hT : T.IsDFS G) (color : Coloring N) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) :
    (sourceRanks T G color).idxOf b < (sourceRanks T G color).idxOf c ↔
      (contourWord T (signedContourOrder T G color)).idxOf (⟨b, true⟩ : Port N) <
        (contourWord T (signedContourOrder T G color)).idxOf (⟨c, true⟩ : Port N) := by
  have hO := validContourOrder_signed hT color
  rw [sourceRanks_eq]
  exact (idxOf_filterMap_lt_iff sourceEdge_inj ((mem_contourWord hT hO _).mpr hb)
    ((mem_contourWord hT hO _).mpr hc) rfl rfl).symm

/-! ### Edge blocks in the word -/

/-- The ports of the block `L_e W(w) R_e` of an outgoing edge `e`. -/
@[expose] noncomputable def edgeBlockWord (T : Forest N) (G : SimpleGraph (Fin N)) (color : Coloring N)
    (v : Fin N) (e : Arc N) : List (Port N) :=
  (edgeBlock T G color v e).flatMap
    (expand (subtreeWord T (signedContourOrder T G color)))

/-- Part IV, Section 2: "For a tree edge e=(v,w), its whole block L_e W(w) R_e is
contiguous." -/
theorem edgeBlockWord_infix (hT : T.IsDFS G) {v : Fin N} {e : Arc N}
    (he : T.Outgoing G v e) :
    edgeBlockWord T G color v e <:+: contourWord T (signedContourOrder T G color) := by
  have hO := validContourOrder_signed hT color
  refine List.IsInfix.trans ?_ (subtreeWord_infix hT hO v)
  rw [subtreeWord_eq hT hO v, signedContourOrder_eq, List.flatMap_assoc]
  exact List.infix_of_mem_flatten
    (List.mem_map_of_mem ((mem_signedOutgoing color v e).mpr he))

/-- A port in the block of a tree edge `(v, w)` has its home below `w`, or is a target port
at `v` of a back edge from below `w`. -/
theorem mem_edgeBlockWord (hT : T.IsDFS G) {v : Fin N} {e : Arc N} (he : T.TreeEdge e)
    {p : Port N} (hp : p ∈ edgeBlockWord T G color v e) :
    T.Ancestor e.2 (portHome p) ∨
      (p.source = false ∧ p.edge.2 = v ∧ T.Ancestor e.2 p.edge.1) := by
  have hO := validContourOrder_signed hT color
  obtain ⟨ev, hev, hp⟩ := List.mem_flatMap.mp hp
  rcases (mem_edgeBlock_tree he).mp hev with rfl | ⟨b, -, hbv, hb, rfl⟩
  · exact Or.inl ((mem_subtreeWord hT hO _ _).mp hp).2
  · rw [expand, List.mem_singleton] at hp
    subst hp
    exact Or.inr ⟨rfl, hbv, hb⟩

end GraphMinor.LRPlanarity.ContourWord
