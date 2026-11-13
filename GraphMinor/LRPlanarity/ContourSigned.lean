module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.ContourTree
import GraphMinor.LRPlanarity.ContourWord
import GraphMinor.LRPlanarity.ContourFork
import GraphMinor.LRPlanarity.ContourSignedOrder
import GraphMinor.LRPlanarity.ForkOrder

/-!
# The signed contour is nonalternating

This file proves `SignedContourStatement`, following Part IV, Sections 2 to 4 of
`docs/planarity/planarity_test.tex`. Validity of the signed order is `validContourOrder_signed`,
and the port-word property holds for every valid order (`isPortWord`). The work is
nonalternation, Section 4.

Take distinct back edges `b = (x₁, u₁)` and `c = (x₂, u₂)`.

* If the two port pairs are separated by a contiguous subword, that is, both ports of one edge
  lie in it and neither port of the other does, they do not alternate
  (`not_alternating_of_infix`). This covers the cases where the fundamental tree paths share no
  edge: the subword is the contour of a head, or the block `L_e W(w) R_e` of the first edge of a
  path.
* If the paths share an edge and `u₂` is strictly above `u₁`, the four-port comparison
  (`not_alternating_iff`) reduces nonalternation to Lemma (A) (`not_alternating_deeper`).
* If `u₁ = u₂` and the paths share their first edge `(u, w)`, then for equal colors both target
  ports lie in one list ordered by decreasing source rank, and the pairs are nested
  (`not_alternating_same_side`). For different colors the pairs are disjoint by Lemma (B)
  (`not_alternating_opposite`).

The source fork `v` of two back edges is the deepest common ancestor of their sources. Its two
outgoing edges toward the sources are distinct, since otherwise their common end would be a
deeper common ancestor (`exists_fork`).
-/

public section

namespace GraphMinor.LRPlanarity.ContourWord

open SearchTree ForkOrder

variable {N : ℕ} {T : Forest N} {G : SimpleGraph (Fin N)} {color : Coloring N}

theorem alternatingIndices_comm {a b c d : ℕ} :
    AlternatingIndices a b c d ↔ AlternatingIndices c d a b := by
  unfold AlternatingIndices
  omega

/-- Two port pairs separated by a contiguous subword do not alternate. "In all cases one pair
is in a contiguous subword that contains neither port of the other, which excludes alternation." -/
theorem not_alternating_of_infix {W S : List (Port N)} (hnd : W.Nodup) (hS : S <:+: W)
    {x y p q : Port N} (hx : x ∈ S) (hy : y ∈ S) (hp : p ∈ W) (hq : q ∈ W) (hpS : p ∉ S)
    (hqS : q ∉ S) :
    ¬ AlternatingIndices (W.idxOf p) (W.idxOf q) (W.idxOf x) (W.idxOf y) ∧
      ¬ AlternatingIndices (W.idxOf x) (W.idxOf y) (W.idxOf p) (W.idxOf q) := by
  obtain ⟨off, hin, hout⟩ := idxOf_of_infix hnd hS
  have h₁ := hin x hx
  have h₂ := hin y hy
  have h₃ := List.idxOf_lt_length_of_mem hx
  have h₄ := List.idxOf_lt_length_of_mem hy
  have h₅ := hout p hp hpS
  have h₆ := hout q hq hqS
  unfold AlternatingIndices
  omega

/-- The ports of a pair that is not a back edge are absent from the word, so they cannot
alternate with anything. -/
theorem not_alternating_of_not_mem {W : List (Port N)} {p q x y : Port N} (hp : p ∉ W)
    (hq : q ∉ W) :
    ¬ AlternatingIndices (W.idxOf p) (W.idxOf q) (W.idxOf x) (W.idxOf y) := by
  rw [List.idxOf_eq_length hp, List.idxOf_eq_length hq]
  have := List.idxOf_le_length (l := W) (a := x)
  have := List.idxOf_le_length (l := W) (a := y)
  unfold AlternatingIndices
  omega

/-- Part IV, Section 2: "At the lowest common ancestor v of two sources, the order of their
source ports is the order of their distinct outgoing fork edges at v. If a source is v itself,
we use the corresponding back edge as that outgoing fork edge." Below a common ancestor `w` of the
two sources, and above `w` for both heads, such a fork exists. -/
theorem exists_fork (hT : T.IsDFS G) {b c : Arc N} (hbc : b ≠ c) (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) {w : Fin N} (hwb : T.Ancestor w b.1) (hwc : T.Ancestor w c.1)
    (hbw : T.depth b.2 < T.depth w) (hcw : T.depth c.2 < T.depth w) :
    ∃ v e f, T.Outgoing G v e ∧ T.Outgoing G v f ∧ e ≠ f ∧ b ∈ T.returns G e ∧
      c ∈ T.returns G f := by
  classical
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter (fun a => T.Ancestor a b.1 ∧ T.Ancestor a c.1)) T.depth
    ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwb, hwc⟩⟩
  obtain ⟨-, hvb, hvc⟩ := Finset.mem_filter.mp hv
  have hwv := hmax w (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwb, hwc⟩)
  obtain ⟨e, he, hbe⟩ := exists_outgoing_returns hb hvb (by omega)
  obtain ⟨f, hf, hcf⟩ := exists_outgoing_returns hc hvc (by omega)
  refine ⟨v, e, f, he, hf, ?_, hbe, hcf⟩
  rintro rfl
  obtain ⟨-, ⟨heb, rfl⟩ | ⟨ht, hyb, -⟩⟩ := hbe
  · obtain ⟨-, ⟨-, rfl⟩ | ⟨ht, -, -⟩⟩ := hcf
    · exact hbc rfl
    · exact not_treeEdge_of_backEdge hT heb ht
  · obtain ⟨-, ⟨hec, rfl⟩ | ⟨-, hyc, -⟩⟩ := hcf
    · exact not_treeEdge_of_backEdge hT hec ht
    · have := hmax _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyb, hyc⟩)
      rw [depth_of_parent hT ht, he.1] at this
      omega

/-- Part IV, Section 4, paths sharing an edge with `h(u1)>h(u2)`: "Both possibilities
contradict Lemma (A)." -/
theorem not_alternating_deeper (hT : T.IsDFS G) (hFC : T.ForkConstraints G color)
    (hWA : T.WeakAlignment G color) {b c : Arc N} (hbc : b ≠ c) (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) {w : Fin N} (hw : T.parent w = some b.2) (hwb : T.Ancestor w b.1)
    (hwc : T.Ancestor w c.1) (hd : T.depth c.2 < T.depth b.2) :
    ¬ AlternatingIndices ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, false⟩) := by
  have hO := validContourOrder_signed hT color
  have hdw := depth_of_parent hT hw
  obtain ⟨v, e, f, he, hf, hef, hbe, hcf⟩ := exists_fork hT hbc hb hc hwb hwc (by omega)
    (by omega)
  refine (not_alternating_iff hT hO hb hc hw hwb hwc hd).mpr ?_
  rw [contourColor_signed hT color hb, source_lt_iff hT hO he hf hef hbe hcf,
    outEvent_lt_iff_signed hT he hf hef]
  exact (forkOrderA_proved N G T color hT hFC hWA v e f b c he hf hef hbe hcf hd).symm

/-- In the signed contour, a target port of color `L` comes before every source port below the
child block, and one of color `R` comes after. -/
theorem target_source_order (hT : T.IsDFS G) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) {w : Fin N} (hw : T.parent w = some b.2) (hwb : T.Ancestor w b.1)
    (hwc : T.Ancestor w c.1) :
    (color b = .left → (contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩ <
        (contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩) ∧
      (color b = .right → (contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩ <
        (contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩) := by
  have hO := validContourOrder_signed hT color
  have hL : color b = .left ↔ (signedContourOrder T G color b.2).idxOf (.port ⟨b, false⟩) <
      (signedContourOrder T G color b.2).idxOf (.child w) := by
    rw [← contourColor_signed hT color hb]
    exact contourColor_eq_left_iff hT hw hwb
  have htO : ContourEvent.port ⟨b, false⟩ ∈ signedContourOrder T G color b.2 :=
    (mem_order_port hO).mpr ⟨hb, portHome_target b⟩
  have hwO : ContourEvent.child w ∈ signedContourOrder T G color b.2 := (mem_order_child hO).mpr hw
  have hs : (⟨c, true⟩ : Port N) ∈ expand (subtreeWord T (signedContourOrder T G color))
      (.child w) := (mem_subtreeWord hT hO w _).mpr ⟨hc, by rw [portHome_source]; exact hwc⟩
  have ht : (⟨b, false⟩ : Port N) ∈ expand (subtreeWord T (signedContourOrder T G color))
      (.port ⟨b, false⟩) := List.mem_singleton_self _
  refine ⟨fun h => idxOf_lt_of_order hT hO htO hwO (hL.mp h) ht hs, fun h => ?_⟩
  have hnot : ¬ (signedContourOrder T G color b.2).idxOf (.port ⟨b, false⟩) <
      (signedContourOrder T G color b.2).idxOf (.child w) := by
    rw [← hL, h]
    simp
  rcases idxOf_lt_or_gt htO (by simp : ContourEvent.port ⟨b, false⟩ ≠ .child w) with h' | h'
  · exact absurd h' hnot
  · exact idxOf_lt_of_order hT hO hwO htO h' hs ht

/-- A target list of the block of `(u, w)` is a contiguous part of the local order at `u`. -/
theorem targetList_infix {u w : Fin N} (hw : T.parent w = some u)
    (side : Color) : targetList T G color u w side <:+: signedContourOrder T G color u := by
  refine List.IsInfix.trans ?_ (edgeBlock_infix (e := (u, w)) ⟨rfl, Or.inl hw⟩)
  have hblk : edgeBlock T G color u (u, w) = targetList T G color u w .left ++
      [.child w] ++ targetList T G color u w .right := edgeBlock_tree (e := (u, w)) hw
  rw [hblk]
  cases side
  · exact ⟨[], [.child w] ++ targetList T G color u w .right, by simp⟩
  · exact ⟨targetList T G color u w .left ++ [.child w], [], by simp⟩

/-- Part IV, Section 4, equal heads and equal colors: "If their colors agree, their target ports are
in one list on the same side, ordered in reverse order of their source ports. Their four ports
are therefore nested, not alternating." -/
theorem not_alternating_same_side (hT : T.IsDFS G) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (hbc : b.2 = c.2) {w : Fin N} (hw : T.parent w = some b.2)
    (hwb : T.Ancestor w b.1) (hwc : T.Ancestor w c.1) (hcol : color b = color c)
    (hlt : (signedContourOrder T G color b.2).idxOf (.port ⟨b, false⟩) <
      (signedContourOrder T G color b.2).idxOf (.port ⟨c, false⟩)) :
    ¬ AlternatingIndices ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, false⟩) := by
  have hO := validContourOrder_signed hT color
  have hw' : T.parent w = some c.2 := hbc ▸ hw
  have htbL : ContourEvent.port ⟨b, false⟩ ∈ targetList T G color b.2 w (color b) :=
    port_mem_targetList.mpr ⟨hb, rfl, hwb, rfl⟩
  have htcL : ContourEvent.port ⟨c, false⟩ ∈ targetList T G color b.2 w (color b) :=
    port_mem_targetList.mpr ⟨hc, hbc.symm, hwc, hcol.symm⟩
  -- The target ports come in the order of the target list.
  have htt := idxOf_lt_of_order hT hO ((mem_order_port hO).mpr ⟨hb, portHome_target b⟩)
    ((mem_order_port hO).mpr ⟨hc, by rw [portHome_target]; exact hbc.symm⟩) hlt
    (List.mem_singleton_self _) (List.mem_singleton_self _)
  -- Their source ports come in the reverse order.
  obtain ⟨off, hin, -⟩ := idxOf_of_infix (hO b.2).1 (targetList_infix hw (color b))
  rw [hin _ htbL, hin _ htcL, Nat.add_lt_add_iff_left] at hlt
  have hrank := rank_le_of_targetList htbL htcL hlt
  have hbc' : b ≠ c := by
    rintro rfl
    exact lt_irrefl _ hlt
  have hsrc : ¬ (contourWord T (signedContourOrder T G color)).idxOf (⟨b, true⟩ : Port N) <
      (contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩ := fun h => by
    have := (rank_lt_iff hT color hb hc).mpr h
    omega
  have hne : (contourWord T (signedContourOrder T G color)).idxOf (⟨b, true⟩ : Port N) ≠
      (contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩ := fun h => by
    have := (List.idxOf_inj ((mem_contourWord hT hO _).mpr hb)).mp h
    simp only [Port.mk.injEq, and_true] at this
    exact hbc' this
  have h₁ := target_source_order (color := color) hT hb hb hw hwb hwb
  have h₂ := target_source_order (color := color) hT hb hc hw hwb hwc
  have h₃ := target_source_order (color := color) hT hc hb hw' hwc hwb
  have h₄ := target_source_order (color := color) hT hc hc hw' hwc hwc
  rw [← hcol] at h₃ h₄
  unfold AlternatingIndices
  cases hcb : color b
  · have := h₁.1 hcb
    have := h₂.1 hcb
    have := h₃.1 hcb
    have := h₄.1 hcb
    omega
  · have := h₁.2 hcb
    have := h₂.2 hcb
    have := h₃.2 hcb
    have := h₄.2 hcb
    omega

/-- Part IV, Section 4, equal heads and different colors: "the target of b1 precedes the shared
child block and the target of b2 follows it. Alternation would require the source of b2 to come
before the source of b1, contrary to Lemma (B)." -/
theorem not_alternating_opposite (hT : T.IsDFS G) (hFC : T.ForkConstraints G color)
    (hWA : T.WeakAlignment G color) {b c : Arc N} (hb : T.BackEdge G b) (hc : T.BackEdge G c)
    (hbc : b.2 = c.2) {w : Fin N} (hw : T.parent w = some b.2) (hwb : T.Ancestor w b.1)
    (hwc : T.Ancestor w c.1) (hbL : color b = .left) (hcR : color c = .right) :
    ¬ AlternatingIndices ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, false⟩) := by
  have hO := validContourOrder_signed hT color
  have hw' : T.parent w = some c.2 := hbc ▸ hw
  have hdw := depth_of_parent hT hw
  have hbc' : b ≠ c := by
    rintro rfl
    rw [hbL] at hcR
    cases hcR
  obtain ⟨v, e, f, he, hf, hef, hbe, hcf⟩ := exists_fork hT hbc' hb hc hwb hwc (by omega)
    (by rw [← hbc]; omega)
  have hidx := forkOrderB_proved N G T color hT hFC hWA v e f b c he hf hef hbe hcf hbc hbL hcR
  have hsrc := (source_lt_iff hT hO he hf hef hbe hcf).mpr
    ((outEvent_lt_iff_signed hT he hf hef).mpr hidx)
  have h₁ := (target_source_order (color := color) hT hb hb hw hwb hwb).1 hbL
  have h₂ := (target_source_order (color := color) hT hc hc hw' hwc hwc).2 hcR
  unfold AlternatingIndices
  omega

/-- Part IV, Section 4, heads strictly comparable. -/
theorem not_alternating_strict (hT : T.IsDFS G) (hFC : T.ForkConstraints G color)
    (hWA : T.WeakAlignment G color) {b c : Arc N} (hbc : b ≠ c) (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (hcb : T.Ancestor c.2 b.2) (hne : c.2 ≠ b.2) :
    ¬ AlternatingIndices ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, false⟩) := by
  have hO := validContourOrder_signed hT color
  have hnd := nodup_contourWord hT hO
  have hpW : (⟨c, true⟩ : Port N) ∈ contourWord T (signedContourOrder T G color) :=
    (mem_contourWord hT hO _).mpr hc
  have hqW : (⟨c, false⟩ : Port N) ∈ contourWord T (signedContourOrder T G color) :=
    (mem_contourWord hT hO _).mpr hc
  obtain ⟨w, hw, hwb⟩ := exists_child_of_ancestor (ancestor_of_backEdge hb) (ne_of_backEdge hb)
  have hd := depth_lt_of_ancestor hT hcb hne
  have hc2 : ¬ T.Ancestor b.2 c.2 := fun h => hne (ancestor_antisymm hT hcb h)
  by_cases h₁ : T.Ancestor w c.1
  · -- "Now suppose that their paths share an edge."
    exact not_alternating_deeper hT hFC hWA hbc hb hc hw hwb h₁ hd
  by_cases h₂ : T.Ancestor b.2 c.1
  · -- The sources diverge at the head of `b`, or `c` starts there.
    have he : T.Outgoing G b.2 (b.2, w) := ⟨rfl, Or.inl hw⟩
    have hx : (⟨b, true⟩ : Port N) ∈ edgeBlockWord T G color b.2 (b.2, w) :=
      List.mem_flatMap.mpr ⟨.child w, (mem_edgeBlock_tree (e := (b.2, w)) hw).mpr (Or.inl rfl),
        (mem_subtreeWord hT hO w _).mpr ⟨hb, by rw [portHome_source]; exact hwb⟩⟩
    have hy : (⟨b, false⟩ : Port N) ∈ edgeBlockWord T G color b.2 (b.2, w) :=
      List.mem_flatMap.mpr ⟨.port ⟨b, false⟩,
        (mem_edgeBlock_tree (e := (b.2, w)) hw).mpr (Or.inr ⟨b, hb, rfl, hwb, rfl⟩),
        List.mem_singleton_self _⟩
    have hp : (⟨c, true⟩ : Port N) ∉ edgeBlockWord T G color b.2 (b.2, w) := by
      intro h
      rcases mem_edgeBlockWord hT (e := (b.2, w)) hw h with h | ⟨h, -⟩
      · rw [portHome_source] at h
        exact h₁ h
      · cases h
    have hq : (⟨c, false⟩ : Port N) ∉ edgeBlockWord T G color b.2 (b.2, w) := by
      intro h
      rcases mem_edgeBlockWord hT (e := (b.2, w)) hw h with h | ⟨-, h, -⟩
      · rw [portHome_target] at h
        exact hc2 (ancestor_trans (ancestor_of_parent hw) h)
      · exact hne h
    exact (not_alternating_of_infix hnd (edgeBlockWord_infix hT he) hx hy hpW hqW hp hq).2
  · -- The source of `c` lies outside the subtree of the head of `b`.
    have hx : (⟨b, true⟩ : Port N) ∈ subtreeWord T (signedContourOrder T G color) b.2 :=
      (mem_subtreeWord hT hO _ _).mpr ⟨hb, by rw [portHome_source]; exact ancestor_of_backEdge hb⟩
    have hy : (⟨b, false⟩ : Port N) ∈ subtreeWord T (signedContourOrder T G color) b.2 :=
      (mem_subtreeWord hT hO _ _).mpr ⟨hb, by rw [portHome_target]; exact ancestor_refl _⟩
    have hp : (⟨c, true⟩ : Port N) ∉ subtreeWord T (signedContourOrder T G color) b.2 := by
      rw [mem_subtreeWord hT hO, portHome_source]
      exact fun h => h₂ h.2
    have hq : (⟨c, false⟩ : Port N) ∉ subtreeWord T (signedContourOrder T G color) b.2 := by
      rw [mem_subtreeWord hT hO, portHome_target]
      exact fun h => hc2 h.2
    exact (not_alternating_of_infix hnd (subtreeWord_infix hT hO _) hx hy hpW hqW hp hq).2

/-- Part IV, Section 4, equal heads: "If u1=u2 and the sources diverge immediately, the pairs
lie in disjoint outgoing child blocks." Otherwise the paths share their first edge. -/
theorem not_alternating_same_head (hT : T.IsDFS G) (hFC : T.ForkConstraints G color)
    (hWA : T.WeakAlignment G color) {b c : Arc N} (hbc : b ≠ c) (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (heq : b.2 = c.2) :
    ¬ AlternatingIndices ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, false⟩) := by
  have hO := validContourOrder_signed hT color
  have hnd := nodup_contourWord hT hO
  obtain ⟨w, hw, hwb⟩ := exists_child_of_ancestor (ancestor_of_backEdge hb) (ne_of_backEdge hb)
  by_cases hwc : T.Ancestor w c.1
  · have hw' : T.parent w = some c.2 := heq ▸ hw
    by_cases hcol : color b = color c
    · have htb : ContourEvent.port ⟨b, false⟩ ∈ signedContourOrder T G color b.2 :=
        (mem_order_port hO).mpr ⟨hb, portHome_target b⟩
      rcases idxOf_lt_or_gt htb (by simpa using hbc) (a' := .port ⟨c, false⟩) with h | h
      · exact not_alternating_same_side hT hb hc heq hw hwb hwc hcol h
      · rw [alternatingIndices_comm]
        rw [heq] at h
        exact not_alternating_same_side hT hc hb heq.symm hw' hwc hwb hcol.symm h
    · cases hbL : color b <;> cases hcR : color c <;> rw [hbL, hcR] at hcol
      · exact absurd rfl hcol
      · exact not_alternating_opposite hT hFC hWA hb hc heq hw hwb hwc hbL hcR
      · rw [alternatingIndices_comm]
        exact not_alternating_opposite hT hFC hWA hc hb heq.symm hw' hwc hwb hcR hbL
      · exact absurd rfl hcol
  · -- The sources diverge immediately: `c` is outside the block of `(b.2, w)`.
    have he : T.Outgoing G b.2 (b.2, w) := ⟨rfl, Or.inl hw⟩
    have hpW : (⟨c, true⟩ : Port N) ∈ contourWord T (signedContourOrder T G color) :=
      (mem_contourWord hT hO _).mpr hc
    have hqW : (⟨c, false⟩ : Port N) ∈ contourWord T (signedContourOrder T G color) :=
      (mem_contourWord hT hO _).mpr hc
    have hx : (⟨b, true⟩ : Port N) ∈ edgeBlockWord T G color b.2 (b.2, w) :=
      List.mem_flatMap.mpr ⟨.child w, (mem_edgeBlock_tree (e := (b.2, w)) hw).mpr (Or.inl rfl),
        (mem_subtreeWord hT hO w _).mpr ⟨hb, by rw [portHome_source]; exact hwb⟩⟩
    have hy : (⟨b, false⟩ : Port N) ∈ edgeBlockWord T G color b.2 (b.2, w) :=
      List.mem_flatMap.mpr ⟨.port ⟨b, false⟩,
        (mem_edgeBlock_tree (e := (b.2, w)) hw).mpr (Or.inr ⟨b, hb, rfl, hwb, rfl⟩),
        List.mem_singleton_self _⟩
    have hp : (⟨c, true⟩ : Port N) ∉ edgeBlockWord T G color b.2 (b.2, w) := by
      intro h
      rcases mem_edgeBlockWord hT (e := (b.2, w)) hw h with h | ⟨h, -⟩
      · rw [portHome_source] at h
        exact hwc h
      · cases h
    have hq : (⟨c, false⟩ : Port N) ∉ edgeBlockWord T G color b.2 (b.2, w) := by
      intro h
      rcases mem_edgeBlockWord hT (e := (b.2, w)) hw h with h | ⟨-, -, h⟩
      · rw [portHome_target, ← heq] at h
        have := depth_le_of_ancestor hT h
        rw [depth_of_parent hT hw] at this
        omega
      · exact hwc h
    exact (not_alternating_of_infix hnd (edgeBlockWord_infix hT he) hx hy hpW hqW hp hq).2

/-- Part IV, Section 4, incomparable heads: "If the heads are incomparable in the rooted tree,
both pairs occur in disjoint subtree words." -/
theorem not_alternating_incomparable (hT : T.IsDFS G) {b c : Arc N} (hb : T.BackEdge G b)
    (hc : T.BackEdge G c) (h₁ : ¬ T.Ancestor c.2 b.2) (h₂ : ¬ T.Ancestor b.2 c.2) :
    ¬ AlternatingIndices ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨b, false⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, true⟩)
      ((contourWord T (signedContourOrder T G color)).idxOf ⟨c, false⟩) := by
  have hO := validContourOrder_signed hT color
  have hx : (⟨c, true⟩ : Port N) ∈ subtreeWord T (signedContourOrder T G color) c.2 :=
    (mem_subtreeWord hT hO _ _).mpr ⟨hc, by rw [portHome_source]; exact ancestor_of_backEdge hc⟩
  have hy : (⟨c, false⟩ : Port N) ∈ subtreeWord T (signedContourOrder T G color) c.2 :=
    (mem_subtreeWord hT hO _ _).mpr ⟨hc, by rw [portHome_target]; exact ancestor_refl _⟩
  have hp : (⟨b, true⟩ : Port N) ∉ subtreeWord T (signedContourOrder T G color) c.2 := by
    rw [mem_subtreeWord hT hO, portHome_source]
    intro h
    rcases ancestor_total h.2 (ancestor_of_backEdge hb) with h' | h'
    · exact h₁ h'
    · exact h₂ h'
  have hq : (⟨b, false⟩ : Port N) ∉ subtreeWord T (signedContourOrder T G color) c.2 := by
    rw [mem_subtreeWord hT hO, portHome_target]
    exact fun h => h₁ h.2
  exact (not_alternating_of_infix (nodup_contourWord hT hO) (subtreeWord_infix hT hO _) hx hy
    ((mem_contourWord hT hO _).mpr hb) ((mem_contourWord hT hO _).mpr hb) hp hq).1

/-- Part IV, Section 4: "No two back-edge port pairs alternate in W". -/
theorem nonalternating_signed (hT : T.IsDFS G) (hFC : T.ForkConstraints G color)
    (hWA : T.WeakAlignment G color) :
    Nonalternating (contourWord T (signedContourOrder T G color)) := by
  have hO := validContourOrder_signed hT color
  intro b c hbc
  by_cases hb : T.BackEdge G b
  swap
  · exact not_alternating_of_not_mem (fun h => hb ((mem_contourWord hT hO _).mp h))
      (fun h => hb ((mem_contourWord hT hO _).mp h))
  by_cases hc : T.BackEdge G c
  swap
  · rw [alternatingIndices_comm]
    exact not_alternating_of_not_mem (fun h => hc ((mem_contourWord hT hO _).mp h))
      (fun h => hc ((mem_contourWord hT hO _).mp h))
  by_cases h₁ : T.Ancestor c.2 b.2
  · by_cases h₂ : c.2 = b.2
    · exact not_alternating_same_head hT hFC hWA hbc hb hc h₂.symm
    · exact not_alternating_strict hT hFC hWA hbc hb hc h₁ h₂
  · by_cases h₃ : T.Ancestor b.2 c.2
    · rw [alternatingIndices_comm]
      exact not_alternating_strict hT hFC hWA (Ne.symm hbc) hc hb h₃
        (fun h => h₁ (h ▸ ancestor_refl _))
    · exact not_alternating_incomparable hT hb hc h₁ h₃

end GraphMinor.LRPlanarity.ContourWord

namespace GraphMinor.LRPlanarity

open ContourWord

/-- Part IV, Sections 2 to 4: the signed contour of an aligned fork coloring is a valid
contour, its word holds each port of each back edge once, and "No two back-edge port pairs
alternate in W". -/
theorem signedContour_proved : SignedContourStatement := by
  intro N G T color hT hFC hWA
  have hO := validContourOrder_signed hT color
  exact ⟨hO, isPortWord hT hO, nonalternating_signed hT hFC hWA⟩

end GraphMinor.LRPlanarity
