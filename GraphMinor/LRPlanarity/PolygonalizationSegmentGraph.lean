module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.LRPlanarity.PolygonalizationArrangement
import GraphMinor.LRPlanarity.PolygonalizationFinitePieces
import Mathlib.Topology.Algebra.Affine

/-!
# Subdividing straight segment graphs

Part IV, Section 7a of the planarity note splits the segment arrangement at
intersection points. Inserting one new vertex either adds an isolated point
or splits one edge into two. Both new edges are compact connected subsets of
the old straight segment and hence are straight segments themselves.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Topology Surface

private theorem line_is_segment {L : Set ℂ} {u v a b : ℂ}
    (hL : IsLineWithEnds L u v) (hsub : L ⊆ segment ℝ a b) :
    ∃ x y : ℂ, L = segment ℝ x y := by
  obtain ⟨f, hf, hr, _, _⟩ := hL.exists_arc
  apply compact_connected_subset_segment hL.isCompact _ ⟨u, hL.left_mem⟩ hsub
  rw [← hr]
  exact isPreconnected_range hf.1

/-- The vertex-insertion step in the segment arrangement of Part IV,
Section 7a, retaining a straight segment for every edge. -/
theorem segment_graph_add_point {V : Set ℂ} {E : Set (Set ℂ)} (h : IsGraph V E)
    (hstraight : ∀ e ∈ E, ∃ a b : ℂ, e = segment ℝ a b) (x : ℂ) :
    ∃ E', IsGraph (insert x V) E' ∧ gr (insert x V) E' = insert x (gr V E) ∧
      ∀ e ∈ E', ∃ a b : ℂ, e = segment ℝ a b := by
  classical
  by_cases hV : x ∈ V
  · refine ⟨E, by rwa [insert_eq_of_mem hV], ?_, hstraight⟩
    rw [insert_eq_of_mem hV, insert_eq_of_mem (.inl hV)]
  by_cases hE : ∃ e ∈ E, x ∈ e
  · obtain ⟨e, he, hx⟩ := hE
    obtain ⟨u, v, huv, hl, hi⟩ := h.edge e he
    have hu : u ∈ V := (hi.symm ▸ mem_insert u {v} : u ∈ e ∩ V).2
    have hv : v ∈ V := (hi.symm ▸ mem_insert_of_mem u rfl : v ∈ e ∩ V).2
    have hxu : x ≠ u := fun he' => hV (he' ▸ hu)
    have hxv : x ≠ v := fun he' => hV (he' ▸ hv)
    obtain ⟨L₁, L₂, h₁, h₂, hun, hin⟩ := hl.split hx hxu hxv
    have hs1 : L₁ ⊆ e := hun ▸ subset_union_left
    have hs2 : L₂ ⊆ e := hun ▸ subset_union_right
    have hof : ∀ f ∈ E, f ≠ e → x ∉ f := fun f hf hne hxf => hV (h.disj e he f hf hne.symm ⟨hx, hxf⟩)
    have hvL : v ∉ L₁ := fun hc => hxv (mem_singleton_iff.mp (hin ▸ (⟨hc, h₂.right_mem⟩ : v ∈ L₁ ∩ L₂))).symm
    have huL : u ∉ L₂ := fun hc => hxu (mem_singleton_iff.mp (hin ▸ (⟨h₁.left_mem, hc⟩ : u ∈ L₁ ∩ L₂))).symm
    refine ⟨insert L₁ (insert L₂ (E \ {e})), ⟨h.fin.insert x, ((h.fine.sdiff).insert _).insert _, ?_, ?_⟩, ?_, ?_⟩
    · rintro f (rfl | rfl | ⟨hf, hne⟩)
      · refine ⟨u, x, hxu.symm, h₁, ?_⟩
        ext y
        constructor
        · rintro ⟨hy, rfl | hy'⟩
          · simp
          · have : y ∈ e ∩ V := ⟨hs1 hy, hy'⟩
            rw [hi] at this
            rcases this with rfl | rfl
            · simp
            · exact absurd hy hvL
        · rintro (rfl | rfl)
          · exact ⟨h₁.left_mem, .inr hu⟩
          · exact ⟨h₁.right_mem, .inl rfl⟩
      · refine ⟨x, v, hxv, h₂, ?_⟩
        ext y
        constructor
        · rintro ⟨hy, rfl | hy'⟩
          · simp
          · have : y ∈ e ∩ V := ⟨hs2 hy, hy'⟩
            rw [hi] at this
            rcases this with rfl | rfl
            · exact absurd hy huL
            · simp
        · rintro (rfl | rfl)
          · exact ⟨h₂.left_mem, .inl rfl⟩
          · exact ⟨h₂.right_mem, .inr hv⟩
      · obtain ⟨a, b, hab, hl', hi'⟩ := h.edge f hf
        refine ⟨a, b, hab, hl', ?_⟩
        rw [inter_insert_of_notMem (hof f hf hne), hi']
    · have hL1 : ∀ g ∈ E \ {e}, L₁ ∩ g ⊆ insert x V := fun g hg y hy =>
        .inr (h.disj e he g hg.1 (Ne.symm hg.2) ⟨hs1 hy.1, hy.2⟩)
      have hL2 : ∀ g ∈ E \ {e}, L₂ ∩ g ⊆ insert x V := fun g hg y hy =>
        .inr (h.disj e he g hg.1 (Ne.symm hg.2) ⟨hs2 hy.1, hy.2⟩)
      have h12 : L₁ ∩ L₂ ⊆ insert x V := by
        rw [hin]
        exact singleton_subset_iff.mpr (mem_insert _ _)
      rintro f (rfl | rfl | hf) g (rfl | rfl | hg) hne
      · exact absurd rfl hne
      · exact h12
      · exact hL1 g hg
      · exact (inter_comm _ _).subset.trans h12
      · exact absurd rfl hne
      · exact hL2 g hg
      · exact (inter_comm _ _).subset.trans (hL1 f hf)
      · exact (inter_comm _ _).subset.trans (hL2 f hf)
      · exact (h.disj f hf.1 g hg.1 hne).trans (subset_insert _ _)
    · ext y
      simp only [gr, mem_union, mem_insert_iff, mem_sUnion, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ((rfl | hy) | ⟨f, (rfl | rfl | ⟨hf, -⟩), hy⟩)
        · exact .inl rfl
        · exact .inr (.inl hy)
        · exact .inr (.inr ⟨e, he, hs1 hy⟩)
        · exact .inr (.inr ⟨e, he, hs2 hy⟩)
        · exact .inr (.inr ⟨f, hf, hy⟩)
      · rintro (rfl | hy | ⟨f, hf, hy⟩)
        · exact .inl (.inl rfl)
        · exact .inl (.inr hy)
        · by_cases hfe : f = e
          · subst hfe
            rw [← hun] at hy
            rcases hy with hy | hy
            · exact .inr ⟨L₁, .inl rfl, hy⟩
            · exact .inr ⟨L₂, .inr (.inl rfl), hy⟩
          · exact .inr ⟨f, .inr (.inr ⟨hf, hfe⟩), hy⟩
    · rintro f (rfl | rfl | hf)
      · obtain ⟨a, b, heq⟩ := hstraight e he
        apply line_is_segment h₁
        rw [← heq]
        exact hs1
      · obtain ⟨a, b, heq⟩ := hstraight e he
        apply line_is_segment h₂
        rw [← heq]
        exact hs2
      · exact hstraight f hf.1
  · push Not at hE
    refine ⟨E, ⟨h.fin.insert x, h.fine, fun e he => ?_, fun e he f hf hne =>
      (h.disj e he f hf hne).trans (subset_insert _ _)⟩, ?_, hstraight⟩
    · obtain ⟨a, b, hab, hl', hi'⟩ := h.edge e he
      refine ⟨a, b, hab, hl', ?_⟩
      rw [inter_insert_of_notMem (hE e he), hi']
    · simp only [gr, insert_union]

/-- The segment-insertion step of Part IV, Section 7a. Split the new segment
at the first and last meetings with the existing graph, insert the uncovered
piece, and repeat over the finitely many remaining pieces. -/
theorem segment_graph_add_path {a : unitInterval → ℂ} (ha : IsArcMap a)
    {p q : ℂ} (hseg : range a ⊆ segment ℝ p q) (n : ℕ) :
    ∀ (V : Set ℂ) (E : Set (Set ℂ)) (F : Set (Set ℂ)), IsGraph V E →
      (∀ e ∈ E, ∃ x y : ℂ, e = segment ℝ x y) →
      a 0 ∈ gr V E → a 1 ∈ gr V E → F.Finite →
      F.ncard = n → (∀ J ∈ F, IsPreconnected J) → ⋃₀ F = range a \ gr V E →
      ∃ V' E', V ⊆ V' ∧ IsGraph V' E' ∧ gr V' E' = gr V E ∪ range a ∧
        ∀ e ∈ E', ∃ x y : ℂ, e = segment ℝ x y := by
  classical
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V E F h hstraight h0 h1 hF hn hJ hU
  by_cases hW : range a ⊆ gr V E
  · exact ⟨V, E, subset_rfl, h, by rw [union_eq_left.mpr hW], hstraight⟩
  obtain ⟨_, ⟨t0, rfl⟩, ht0⟩ := not_subset.mp hW
  have hcl : IsClosed (a ⁻¹' gr V E) := h.isClosed_gr.preimage ha.1
  have hc1 : IsCompact (a ⁻¹' gr V E ∩ Iic t0) := (hcl.inter isClosed_Iic).isCompact
  have hc2 : IsCompact (a ⁻¹' gr V E ∩ Ici t0) := (hcl.inter isClosed_Ici).isCompact
  obtain ⟨s, ⟨hs1, hs2⟩, hsg⟩ := hc1.exists_isGreatest ⟨0, h0, unitInterval.nonneg t0⟩
  obtain ⟨r, ⟨hr1, hr2⟩, hrl⟩ := hc2.exists_isLeast ⟨1, h1, unitInterval.le_one t0⟩
  have hst : s < t0 := lt_of_le_of_ne hs2 fun he => ht0 (he ▸ hs1)
  have htr : t0 < r := lt_of_le_of_ne hr2 fun he => ht0 (he ▸ hr1)
  have hsr : s < r := hst.trans htr
  have hsrR : (s : ℝ) < r := hsr
  set A : Set ℂ := a '' Icc s r with hAdef
  have hline : IsLineWithEnds A (a s) (a r) := by
    have := (IsArcMap.sub ha hsr.ne).isLineWithEnds
    rw [range_subArc a hsr.le, subArc_zero, subArc_one] at this
    exact this
  have hne : a s ≠ a r := fun he => hsr.ne (ha.2 he)
  have hAi : A ∩ gr V E = {a s, a r} := by
    ext y
    constructor
    · rintro ⟨⟨t, ⟨h3, h4⟩, rfl⟩, hy⟩
      rcases le_total t t0 with h5 | h5
      · have : t ≤ s := hsg ⟨hy, h5⟩
        exact .inl (congrArg a (le_antisymm this h3))
      · have : r ≤ t := hrl ⟨hy, h5⟩
        exact .inr (congrArg a (le_antisymm h4 this))
    · rintro (rfl | rfl)
      · exact ⟨⟨s, ⟨le_rfl, hsr.le⟩, rfl⟩, hs1⟩
      · exact ⟨⟨r, ⟨hsr.le, le_rfl⟩, rfl⟩, hr1⟩
  obtain ⟨E1, hG1, hg1, hu1⟩ := segment_graph_add_point h hstraight (a s)
  obtain ⟨E2, hG2, hg2, hu2⟩ := segment_graph_add_point hG1 hu1 (a r)
  have hgr : gr (insert (a r) (insert (a s) V)) E2 = gr V E := by
    rw [hg2, hg1, insert_eq_of_mem (show a s ∈ gr V E from hs1),
      insert_eq_of_mem (show a r ∈ gr V E from hr1)]
  obtain ⟨hG3, hg3⟩ := hG2.add_arc hne hline (.inr (.inl rfl)) (.inl rfl) (by rw [hgr, hAi])
  have hstraight3 : ∀ e ∈ insert A E2, ∃ x y : ℂ, e = segment ℝ x y := by
    rintro e (rfl | he)
    · exact line_is_segment hline ((image_subset_range a _).trans hseg)
    · exact hu2 e he
  rw [hgr] at hg3
  have hsame : ∀ J ∈ F, (J ∩ A).Nonempty → J ⊆ A := by
    rintro J hJF ⟨_, hy, ⟨t, ht, rfl⟩⟩ y' hy'
    have hJW : J ⊆ range a \ gr V E := hU ▸ subset_sUnion_of_mem hJF
    obtain ⟨t', rfl⟩ := (hJW hy').1
    have hemb : IsEmbedding a := (ha.1.isClosedEmbedding ha.2).isEmbedding
    have hpc : IsPreconnected (a ⁻¹' J) := by
      refine hemb.isInducing.isPreconnected_image.mp ?_
      rw [image_preimage_eq_inter_range, inter_eq_left.mpr fun z hz => (hJW hz).1]
      exact hJ J hJF
    have hord := hpc.ordConnected
    by_contra hcon
    have ht' : t' < s ∨ r < t' := by
      by_contra hc
      push Not at hc
      exact hcon ⟨t', ⟨hc.1, hc.2⟩, rfl⟩
    have hbad : ∀ w ∈ a ⁻¹' J, w ∉ a ⁻¹' gr V E := fun w hw => (hJW hw).2
    rcases ht' with h3 | h3
    · exact hbad s (hord.out hy' hy ⟨h3.le, ht.1⟩) hs1
    · exact hbad r (hord.out hy hy' ⟨ht.2, h3.le⟩) hr1
  let F' : Set (Set ℂ) := {J ∈ F | Disjoint J A}
  obtain ⟨J0, hJ0, hx0⟩ : ∃ J ∈ F, a t0 ∈ J := by
    have : a t0 ∈ ⋃₀ F := hU ▸ ⟨⟨t0, rfl⟩, ht0⟩
    exact this
  have hA0 : a t0 ∈ A := ⟨t0, ⟨hst.le, htr.le⟩, rfl⟩
  have hlt : F'.ncard < n := by
    rw [← hn]
    refine ncard_lt_ncard ?_ hF
    refine ⟨fun J hJ => hJ.1, fun hc => ?_⟩
    exact Set.disjoint_left.mp (hc hJ0).2 hx0 hA0
  obtain ⟨V', E', hVV, hG', hg', hno⟩ := ih _ hlt _ _ F' hG3 hstraight3 (by rw [hg3]; exact .inl h0) (by rw [hg3]; exact .inl h1)
    (hF.subset fun J hJ => hJ.1) rfl (fun J hJ' => hJ J hJ'.1) (by
      rw [hg3]
      ext y
      constructor
      · rintro ⟨J, ⟨hJF, hd⟩, hy⟩
        have : y ∈ range a \ gr V E := hU ▸ mem_sUnion_of_mem hy hJF
        exact ⟨this.1, fun hc => hc.elim this.2 (Set.disjoint_left.mp hd hy)⟩
      · rintro ⟨hy1, hy2⟩
        have hy3 : y ∈ ⋃₀ F := hU ▸ ⟨hy1, fun hc => hy2 (.inl hc)⟩
        obtain ⟨J, hJF, hyJ⟩ := hy3
        refine ⟨J, ⟨hJF, ?_⟩, hyJ⟩
        rw [Set.disjoint_iff_inter_eq_empty, ← not_nonempty_iff_eq_empty]
        intro hne'
        exact hy2 (.inr (hsame J hJF hne' hyJ)))
  refine ⟨V', E', (subset_insert _ _).trans ((subset_insert _ _).trans hVV), hG', ?_, hno⟩
  rw [hg', hg3, union_assoc, union_eq_right.mpr (image_subset_range a _)]

private theorem segment_graph_drawn_set {V : Set ℂ} {E : Set (Set ℂ)} (h : IsGraph V E)
    (hstraight : ∀ e ∈ E, ∃ a b : ℂ, e = segment ℝ a b) :
    ∃ pieces : Finset (ℂ × ℂ), gr V E = ⋃ p ∈ pieces, segment ℝ p.1 p.2 := by
  classical
  let : Fintype V := h.fin.fintype
  let : Fintype E := h.fine.fintype
  choose a b hab using (fun e : E => hstraight e.val e.property)
  let pieces := (Finset.univ.image (fun v : V => (v.val, v.val))) ∪
    (Finset.univ.image (fun e : E => (a e, b e)))
  refine ⟨pieces, ?_⟩
  ext x
  constructor
  · rintro (hx | ⟨e, he, hxe⟩)
    · apply mem_iUnion.mpr
      refine ⟨(x, x), mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_univ _, rfl⟩)
      · exact left_mem_segment _ _ _
    · apply mem_iUnion.mpr
      refine ⟨(a ⟨e, he⟩, b ⟨e, he⟩), mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩)
      · exact hab ⟨e, he⟩ ▸ hxe
  · intro hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    obtain ⟨hp, hxp⟩ := mem_iUnion.mp hp
    rcases Finset.mem_union.mp hp with hp | hp
    · obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hp
      have hx : x = v.val := by simpa only [segment_same, mem_singleton_iff] using hxp
      exact Or.inl (hx ▸ v.property)
    · obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hp
      exact Or.inr ⟨e.val, e.property, (hab e).symm ▸ hxp⟩

/-- Part IV, Section 7a: insert a whole straight segment into a finite
straight segment graph, splitting at its meetings with the graph. -/
theorem segment_graph_insert_segment {V : Set ℂ} {E : Set (Set ℂ)} (h : IsGraph V E)
    (hstraight : ∀ e ∈ E, ∃ x y : ℂ, e = segment ℝ x y) (a b : ℂ) :
    ∃ V' E', V ⊆ V' ∧ a ∈ V' ∧ b ∈ V' ∧ IsGraph V' E' ∧
      gr V' E' = gr V E ∪ segment ℝ a b ∧
      ∀ e ∈ E', ∃ x y : ℂ, e = segment ℝ x y := by
  classical
  by_cases hab : a = b
  · subst b
    obtain ⟨E', hG, hgr, hS⟩ := segment_graph_add_point h hstraight a
    refine ⟨insert a V, E', subset_insert _ _, Or.inl rfl, Or.inl rfl, hG, ?_, hS⟩
    rw [hgr, segment_same, union_singleton]
  · obtain ⟨E1, hG1, hg1, hS1⟩ := segment_graph_add_point h hstraight a
    obtain ⟨E2, hG2, hg2, hS2⟩ := segment_graph_add_point hG1 hS1 b
    obtain ⟨pieces, hpieces⟩ := segment_graph_drawn_set hG2 hS2
    let f : unitInterval → ℂ := fun t => AffineMap.lineMap a b (t : ℝ)
    have hf : IsArcMap f := ⟨AffineMap.lineMap_continuous.comp continuous_subtype_val,
      (AffineMap.lineMap_injective ℝ hab).comp Subtype.val_injective⟩
    have hzero : f 0 = a := AffineMap.lineMap_apply_zero _ _
    have hone : f 1 = b := AffineMap.lineMap_apply_one _ _
    have hrange : range f = segment ℝ a b := by
      rw [segment_eq_image_lineMap]
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨t, t.2, rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact ⟨⟨t, ht⟩, rfl⟩
    have hF : FinConn (range f \ gr (insert b (insert a V)) E2) := by
      rw [hrange, hpieces]
      exact finConn_segment_sdiff_segments a b pieces
    obtain ⟨F, hFfin, hFpre, hFU⟩ := hF
    obtain ⟨V', E', hVV, hG', hgr', hS'⟩ :=
      segment_graph_add_path hf (by rw [hrange]) F.ncard
        (insert b (insert a V)) E2 F hG2 hS2
        (by rw [hzero]; exact Or.inl (Or.inr (Or.inl rfl)))
        (by rw [hone]; exact Or.inl (Or.inl rfl)) hFfin rfl hFpre hFU
    refine ⟨V', E', (subset_insert a V).trans ((subset_insert b _).trans hVV),
      hVV (Or.inr (Or.inl rfl)), hVV (Or.inl rfl), hG', ?_, hS'⟩
    rw [hgr', hg2, hg1, hrange]
    have haU : a ∈ gr V E ∪ segment ℝ a b := Or.inr (left_mem_segment ℝ a b)
    have hbU : b ∈ gr V E ∪ segment ℝ a b := Or.inr (right_mem_segment ℝ a b)
    simp only [insert_union]
    rw [insert_eq_of_mem haU, insert_eq_of_mem hbU]

/-- Part IV, Section 7a: the union of finitely many straight segments is a
finite embedded graph with straight edges. Insert the segments successively,
splitting at intersection and overlap ends. -/
theorem exists_straight_segment_arrangement (pieces : Finset (ℂ × ℂ)) :
    ∃ (V : Set ℂ) (E : Set (Set ℂ)), IsGraph V E ∧
      gr V E = ⋃ p ∈ pieces, segment ℝ p.1 p.2 ∧
      (∀ p ∈ pieces, p.1 ∈ V ∧ p.2 ∈ V) ∧
      ∀ e ∈ E, ∃ a b : ℂ, e = segment ℝ a b := by
  classical
  induction pieces using Finset.induction_on with
  | empty =>
    refine ⟨∅, ∅, isGraph_empty, ?_, ?_, ?_⟩
    · simp [gr]
    · intro p hp
      exact (Finset.notMem_empty p hp).elim
    · intro e he
      exact he.elim
  | @insert p pieces hp ih =>
    obtain ⟨V, E, hG, hgr, hends, hS⟩ := ih
    obtain ⟨V', E', hVV, ha, hb, hG', hgr', hS'⟩ := segment_graph_insert_segment hG hS p.1 p.2
    refine ⟨V', E', hG', ?_, ?_, hS'⟩
    · rw [hgr', hgr, Finset.set_biUnion_insert, union_comm]
    · intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact ⟨ha, hb⟩
      · exact ⟨hVV (hends q hq).1, hVV (hends q hq).2⟩

end GraphMinor.LRPlanarity
