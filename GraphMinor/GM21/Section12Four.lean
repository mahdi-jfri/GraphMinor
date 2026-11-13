module

public import GraphMinor.GM21.Section12FourRun
public import GraphMinor.GM21.Section12ThreeStep

/-!
# Graph Minors XXI, (12.4)

"For every integer $p \ge 0$ there exists $p' \ge 0$ such that every graph with a vital
$p$-linkage is a $p'$-chain."

The paper sketches a proof with a linked path-decomposition. We follow the sketch with the linked
tree-decomposition of (11.2) used in (12.3), and with the corrections to the converse of (12.1) and
to the proof of (12.4) in `corrections/GM21.md`:

1. Choose a good tree-decomposition `(T, W)` (`IsGoodDecomp`) with as few bad vertices as possible,
   and keep each edge of `G` in one bag. Claim (1) holds for the bad vertices
   (`claim_12_4_one`), so every path of `T` has at most `n` bad vertices
   (`ncard_inter_path_le`), and so there are at most `3 · 2 ^ n` bad vertices
   (`ncard_le_of_paths`).
2. Let `Z` be the union of the bags at bad vertices. The good vertices fall into runs between bad
   vertices, and each run gives a `(w + 1)`-chain of `G \ Z` (`IsRun.isChain`). These chains are
   disjoint and cover `G \ Z`, and there are at most `3 · |N|` of them, so `G \ Z` is a chain
   (`isChain_of_good`). Adding back `Z` gives the bound.

A graph with no edges at all is handled on its own (`isChain_of_edgeSet_empty`): it is a chain of its
one-vertex paths.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Graphs with no edges -/

/-- A graph with a vital `p`-linkage and no edges is a `p`-chain: its vertices are the terminals of
the linkage, and the one-vertex paths are the only set of `|V(G)|` disjoint paths between `V(G)`
and `V(G)`. -/
theorem isChain_of_edgeSet_empty {G L : Hypergraph α β} {p : ℕ} (hL : IsVitalPLinkage G L p)
    (hE : G.edgeSet = ∅) : IsChain G p := by
  obtain ⟨⟨hLk, hLV, -⟩, -, hterm⟩ := hL
  have hLE : L.edgeSet = ∅ := subset_empty_iff.1 (hE ▸ hLk.1.edgeSet_subset)
  have hLG : L = G := GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hLk.1 le_rfl hLV (hLE.trans hE.symm)
  subst hLG
  have hpat := linkagePattern_eq_of_edgeSet_empty hLk hLE
  -- Every vertex is a terminal.
  have hVp : L.vertexSet.ncard ≤ p := by
    have hsub : L.vertexSet ⊆ terminals L := by
      intro v hv
      refine ⟨hv, ?_⟩
      have hinc : incidentEdges L v = ∅ := eq_empty_of_forall_notMem fun e he ↦ by
        have h := he.1
        rw [hLE] at h
        exact h
      unfold vertexDegree
      rw [hinc]
      simp
    exact (ncard_le_ncard hsub (L.vertexSet_finite.subset fun _ h ↦ h.1)).trans hterm
  refine ⟨L.vertexSet, L.vertexSet, subset_rfl, subset_rfl, rfl, hVp, L,
    ⟨hLk, ?_, ?_⟩, fun M' hM' ↦ ?_, rfl⟩
  · rw [hpat, ncard_image_of_injective _ singleton_injective]
  · rw [hpat]
    rintro P ⟨v, hv, rfl⟩
    exact ⟨v, hv, v, hv, (pair_eq_singleton v).symm⟩
  · have hM'E : M'.edgeSet = ∅ := subset_empty_iff.1 (hLE ▸ hM'.1.1.edgeSet_subset)
    obtain ⟨hM'V, -⟩ := vertexSet_eq_of_edgeSet_empty hM'.1 hM'E hM'.2.1 hM'.2.2 rfl
      L.vertexSet_finite
    exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hM'.1.1 le_rfl hM'V (hM'E.trans hLE.symm)

/-! ## The runs of a decomposition -/

section Runs

variable {κ : Type*} [Fintype κ] {T : SimpleGraph κ} {G : Hypergraph α β}
  {W : κ → Hypergraph α β} {N : Set κ}

/-- The vertices joined to `t` by a path of `T` with no vertex in `N`. -/
def goodReach (T : SimpleGraph κ) (N : Set κ) (t : κ) : Set κ :=
  {z | ∀ x, Thomas.OnTreePath T t z x → x ∉ N}

variable (hT : T.IsTree)

include hT

/-- For a vertex `z` of a run, `goodReach z` is the set of inner vertices of the run. -/
theorem IsRun.goodReach_eq {s : ℕ → κ} {m : ℕ} (hr : IsRun T N s m) {z : κ}
    (hz : z ∈ runSet s m) : goodReach T N z = runSet s m := by
  ext x
  constructor
  · intro hx
    by_contra hxI
    rcases hr.exit hT hz hxI with h | h
    · exact hx _ h.onTreePath_right hr.first
    · exact hx _ h.onTreePath_right hr.last
  · intro hx y hy
    exact hr.notMem_of_mem (hr.mem_of_onTreePath hT hz hx hy)

/-- **The run around a good vertex.** If every vertex outside `N` is good, then every vertex
`t ∉ N` is an inner vertex of a run: from `t`, go in each of its two directions to the first vertex
in `N` (`exists_first_bad`). -/
theorem exists_run (hgood : ∀ z ∉ N, GoodAt T W z) {t : κ} (ht : t ∉ N) :
    ∃ (s : ℕ → κ) (m : ℕ), IsRun T N s m ∧ t ∈ runSet s m := by
  classical
  obtain ⟨u, u', huu', hN, -⟩ := hgood t ht
  have hu : T.Adj t u := (hN u).2 (Or.inl rfl)
  have hu' : T.Adj t u' := (hN u').2 (Or.inr rfl)
  obtain ⟨b, hb, hbu, hbN⟩ := exists_first_bad hT hgood ht hu
  obtain ⟨b', hb', hbu', hbN'⟩ := exists_first_bad hT hgood ht hu'
  -- `t` is on the path from `b` to `b'`.
  have htbb : Thomas.OnTreePath T b b' t := by
    have hs₁ : Thomas.OnTreePath T b' u t := by
      rcases Thomas.onTreePath_adj_dichotomy hT hu b' with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (eq_of_adj_of_onTreePath hT hu hu' (Thomas.onTreePath_symm h) hbu') huu'
    exact Thomas.onTreePath_symm
      (Thomas.onTreePath_of_sides hT hu hs₁ (Thomas.onTreePath_symm hbu)).1
  have htb : t ≠ b := fun h ↦ ht (h ▸ hb)
  have htb' : t ≠ b' := fun h ↦ ht (h ▸ hb')
  -- The path from `b` to `b'` as a sequence.
  set q := Thomas.treePath hT b b' with hq_def
  have hq : q.IsPath := Thomas.treePath_isPath hT b b'
  set s : ℕ → κ := fun j ↦ q.getVert j with hs_def
  set L := q.length with hL
  have hs : IsSeqPath T s L :=
    ⟨fun i hi j hj hij ↦ hq.getVert_injOn (by rw [Set.mem_ofPred]; exact mem_Iic.1 hi)
      (by rw [Set.mem_ofPred]; exact mem_Iic.1 hj) hij, fun j hj ↦ q.adj_getVert_succ hj⟩
  have hs0 : s 0 = b := q.getVert_zero
  have hsL : s L = b' := q.getVert_length
  have hmem : ∀ z, Thomas.OnTreePath T b b' z → ∃ j ≤ L, s j = z := fun z hz ↦ by
    rw [Thomas.onTreePath_iff_mem_treePath hT] at hz
    obtain ⟨j, hj, hjL⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.1 hz
    exact ⟨j, hjL, hj⟩
  have hon : ∀ j, Thomas.OnTreePath T b b' (s j) := fun j ↦ by
    rw [Thomas.onTreePath_iff_mem_treePath hT]
    exact q.getVert_mem_support j
  have hinj : ∀ i j, i ≤ L → j ≤ L → s i = s j → i = j := fun i j hi hj h ↦
    hs.injOn (mem_Iic.2 hi) (mem_Iic.2 hj) h
  obtain ⟨jt, hjtL, hjt⟩ := hmem t htbb
  have hjt0 : jt ≠ 0 := fun h ↦ htb (by rw [← hjt, h, hs0])
  have hjtL' : jt ≠ L := fun h ↦ htb' (by rw [← hjt, h, hsL])
  -- The inner vertices are not in `N`.
  have hinner : ∀ j, 1 ≤ j → j < L → s j ∉ N := by
    intro j hj1 hjL hjN
    have hb0 : s j ≠ b := fun h ↦ by
      have := hinj j 0 hjL.le (Nat.zero_le _) (h.trans hs0.symm)
      omega
    have hb1 : s j ≠ b' := fun h ↦ by
      have := hinj j L hjL.le le_rfl (h.trans hsL.symm)
      omega
    rcases (Thomas.onTreePath_split_iff hT htbb).1 (hon j) with h | h
    · exact hbN _ (Thomas.onTreePath_symm h) hb0 hjN
    · exact hbN' _ h hb1 hjN
  refine ⟨s, L - 1, ⟨by rw [show L - 1 + 1 = L by omega]; exact hs, by omega, hs0 ▸ hb,
    by rw [show L - 1 + 1 = L by omega, hsL]; exact hb', fun j hj1 hjm ↦ hinner j hj1 (by omega),
    fun j hj1 hjm z hz ↦ ?_⟩, ⟨jt, by omega, by omega, hjt⟩⟩
  have hgj := hgood _ (hinner j hj1 (by omega))
  have hl : T.Adj (s j) (s (j - 1)) := by
    have := hs.adj (j - 1) (by omega)
    rw [Nat.sub_add_cancel hj1] at this
    exact this.symm
  have hr : T.Adj (s j) (s (j + 1)) := hs.adj j (by omega)
  have hne : s (j - 1) ≠ s (j + 1) := fun h ↦ by
    have := hinj _ _ (by omega) (by omega) h
    omega
  exact hgj.eq_or_eq hl hr hne z hz

/-- `goodReach` is the same for two vertices joined by a path with no vertex in `N`. -/
theorem goodReach_eq_of_mem (hgood : ∀ z ∉ N, GoodAt T W z) {t z : κ} (ht : t ∉ N)
    (hz : z ∈ goodReach T N t) : goodReach T N z = goodReach T N t := by
  obtain ⟨s, m, hr, hts⟩ := exists_run hT hgood ht
  rw [hr.goodReach_eq hT hts] at hz ⊢
  exact hr.goodReach_eq hT hz

omit hT in
theorem mem_goodReach_self {t : κ} (ht : t ∉ N) : t ∈ goodReach T N t := fun x hx ↦ by
  rw [Thomas.onTreePath_self] at hx
  exact hx ▸ ht

/-- **The chain of `G \ Z`.** Let each edge of `G` be in one bag, let `T` have maximum degree
`≤ 3`, and let every vertex of `T` outside `N` be good. Then `G` is a
`(3 |N| (w + 1) + |N| (w + 1))`-chain. -/
theorem isChain_of_good [Nonempty β] (hG : G.IsGraph) (hTD : GM10.IsTreeDecomposition G T W)
    (hdeg : ∀ t, (T.neighborSet t).ncard ≤ 3) (hgood : ∀ z ∉ N, GoodAt T W z) {w : ℕ}
    (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1) :
    IsChain G (3 * N.ncard * (w + 1) + N.ncard * (w + 1)) := by
  classical
  set D := (bagUnion W (· ∈ N)).vertexSet with hD
  have hDf : D.Finite := (bagUnion W (· ∈ N)).vertexSet_finite
  set P : Set κ → Hypergraph α β := fun X ↦ (bagUnion W (· ∈ X)).deleteVertices D with hP
  set S : Finset (Set κ) := (Finset.univ.filter (· ∉ N)).image (goodReach T N) with hS
  have hmemS : ∀ X ∈ S, ∃ t ∉ N, goodReach T N t = X := fun X hX ↦ by
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hX
    exact ⟨t, (Finset.mem_filter.1 ht).2, rfl⟩
  have hbagG : ∀ X : Set κ, bagUnion W (· ∈ X) ≤ G := fun X ↦
    GM10.biUnion_le_of_le fun t _ ↦ hTD.le t
  have hinc : ∀ {K : Hypergraph α β}, K ≤ G → ∀ {f : β}, f ∈ K.edgeSet → ∀ y,
      K.Inc f y ↔ G.Inc f y := by
    intro K hK f hf y
    change y ∈ K.ends f ↔ y ∈ G.ends f
    rw [hK.ends_eq f hf]
  have hKG : G.deleteVertices D ≤ G := GM10.deleteVertices_le _ _
  have hPK : ∀ X, P X ≤ G.deleteVertices D := fun X ↦
    le_of_subset_of_le ((GM10.deleteVertices_le _ _).trans (hbagG X)) hKG
      (fun y hy ↦ ⟨(hbagG X).vertexSet_subset hy.1, hy.2⟩)
      (fun f hf ↦ ⟨(hbagG X).edgeSet_subset hf.1, fun v hv h ↦ hf.2 v hv
        ((hinc (hbagG X) hf.1 v).2 h)⟩)
  -- A vertex of a bag at a good vertex `z` that is not in `D` stays in the pieces through `z`.
  have hpath : ∀ {z z' : κ} {y : α}, y ∈ (W z).vertexSet → y ∈ (W z').vertexSet → y ∉ D →
      z' ∈ goodReach T N z := by
    intro z z' y hyz hyz' hyD x hx hxN
    exact hyD (mem_bagUnion_vertexSet.2 ⟨x, hxN, (hTD.inter_le hx).vertexSet_subset ⟨hyz, hyz'⟩⟩)
  have hch := isChain_biUnion S P (q := w + 1) (fun X _ ↦ hPK X) ?_ ?_ ?_ ?_
  · -- Adding back `D`.
    have := IsChain.of_deleteVertices hDf.toFinset (K := G) (by rw [Finite.coe_toFinset]; exact hch)
    refine this.mono ?_
    -- The number of pieces.
    have hScard : S.card ≤ 3 * N.ncard := by
      set pairs : Finset (κ × κ) := Finset.univ.filter fun bp ↦ bp.1 ∈ N ∧ T.Adj bp.1 bp.2
      have hsub : S ⊆ pairs.image fun bp ↦ goodReach T N bp.2 := by
        intro X hX
        obtain ⟨t, ht, rfl⟩ := hmemS X hX
        obtain ⟨s, m, hr, hts⟩ := exists_run hT hgood ht
        have h1 : s 1 ∈ runSet s m := ⟨1, le_rfl, hr.one_le, rfl⟩
        refine Finset.mem_image.2 ⟨(s 0, s 1), Finset.mem_filter.2 ⟨Finset.mem_univ _, hr.first,
          hr.seq.adj 0 (by omega)⟩, ?_⟩
        rw [hr.goodReach_eq hT h1, hr.goodReach_eq hT hts]
      refine (Finset.card_le_card hsub).trans (Finset.card_image_le.trans ?_)
      have := Finset.card_le_mul_card_image_of_maps_to (f := Prod.fst) (s := pairs)
        (t := (toFinite N).toFinset) (fun bp hbp ↦ (toFinite N).mem_toFinset.2
          (Finset.mem_filter.1 hbp).2.1) 3 (fun b hb ↦ ?_)
      · rw [← ncard_eq_toFinset_card N (toFinite N)] at this
        exact this
      · refine (Finset.card_le_card_of_injOn Prod.snd (t := (toFinite (T.neighborSet b)).toFinset)
          (fun bp hbp ↦ ?_) (fun bp hbp bp' hbp' h ↦ ?_)).trans ?_
        · have h1 := (Finset.mem_filter.1 hbp)
          have h2 := (Finset.mem_filter.1 h1.1).2
          rw [Finset.mem_coe, (toFinite _).mem_toFinset, mem_neighborSet, ← h1.2]
          exact h2.2
        · have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hbp)).2
          have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hbp')).2
          exact Prod.ext (h1.trans h2.symm) h
        · rw [← ncard_eq_toFinset_card _ (toFinite _)]
          exact hdeg b
    -- The size of `D`.
    have hDn : D.ncard ≤ N.ncard * (w + 1) := by
      have hDV : D ⊆ ⋃ t : N, (W t).vertexSet := fun y hy ↦ by
        obtain ⟨t, htN, hyt⟩ := mem_bagUnion_vertexSet.1 hy
        exact mem_iUnion.2 ⟨⟨t, htN⟩, hyt⟩
      refine (ncard_le_ncard hDV (finite_iUnion fun t : N ↦ (W t.1).vertexSet_finite)).trans
        ((ncard_iUnion_le_of_fintype _).trans ?_)
      refine (Finset.sum_le_sum fun t _ ↦ hw t.1).trans ?_
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card,
        Nat.card_coe_set_eq]
    rw [← ncard_eq_toFinset_card D hDf]
    have := Nat.mul_le_mul_right (w + 1) hScard
    omega
  · -- The pieces are disjoint.
    intro X hX X' hX' hXX'
    obtain ⟨t, ht, rfl⟩ := hmemS X hX
    obtain ⟨t', ht', rfl⟩ := hmemS X' hX'
    rw [Set.disjoint_left]
    rintro y ⟨hy, hyD⟩ ⟨hy', -⟩
    obtain ⟨z, hz, hyz⟩ := mem_bagUnion_vertexSet.1 hy
    obtain ⟨z', hz', hyz'⟩ := mem_bagUnion_vertexSet.1 hy'
    have hzN : z ∉ N := hz z (Thomas.onTreePath_right T t z)
    refine hXX' ?_
    rw [← goodReach_eq_of_mem hT hgood ht hz, ← goodReach_eq_of_mem hT hgood ht' hz',
      goodReach_eq_of_mem hT hgood hzN (hpath hyz hyz' hyD)]
  · -- They cover the vertices.
    ext y
    constructor
    · rintro ⟨hy, hyD⟩
      rw [← hTD.biUnion_eq] at hy
      obtain ⟨t, -, hyt⟩ : ∃ t ∈ Finset.univ, y ∈ (W t).vertexSet := by
        simpa [Hypergraph.biUnion] using hy
      have htN : t ∉ N := fun h ↦ hyD (mem_bagUnion_vertexSet.2 ⟨t, h, hyt⟩)
      refine mem_iUnion₂.2 ⟨goodReach T N t, Finset.mem_image.2 ⟨t, Finset.mem_filter.2
        ⟨Finset.mem_univ _, htN⟩, rfl⟩, ?_⟩
      exact ⟨mem_bagUnion_vertexSet.2 ⟨t, mem_goodReach_self htN, hyt⟩, hyD⟩
    · intro hy
      obtain ⟨X, -, hyX⟩ := mem_iUnion₂.1 hy
      exact (hPK X).vertexSet_subset hyX
  · -- They cover the edges.
    ext f
    constructor
    · rintro ⟨hf, hfD⟩
      have hfG := hf
      rw [← hTD.biUnion_eq] at hf
      obtain ⟨t, -, hft⟩ : ∃ t ∈ Finset.univ, f ∈ (W t).edgeSet := by
        simpa [Hypergraph.biUnion] using hf
      obtain ⟨y, hy⟩ := (hG f hfG).1
      have hyt : y ∈ (W t).vertexSet := by
        have : y ∈ (W t).ends f := by rw [← (hTD.le t).ends_eq f hft]; exact hy
        exact (W t).vertex_mem_of_inc this
      have htN : t ∉ N := fun h ↦ hfD y (mem_bagUnion_vertexSet.2 ⟨t, h, hyt⟩) hy
      refine mem_iUnion₂.2 ⟨goodReach T N t, Finset.mem_image.2 ⟨t, Finset.mem_filter.2
        ⟨Finset.mem_univ _, htN⟩, rfl⟩, ?_⟩
      have hfb : f ∈ (bagUnion W (· ∈ goodReach T N t)).edgeSet :=
        mem_bagUnion_edgeSet.2 ⟨t, mem_goodReach_self htN, hft⟩
      exact ⟨hfb, fun v hv h ↦ hfD v hv ((hinc (hbagG _) hfb v).1 h)⟩
    · intro hf
      obtain ⟨X, -, hfX⟩ := mem_iUnion₂.1 hf
      exact (hPK X).edgeSet_subset hfX
  · -- Each piece is a chain.
    intro X hX
    obtain ⟨t, ht, rfl⟩ := hmemS X hX
    obtain ⟨s, m, hr, hts⟩ := exists_run hT hgood ht
    rw [hr.goodReach_eq hT hts]
    exact hr.isChain hTD hgood hw

end Runs

/-! ## (12.4) -/

/-- **Graph Minors XXI, (12.4)**, in the form used by `theorem_12_4`. -/
theorem theorem_12_4_proof (p : ℕ) :
    ∃ p' : ℕ, ∀ {α : Type u} {β : Type v} (G : Hypergraph α β), G.IsGraph →
      HasVitalPLinkage G p → IsChain G p' := by
  obtain ⟨w', hw'⟩ := Final.hypergraph_treeWidthPlusOne_le_of_hasVitalPLinkage.{u, v} p
  obtain ⟨n, hn⟩ := exists_isSixBound.{u, v} p (w' + 1)
  refine ⟨p + 4 * (3 * 2 ^ n) * (w' + 1), ?_⟩
  intro α β G hG ⟨L, hL⟩
  classical
  rcases isEmpty_or_nonempty β with hβ | hβ
  · exact (isChain_of_edgeSet_empty hL (eq_empty_of_isEmpty _)).mono (Nat.le_add_right _ _)
  have htw := hw' G hG ⟨L, hL⟩
  -- Choose `(T, W)` with as few bad vertices as possible.
  have hQ : ∃ N, ∃ (κ : Type) (_ : Fintype κ) (T : SimpleGraph κ) (W : κ → Hypergraph α β),
      IsGoodDecomp G w' T W ∧ (badSet T W).ncard = N := by
    obtain ⟨κ, _, T, W, h1, h2, h3, h4⟩ := exists_good_treeDecomposition hG htw
    exact ⟨_, κ, inferInstance, T, W, ⟨h1.isTreeDecomp21, h2, h3, h4⟩, rfl⟩
  obtain ⟨κ, _, T, W, ⟨h, hlink, hw, hdeg⟩, hcard⟩ := Nat.find_spec hQ
  have hmin : ∀ (κ' : Type) (_ : Fintype κ') (T' : SimpleGraph κ') (W' : κ' → Hypergraph α β),
      IsGoodDecomp G w' T' W' → (badSet T W).ncard ≤ (badSet T' W').ncard :=
    fun κ' _ T' W' hg ↦ hcard ▸ Nat.find_min' hQ ⟨κ', inferInstance, T', W', hg, rfl⟩
  -- Keep each edge in one bag; the vertex sets stay the same.
  obtain ⟨W₀, hTD, hV, hE⟩ := exists_trim h
  have hE' : ∀ {u v : κ}, T.Adj u v → treeEdgeSet T W₀ u v = treeEdgeSet T W u v := fun huv ↦ by
    rw [hTD.isTreeDecomp21.treeEdgeSet_eq huv, h.treeEdgeSet_eq huv, hV, hV]
  have hlink₀ : IsLinkedTreeDecomp G T W₀ := by
    intro a₁ b₁ a₂ b₂ h₁ h₂ hb₁ ha₂ k hk₁ hk₂ hpath
    rw [hE' h₁] at hk₁
    rw [hE' h₂] at hk₂
    rw [hE' h₁, hE' h₂]
    exact hlink h₁ h₂ hb₁ ha₂ k hk₁ hk₂ fun s s' hss ↦ hE' hss.1 ▸ hpath hss
  have hw₀ : ∀ t, (W₀ t).vertexSet.ncard ≤ w' + 1 := fun t ↦ hV t ▸ hw t
  have hgood : ∀ z ∉ badSet T W, GoodAt T W₀ z := fun z hz ↦
    (not_not.1 hz).of_trim h hTD hV hE
  -- Claims (1) and (2) for the bad vertices, and the bound on their number.
  have hone := claim_12_4_one hG h hTD hV hE hlink₀ hw₀ hdeg hmin
  have h2 := ncard_inter_path_le hG hTD hlink₀ hw₀ hone hL hn
  have hN := ncard_le_of_paths h.isTree hdeg (fun s hs ↦ (hgood s hs).ncard_neighborSet_le) h2
  -- The chain.
  have hch := isChain_of_good h.isTree hG hTD hdeg hgood hw₀
  refine hch.mono ?_
  have := Nat.mul_le_mul_right (w' + 1) hN
  nlinarith
