module

public import GraphMinor.GM21.Section11Lift

/-!
# Graph Minors XXI, (11.1): intertwinings have bounded rank

The proof is the paper's induction on `|V(G)| + |E(G)|`.

* Step (1): delete an isolated vertex (`isIntertwining_delete`, `graphRank_le_delete`).
* Steps (2) and (3): contract an edge `e` of a linkage `L₁'` with the pattern of `L₁`, where `e` is
  also an edge of a linkage `L₂'` with the pattern of `L₂`, or one end of `e` is not in `L₂'`
  (`isIntertwining_contract`, `graphRank_le_contract`).
* After that, `L₁` and `L₂` are vital, and `ncard_edgeSet_le_of_vital_union` bounds `|E(G)|`.

The rank is at most `|E(G)|`, since a graph has at most `|V(G)|` components.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- A graph has at most `|V(G)|` components. -/
theorem numComponents_le_ncard {G : Hypergraph α β} (hG : G.IsGraph) :
    numComponents G ≤ G.vertexSet.ncard := by
  rw [numComponents_eq hG]
  exact ncard_image_le G.vertexSet_finite

/-- The rank of a graph is at most its number of edges. -/
theorem graphRank_le_ncard_edgeSet {G : Hypergraph α β} (hG : G.IsGraph) :
    graphRank G ≤ G.edgeSet.ncard := by
  have := numComponents_le_ncard hG
  unfold graphRank
  omega

/-! ## Contracting an edge -/

section ContractStep

variable {G : Hypergraph α β} {x y : α} {e : β}

/-- If `G` is an intertwining of `L₁` and `L₂`, then `G / e` is an intertwining of any two
linkages whose patterns are the images of the patterns of `L₁` and `L₂`. -/
theorem isIntertwining_contract (hG : G.IsGraph) (hex : G.Inc e x) (hey : G.Inc e y)
    (hxy : x ≠ y) (hends : ∀ v, G.Inc e v → v = x ∨ v = y) {L₁ L₂ N₁ N₂ : Hypergraph α β}
    (hL₁ : IsLinkage G L₁) (hL₂ : IsLinkage G L₂) (hI : IsIntertwining G L₁ L₂)
    (hC₁ : x ∈ terminals L₁ → y ∈ terminals L₁ → {x, y} ∈ linkagePattern L₁)
    (hC₂ : x ∈ terminals L₂ → y ∈ terminals L₂ → {x, y} ∈ linkagePattern L₂)
    (hN₁ : linkagePattern N₁ = image (mergeVertex x y) '' linkagePattern L₁)
    (hN₂ : linkagePattern N₂ = image (mergeVertex x y) '' linkagePattern L₂) :
    IsIntertwining (contract x y e G) N₁ N₂ := by
  intro M₁ M₂ hM₁ hM₂ hp₁ hp₂
  obtain ⟨K₁, hK₁, hK₁p, hK₁c⟩ := exists_lift hG hex hey hxy hends hL₁ hC₁ hM₁ (hp₁.trans hN₁)
  obtain ⟨K₂, hK₂, hK₂p, hK₂c⟩ := exists_lift hG hex hey hxy hends hL₂ hC₂ hM₂ (hp₂.trans hN₂)
  rw [← hK₁c, ← hK₂c, ← contract_union, hI K₁ K₂ hK₁ hK₂ hK₁p hK₂p]

/-- A linkage that contains `e` gives a linkage of `G / e`. -/
theorem contract_data_of_mem (hxy : x ≠ y) {L : Hypergraph α β} (hL : IsLinkage G L)
    (heL : e ∈ L.edgeSet) (hex : G.Inc e x) (hey : G.Inc e y) :
    ∃ N, IsLinkage (contract x y e G) N ∧
      linkagePattern N = image (mergeVertex x y) '' linkagePattern L ∧
      (x ∈ terminals L → y ∈ terminals L → {x, y} ∈ linkagePattern L) ∧
      (terminals N).ncard ≤ (terminals L).ncard := by
  have hLx : L.Inc e x := (GM10.inc_iff_of_le hL.1 heL).2 hex
  have hLy : L.Inc e y := (GM10.inc_iff_of_le hL.1 heL).2 hey
  refine ⟨contract x y e L, isLinkage_contract hL heL hLx hLy hxy hL.1,
    linkagePattern_contract hL heL hLx hLy hxy hL.1, fun hx hy ↦
      (hL.pair_mem_linkagePattern_iff hx hy hxy).2
        (SimpleGraph.Adj.reachable ⟨hxy, e, hLx, hLy⟩), ?_⟩
  rw [terminals_contract hL heL hLx hLy hxy]
  exact ncard_image_le (L.vertexSet_finite.subset fun _ h ↦ h.1)

/-- A linkage that avoids `y` and `e` is a linkage of `G / e`. -/
theorem contract_data_of_notMem {L : Hypergraph α β} (hL : IsLinkage G L)
    (hyL : y ∉ L.vertexSet) (heL : e ∉ L.edgeSet) :
    ∃ N, IsLinkage (contract x y e G) N ∧
      linkagePattern N = image (mergeVertex x y) '' linkagePattern L ∧
      (x ∈ terminals L → y ∈ terminals L → {x, y} ∈ linkagePattern L) ∧
      (terminals N).ncard ≤ (terminals L).ncard := by
  have hle := contract_le (x := x) (y := y) (e := e) hL.1
  rw [contract_eq_self hyL heL] at hle
  refine ⟨L, hL.mono_ambient hle, ?_, fun _ hy ↦ absurd hy.1 hyL, le_rfl⟩
  refine (image_eq_self_of_forall fun B hB ↦ image_mergeVertex_of_notMem fun hy ↦ ?_).symm
  have : y ∈ terminals L := by
    rw [hL.terminals_eq_sUnion_linkagePattern]
    exact ⟨B, hB, hy⟩
  exact hyL this.1

/-- Contracting `e` does not lower the rank, and it makes the graph smaller. -/
theorem graphRank_le_contract (hG : G.IsGraph) (hex : G.Inc e x) (hey : G.Inc e y)
    (hxy : x ≠ y) :
    graphRank G ≤ graphRank (contract x y e G) ∧
      (contract x y e G).vertexSet.ncard + (contract x y e G).edgeSet.ncard <
        G.vertexSet.ncard + G.edgeSet.ncard := by
  have hV : (contract x y e G).vertexSet = G.vertexSet \ {y} := by
    ext v
    rw [mem_contract_vertexSet]
    constructor
    · rintro (⟨hv, hvy⟩ | ⟨rfl, -⟩)
      exacts [⟨hv, hvy⟩, ⟨G.vertex_mem_of_inc hex, hxy⟩]
    · rintro ⟨hv, hvy⟩
      exact Or.inl ⟨hv, hvy⟩
  have hE : (contract x y e G).edgeSet = G.edgeSet \ {e} := rfl
  have h1 := ncard_sdiff_singleton_add_one (G.vertex_mem_of_inc hey) G.vertexSet_finite
  have h2 := ncard_sdiff_singleton_add_one (G.edge_mem_of_inc hex) G.edgeSet_finite
  have h3 := numComponents_le_contract hG (isGraph_contract hG) hex hey
  unfold graphRank
  rw [hV, hE]
  constructor <;> omega

end ContractStep

/-! ## Deleting an isolated vertex -/

section DeleteStep

variable {G : Hypergraph α β} {v : α}

theorem deleteVertices_le_of_le {L : Hypergraph α β} (hLG : L ≤ G) (hiso : ∀ f, ¬ G.Inc f v) :
    GM10.deleteVertices L {v} ≤ GM10.deleteVertices G {v} where
  vertexSet_subset w hw := ⟨hLG.vertexSet_subset hw.1, hw.2⟩
  edgeSet_subset f hf := ⟨hLG.edgeSet_subset hf.1, by rintro u rfl; exact hiso f⟩
  ends_eq f hf := by
    ext w
    constructor
    · rintro ⟨h, -⟩
      refine ⟨(GM10.inc_iff_of_le hLG hf.1).2 h, ?_⟩
      rintro u rfl h'
      exact hiso f ((GM10.inc_iff_of_le hLG hf.1).1 h')
    · rintro ⟨h, -⟩
      refine ⟨(GM10.inc_iff_of_le hLG hf.1).1 h, ?_⟩
      rintro u rfl h'
      exact hiso f h'

/-- A linkage is its part away from `v` together with `v`, if `v` is in it. -/
theorem deleteVertices_union_subOn (hiso : ∀ f, ¬ G.Inc f v) {L : Hypergraph α β}
    (hLG : L ≤ G) : GM10.deleteVertices L {v} ∪ subOn L {v} ∅ = L := by
  ext f
  · constructor
    · rintro (⟨h, -⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      by_cases hw : f = v
      · exact Or.inr ⟨hw, h⟩
      · exact Or.inl ⟨h, hw⟩
  · constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩)
      exacts [h, absurd h (notMem_empty f)]
    · intro h
      refine Or.inl ⟨h, ?_⟩
      rintro u rfl h'
      exact hiso f ((GM10.inc_iff_of_le hLG h).1 h')
  · rename_i w
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      refine Or.inl ⟨h, ?_⟩
      rintro u rfl h'
      exact hiso f ((GM10.inc_iff_of_le hLG (L.edge_mem_of_inc h)).1 h')

theorem subOn_singleton_le (L : Hypergraph α β) : subOn L {v} ∅ ≤ L :=
  subOn_le fun f hf ↦ absurd hf (notMem_empty f)

/-- Deleting an isolated vertex from a linkage gives a linkage with no more terminals. -/
theorem delete_data (hG : G.IsGraph) (hiso : ∀ f, ¬ G.Inc f v) {L : Hypergraph α β}
    (hL : IsLinkage G L) :
    IsLinkage (GM10.deleteVertices G {v}) (GM10.deleteVertices L {v}) ∧
      (terminals (GM10.deleteVertices L {v})).ncard ≤ (terminals L).ncard := by
  refine ⟨isLinkage_of_le hL (GM10.deleteVertices_le L {v}) (deleteVertices_le_of_le hL.1 hiso),
    ?_⟩
  have hd : Disjoint (GM10.deleteVertices L {v}).vertexSet (subOn L {v} ∅).vertexSet :=
    disjoint_left.2 fun _ hw hw' ↦ hw.2 hw'.1
  have hT := terminals_union hG ((GM10.deleteVertices_le L {v}).trans hL.1)
    ((subOn_singleton_le L).trans hL.1) hd
  rw [deleteVertices_union_subOn hiso hL.1] at hT
  have hfin : (terminals L).Finite := L.vertexSet_finite.subset fun _ h ↦ h.1
  exact ncard_le_ncard (by rw [hT]; exact subset_union_left) hfin

/-- If `G` is an intertwining of `L₁` and `L₂`, and `v` is an isolated vertex, then `G \ v` is an
intertwining of `L₁ \ v` and `L₂ \ v`. This is Claim (1) of the proof of (11.1), where the print
writes "the $p$-linkages $L'_i$ and $L'_2$" for $L'_1$ and $L'_2$ (see the correction to the proof
of (11.1) in `corrections/GM21.md`). -/
theorem isIntertwining_delete (hG : G.IsGraph) (hiso : ∀ f, ¬ G.Inc f v)
    {L₁ L₂ : Hypergraph α β} (hL₁ : IsLinkage G L₁) (hL₂ : IsLinkage G L₂)
    (hI : IsIntertwining G L₁ L₂) :
    IsIntertwining (GM10.deleteVertices G {v}) (GM10.deleteVertices L₁ {v})
      (GM10.deleteVertices L₂ {v}) := by
  intro M₁ M₂ hM₁ hM₂ hp₁ hp₂
  have hDG : GM10.deleteVertices G {v} ≤ G := GM10.deleteVertices_le G {v}
  have hext : ∀ {L M : Hypergraph α β}, IsLinkage G L →
      IsLinkage (GM10.deleteVertices G {v}) M →
      linkagePattern M = linkagePattern (GM10.deleteVertices L {v}) →
      IsLinkage G (M ∪ subOn L {v} ∅) ∧
        linkagePattern (M ∪ subOn L {v} ∅) = linkagePattern L := by
    intro L M hL hM hp
    have hSG := (subOn_singleton_le (v := v) L).trans hL.1
    have hSl : IsLinkage G (subOn L {v} ∅) := isLinkage_of_le hL (subOn_singleton_le L) hSG
    have hd : ∀ {A : Hypergraph α β}, v ∉ A.vertexSet →
        Disjoint A.vertexSet (subOn L {v} ∅).vertexSet := fun h ↦
      disjoint_left.2 fun w hw hw' ↦ h ((mem_singleton_iff.1 hw'.1) ▸ hw)
    have hvM : v ∉ M.vertexSet := fun h ↦ (hM.1.vertexSet_subset h).2 rfl
    have hL'G := (GM10.deleteVertices_le L {v}).trans hL.1
    have hL' : IsLinkage G (GM10.deleteVertices L {v}) :=
      isLinkage_of_le hL (GM10.deleteVertices_le L {v}) hL'G
    have hU1 := isLinkage_union hG (hM.1.trans hDG) hSG (hd hvM) (hM.mono_ambient (hM.1.trans hDG))
      hSl
    have hU2 := isLinkage_union hG hL'G hSG (hd fun h ↦ h.2 rfl) hL' hSl
    refine ⟨hU1.1, ?_⟩
    rw [hU1.2, hp, ← hU2.2, deleteVertices_union_subOn hiso hL.1]
  obtain ⟨hK₁, hK₁p⟩ := hext hL₁ hM₁ hp₁
  obtain ⟨hK₂, hK₂p⟩ := hext hL₂ hM₂ hp₂
  have hU := hI _ _ hK₁ hK₂ hK₁p hK₂p
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq (GM10.union_le hM₁.1 hM₂.1) le_rfl ?_ ?_
  · refine Subset.antisymm (GM10.union_le hM₁.1 hM₂.1).vertexSet_subset ?_
    rintro w ⟨hwG, hwv⟩
    rw [← hU] at hwG
    rcases hwG with (h | h) | (h | h)
    · exact Or.inl h
    · exact absurd h.1 hwv
    · exact Or.inr h
    · exact absurd h.1 hwv
  · refine Subset.antisymm (GM10.union_le hM₁.1 hM₂.1).edgeSet_subset ?_
    rintro f ⟨hfG, -⟩
    rw [← hU] at hfG
    rcases hfG with (h | h) | (h | h)
    · exact Or.inl h
    · exact absurd h.1 (notMem_empty f)
    · exact Or.inr h
    · exact absurd h.1 (notMem_empty f)

/-- Deleting an isolated vertex does not change the rank, and it makes the graph smaller. -/
theorem graphRank_le_delete (hG : G.IsGraph) (hv : v ∈ G.vertexSet) (hiso : ∀ f, ¬ G.Inc f v) :
    graphRank G ≤ graphRank (GM10.deleteVertices G {v}) ∧
      (GM10.deleteVertices G {v}).vertexSet.ncard + (GM10.deleteVertices G {v}).edgeSet.ncard <
        G.vertexSet.ncard + G.edgeSet.ncard := by
  have hE : (GM10.deleteVertices G {v}).edgeSet = G.edgeSet := by
    ext f
    exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, by rintro u rfl; exact hiso f⟩⟩
  have hV : (GM10.deleteVertices G {v}).vertexSet.ncard + 1 = G.vertexSet.ncard :=
    ncard_sdiff_singleton_add_one hv G.vertexSet_finite
  have hDg : (GM10.deleteVertices G {v}).IsGraph :=
    isGraph_of_le (GM10.deleteVertices_le G {v}) hG
  have hκ := numComponents_le_delete v hG hDg
  unfold graphRank
  rw [hE]
  constructor <;> omega

end DeleteStep

/-! ## The induction -/

/-- **Graph Minors XXI, (11.1).** For every `p` there is `r` such that every intertwining of two
`p`-linkages has rank at most `r`.

The proof is the paper's induction on `|V(G)| + |E(G)|`, with `r` the bound on `|E(G)|` of
`ncard_edgeSet_le_of_vital_union`. -/
theorem graphRank_le_of_isIntertwining (p : ℕ) :
    ∃ r : ℕ, ∀ {α : Type u} {β : Type v} (G L₁ L₂ : Hypergraph α β), G.IsGraph →
      IsPLinkage G L₁ p → IsPLinkage G L₂ p → IsIntertwining G L₁ L₂ → graphRank G ≤ r := by
  obtain ⟨R, hR⟩ := ncard_edgeSet_le_of_vital_union.{u, v} p
  refine ⟨R, ?_⟩
  intro α β G
  suffices h : ∀ n, ∀ G : Hypergraph α β, G.vertexSet.ncard + G.edgeSet.ncard = n →
      ∀ L₁ L₂ : Hypergraph α β, G.IsGraph → IsPLinkage G L₁ p → IsPLinkage G L₂ p →
        IsIntertwining G L₁ L₂ → graphRank G ≤ R from h _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G hn L₁ L₂ hG hL₁ hL₂ hI
  classical
  have hpl : ∀ {L L' : Hypergraph α β}, IsPLinkage G L p → IsLinkage G L' →
      linkagePattern L' = linkagePattern L → IsPLinkage G L' p := fun hL hL' hp ↦
    ⟨hL', by rw [terminals_eq_of_linkagePattern_eq hL' hL.1 hp]; exact hL.2⟩
  -- Step (1): an isolated vertex.
  by_cases h1 : ∃ v ∈ G.vertexSet, ∀ f, ¬ G.Inc f v
  · obtain ⟨v, hv, hiso⟩ := h1
    obtain ⟨hrank, hsize⟩ := graphRank_le_delete hG hv hiso
    have hDg : (GM10.deleteVertices G {v}).IsGraph :=
      isGraph_of_le (GM10.deleteVertices_le G {v}) hG
    obtain ⟨hD₁, hT₁⟩ := delete_data hG hiso hL₁.1
    obtain ⟨hD₂, hT₂⟩ := delete_data hG hiso hL₂.1
    exact hrank.trans (ih _ (by omega) _ rfl _ _ hDg ⟨hD₁, hT₁.trans hL₁.2⟩
      ⟨hD₂, hT₂.trans hL₂.2⟩ (isIntertwining_delete hG hiso hL₁.1 hL₂.1 hI))
  push Not at h1
  -- The step that contracts an edge, used for (2) and (3).
  have hstep : ∀ P₁ P₂ : Hypergraph α β, IsPLinkage G P₁ p → IsPLinkage G P₂ p →
      IsIntertwining G P₁ P₂ → ∀ (e : β) (x y : α), e ∈ P₁.edgeSet → G.Inc e x → G.Inc e y →
      x ≠ y → (e ∈ P₂.edgeSet ∨ (y ∉ P₂.vertexSet ∧ e ∉ P₂.edgeSet)) → graphRank G ≤ R := by
    intro P₁ P₂ hP₁ hP₂ hIP e x y heP₁ hex hey hxy hP₂e
    have hGe : (G.ends e).ncard = 2 := by
      rw [hP₁.1.1.ends_eq e heP₁]
      exact hP₁.1.ends_ncard_eq_two heP₁
    have hpair := ends_eq_pair_of_ncard hGe hex hey hxy
    have hends : ∀ w, G.Inc e w → w = x ∨ w = y := fun w hw ↦ by
      have : w ∈ G.ends e := hw
      rw [hpair] at this
      exact this
    obtain ⟨N₁, hN₁, hN₁p, hC₁, hN₁T⟩ := contract_data_of_mem hxy hP₁.1 heP₁ hex hey
    obtain ⟨N₂, hN₂, hN₂p, hC₂, hN₂T⟩ : ∃ N, IsLinkage (contract x y e G) N ∧
        linkagePattern N = image (mergeVertex x y) '' linkagePattern P₂ ∧
        (x ∈ terminals P₂ → y ∈ terminals P₂ → {x, y} ∈ linkagePattern P₂) ∧
        (terminals N).ncard ≤ (terminals P₂).ncard := by
      rcases hP₂e with heP₂ | ⟨hyP₂, heP₂⟩
      · exact contract_data_of_mem hxy hP₂.1 heP₂ hex hey
      · exact contract_data_of_notMem hP₂.1 hyP₂ heP₂
    obtain ⟨hrank, hsize⟩ := graphRank_le_contract hG hex hey hxy
    exact hrank.trans (ih _ (by omega) _ rfl N₁ N₂ (isGraph_contract hG)
      ⟨hN₁, hN₁T.trans hP₁.2⟩ ⟨hN₂, hN₂T.trans hP₂.2⟩
      (isIntertwining_contract hG hex hey hxy hends hP₁.1 hP₂.1 hIP hC₁ hC₂ hN₁p hN₂p))
  have hI' : ∀ {L₁' L₂' : Hypergraph α β}, linkagePattern L₁' = linkagePattern L₁ →
      linkagePattern L₂' = linkagePattern L₂ → IsIntertwining G L₁' L₂' :=
    fun hp₁ hp₂ M₁ M₂ hM₁ hM₂ hq₁ hq₂ ↦ hI M₁ M₂ hM₁ hM₂ (hq₁.trans hp₁) (hq₂.trans hp₂)
  have hIswap : ∀ {L₁' L₂' : Hypergraph α β}, IsIntertwining G L₁' L₂' →
      IsIntertwining G L₂' L₁' := fun h M₁ M₂ hM₁ hM₂ hq₁ hq₂ ↦ by
    rw [GM10.union_comm]
    exact h M₂ M₁ hM₂ hM₁ hq₂ hq₁
  -- Step (2): a vertex that is not in one of the linkages.
  by_cases h2 : ∃ L₁' L₂' : Hypergraph α β, IsLinkage G L₁' ∧ IsLinkage G L₂' ∧
      linkagePattern L₁' = linkagePattern L₁ ∧ linkagePattern L₂' = linkagePattern L₂ ∧
      ∃ v ∈ G.vertexSet, v ∉ L₁'.vertexSet ∨ v ∉ L₂'.vertexSet
  · obtain ⟨L₁', L₂', hL₁', hL₂', hp₁, hp₂, v, hv, hvL⟩ := h2
    have hU : L₁' ∪ L₂' = G := hI _ _ hL₁' hL₂' hp₁ hp₂
    obtain ⟨e, hev⟩ := h1 v hv
    have hsub : ∀ {A B : Hypergraph α β}, IsLinkage G A → IsLinkage G B → A ∪ B = G →
        v ∉ B.vertexSet → e ∈ A.edgeSet ∧ e ∉ B.edgeSet ∧ ∃ x, x ≠ v ∧ G.Inc e x := by
      intro A B hA hB hAB hvB
      have heB : e ∉ B.edgeSet := fun he ↦
        hvB (B.vertex_mem_of_inc ((GM10.inc_iff_of_le hB.1 he).2 hev))
      have heG : e ∈ G.edgeSet := G.edge_mem_of_inc hev
      rw [← hAB] at heG
      have heA : e ∈ A.edgeSet := heG.resolve_right heB
      refine ⟨heA, heB, ?_⟩
      by_contra hcon
      push Not at hcon
      have h2 := hA.ends_ncard_eq_two heA
      have : (A.ends e).ncard ≤ 1 :=
        (ncard_le_ncard (fun w hw ↦ by
          by_contra hwv
          exact hcon w hwv ((GM10.inc_iff_of_le hA.1 heA).1 hw)) (finite_singleton v)).trans_eq
          (ncard_singleton v)
      omega
    rcases hvL with hv1 | hv2
    · obtain ⟨heA, heB, x, hxv, hex⟩ :=
        hsub hL₂' hL₁' (by rw [GM10.union_comm]; exact hU) hv1
      exact hstep L₂' L₁' (hpl hL₂ hL₂' hp₂) (hpl hL₁ hL₁' hp₁) (hIswap (hI' hp₁ hp₂)) e x v
        heA hex hev hxv (Or.inr ⟨hv1, heB⟩)
    · obtain ⟨heA, heB, x, hxv, hex⟩ := hsub hL₁' hL₂' hU hv2
      exact hstep L₁' L₂' (hpl hL₁ hL₁' hp₁) (hpl hL₂ hL₂' hp₂) (hI' hp₁ hp₂) e x v
        heA hex hev hxv (Or.inr ⟨hv2, heB⟩)
  -- Step (3): an edge in both linkages.
  by_cases h3 : ∃ L₁' L₂' : Hypergraph α β, IsLinkage G L₁' ∧ IsLinkage G L₂' ∧
      linkagePattern L₁' = linkagePattern L₁ ∧ linkagePattern L₂' = linkagePattern L₂ ∧
      ∃ e, e ∈ L₁'.edgeSet ∧ e ∈ L₂'.edgeSet
  · obtain ⟨L₁', L₂', hL₁', hL₂', hp₁, hp₂, e, he₁, he₂⟩ := h3
    obtain ⟨x, y, hxy, hends⟩ := ncard_eq_two.1 (hL₁'.ends_ncard_eq_two he₁)
    have hex : G.Inc e x := (GM10.inc_iff_of_le hL₁'.1 he₁).1
      (show x ∈ L₁'.ends e by rw [hends]; exact Or.inl rfl)
    have hey : G.Inc e y := (GM10.inc_iff_of_le hL₁'.1 he₁).1
      (show y ∈ L₁'.ends e by rw [hends]; exact Or.inr rfl)
    exact hstep L₁' L₂' (hpl hL₁ hL₁' hp₁) (hpl hL₂ hL₂' hp₂) (hI' hp₁ hp₂) e x y he₁ hex hey
      hxy (Or.inl he₂)
  -- Now both linkages are vital, and they share no edge.
  have hV : ∀ {L₁' L₂' : Hypergraph α β}, IsLinkage G L₁' → IsLinkage G L₂' →
      linkagePattern L₁' = linkagePattern L₁ → linkagePattern L₂' = linkagePattern L₂ →
      L₁'.vertexSet = G.vertexSet ∧ L₂'.vertexSet = G.vertexSet := by
    intro L₁' L₂' hL₁' hL₂' hp₁ hp₂
    refine ⟨Subset.antisymm hL₁'.1.vertexSet_subset fun v hv ↦ ?_,
      Subset.antisymm hL₂'.1.vertexSet_subset fun v hv ↦ ?_⟩
    · by_contra h
      exact h2 ⟨L₁', L₂', hL₁', hL₂', hp₁, hp₂, v, hv, Or.inl h⟩
    · by_contra h
      exact h2 ⟨L₁', L₂', hL₁', hL₂', hp₁, hp₂, v, hv, Or.inr h⟩
  have hE : ∀ {L₁' L₂' : Hypergraph α β}, IsLinkage G L₁' → IsLinkage G L₂' →
      linkagePattern L₁' = linkagePattern L₁ → linkagePattern L₂' = linkagePattern L₂ →
      ∀ f, f ∈ L₁'.edgeSet → f ∉ L₂'.edgeSet := fun hL₁' hL₂' hp₁ hp₂ f h h' ↦
    h3 ⟨_, _, hL₁', hL₂', hp₁, hp₂, f, h, h'⟩
  have hU : L₁ ∪ L₂ = G := hI L₁ L₂ hL₁.1 hL₂.1 rfl rfl
  have hvital₁ : IsVitalPLinkage G L₁ p := by
    refine ⟨⟨hL₁.1, (hV hL₁.1 hL₂.1 rfl rfl).1, fun L' hL' hp ↦ ?_⟩, hL₁⟩
    have hU' : L' ∪ L₂ = G := hI L' L₂ hL' hL₂.1 hp rfl
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hL'.1 hL₁.1.1
      ((hV hL' hL₂.1 hp rfl).1.trans (hV hL₁.1 hL₂.1 rfl rfl).1.symm) ?_
    ext f
    constructor
    · intro hf
      have hfG : f ∈ G.edgeSet := hL'.1.edgeSet_subset hf
      rw [← hU] at hfG
      exact hfG.resolve_right (hE hL' hL₂.1 hp rfl f hf)
    · intro hf
      have hfG : f ∈ G.edgeSet := hL₁.1.1.edgeSet_subset hf
      rw [← hU'] at hfG
      exact hfG.resolve_right (hE hL₁.1 hL₂.1 rfl rfl f hf)
  have hvital₂ : IsVitalPLinkage G L₂ p := by
    refine ⟨⟨hL₂.1, (hV hL₁.1 hL₂.1 rfl rfl).2, fun L' hL' hp ↦ ?_⟩, hL₂⟩
    have hU' : L₁ ∪ L' = G := hI L₁ L' hL₁.1 hL' rfl hp
    refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hL'.1 hL₂.1.1
      ((hV hL₁.1 hL' rfl hp).2.trans (hV hL₁.1 hL₂.1 rfl rfl).2.symm) ?_
    ext f
    constructor
    · intro hf
      have hfG : f ∈ G.edgeSet := hL'.1.edgeSet_subset hf
      rw [← hU] at hfG
      exact hfG.resolve_left fun h ↦ hE hL₁.1 hL' rfl hp f h hf
    · intro hf
      have hfG : f ∈ G.edgeSet := hL₂.1.1.edgeSet_subset hf
      rw [← hU'] at hfG
      exact hfG.resolve_left fun h ↦ hE hL₁.1 hL₂.1 rfl rfl f h hf
  have hEmpty : (L₁ ∩ L₂).edgeSet = ∅ :=
    eq_empty_iff_forall_notMem.2 fun f hf ↦ hE hL₁.1 hL₂.1 rfl rfl f hf.1 hf.2
  have := hR G L₁ L₂ hG hvital₁ hvital₂ hU hEmpty
  exact (graphRank_le_ncard_edgeSet hG).trans (by exact_mod_cast this)

/-- **Graph Minors XXI, (11.1)**, as stated in `Results.lean`. -/
theorem theorem_11_1_proof (p : ℕ) :
    ∃ r : ℕ, ∀ {α : Type u} {β : Type v} (G L₁ L₂ : Hypergraph α β), G.IsGraph →
      IsPLinkage G L₁ p → IsPLinkage G L₂ p → IsIntertwining G L₁ L₂ → graphRank G ≤ r :=
  graphRank_le_of_isIntertwining p

end GM21
end GraphMinor
