module

public import GraphMinor.GM22.Section2

/-!
# Graph Minors XXII, Section 6: Rooted Digraphs

This file formalizes Section 6 (pages 542–545) of N. Robertson and P. D. Seymour,
*Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563:

- **6.1** (`theorem_6_1`): Every basis for a model of a rooted digraph of detail $\le \delta$
  with $q$ roots includes a basis of cardinality $\le q + 3\delta$.
- **6.2** (`theorem_6_2`): Replacing $L = \bigcup_{v \in V(H)} \phi(v)$ by a subgraph
  $L' \subseteq G \setminus \phi(E(H))$ with the same effect on a basis $Z$ yields a model $\phi'$.
- **6.3** (`theorem_6_3`): The rooted-digraph pasting lemma across a $Z$-division and a
  $Z'$-division whose pieces have the same $\delta$-folio.
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Graph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09

universe u v w u' v' uH vH

/-! ## 1. Universe-Polymorphic Transport for $\delta$-Folios -/

/-- Transporting a finite rooted digraph `R_H` across equivalences `V(H) ≃ Fin nv` and
`E(H) ≃ Fin ne` into `Type`. -/
private def reindexRootedDigraph {αH : Type uH} {βH : Type vH} {q nv ne : ℕ}
    (R_H : RootedDigraph αH βH q)
    (eV : ↥V(R_H.G.toGraph) ≃ Fin nv) (eE : ↥E(R_H.G.toGraph) ≃ Fin ne) :
    RootedDigraph (Fin nv) (Fin ne) q where
  G := {
    toGraph := {
      vertexSet := univ
      edgeSet := univ
      IsLink e x y := R_H.G.toGraph.IsLink (eE.symm e).1 (eV.symm x).1 (eV.symm y).1
      isLink_symm _ _ := ⟨fun _ _ h => h.symm⟩
      eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := by
        rcases R_H.G.toGraph.eq_or_eq_of_isLink_of_isLink h₁ h₂ with h | h
        · exact Or.inl (eV.symm.injective (Subtype.ext h))
        · exact Or.inr (eV.symm.injective (Subtype.ext h))
      edge_mem_iff_exists_isLink e := by
        simp only [mem_univ, true_iff]
        have he := (eE.symm e).2
        obtain ⟨u, v, hlink⟩ := R_H.G.toGraph.exists_isLink_of_mem_edgeSet he
        refine ⟨eV ⟨u, hlink.left_mem⟩, eV ⟨v, hlink.right_mem⟩, ?_⟩
        simpa using hlink
      left_mem_of_isLink _ _ _ _ := mem_univ _
    }
    head e := eV ⟨R_H.G.head (eE.symm e).1, (R_H.G.isLink_of_mem _ (eE.symm e).2).right_mem⟩
    tail e := eV ⟨R_H.G.tail (eE.symm e).1, (R_H.G.isLink_of_mem _ (eE.symm e).2).left_mem⟩
    isLink_of_mem e _ := by
      change R_H.G.toGraph.IsLink (eE.symm e).1 _ _
      simpa using R_H.G.isLink_of_mem (eE.symm e).1 (eE.symm e).2
  }
  roots i := eV ⟨R_H.roots i, R_H.roots_mem i⟩
  roots_mem _ := mem_univ _

private theorem reindexRootedDigraph_hasDetailLE {αH : Type uH} {βH : Type vH} {q nv ne δ : ℕ}
    (R_H : RootedDigraph αH βH q)
    (eV : ↥V(R_H.G.toGraph) ≃ Fin nv) (eE : ↥E(R_H.G.toGraph) ≃ Fin ne)
    (hdetail : R_H.HasDetailLE δ) :
    (reindexRootedDigraph R_H eV eE).HasDetailLE δ := by
  let R' := reindexRootedDigraph R_H eV eE
  have hV_fin : V(R'.G.toGraph).Finite := finite_univ
  have hE_fin : E(R'.G.toGraph).Finite := finite_univ
  refine ⟨hV_fin, hE_fin, ?_, ?_⟩
  · have hinj : Function.Injective (fun e : Fin ne => (eE.symm e).1) :=
      fun _ _ hxy => eE.symm.injective (Subtype.ext hxy)
    have himg : (fun e : Fin ne => (eE.symm e).1) '' E(R'.G.toGraph) ⊆ E(R_H.G.toGraph) := by
      rintro _ ⟨e, _, rfl⟩
      exact (eE.symm e).2
    calc E(R'.G.toGraph).ncard
      _ = ((fun e : Fin ne => (eE.symm e).1) '' E(R'.G.toGraph)).ncard :=
          (ncard_image_of_injective _ hinj).symm
      _ ≤ E(R_H.G.toGraph).ncard := ncard_le_ncard himg hdetail.2.1
      _ ≤ δ := hdetail.2.2.1
  · have hinj : Function.Injective (fun x : Fin nv => (eV.symm x).1) :=
      fun _ _ hxy => eV.symm.injective (Subtype.ext hxy)
    have himg : (fun x : Fin nv => (eV.symm x).1) '' (V(R'.G.toGraph) \ range R'.roots) ⊆
        V(R_H.G.toGraph) \ range R_H.roots := by
      rintro _ ⟨x, ⟨_, hx_not⟩, rfl⟩
      refine ⟨(eV.symm x).2, ?_⟩
      rintro ⟨i, hi⟩
      apply hx_not
      refine ⟨i, ?_⟩
      change eV ⟨R_H.roots i, R_H.roots_mem i⟩ = x
      have hsub : (⟨R_H.roots i, R_H.roots_mem i⟩ : ↥V(R_H.G.toGraph)) = eV.symm x :=
        Subtype.ext hi
      rw [hsub, eV.apply_symm_apply]
    have hfin_diff : (V(R_H.G.toGraph) \ range R_H.roots).Finite :=
      hdetail.1.subset sdiff_subset
    calc (V(R'.G.toGraph) \ range R'.roots).ncard
      _ = ((fun x : Fin nv => (eV.symm x).1) '' (V(R'.G.toGraph) \ range R'.roots)).ncard :=
          (ncard_image_of_injective _ hinj).symm
      _ ≤ (V(R_H.G.toGraph) \ range R_H.roots).ncard := ncard_le_ncard himg hfin_diff
      _ ≤ δ := hdetail.2.2.2

private theorem hasRootedDigraphModel_reindex_iff
    {α₁ : Type u} {β₁ : Type v} {αH : Type uH} {βH : Type vH} {q nv ne : ℕ}
    (R : RootedDigraph α₁ β₁ q) (R_H : RootedDigraph αH βH q)
    (hE_univ : E(R_H.G.toGraph) = univ)
    (eV : ↥V(R_H.G.toGraph) ≃ Fin nv) (eE : ↥E(R_H.G.toGraph) ≃ Fin ne) :
    HasRootedDigraphModel R R_H ↔
      HasRootedDigraphModel R (reindexRootedDigraph R_H eV eE) := by
  classical
  constructor
  · rintro ⟨φV, φE, hφ⟩
    refine ⟨fun x => φV (eV.symm x).1, fun e => φE (eE.symm e).1, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x _; exact hφ.subgraph_of_mem _ (eV.symm x).2
    · intro x _; exact hφ.connected_of_mem _ (eV.symm x).2
    · intro x _ y _ hxy
      apply hφ.disjoint_V _ (eV.symm x).2 _ (eV.symm y).2
      intro heq
      exact hxy (eV.symm.injective (Subtype.ext heq))
    · intro i
      dsimp [reindexRootedDigraph]
      rw [eV.symm_apply_apply]
      exact hφ.root_mem i
    · intro e _; exact hφ.edge_mem _ (eE.symm e).2
    · intro e₁ _ e₂ _ heq
      have hsub := hφ.injOn_E (eE.symm e₁).2 (eE.symm e₂).2 heq
      exact eE.symm.injective (Subtype.ext hsub)
    · intro e _ x _
      exact hφ.edge_not_mem_φV _ (eE.symm e).2 _ (eV.symm x).2
    · intro e _
      dsimp [reindexRootedDigraph]
      rw [eV.symm_apply_apply]
      exact hφ.head_mem _ (eE.symm e).2
    · intro e _
      dsimp [reindexRootedDigraph]
      rw [eV.symm_apply_apply]
      exact hφ.tail_mem _ (eE.symm e).2
  · rintro ⟨φV', φE', hφ'⟩
    have hV_univ' : ∀ x : Fin nv, x ∈ V((reindexRootedDigraph R_H eV eE).G.toGraph) :=
      fun x => mem_univ x
    have hE_univ' : ∀ e : Fin ne, e ∈ E((reindexRootedDigraph R_H eV eE).G.toGraph) :=
      fun e => mem_univ e
    refine ⟨fun v => if hv : v ∈ V(R_H.G.toGraph) then φV' (eV ⟨v, hv⟩) else ⊥,
      fun e => φE' (eE ⟨e, hE_univ ▸ mem_univ e⟩), ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro v hv; simp only [hv, ↓reduceDIte]; exact hφ'.subgraph_of_mem _ (hV_univ' _)
    · intro v hv; simp only [hv, ↓reduceDIte]; exact hφ'.connected_of_mem _ (hV_univ' _)
    · intro v₁ hv₁ v₂ hv₂ hne
      simp only [hv₁, hv₂, ↓reduceDIte]
      apply hφ'.disjoint_V _ (hV_univ' _) _ (hV_univ' _)
      intro heq
      exact hne (congr_arg Subtype.val (eV.injective heq))
    · intro i
      simp only [R_H.roots_mem i, ↓reduceDIte]
      exact hφ'.root_mem i
    · intro e _; exact hφ'.edge_mem _ (hE_univ' _)
    · intro e₁ _ e₂ _ heq
      have hsub := hφ'.injOn_E (hE_univ' _) (hE_univ' _) heq
      exact congr_arg Subtype.val (eE.injective hsub)
    · intro e _ v hv
      simp only [hv, ↓reduceDIte]
      exact hφ'.edge_not_mem_φV _ (hE_univ' _) _ (hV_univ' _)
    · intro e he
      have hhead : R_H.G.head e ∈ V(R_H.G.toGraph) :=
        (R_H.G.isLink_of_mem e he).right_mem
      simp only [hhead, ↓reduceDIte]
      have h := hφ'.head_mem (eE ⟨e, hE_univ ▸ mem_univ e⟩) (hE_univ' _)
      dsimp [reindexRootedDigraph] at h
      simpa [eE.symm_apply_apply] using h
    · intro e he
      have htail : R_H.G.tail e ∈ V(R_H.G.toGraph) :=
        (R_H.G.isLink_of_mem e he).left_mem
      simp only [htail, ↓reduceDIte]
      have h := hφ'.tail_mem (eE ⟨e, hE_univ ▸ mem_univ e⟩) (hE_univ' _)
      dsimp [reindexRootedDigraph] at h
      simpa [eE.symm_apply_apply] using h

/-- `HasSameDeltaFolio` applies to any rooted digraph `R_H` of detail `≤ δ` in arbitrary universes
whose edge set is `univ` on its edge type (for example when `βH` is the subtype of edges of `H`). -/
theorem HasSameDeltaFolio.iff_of_hasDetailLE
    {α₁ : Type u} {β₁ : Type v} {α₂ : Type u'} {β₂ : Type v'}
    {αH : Type uH} {βH : Type vH} {q δ : ℕ}
    {R₁ : RootedDigraph α₁ β₁ q} {R₂ : RootedDigraph α₂ β₂ q}
    (hfolio : HasSameDeltaFolio R₁ R₂ δ)
    (R_H : RootedDigraph αH βH q) (hE_univ : E(R_H.G.toGraph) = univ)
    (hdetail : R_H.HasDetailLE δ) :
    HasRootedDigraphModel R₁ R_H ↔ HasRootedDigraphModel R₂ R_H := by
  classical
  have _ : Fintype ↥V(R_H.G.toGraph) := hdetail.1.fintype
  have _ : Fintype ↥E(R_H.G.toGraph) := hdetail.2.1.fintype
  let eV := Fintype.equivFin ↥V(R_H.G.toGraph)
  let eE := Fintype.equivFin ↥E(R_H.G.toGraph)
  rw [hasRootedDigraphModel_reindex_iff R₁ R_H hE_univ eV eE,
    hasRootedDigraphModel_reindex_iff R₂ R_H hE_univ eV eE]
  exact hfolio (reindexRootedDigraph R_H eV eE) (reindexRootedDigraph_hasDetailLE R_H eV eE hdetail)

theorem HasSameDeltaFolio.refl {α : Type u} {β : Type v} {q δ : ℕ}
    (R : RootedDigraph α β q) : HasSameDeltaFolio R R δ :=
  fun _ _ => Iff.rfl

theorem HasSameDeltaFolio.symm {α₁ : Type u} {β₁ : Type v} {α₂ : Type u'} {β₂ : Type v'}
    {q δ : ℕ} {R₁ : RootedDigraph α₁ β₁ q} {R₂ : RootedDigraph α₂ β₂ q}
    (h : HasSameDeltaFolio R₁ R₂ δ) : HasSameDeltaFolio R₂ R₁ δ :=
  fun R_H hdetail => (h R_H hdetail).symm

/-! ## 2. Proof of 6.1 -/

/-- **Graph Minors XXII, 6.1** (Section 6, page 542):
"If $H$ has detail $\le \delta$, every basis for $\phi$ includes a basis of cardinality
$\le q + 3\delta$." -/
theorem theorem_6_1_proof {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q δ : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α}
    (hdetail : R_H.HasDetailLE δ)
    (hφ : IsRootedDigraphModel R_G R_H φV φE)
    (hZ : IsModelBasis R_G R_H φV φE Z) :
    ∃ Z₀ ⊆ Z, Z₀.Finite ∧ Z₀.ncard ≤ q + 3 * δ ∧ IsModelBasis R_G R_H φV φE Z₀ := by
  classical
  let S_roots : Set α := range R_G.roots
  let S_head : Set α := (fun e => R_G.G.head (φE e)) '' E(R_H.G.toGraph)
  let S_tail : Set α := (fun e => R_G.G.tail (φE e)) '' E(R_H.G.toGraph)
  have hfin_roots : S_roots.Finite := finite_range R_G.roots
  have hfin_head : S_head.Finite := hdetail.2.1.image _
  have hfin_tail : S_tail.Finite := hdetail.2.1.image _
  have hcard_roots : S_roots.ncard ≤ q := by
    have h := ncard_image_le (s := (univ : Set (Fin q))) (f := R_G.roots) finite_univ
    simpa [S_roots, image_univ, ncard_univ, Nat.card_fin] using h
  have hcard_head : S_head.ncard ≤ δ :=
    (ncard_image_le hdetail.2.1).trans hdetail.2.2.1
  have hcard_tail : S_tail.ncard ≤ δ :=
    (ncard_image_le hdetail.2.1).trans hdetail.2.2.1
  have hsub_roots : S_roots ⊆ Z := by
    rintro _ ⟨i, rfl⟩; exact hZ.roots_mem i
  have hsub_head : S_head ⊆ Z := by
    rintro _ ⟨e, he, rfl⟩; exact hZ.head_mem e he
  have hsub_tail : S_tail ⊆ Z := by
    rintro _ ⟨e, he, rfl⟩; exact hZ.tail_mem e he
  rcases (V(R_H.G.toGraph) \ range R_H.roots).eq_empty_or_nonempty with hempty | ⟨v₀, hv₀⟩
  · let Z₀ := S_roots ∪ S_head ∪ S_tail
    have hZ₀_sub : Z₀ ⊆ Z := union_subset (union_subset hsub_roots hsub_head) hsub_tail
    have hZ₀_fin : Z₀.Finite := (hfin_roots.union hfin_head).union hfin_tail
    have hZ₀_card : Z₀.ncard ≤ q + 3 * δ := by
      have h₁ : Z₀.ncard ≤ (S_roots ∪ S_head).ncard + S_tail.ncard :=
        ncard_union_le (S_roots ∪ S_head) S_tail
      have h₂ : (S_roots ∪ S_head).ncard ≤ S_roots.ncard + S_head.ncard :=
        ncard_union_le S_roots S_head
      omega
    refine ⟨Z₀, hZ₀_sub, hZ₀_fin, hZ₀_card, hZ₀_sub.trans hZ.subset_V,
      fun i => Or.inl (Or.inl (mem_range_self i)),
      fun e he => Or.inl (Or.inr (mem_image_of_mem _ he)),
      fun e he => Or.inr (mem_image_of_mem _ he), ?_⟩
    intro v hv
    have hv_root : v ∈ range R_H.roots := by
      by_contra hnot
      have : v ∈ V(R_H.G.toGraph) \ range R_H.roots := ⟨hv, hnot⟩
      rw [hempty] at this
      exact this
    obtain ⟨i, rfl⟩ := hv_root
    exact ⟨R_G.roots i, Or.inl (Or.inl (mem_range_self i)), hφ.root_mem i⟩
  · let z₀ : α := (hZ.inter_φV_nonempty v₀ hv₀.1).some
    let pickZ : αH → α := fun v =>
      if hv : v ∈ V(R_H.G.toGraph) then (hZ.inter_φV_nonempty v hv).some else z₀
    let S_vert : Set α := pickZ '' (V(R_H.G.toGraph) \ range R_H.roots)
    have hfin_diff : (V(R_H.G.toGraph) \ range R_H.roots).Finite :=
      hdetail.1.subset sdiff_subset
    have hfin_vert : S_vert.Finite := hfin_diff.image pickZ
    have hcard_vert : S_vert.ncard ≤ δ :=
      (ncard_image_le hfin_diff).trans hdetail.2.2.2
    have hsub_vert : S_vert ⊆ Z := by
      rintro _ ⟨v, ⟨hv, _⟩, rfl⟩
      simp only [pickZ, hv, ↓reduceDIte]
      exact (hZ.inter_φV_nonempty v hv).some_mem.1
    let Z₀ := S_roots ∪ S_head ∪ S_tail ∪ S_vert
    have hZ₀_sub : Z₀ ⊆ Z :=
      union_subset (union_subset (union_subset hsub_roots hsub_head) hsub_tail) hsub_vert
    have hZ₀_fin : Z₀.Finite :=
      ((hfin_roots.union hfin_head).union hfin_tail).union hfin_vert
    have hZ₀_card : Z₀.ncard ≤ q + 3 * δ := by
      have h₁ : Z₀.ncard ≤ (S_roots ∪ S_head ∪ S_tail).ncard + S_vert.ncard :=
        ncard_union_le (S_roots ∪ S_head ∪ S_tail) S_vert
      have h₂ : (S_roots ∪ S_head ∪ S_tail).ncard ≤ (S_roots ∪ S_head).ncard + S_tail.ncard :=
        ncard_union_le (S_roots ∪ S_head) S_tail
      have h₃ : (S_roots ∪ S_head).ncard ≤ S_roots.ncard + S_head.ncard :=
        ncard_union_le S_roots S_head
      omega
    refine ⟨Z₀, hZ₀_sub, hZ₀_fin, hZ₀_card, hZ₀_sub.trans hZ.subset_V,
      fun i => Or.inl (Or.inl (Or.inl (mem_range_self i))),
      fun e he => Or.inl (Or.inl (Or.inr (mem_image_of_mem _ he))),
      fun e he => Or.inl (Or.inr (mem_image_of_mem _ he)), ?_⟩
    intro v hv
    by_cases hv_root : v ∈ range R_H.roots
    · obtain ⟨i, rfl⟩ := hv_root
      exact ⟨R_G.roots i, Or.inl (Or.inl (Or.inl (mem_range_self i))), hφ.root_mem i⟩
    · refine ⟨pickZ v, Or.inr (mem_image_of_mem pickZ ⟨hv, hv_root⟩), ?_⟩
      simp only [pickZ, hv, ↓reduceDIte]
      exact (hZ.inter_φV_nonempty v hv).some_mem.2

/-! ## 3. Proof of 6.2 -/

/-- Distinct components `C₁ ≠ C₂` of a graph `G` have disjoint vertex sets and disjoint edge sets. -/
theorem isGraphComponent_disjoint {α : Type u} {β : Type v} {G C₁ C₂ : Graph α β}
    (h₁ : IsGraphComponent C₁ G) (h₂ : IsGraphComponent C₂ G) (hne : C₁ ≠ C₂) :
    Disjoint V(C₁) V(C₂) ∧ Disjoint E(C₁) E(C₂) := by
  refine ⟨disjoint_left.mpr fun x hx₁ hx₂ =>
    hne (isGraphComponent_eq_of_mem_inter h₁ h₂ ⟨x, hx₁, hx₂⟩),
    disjoint_left.mpr fun e he₁ he₂ => ?_⟩
  obtain ⟨x, y, hl₁⟩ := C₁.exists_isLink_of_mem_edgeSet he₁
  have hl₂ : C₂.IsLink e x y := (h₂.1.isLink_iff he₂).mpr (hl₁.mono h₁.1)
  exact hne (isGraphComponent_eq_of_mem_inter h₁ h₂ ⟨x, hl₁.left_mem, hl₂.left_mem⟩)

/-- If `φ` is a model of `R_H` in `R_G`, then for each `v ∈ V(H)`, `φV v` is a component of
`L = ⋃ (φV v : v ∈ V(H))`. -/
theorem IsRootedDigraphModel.isGraphComponent_subgraphSUnion
    {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β}
    (hφ : IsRootedDigraphModel R_G R_H φV φE)
    {v : αH} (hv : v ∈ V(R_H.G.toGraph)) :
    IsGraphComponent (φV v) (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))) := by
  let L := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
  have hle_fam : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨w, hw, rfl⟩; exact hφ.subgraph_of_mem w hw
  have hL_le : L ≤ R_G.G.toGraph := subgraphSUnion_le hle_fam
  have hφv_le_L : φV v ≤ L :=
    le_subgraphSUnion hle_fam (mem_image_of_mem φV hv)
  refine ⟨hφv_le_L, hφ.connected_of_mem v hv, ?_⟩
  intro C hφv_C hCL hC_conn
  -- Every walk in `L` starting in `V(φV v)` stays in `φV v`.
  have hwalk_stay : ∀ {a b : α} (W : GraphWalk L a b),
      a ∈ V(φV v) → b ∈ V(φV v) ∧ ∀ e ∈ W.edges, e ∈ E(φV v) := by
    intro a b W
    induction W with
    | nil _ => exact fun ha => ⟨ha, by simp⟩
    | @cons a₁ m₁ b₁ e hl rest ih =>
      intro ha₁
      have heL : e ∈ E(L) := hl.edge_mem
      rw [edgeSet_subgraphSUnion hle_fam] at heL
      obtain ⟨_, ⟨w, hw, rfl⟩, he_w⟩ := mem_iUnion₂.mp heL
      have hl_G : R_G.G.toGraph.IsLink e a₁ m₁ := hl.mono hL_le
      have hl_w : (φV w).IsLink e a₁ m₁ := ((hφ.subgraph_of_mem w hw).isLink_iff he_w).mpr hl_G
      have hvw : v = w := by
        by_contra hne
        exact disjoint_left.mp (hφ.disjoint_V v hv w hw hne).1 ha₁ hl_w.left_mem
      subst hvw
      have ⟨hb₁, hE_rest⟩ := ih hl_w.right_mem
      refine ⟨hb₁, ?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he_w
      · exact hE_rest f hf
  obtain ⟨u₀, hu₀⟩ := (hφ.connected_of_mem v hv).1
  have hu₀_C : u₀ ∈ V(C) := hφv_C.vertexSet_mono hu₀
  have hVC : V(C) ⊆ V(φV v) := by
    intro x hx
    obtain ⟨W⟩ := hC_conn.2 u₀ hu₀_C x hx
    obtain ⟨W_L, _, _⟩ := exists_walk_up_of_le hCL W
    exact (hwalk_stay W_L hu₀).1
  have hEC : E(C) ⊆ E(φV v) := by
    intro e he
    obtain ⟨x, y, hl⟩ := C.exists_isLink_of_mem_edgeSet he
    obtain ⟨W⟩ := hC_conn.2 u₀ hu₀_C x hl.left_mem
    let hW' : GraphWalk C u₀ y := W.append (.cons hl (.nil hl.right_mem))
    obtain ⟨W_L, _, hE_eq⟩ := exists_walk_up_of_le hCL hW'
    have he_mem : e ∈ W_L.edges := by
      rw [hE_eq]
      change e ∈ (W.append (.cons hl (.nil hl.right_mem))).edges
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ (by simp)
    exact (hwalk_stay W_L hu₀).2 e he_mem
  have hC_le_φv : C ≤ φV v :=
    (Compatible.of_le_le (hCL.trans hL_le) (hφ.subgraph_of_mem v hv)).le_iff.mpr ⟨hVC, hEC⟩
  exact le_antisymm hC_le_φv hφv_C

/-- **Graph Minors XXII, 6.2** (Section 6, page 542):
"Let $\phi$ be a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$, let $Z$ be a basis for
$\phi$, let $L = \bigcup(\phi(v) : v \in V(H))$, and let $L' \subseteq G \setminus \phi(E(H))$ with
the same effect on $Z$ as $L$. Define $\phi'(e) = \phi(e)$ ($e \in E(H)$), and for $v \in V(H)$ let
$\phi'(v)$ be the component $T$ of $L'$ with $V(T) \cap Z = V(\phi(v)) \cap Z$. Then $\phi'$ is a
model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$." -/
theorem theorem_6_2_proof {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α} {L' : Graph α β}
    (hφ : IsRootedDigraphModel R_G R_H φV φE)
    (hZ : IsModelBasis R_G R_H φV φE Z)
    (hL'_le : L' ≤ R_G.G.toGraph.deleteEdges (φE '' E(R_H.G.toGraph)))
    (heff : effectOn L' Z =
      effectOn (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))) Z) :
    ∃ φV' : αH → Graph α β,
      (∀ v ∈ V(R_H.G.toGraph),
        IsGraphComponent (φV' v) L' ∧ V(φV' v) ∩ Z = V(φV v) ∩ Z) ∧
      IsRootedDigraphModel R_G R_H φV' φE := by
  classical
  let L := subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph))
  have hex_comp : ∀ v ∈ V(R_H.G.toGraph),
      ∃ T : Graph α β, IsGraphComponent T L' ∧ V(T) ∩ Z = V(φV v) ∩ Z := by
    intro v hv
    have hcomp_L : IsGraphComponent (φV v) L := hφ.isGraphComponent_subgraphSUnion hv
    have hne : (V(φV v) ∩ Z).Nonempty := by
      rw [inter_comm]; exact hZ.inter_φV_nonempty v hv
    have hmem_eff : V(φV v) ∩ Z ∈ effectOn L Z := ⟨hne, φV v, hcomp_L, rfl⟩
    rw [← heff] at hmem_eff
    rcases hmem_eff with ⟨_, T, hT, hTZ⟩
    exact ⟨T, hT, hTZ.symm⟩
  let φV' : αH → Graph α β := fun v =>
    if hv : v ∈ V(R_H.G.toGraph) then (hex_comp v hv).choose else ⊥
  have hφV'_spec : ∀ v ∈ V(R_H.G.toGraph),
      IsGraphComponent (φV' v) L' ∧ V(φV' v) ∩ Z = V(φV v) ∩ Z := by
    intro v hv
    simp only [φV', hv, ↓reduceDIte]
    exact (hex_comp v hv).choose_spec
  have hL'_G : L' ≤ R_G.G.toGraph := hL'_le.trans deleteEdges_le
  refine ⟨φV', hφV'_spec, ?_, ?_, ?_, ?_, hφ.edge_mem, hφ.injOn_E, ?_, ?_, ?_⟩
  · intro v hv
    exact (hφV'_spec v hv).1.1.trans hL'_G
  · intro v hv
    exact (hφV'_spec v hv).1.2.1
  · intro v₁ hv₁ v₂ hv₂ hne
    obtain ⟨z, hzZ, hzv₁⟩ := hZ.inter_φV_nonempty v₁ hv₁
    have hzv₁' : z ∈ V(φV' v₁) := by
      have : z ∈ V(φV' v₁) ∩ Z := by rw [(hφV'_spec v₁ hv₁).2]; exact ⟨hzv₁, hzZ⟩
      exact this.1
    have hzv₂ : z ∉ V(φV v₂) :=
      disjoint_left.mp (hφ.disjoint_V v₁ hv₁ v₂ hv₂ hne).1 hzv₁
    have hzv₂' : z ∉ V(φV' v₂) := by
      intro hmem
      have : z ∈ V(φV v₂) ∩ Z := by rw [← (hφV'_spec v₂ hv₂).2]; exact ⟨hmem, hzZ⟩
      exact hzv₂ this.1
    have hne_comp : φV' v₁ ≠ φV' v₂ := fun heq => hzv₂' (heq ▸ hzv₁')
    exact isGraphComponent_disjoint (hφV'_spec v₁ hv₁).1 (hφV'_spec v₂ hv₂).1 hne_comp
  · intro i
    have hvi : R_H.roots i ∈ V(R_H.G.toGraph) := R_H.roots_mem i
    have hmem : R_G.roots i ∈ V(φV (R_H.roots i)) ∩ Z :=
      ⟨hφ.root_mem i, hZ.roots_mem i⟩
    rw [← (hφV'_spec _ hvi).2] at hmem
    exact hmem.1
  · intro e he v hv hmem
    have he_L' : φE e ∈ E(L') := (hφV'_spec v hv).1.1.edgeSet_mono hmem
    have he_del : φE e ∈ E(R_G.G.toGraph.deleteEdges (φE '' E(R_H.G.toGraph))) :=
      hL'_le.edgeSet_mono he_L'
    rw [edgeSet_deleteEdges] at he_del
    exact he_del.2 (mem_image_of_mem φE he)
  · intro e he
    have hv : R_H.G.head e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).right_mem
    have hmem : R_G.G.head (φE e) ∈ V(φV (R_H.G.head e)) ∩ Z :=
      ⟨hφ.head_mem e he, hZ.head_mem e he⟩
    rw [← (hφV'_spec _ hv).2] at hmem
    exact hmem.1
  · intro e he
    have hv' : R_H.G.tail e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).left_mem
    have hmem : R_G.G.tail (φE e) ∈ V(φV (R_H.G.tail e)) ∩ Z :=
      ⟨hφ.tail_mem e he, hZ.tail_mem e he⟩
    rw [← (hφV'_spec _ hv').2] at hmem
    exact hmem.1

/-! ## 4. Helper Lemmas on $Z$-Divisions and Proof of 6.3 -/

/-- If a walk `W` in `M ≤ G` starts in `V(A m)` and never visits `Z`, then all vertices and edges
of `W` belong to `A m`. -/
private theorem walk_in_piece_of_disjoint_Z
    {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    {G M : Graph α β} {Z : Set α} {A : ι → Graph α β}
    (hMG : M ≤ G) (hdiv : IsIndexedZDivision G Z A) (m : ι)
    {a b : α} (W : GraphWalk M a b) (ha : a ∈ V(A m))
    (hno_Z : ∀ x ∈ W.support, x ∉ Z) :
    (b ∈ V(A m) ∧ ∀ x ∈ W.support, x ∈ V(A m)) ∧ ∀ e ∈ W.edges, e ∈ E(A m) := by
  induction W with
  | nil _ =>
    exact ⟨⟨ha, by simp [ha]⟩, by simp⟩
  | @cons a₁ m₁ b₁ e hl rest ih =>
    have ha₁_not_Z : a₁ ∉ Z := hno_Z a₁ (by simp)
    have heG : e ∈ E(G) := hMG.edgeSet_mono hl.edge_mem
    rw [← hdiv.edgeSet_iUnion, mem_iUnion] at heG
    obtain ⟨j, he_Aj⟩ := heG
    have hl_Aj : (A j).IsLink e a₁ m₁ :=
      ((hdiv.1 j).isLink_iff he_Aj).mpr (hl.mono hMG)
    have hmj : m = j := by
      by_contra hne
      exact ha₁_not_Z ((hdiv.2.2 m j hne).2 ⟨ha, hl_Aj.left_mem⟩)
    subst hmj
    have ⟨⟨hb₁, hsupp⟩, hE⟩ := ih hl_Aj.right_mem (fun x hx => hno_Z x (List.mem_cons_of_mem _ hx))
    refine ⟨⟨hb₁, ?_⟩, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ha
      · exact hsupp x hx
    · intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he_Aj
      · exact hE f hf

/-- If `P ≤ G` is connected, `Disjoint V(P) Z`, and `V(P) ∩ V(A m)` is nonempty, then `P ≤ A m`. -/
theorem le_piece_of_connected_disjoint_Z
    {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    {G P : Graph α β} {Z : Set α} {A : ι → Graph α β}
    (hPG : P ≤ G) (hconn : IsGraphConnected P) (hdiv : IsIndexedZDivision G Z A)
    (hPZ : Disjoint V(P) Z) {m : ι} (hmeet : (V(P) ∩ V(A m)).Nonempty) :
    P ≤ A m := by
  obtain ⟨u₀, hu₀P, hu₀A⟩ := hmeet
  have hVP : V(P) ⊆ V(A m) := by
    intro x hx
    obtain ⟨W⟩ := hconn.2 u₀ hu₀P x hx
    have hno_Z : ∀ z ∈ W.support, z ∉ Z := fun z hz =>
      disjoint_left.mp hPZ (W.mem_vertexSet_of_mem_support hz)
    exact (walk_in_piece_of_disjoint_Z hPG hdiv m W hu₀A hno_Z).1.1
  have hEP : E(P) ⊆ E(A m) := by
    intro e he
    obtain ⟨x, y, hl⟩ := P.exists_isLink_of_mem_edgeSet he
    obtain ⟨W⟩ := hconn.2 u₀ hu₀P x hl.left_mem
    let hW' : GraphWalk P u₀ y := W.append (.cons hl (.nil hl.right_mem))
    have hno_Z : ∀ z ∈ hW'.support, z ∉ Z := fun z hz =>
      disjoint_left.mp hPZ (hW'.mem_vertexSet_of_mem_support hz)
    have hE := (walk_in_piece_of_disjoint_Z hPG hdiv m hW' hu₀A hno_Z).2
    apply hE e
    change e ∈ (W.append (.cons hl (.nil hl.right_mem))).edges
    rw [GraphWalk.edges_append]
    exact List.mem_append_right _ (by simp)
  exact (Compatible.of_le_le hPG (hdiv.1 m)).le_iff.mpr ⟨hVP, hEP⟩

/-- If `P` is a component of `M ∩ A m` with `Disjoint V(P) Z`, where `A` is a `Z`-division of `G`
and `M ≤ G`, then `P` is a component of `M`. -/
theorem isGraphComponent_of_component_subgraphInter_disjoint_Z
    {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    {G M : Graph α β} {Z : Set α} {A : ι → Graph α β}
    (hMG : M ≤ G) (hdiv : IsIndexedZDivision G Z A) (m : ι)
    {P : Graph α β} (hP : IsGraphComponent P (subgraphInter G M (A m)))
    (hPZ : Disjoint V(P) Z) :
    IsGraphComponent P M := by
  have hInter_le_M : subgraphInter G M (A m) ≤ M := subgraphInter_le_left hMG (hdiv.1 m)
  have hInter_le_A : subgraphInter G M (A m) ≤ A m := subgraphInter_le_right hMG (hdiv.1 m)
  refine ⟨hP.1.trans hInter_le_M, hP.2.1, ?_⟩
  intro C hPC hCM hC_conn
  -- Every walk in `M` starting in `V(P)` stays in `P` (hence never hits `Z`).
  have hwalk_in_P : ∀ {a b : α} (W : GraphWalk M a b),
      a ∈ V(P) → b ∈ V(P) ∧ ∀ e ∈ W.edges, e ∈ E(P) := by
    intro a b W
    induction W with
    | nil _ => exact fun ha => ⟨ha, by simp⟩
    | @cons a₁ m₁ b₁ e hl rest ih =>
      intro ha₁
      have ha₁_Am : a₁ ∈ V(A m) :=
        hInter_le_A.vertexSet_mono (hP.1.vertexSet_mono ha₁)
      have ha₁_not_Z : a₁ ∉ Z := disjoint_left.mp hPZ ha₁
      have heG : e ∈ E(G) := hMG.edgeSet_mono hl.edge_mem
      rw [← hdiv.edgeSet_iUnion, mem_iUnion] at heG
      obtain ⟨j, he_Aj⟩ := heG
      have hl_Aj : (A j).IsLink e a₁ m₁ :=
        ((hdiv.1 j).isLink_iff he_Aj).mpr (hl.mono hMG)
      have hmj : m = j := by
        by_contra hne
        exact ha₁_not_Z ((hdiv.2.2 m j hne).2 ⟨ha₁_Am, hl_Aj.left_mem⟩)
      subst hmj
      have he_Inter : e ∈ E(subgraphInter G M (A m)) := by
        rw [edgeSet_subgraphInter hMG (hdiv.1 m)]
        exact ⟨hl.edge_mem, he_Aj⟩
      have hl_Inter : (subgraphInter G M (A m)).IsLink e a₁ m₁ :=
        (hInter_le_M.isLink_iff he_Inter).mpr hl
      have hm₁_P : m₁ ∈ V(P) :=
        (mem_graphComponent_iff_of_isLink hP hl_Inter).mp ha₁
      have he_P : e ∈ E(P) :=
        (isClosedSubgraph_of_isGraphComponent hP).closed hl_Inter.inc_left ha₁
      have ⟨hb₁, hE_rest⟩ := ih hm₁_P
      refine ⟨hb₁, ?_⟩
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he_P
      · exact hE_rest f hf
  obtain ⟨u₀, hu₀P⟩ := hP.2.1.1
  have hu₀C : u₀ ∈ V(C) := hPC.vertexSet_mono hu₀P
  have hVC : V(C) ⊆ V(P) := by
    intro x hx
    obtain ⟨W⟩ := hC_conn.2 u₀ hu₀C x hx
    obtain ⟨W_M, _, _⟩ := exists_walk_up_of_le hCM W
    exact (hwalk_in_P W_M hu₀P).1
  have hEC : E(C) ⊆ E(P) := by
    intro e he
    obtain ⟨x, y, hl⟩ := C.exists_isLink_of_mem_edgeSet he
    obtain ⟨W⟩ := hC_conn.2 u₀ hu₀C x hl.left_mem
    let hW' : GraphWalk C u₀ y := W.append (.cons hl (.nil hl.right_mem))
    obtain ⟨W_M, _, hE_eq⟩ := exists_walk_up_of_le hCM hW'
    have he_mem : e ∈ W_M.edges := by
      rw [hE_eq]
      change e ∈ (W.append (.cons hl (.nil hl.right_mem))).edges
      rw [GraphWalk.edges_append]
      exact List.mem_append_right _ (by simp)
    exact (hwalk_in_P W_M hu₀P).2 e he_mem
  have hC_le_P : C ≤ P :=
    (Compatible.of_le_le (hCM.trans hMG)
      ((hP.1.trans hInter_le_M).trans hMG)).le_iff.mpr ⟨hVC, hEC⟩
  exact le_antisymm hC_le_P hPC

/-! ## 5. Proof of 6.3 (Claims (1)–(10)) -/

/-- The minimal subgraph $L \subseteq G$ such that $Z \subseteq V(L)$ and $\phi(v) \subseteq L$
for each $v \in V(H)$. -/
def minimalModelSubgraph {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q : ℕ}
    (R_G : RootedDigraph α β q) (R_H : RootedDigraph αH βH q)
    (φV : αH → Graph α β) (Z : Set α) : Graph α β :=
  subgraphUnion R_G.G.toGraph (Graph.noEdge Z β)
    (subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)))

theorem minimalModelSubgraph_le {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α}
    (hZ : Z ⊆ V(R_G.G.toGraph)) (hφ : IsRootedDigraphModel R_G R_H φV φE) :
    minimalModelSubgraph R_G R_H φV Z ≤ R_G.G.toGraph := by
  have hle_fam : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩; exact hφ.subgraph_of_mem v hv
  exact subgraphUnion_le (Graph.noEdge_le_iff.mpr hZ) (subgraphSUnion_le hle_fam)

theorem vertexSet_minimalModelSubgraph {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH}
    {q : ℕ} (R_G : RootedDigraph α β q) (R_H : RootedDigraph αH βH q)
    (φV : αH → Graph α β) (Z : Set α) :
    V(minimalModelSubgraph R_G R_H φV Z) = Z ∪ ⋃ v ∈ V(R_H.G.toGraph), V(φV v) := by
  simp [minimalModelSubgraph, vertexSet_subgraphUnion, vertexSet_subgraphSUnion]

theorem edgeSet_minimalModelSubgraph {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH}
    {q : ℕ} {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α}
    (hZ : Z ⊆ V(R_G.G.toGraph)) (hφ : IsRootedDigraphModel R_G R_H φV φE) :
    E(minimalModelSubgraph R_G R_H φV Z) = ⋃ v ∈ V(R_H.G.toGraph), E(φV v) := by
  have hle_fam : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩; exact hφ.subgraph_of_mem v hv
  rw [minimalModelSubgraph,
    edgeSet_subgraphUnion (Graph.noEdge_le_iff.mpr hZ) (subgraphSUnion_le hle_fam),
    edgeSet_subgraphSUnion hle_fam]
  simp

/-- **Graph Minors XXII, 6.3 Claim (1)** (Section 6, page 543):
"For each $v \in V(H)$, $\phi(v)$ is a component of $L$, and every other component of $L$ is an
isolated vertex in $Z$." -/
theorem lemma_6_3_claim_1 {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH} {q : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α}
    (hZ : Z ⊆ V(R_G.G.toGraph)) (hφ : IsRootedDigraphModel R_G R_H φV φE) :
    let L := minimalModelSubgraph R_G R_H φV Z
    (∀ v ∈ V(R_H.G.toGraph), IsGraphComponent (φV v) L) ∧
      (∀ P : Graph α β, IsGraphComponent P L →
        (∃ v ∈ V(R_H.G.toGraph), P = φV v) ∨ (∃ z ∈ Z, P = Graph.noEdge {z} β)) ∧
      (∀ x y : α, AreConnectedIn L x y ↔
        (x ∈ Z ∧ x = y) ∨ ∃ v ∈ V(R_H.G.toGraph), x ∈ V(φV v) ∧ y ∈ V(φV v)) := by
  intro L
  have hL_le : L ≤ R_G.G.toGraph := minimalModelSubgraph_le hZ hφ
  have hle_fam : ∀ P ∈ φV '' V(R_H.G.toGraph), P ≤ R_G.G.toGraph := by
    rintro _ ⟨v, hv, rfl⟩; exact hφ.subgraph_of_mem v hv
  have hSUnion_le_L : subgraphSUnion R_G.G.toGraph (φV '' V(R_H.G.toGraph)) ≤ L :=
    le_subgraphUnion_right (Graph.noEdge_le_iff.mpr hZ) (subgraphSUnion_le hle_fam)
  -- Helper: any step of `L` from `x` to `y` along `e` means `e ∈ E(φV v)` and `x, y ∈ V(φV v)`.
  have hstep_L : ∀ {e : β} {x y : α}, L.IsLink e x y →
      ∃ v ∈ V(R_H.G.toGraph), (φV v).IsLink e x y := by
    intro e x y hl
    have he : e ∈ E(L) := hl.edge_mem
    rw [edgeSet_minimalModelSubgraph hZ hφ] at he
    obtain ⟨v, hv, he_v⟩ := mem_iUnion₂.mp he
    exact ⟨v, hv, ((hφ.subgraph_of_mem v hv).isLink_iff he_v).mpr (hl.mono hL_le)⟩
  -- Walk invariance in `L`: a walk starting in `V(φV v)` stays in `φV v`.
  have hwalk_φV : ∀ {v : αH} (hv : v ∈ V(R_H.G.toGraph)) {a b : α} (W : GraphWalk L a b),
      a ∈ V(φV v) → b ∈ V(φV v) ∧ ∀ e ∈ W.edges, e ∈ E(φV v) := by
    intro v hv a b W
    induction W with
    | nil _ => exact fun ha => ⟨ha, by simp⟩
    | @cons a₁ m₁ b₁ e hl rest ih =>
      intro ha₁
      obtain ⟨w, hw, hl_w⟩ := hstep_L hl
      have hvw : v = w := by
        by_contra hne
        exact disjoint_left.mp (hφ.disjoint_V v hv w hw hne).1 ha₁ hl_w.left_mem
      subst hvw
      have ⟨hb₁, hE⟩ := ih hl_w.right_mem
      refine ⟨hb₁, fun f hf => ?_⟩
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hl_w.edge_mem
      · exact hE f hf
  have hcomp_φV : ∀ v ∈ V(R_H.G.toGraph), IsGraphComponent (φV v) L := by
    intro v hv
    have hφv_L : φV v ≤ L :=
      (le_subgraphSUnion hle_fam (mem_image_of_mem φV hv)).trans hSUnion_le_L
    refine ⟨hφv_L, hφ.connected_of_mem v hv, ?_⟩
    intro C hφv_C hCL hC_conn
    obtain ⟨u₀, hu₀⟩ := (hφ.connected_of_mem v hv).1
    have hu₀C : u₀ ∈ V(C) := hφv_C.vertexSet_mono hu₀
    have hVC : V(C) ⊆ V(φV v) := by
      intro x hx
      obtain ⟨W⟩ := hC_conn.2 u₀ hu₀C x hx
      obtain ⟨W_L, _, _⟩ := exists_walk_up_of_le hCL W
      exact (hwalk_φV hv W_L hu₀).1
    have hEC : E(C) ⊆ E(φV v) := by
      intro e he
      obtain ⟨x, y, hl⟩ := C.exists_isLink_of_mem_edgeSet he
      obtain ⟨W⟩ := hC_conn.2 u₀ hu₀C x hl.left_mem
      let hW' : GraphWalk C u₀ y := W.append (.cons hl (.nil hl.right_mem))
      obtain ⟨W_L, _, hE_eq⟩ := exists_walk_up_of_le hCL hW'
      have he_mem : e ∈ W_L.edges := by
        rw [hE_eq]
        change e ∈ (W.append (.cons hl (.nil hl.right_mem))).edges
        rw [GraphWalk.edges_append]
        exact List.mem_append_right _ (by simp)
      exact (hwalk_φV hv W_L hu₀).2 e he_mem
    have hC_le : C ≤ φV v :=
      (Compatible.of_le_le (hCL.trans hL_le) (hφ.subgraph_of_mem v hv)).le_iff.mpr ⟨hVC, hEC⟩
    exact le_antisymm hC_le hφv_C
  have hother : ∀ P : Graph α β, IsGraphComponent P L →
      (∃ v ∈ V(R_H.G.toGraph), P = φV v) ∨ (∃ z ∈ Z, P = Graph.noEdge {z} β) := by
    intro P hP
    obtain ⟨x, hxP⟩ := hP.2.1.1
    have hxL : x ∈ V(L) := hP.1.vertexSet_mono hxP
    rw [vertexSet_minimalModelSubgraph] at hxL
    by_cases hx_φ : ∃ v ∈ V(R_H.G.toGraph), x ∈ V(φV v)
    · obtain ⟨v, hv, hxv⟩ := hx_φ
      exact Or.inl ⟨v, hv, isGraphComponent_eq_of_mem_inter hP (hcomp_φV v hv) ⟨x, hxP, hxv⟩⟩
    · push Not at hx_φ
      have hxZ : x ∈ Z := by
        rcases hxL with hxZ | hxU
        · exact hxZ
        · obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.mp hxU
          exact (hx_φ v hv hxv).elim
      refine Or.inr ⟨x, hxZ, ?_⟩
      have hnoEdge_le_P : Graph.noEdge {x} β ≤ P :=
        Graph.noEdge_le_iff.mpr (singleton_subset_iff.mpr hxP)
      have hVP : V(P) ⊆ {x} := by
        intro y hy
        rw [mem_singleton_iff]
        obtain ⟨W⟩ := hP.2.1.2 x hxP y hy
        cases W with
        | nil _ => rfl
        | @cons _ m _ e hl _ =>
          obtain ⟨v, hv, hl_v⟩ := hstep_L (hl.mono hP.1)
          exact (hx_φ v hv hl_v.left_mem).elim
      have hEP : E(P) ⊆ ∅ := by
        intro e he
        obtain ⟨a, b, hl⟩ := P.exists_isLink_of_mem_edgeSet he
        have ha : a = x := hVP hl.left_mem
        subst ha
        obtain ⟨v, hv, hl_v⟩ := hstep_L (hl.mono hP.1)
        exact hx_φ v hv hl_v.left_mem
      have hP_le : P ≤ Graph.noEdge {x} β :=
        (Compatible.of_le_le (hP.1.trans hL_le)
          ((hnoEdge_le_P.trans hP.1).trans hL_le)).le_iff.mpr ⟨hVP, hEP⟩
      exact le_antisymm hP_le hnoEdge_le_P
  refine ⟨hcomp_φV, hother, ?_⟩
  intro x y
  constructor
  · rintro ⟨C, hC, hxC, hyC⟩
    rcases hother C hC with ⟨v, hv, rfl⟩ | ⟨z, hz, rfl⟩
    · exact Or.inr ⟨v, hv, hxC, hyC⟩
    · change x ∈ ({z} : Set α) at hxC
      change y ∈ ({z} : Set α) at hyC
      rw [mem_singleton_iff] at hxC hyC
      subst hxC hyC
      exact Or.inl ⟨hz, rfl⟩
  · rintro (⟨hxZ, rfl⟩ | ⟨v, hv, hxv, hyv⟩)
    · rw [areConnectedIn_self_iff, vertexSet_minimalModelSubgraph]
      exact Or.inl hxZ
    · exact ⟨φV v, hcomp_φV v hv, hxv, hyv⟩

/-- The auxiliary rooted digraph `(J, P_1, ..., P_t)` in Claim (2) of **6.3** for piece `A i.succ`,
with vertex set the subtype of components of `L_i = L ∩ A_{i+1}` and edge set the subtype of
`φ(E(H)) ∩ E(A_{i+1})`. Its `j`-th root is the component of `L_i` that contains the `j`-th term
of `π_i`. The print (page 543) says "for $1 \le j \le t$ let $P_i$ be the component of $L_i$ with
$p_i \in V(P_i)$", a misprint for $P_j$ and $p_j$, and the proof of Claim (5) (page 544) has the
same slip. The Lean uses $P_j$ and $p_j$ (see the correction to the proof of (6.3) in
`corrections/GM22.md`). -/
noncomputable def rootedDigraphJ {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH}
    {q n_i : ℕ}
    (R_G : RootedDigraph α β q) (R_H : RootedDigraph αH βH q)
    (φV : αH → Graph α β) (φE : βH → β) (Z : Set α)
    (A_i : Graph α β) (hA_i : A_i ≤ R_G.G.toGraph)
    (π_i : Fin n_i → α) (hπ_i : ∀ j : Fin n_i, π_i j ∈ Z ∩ V(A_i))
    (hZ : Z ⊆ V(R_G.G.toGraph)) (hφ : IsRootedDigraphModel R_G R_H φV φE) :
    let L := minimalModelSubgraph R_G R_H φV Z
    let L_i := subgraphInter R_G.G.toGraph L A_i
    RootedDigraph ↥{P : Graph α β | IsGraphComponent P L_i}
      ↥((φE '' E(R_H.G.toGraph)) ∩ E(A_i)) n_i := by
  intro L L_i
  have hL_le : L ≤ R_G.G.toGraph := minimalModelSubgraph_le hZ hφ
  have hhead_mem : ∀ e : ↥((φE '' E(R_H.G.toGraph)) ∩ E(A_i)),
      R_G.G.head e.1 ∈ V(L_i) := by
    rintro ⟨e, ⟨f, hf, rfl⟩, he_Ai⟩
    rw [vertexSet_subgraphInter]
    have hl_Ai : A_i.IsLink (φE f) (R_G.G.tail (φE f)) (R_G.G.head (φE f)) :=
      (hA_i.isLink_iff he_Ai).mpr (R_G.G.isLink_of_mem _ (hA_i.edgeSet_mono he_Ai))
    refine ⟨?_, hl_Ai.right_mem⟩
    rw [vertexSet_minimalModelSubgraph]
    exact Or.inr (mem_iUnion₂.mpr ⟨R_H.G.head f,
      (R_H.G.isLink_of_mem f hf).right_mem, hφ.head_mem f hf⟩)
  have htail_mem : ∀ e : ↥((φE '' E(R_H.G.toGraph)) ∩ E(A_i)),
      R_G.G.tail e.1 ∈ V(L_i) := by
    rintro ⟨e, ⟨f, hf, rfl⟩, he_Ai⟩
    rw [vertexSet_subgraphInter]
    have hl_Ai : A_i.IsLink (φE f) (R_G.G.tail (φE f)) (R_G.G.head (φE f)) :=
      (hA_i.isLink_iff he_Ai).mpr (R_G.G.isLink_of_mem _ (hA_i.edgeSet_mono he_Ai))
    refine ⟨?_, hl_Ai.left_mem⟩
    rw [vertexSet_minimalModelSubgraph]
    exact Or.inr (mem_iUnion₂.mpr ⟨R_H.G.tail f,
      (R_H.G.isLink_of_mem f hf).left_mem, hφ.tail_mem f hf⟩)
  have hroot_mem : ∀ j : Fin n_i, π_i j ∈ V(L_i) := by
    intro j
    rw [vertexSet_subgraphInter]
    refine ⟨?_, (hπ_i j).2⟩
    rw [vertexSet_minimalModelSubgraph]
    exact Or.inl (hπ_i j).1
  let headJ : ↥((φE '' E(R_H.G.toGraph)) ∩ E(A_i)) → ↥{P : Graph α β | IsGraphComponent P L_i} :=
    fun e => ⟨compOf L_i (R_G.G.head e.1), isGraphComponent_compOf (hhead_mem e)⟩
  let tailJ : ↥((φE '' E(R_H.G.toGraph)) ∩ E(A_i)) → ↥{P : Graph α β | IsGraphComponent P L_i} :=
    fun e => ⟨compOf L_i (R_G.G.tail e.1), isGraphComponent_compOf (htail_mem e)⟩
  exact {
    G := {
      toGraph := {
        vertexSet := univ
        edgeSet := univ
        IsLink e P Q := (P = tailJ e ∧ Q = headJ e) ∨ (P = headJ e ∧ Q = tailJ e)
        isLink_symm _ _ := ⟨fun _ _ h => by
          rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
          · exact Or.inr ⟨h₂, h₁⟩
          · exact Or.inl ⟨h₂, h₁⟩⟩
        eq_or_eq_of_isLink_of_isLink _ _ _ _ _ h₁ h₂ := by
          rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
        edge_mem_iff_exists_isLink e := by
          simp only [mem_univ, true_iff]
          exact ⟨tailJ e, headJ e, Or.inl ⟨rfl, rfl⟩⟩
        left_mem_of_isLink _ _ _ _ := mem_univ _
      }
      head := headJ
      tail := tailJ
      isLink_of_mem e _ := Or.inl ⟨rfl, rfl⟩
    }
    roots j := ⟨compOf L_i (π_i j), isGraphComponent_compOf (hroot_mem j)⟩
    roots_mem _ := mem_univ _
  }

/-- **Graph Minors XXII, 6.3 Claim (2)** (Section 6, page 543):
"$(J, P_1, \ldots, P_t)$ has detail $\le \delta$, and there is a model of it in $(A_i, \pi_i)$." -/
theorem lemma_6_3_claim_2 {α : Type u} {β : Type v} {αH : Type uH} {βH : Type vH}
    {q k δ : ℕ}
    {R_G : RootedDigraph α β q} {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α}
    {A : Fin (k + 1) → Graph α β}
    {n : Fin k → ℕ} {π : ∀ i : Fin k, Fin (n i) → α}
    (hZ : Z ⊆ V(R_G.G.toGraph))
    (hroots_Z : ∀ r : Fin q, R_G.roots r ∈ Z)
    (hdiv : IsIndexedZDivision R_G.G.toGraph Z A)
    (hπ : ∀ i : Fin k, IsOrderingOf (Z ∩ V(A i.succ)) (π i))
    (hdetail : R_H.HasDetailLE δ)
    (hφ : IsRootedDigraphModel R_G R_H φV φE)
    (i : Fin k) :
    let hπ_mem : ∀ j : Fin (n i), π i j ∈ Z ∩ V(A i.succ) :=
      fun j => (hπ i).2 ▸ mem_range_self j
    let R_J := rootedDigraphJ R_G R_H φV φE Z (A i.succ) (hdiv.1 i.succ) (π i) hπ_mem hZ hφ
    let R_Ai := subRootedDigraph R_G.G (A i.succ) (hdiv.1 i.succ) (π i) (fun j => (hπ_mem j).2)
    R_J.HasDetailLE δ ∧ HasRootedDigraphModel R_Ai R_J := by
  intro hπ_mem R_J R_Ai
  let L := minimalModelSubgraph R_G R_H φV Z
  let L_i := subgraphInter R_G.G.toGraph L (A i.succ)
  have hL_le : L ≤ R_G.G.toGraph := minimalModelSubgraph_le hZ hφ
  have hLi_le_Ai : L_i ≤ A i.succ := subgraphInter_le_right hL_le (hdiv.1 i.succ)
  have ⟨hcomp_φV, hother_L, _⟩ := lemma_6_3_claim_1 hZ hφ
  -- Step 1: Every non-root vertex `P` of `R_J` satisfies `P.1 = φV v` for some `v ∈ V(H) \ range R_H.roots`.
  have hnonroot_sub :
      Subtype.val '' (V(R_J.G.toGraph) \ range R_J.roots) ⊆
        φV '' (V(R_H.G.toGraph) \ range R_H.roots) := by
    rintro _ ⟨⟨P, hP_comp⟩, ⟨_, hP_not_root⟩, rfl⟩
    have hPZ : Disjoint V(P) Z := by
      rw [disjoint_left]
      intro z hzP hzZ
      have hz_Ai : z ∈ V(A i.succ) := hLi_le_Ai.vertexSet_mono (hP_comp.1.vertexSet_mono hzP)
      have hz_range : z ∈ range (π i) := by rw [(hπ i).2]; exact ⟨hzZ, hz_Ai⟩
      obtain ⟨j, rfl⟩ := hz_range
      apply hP_not_root
      refine ⟨j, Subtype.ext ?_⟩
      have hπj_Li : π i j ∈ V(L_i) := hP_comp.1.vertexSet_mono hzP
      exact isGraphComponent_eq_of_mem_inter
        (isGraphComponent_compOf hπj_Li) hP_comp ⟨π i j, self_mem_reachSet hπj_Li, hzP⟩
    have hP_comp_L : IsGraphComponent P L :=
      isGraphComponent_of_component_subgraphInter_disjoint_Z hL_le hdiv i.succ hP_comp hPZ
    rcases hother_L P hP_comp_L with ⟨v, hv, rfl⟩ | ⟨z, hzZ, rfl⟩
    · refine ⟨v, ⟨hv, ?_⟩, rfl⟩
      rintro ⟨r, rfl⟩
      exact disjoint_left.mp hPZ (hφ.root_mem r) (hroots_Z r)
    · exfalso
      exact disjoint_left.mp hPZ (mem_singleton z) hzZ
  -- Step 2: `R_J.HasDetailLE δ`.
  have hfin_diff_H : (V(R_H.G.toGraph) \ range R_H.roots).Finite :=
    hdetail.1.subset sdiff_subset
  have hfin_img_φV : (φV '' (V(R_H.G.toGraph) \ range R_H.roots)).Finite :=
    hfin_diff_H.image φV
  have hinj_val_V : InjOn Subtype.val (V(R_J.G.toGraph) \ range R_J.roots) :=
    Subtype.val_injective.injOn
  have hfin_nonroot_J : (V(R_J.G.toGraph) \ range R_J.roots).Finite :=
    (hfin_img_φV.subset hnonroot_sub).of_finite_image hinj_val_V
  have hfin_VJ : V(R_J.G.toGraph).Finite := by
    have hsub : V(R_J.G.toGraph) ⊆ range R_J.roots ∪ (V(R_J.G.toGraph) \ range R_J.roots) := by
      intro x hx
      by_cases h : x ∈ range R_J.roots
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    exact ((finite_range R_J.roots).union hfin_nonroot_J).subset hsub
  have hsub_EJ : Subtype.val '' E(R_J.G.toGraph) ⊆ φE '' E(R_H.G.toGraph) := by
    rintro _ ⟨⟨e, he_img, _⟩, _, rfl⟩
    exact he_img
  have hfin_img_φE : (φE '' E(R_H.G.toGraph)).Finite := hdetail.2.1.image φE
  have hinj_val_E : InjOn Subtype.val E(R_J.G.toGraph) := Subtype.val_injective.injOn
  have hfin_EJ : E(R_J.G.toGraph).Finite :=
    (hfin_img_φE.subset hsub_EJ).of_finite_image hinj_val_E
  have hcard_EJ : E(R_J.G.toGraph).ncard ≤ δ := by
    calc E(R_J.G.toGraph).ncard
      _ = (Subtype.val '' E(R_J.G.toGraph)).ncard :=
          (ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (φE '' E(R_H.G.toGraph)).ncard := ncard_le_ncard hsub_EJ hfin_img_φE
      _ ≤ E(R_H.G.toGraph).ncard := ncard_image_le hdetail.2.1
      _ ≤ δ := hdetail.2.2.1
  have hcard_VJ : (V(R_J.G.toGraph) \ range R_J.roots).ncard ≤ δ := by
    calc (V(R_J.G.toGraph) \ range R_J.roots).ncard
      _ = (Subtype.val '' (V(R_J.G.toGraph) \ range R_J.roots)).ncard :=
          (ncard_image_of_injective _ Subtype.val_injective).symm
      _ ≤ (φV '' (V(R_H.G.toGraph) \ range R_H.roots)).ncard :=
          ncard_le_ncard hnonroot_sub hfin_img_φV
      _ ≤ (V(R_H.G.toGraph) \ range R_H.roots).ncard := ncard_image_le hfin_diff_H
      _ ≤ δ := hdetail.2.2.2
  refine ⟨⟨hfin_VJ, hfin_EJ, hcard_EJ, hcard_VJ⟩, ?_⟩
  -- Step 3: `ψ(P) = P.1` and `ψ(e) = e.1` is a model of `R_J` in `R_Ai`.
  refine ⟨fun P => P.1, fun e => e.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P _
    exact P.2.1.trans hLi_le_Ai
  · intro P _
    exact P.2.2.1
  · intro P₁ _ P₂ _ hne
    exact isGraphComponent_disjoint P₁.2 P₂.2 (fun h => hne (Subtype.ext h))
  · intro j
    have hπj_Li : π i j ∈ V(L_i) := by
      rw [vertexSet_subgraphInter]
      refine ⟨?_, (hπ_mem j).2⟩
      rw [vertexSet_minimalModelSubgraph]
      exact Or.inl (hπ_mem j).1
    exact self_mem_reachSet hπj_Li
  · intro e _
    exact e.2.2
  · intro e₁ _ e₂ _ heq
    exact Subtype.ext heq
  · intro e _ P _ hmem
    obtain ⟨f, hf, hfe⟩ := e.2.1
    have he_L : e.1 ∈ E(L) :=
      (subgraphInter_le_left hL_le (hdiv.1 i.succ)).edgeSet_mono (P.2.1.edgeSet_mono hmem)
    rw [edgeSet_minimalModelSubgraph hZ hφ] at he_L
    obtain ⟨v, hv, he_v⟩ := mem_iUnion₂.mp he_L
    exact hφ.edge_not_mem_φV f hf v hv (hfe ▸ he_v)
  · intro e _
    obtain ⟨f, hf, hfe⟩ := e.2.1
    have hhead_Li : R_G.G.head e.1 ∈ V(L_i) := by
      rw [vertexSet_subgraphInter]
      have hl_Ai : (A i.succ).IsLink e.1 (R_G.G.tail e.1) (R_G.G.head e.1) :=
        ((hdiv.1 i.succ).isLink_iff e.2.2).mpr
          (R_G.G.isLink_of_mem _ ((hdiv.1 i.succ).edgeSet_mono e.2.2))
      refine ⟨?_, hl_Ai.right_mem⟩
      rw [vertexSet_minimalModelSubgraph, ← hfe]
      exact Or.inr (mem_iUnion₂.mpr ⟨R_H.G.head f,
        (R_H.G.isLink_of_mem f hf).right_mem, hφ.head_mem f hf⟩)
    exact self_mem_reachSet hhead_Li
  · intro e _
    obtain ⟨f, hf, hfe⟩ := e.2.1
    have htail_Li : R_G.G.tail e.1 ∈ V(L_i) := by
      rw [vertexSet_subgraphInter]
      have hl_Ai : (A i.succ).IsLink e.1 (R_G.G.tail e.1) (R_G.G.head e.1) :=
        ((hdiv.1 i.succ).isLink_iff e.2.2).mpr
          (R_G.G.isLink_of_mem _ ((hdiv.1 i.succ).edgeSet_mono e.2.2))
      refine ⟨?_, hl_Ai.left_mem⟩
      rw [vertexSet_minimalModelSubgraph, ← hfe]
      exact Or.inr (mem_iUnion₂.mpr ⟨R_H.G.tail f,
        (R_H.G.isLink_of_mem f hf).left_mem, hφ.tail_mem f hf⟩)
    exact self_mem_reachSet htail_Li

/-- If `ψ_i` is a model of `R_J` in `(A'_{i+1}, π'_i)`, then for any component `P` of `L_i` and
any `j : Fin (n i)`, `π i j ∈ V(P)` if and only if `π' i j ∈ V(ψ_i(P))` (Claim (3)(i) of **6.3**). -/
theorem lemma_6_3_claim_3_root_iff
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {αH : Type uH} {βH : Type vH} {q n_i : ℕ}
    {R_G : RootedDigraph α β q} {R_G' : RootedDigraph α' β' q}
    {R_H : RootedDigraph αH βH q}
    {φV : αH → Graph α β} {φE : βH → β} {Z : Set α}
    {A_i : Graph α β} (hA_i : A_i ≤ R_G.G.toGraph)
    {A'_i : Graph α' β'} (hA'_i : A'_i ≤ R_G'.G.toGraph)
    {π_i : Fin n_i → α} (hπ_i : ∀ j : Fin n_i, π_i j ∈ Z ∩ V(A_i))
    {π'_i : Fin n_i → α'} (hπ'_i : ∀ j : Fin n_i, π'_i j ∈ V(A'_i))
    (hZ : Z ⊆ V(R_G.G.toGraph)) (hφ : IsRootedDigraphModel R_G R_H φV φE)
    {ψV : ↥{P : Graph α β | IsGraphComponent P (subgraphInter R_G.G.toGraph
      (minimalModelSubgraph R_G R_H φV Z) A_i)} → Graph α' β'}
    {ψE : ↥((φE '' E(R_H.G.toGraph)) ∩ E(A_i)) → β'}
    (hψ : IsRootedDigraphModel (subRootedDigraph R_G'.G A'_i hA'_i π'_i hπ'_i)
      (rootedDigraphJ R_G R_H φV φE Z A_i hA_i π_i hπ_i hZ hφ) ψV ψE)
    (P : ↥{P : Graph α β | IsGraphComponent P (subgraphInter R_G.G.toGraph
      (minimalModelSubgraph R_G R_H φV Z) A_i)})
    (j : Fin n_i) :
    π_i j ∈ V(P.1) ↔ π'_i j ∈ V(ψV P) := by
  let L := minimalModelSubgraph R_G R_H φV Z
  let L_i := subgraphInter R_G.G.toGraph L A_i
  let R_J := rootedDigraphJ R_G R_H φV φE Z A_i hA_i π_i hπ_i hZ hφ
  have hVJ : ∀ Q : ↥{P : Graph α β | IsGraphComponent P L_i}, Q ∈ V(R_J.G.toGraph) :=
    fun _ => trivial
  have hπj_Li : π_i j ∈ V(L_i) := by
    rw [vertexSet_subgraphInter]
    refine ⟨?_, (hπ_i j).2⟩
    rw [vertexSet_minimalModelSubgraph]
    exact Or.inl (hπ_i j).1
  have hroot_mem' : π'_i j ∈ V(ψV (R_J.roots j)) := hψ.root_mem j
  constructor
  · intro hmem
    have heq : P = R_J.roots j := by
      apply Subtype.ext
      exact isGraphComponent_eq_of_mem_inter P.2 (R_J.roots j).2
        ⟨π_i j, hmem, self_mem_reachSet hπj_Li⟩
    exact heq ▸ hroot_mem'
  · intro hmem'
    have heq : P = R_J.roots j := by
      by_contra hne
      exact disjoint_left.mp (hψ.disjoint_V P (hVJ P) (R_J.roots j) (hVJ _) hne).1
        hmem' hroot_mem'
    rw [heq]
    exact self_mem_reachSet hπj_Li

/-- **Graph Minors XXII, 6.3** (Section 6, pages 543–545):
"Suppose that the following hold:
• $(G, u_1, \ldots, u_q)$, $(G', u'_1, \ldots, u'_q)$ and $(H, v_1, \ldots, v_q)$ are rooted digraphs;
• $Z \subseteq V(G)$ with $u_1, \ldots, u_q \in Z$; $\{A_0, A_1, \ldots, A_k\}$ is a $Z$-division of
  $G$ with $Z \subseteq V(A_0)$, and for $1 \le i \le k$, $\pi_i$ is an ordering of $Z \cap V(A_i)$;
• $Z' \subseteq V(G')$ with $u'_1, \ldots, u'_q \in Z'$; $\{A'_0, A'_1, \ldots, A'_k\}$ is a
  $Z'$-division of $G'$ with $Z' \subseteq V(A'_0)$; and for $1 \le i \le k$, $\pi'_i$ is an
  ordering of $Z' \cap V(A'_i)$;
• $\delta \ge 0$ is an integer such that $(H, v_1, \ldots, v_q)$ has detail $\le \delta$, and for
  $1 \le i \le k$, $(A'_i, \pi'_i)$ has the same $\delta$-folio as $(A_i, \pi_i)$;
• $\alpha \colon Z' \to Z$ is a function mapping $Z'$ onto $Z$ and for $1 \le i \le k$ mapping
  $\pi'_i$ to $\pi_i$;
• $\phi$ is a model of $(H, v_1, \ldots, v_q)$ in $(G, u_1, \ldots, u_q)$ such that
  $\phi(E(H)) \subseteq E(A_1 \cup \dots \cup A_k)$ and $\phi(v) \cap (A_1 \cup \dots \cup A_k)$ is
  non-null for each $v \in V(H)$;
• there exists $L'_0 \subseteq A'_0$ such that $u, v \in Z'$ are $L'_0$-connected if and only if
  $\alpha(u), \alpha(v)$ are $(L \cap A_0)$-connected, where $L \subseteq G$ is minimal such that
  $Z \subseteq V(L)$ and $\phi(v) \subseteq L$ for each $v \in V(H)$.

*Then there is a model $\phi'$ of $(H, v_1, \ldots, v_q)$ in $(G', u'_1, \ldots, u'_q)$ such that*
$$
\phi'(E(H)) \subseteq E(A'_1 \cup \dots \cup A'_k)
$$
*and $\phi'(v) \cap (A'_1 \cup \dots \cup A'_k)$ is non-null for each $v \in V(H)$.*" -/
theorem theorem_6_3_proof {α : Type u} {β : Type v} {α' : Type u'}
    {αH : Type uH} {βH : Type vH} {q k δ : ℕ}
    {R_G : RootedDigraph α β q} {R_G' : RootedDigraph α' β q}
    {R_H : RootedDigraph αH βH q}
    {Z : Set α} {A : Fin (k + 1) → Graph α β}
    {n : Fin k → ℕ} {π : ∀ i : Fin k, Fin (n i) → α}
    {Z' : Set α'} {A' : Fin (k + 1) → Graph α' β}
    {π' : ∀ i : Fin k, Fin (n i) → α'}
    {α_map : α' → α}
    {φV : αH → Graph α β} {φE : βH → β}
    {L'0 : Graph α' β}
    (hZ : Z ⊆ V(R_G.G.toGraph))
    (hroots_Z : ∀ r : Fin q, R_G.roots r ∈ Z)
    (hdiv : IsIndexedZDivision R_G.G.toGraph Z A)
    (hZ_A0 : Z ⊆ V(A 0))
    (hπ : ∀ i : Fin k, IsOrderingOf (Z ∩ V(A i.succ)) (π i))
    (hZ' : Z' ⊆ V(R_G'.G.toGraph))
    (hroots_Z' : ∀ r : Fin q, R_G'.roots r ∈ Z')
    (hdiv' : IsIndexedZDivision R_G'.G.toGraph Z' A')
    (hZ'_A'0 : Z' ⊆ V(A' 0))
    (hπ' : ∀ i : Fin k, IsOrderingOf (Z' ∩ V(A' i.succ)) (π' i))
    (hdetail : R_H.HasDetailLE δ)
    (hfolio : ∀ i : Fin k,
      HasSameDeltaFolio
        (subRootedDigraph R_G'.G (A' i.succ) (hdiv'.1 i.succ) (π' i)
          (fun j => ((hπ' i).2 ▸ mem_range_self j).2))
        (subRootedDigraph R_G.G (A i.succ) (hdiv.1 i.succ) (π i)
          (fun j => ((hπ i).2 ▸ mem_range_self j).2))
        δ)
    (hα_surj : α_map '' Z' = Z)
    (hα_π : ∀ i : Fin k, ∀ j : Fin (n i), α_map (π' i j) = π i j)
    (hα_roots : ∀ r : Fin q, α_map (R_G'.roots r) = R_G.roots r)
    (hφ : IsRootedDigraphModel R_G R_H φV φE)
    (hφE_mem : ∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE e ∈ E(A i.succ))
    (hφV_meets : ∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV v) ∩ V(A i.succ)).Nonempty)
    (hL'0_le : L'0 ≤ A' 0)
    (hL'0_conn : ∀ u ∈ Z', ∀ v ∈ Z',
      AreConnectedIn L'0 u v ↔
        AreConnectedIn
          (subgraphInter R_G.G.toGraph (minimalModelSubgraph R_G R_H φV Z) (A 0))
          (α_map u) (α_map v)) :
    ∃ (φV' : αH → Graph α' β) (φE' : βH → β),
      IsRootedDigraphModel R_G' R_H φV' φE' ∧
      (∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE' e ∈ E(A' i.succ)) ∧
      (∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV' v) ∩ V(A' i.succ)).Nonempty) := by
  classical
  let G := R_G.G.toGraph
  let G' := R_G'.G.toGraph
  let L := minimalModelSubgraph R_G R_H φV Z
  have hL_le : L ≤ G := minimalModelSubgraph_le hZ hφ
  have ⟨hcomp_φV, hother_L, hconn_L_iff⟩ := lemma_6_3_claim_1 hZ hφ
  let hπ_mem : ∀ i : Fin k, ∀ j : Fin (n i), π i j ∈ Z ∩ V(A i.succ) :=
    fun i j => (hπ i).2 ▸ mem_range_self j
  let hπ'_mem : ∀ i : Fin k, ∀ j : Fin (n i), π' i j ∈ Z' ∩ V(A' i.succ) :=
    fun i j => (hπ' i).2 ▸ mem_range_self j
  let R_J : ∀ i : Fin k, _ := fun i =>
    rootedDigraphJ R_G R_H φV φE Z (A i.succ) (hdiv.1 i.succ) (π i) (hπ_mem i) hZ hφ
  let R_Ai : ∀ i : Fin k, _ := fun i =>
    subRootedDigraph R_G.G (A i.succ) (hdiv.1 i.succ) (π i) (fun j => (hπ_mem i j).2)
  let R_A'i : ∀ i : Fin k, _ := fun i =>
    subRootedDigraph R_G'.G (A' i.succ) (hdiv'.1 i.succ) (π' i) (fun j => (hπ'_mem i j).2)
  have hVJ_univ : ∀ (i : Fin k) (P : ↥{P : Graph α β |
      IsGraphComponent P (subgraphInter G L (A i.succ))}), P ∈ V((R_J i).G.toGraph) :=
    fun _ _ => trivial
  have hEJ_univ : ∀ (i : Fin k) (e : ↥((φE '' E(R_H.G.toGraph)) ∩ E(A i.succ))),
      e ∈ E((R_J i).G.toGraph) :=
    fun _ _ => trivial
  -- Claim (2) & Claim (3): For each `i : Fin k`, obtain a model `(ψV i, ψE i)` of `R_J i` in `R_A'i i`.
  have hclaim3_exists : ∀ i : Fin k, HasRootedDigraphModel (R_A'i i) (R_J i) := by
    intro i
    have ⟨hRJ_det, hRJ_mod⟩ := lemma_6_3_claim_2 hZ hroots_Z hdiv hπ hdetail hφ i
    exact (HasSameDeltaFolio.iff_of_hasDetailLE (hfolio i) (R_J i) rfl hRJ_det).mpr hRJ_mod
  let ψV : ∀ i : Fin k, _ := fun i => (hclaim3_exists i).choose
  let ψE : ∀ i : Fin k, _ := fun i => (hclaim3_exists i).choose_spec.choose
  have hψ : ∀ i : Fin k, IsRootedDigraphModel (R_A'i i) (R_J i) (ψV i) (ψE i) :=
    fun i => (hclaim3_exists i).choose_spec.choose_spec
  -- Define `L'_fam : Fin (k + 1) → Graph α' β` and `L' = ⋃_{m} L'_fam m`.
  let L'_piece : ∀ i : Fin k, Graph α' β := fun i =>
    subgraphSUnion (A' i.succ) (ψV i '' V((R_J i).G.toGraph))
  let L'_fam : Fin (k + 1) → Graph α' β :=
    Fin.cases L'0 L'_piece
  have hL'_piece_le : ∀ i : Fin k, L'_piece i ≤ A' i.succ := by
    intro i
    apply subgraphSUnion_le
    rintro _ ⟨P, hP, rfl⟩
    exact (hψ i).subgraph_of_mem P hP
  have hL'_fam_le : ∀ m : Fin (k + 1), L'_fam m ≤ A' m := by
    intro m
    refine Fin.cases ?_ ?_ m
    · exact hL'0_le
    · intro i; exact hL'_piece_le i
  let L'_tot := subgraphSUnion G' (range L'_fam)
  have hL'_tot_le : L'_tot ≤ G' := by
    apply subgraphSUnion_le
    rintro _ ⟨m, rfl⟩
    exact (hL'_fam_le m).trans (hdiv'.1 m)
  have hL'_piece_le_tot : ∀ i : Fin k, L'_piece i ≤ L'_tot := by
    intro i
    have hle_fam : ∀ P ∈ range L'_fam, P ≤ G' := by
      rintro _ ⟨m, rfl⟩; exact (hL'_fam_le m).trans (hdiv'.1 m)
    exact le_subgraphSUnion hle_fam ⟨i.succ, rfl⟩
  -- Components of `L'_piece i` are precisely `ψV i P`.
  have hcomp_ψV : ∀ (i : Fin k) (P : ↥{P : Graph α β |
      IsGraphComponent P (subgraphInter G L (A i.succ))}),
      IsGraphComponent (ψV i P) (L'_piece i) :=
    fun i P => (hψ i).isGraphComponent_subgraphSUnion (hVJ_univ i P)
  have hconn_L'_piece_iff : ∀ (i : Fin k) (u v : α'),
      AreConnectedIn (L'_piece i) u v ↔
        ∃ P : ↥{P : Graph α β | IsGraphComponent P (subgraphInter G L (A i.succ))},
          u ∈ V(ψV i P) ∧ v ∈ V(ψV i P) := by
    intro i u v
    constructor
    · rintro ⟨C, hC, huC, hvC⟩
      obtain ⟨x, hxC⟩ := hC.2.1.1
      have hx_piece : x ∈ V(L'_piece i) := hC.1.vertexSet_mono hxC
      rw [vertexSet_subgraphSUnion] at hx_piece
      obtain ⟨_, ⟨P, _, rfl⟩, hxP⟩ := mem_iUnion₂.mp hx_piece
      have hC_eq : C = ψV i P :=
        isGraphComponent_eq_of_mem_inter hC (hcomp_ψV i P) ⟨x, hxC, hxP⟩
      subst hC_eq
      exact ⟨P, huC, hvC⟩
    · rintro ⟨P, huP, hvP⟩
      exact ⟨ψV i P, hcomp_ψV i P, huP, hvP⟩
  -- Claim (5): for `0 ≤ m ≤ k`, `u, v ∈ Z' ∩ V(A' m)` are `L'_fam m`-connected if and only if
  -- `α(u), α(v)` are `L ∩ A_m`-connected.
  have hclaim5 : ∀ (m : Fin (k + 1)), ∀ u ∈ Z' ∩ V(A' m), ∀ v ∈ Z' ∩ V(A' m),
      AreConnectedIn (L'_fam m) u v ↔
        AreConnectedIn (subgraphInter G L (A m)) (α_map u) (α_map v) := by
    intro m
    refine Fin.cases ?_ ?_ m
    · intro u hu v hv
      exact hL'0_conn u hu.1 v hv.1
    · intro i u hu v hv
      have hu_range : u ∈ range (π' i) := by rw [(hπ' i).2]; exact hu
      have hv_range : v ∈ range (π' i) := by rw [(hπ' i).2]; exact hv
      obtain ⟨r, rfl⟩ := hu_range
      obtain ⟨s, rfl⟩ := hv_range
      change AreConnectedIn (L'_piece i) (π' i r) (π' i s) ↔
        AreConnectedIn (subgraphInter G L (A i.succ)) (α_map (π' i r)) (α_map (π' i s))
      rw [hα_π i r, hα_π i s, hconn_L'_piece_iff i]
      constructor
      · rintro ⟨P, hrP, hsP⟩
        have hr : π i r ∈ V(P.1) :=
          (lemma_6_3_claim_3_root_iff (hdiv.1 i.succ) (hdiv'.1 i.succ) (hπ_mem i)
            (fun j => (hπ'_mem i j).2) hZ hφ (hψ i) P r).mpr hrP
        have hs : π i s ∈ V(P.1) :=
          (lemma_6_3_claim_3_root_iff (hdiv.1 i.succ) (hdiv'.1 i.succ) (hπ_mem i)
            (fun j => (hπ'_mem i j).2) hZ hφ (hψ i) P s).mpr hsP
        exact ⟨P.1, P.2, hr, hs⟩
      · rintro ⟨C, hC, hrC, hsC⟩
        let P : ↥{P : Graph α β | IsGraphComponent P (subgraphInter G L (A i.succ))} := ⟨C, hC⟩
        have hrP : π' i r ∈ V(ψV i P) :=
          (lemma_6_3_claim_3_root_iff (hdiv.1 i.succ) (hdiv'.1 i.succ) (hπ_mem i)
            (fun j => (hπ'_mem i j).2) hZ hφ (hψ i) P r).mp hrC
        have hsP : π' i s ∈ V(ψV i P) :=
          (lemma_6_3_claim_3_root_iff (hdiv.1 i.succ) (hdiv'.1 i.succ) (hπ_mem i)
            (fun j => (hπ'_mem i j).2) hZ hφ (hψ i) P s).mp hsC
        exact ⟨P, hrP, hsP⟩
  -- Hypotheses (a) and (b) of `theorem_2_5_proof`:
  have h25_a : ∀ m : Fin (k + 1), α_map '' (Z' ∩ V(A' m)) = Z ∩ V(A m) := by
    intro m
    refine Fin.cases ?_ ?_ m
    · rw [inter_eq_self_of_subset_left hZ'_A'0, inter_eq_self_of_subset_left hZ_A0]
      exact hα_surj
    · intro i
      rw [← (hπ' i).2, ← (hπ i).2, ← range_comp]
      ext x
      simp only [mem_range, Function.comp_apply, hα_π i]
  have h25_b : ∀ u ∈ Z', ∀ v ∈ Z', u ≠ v → α_map u = α_map v →
      ∃ m : Fin (k + 1), u ∈ V(A' m) ∧ v ∈ V(A' m) :=
    fun u hu v hv _ _ => ⟨0, hZ'_A'0 hu, hZ'_A'0 hv⟩
  -- Claim (6): Apply `theorem_2_5_proof`.
  have ⟨hclaim6_inter, hclaim6_conn⟩ :=
    theorem_2_5_proof hL_le hZ hdiv hZ' hdiv' hL'_fam_le h25_a h25_b hclaim5
  -- Claim (4): `Z' ⊆ V(L'_tot)`.
  have hZ'_sub_L'_tot : Z' ⊆ V(L'_tot) := by
    intro z' hz'
    have hαz' : α_map z' ∈ Z := by rw [← hα_surj]; exact mem_image_of_mem α_map hz'
    have hconn_L : AreConnectedIn L (α_map z') (α_map z') := by
      rw [areConnectedIn_self_iff, vertexSet_minimalModelSubgraph]
      exact Or.inl hαz'
    exact ((hclaim6_conn z' hz' z' hz').mpr hconn_L).left_mem
  -- Define `φE' : βH → β`.
  let φE' : βH → β := fun e =>
    if he : e ∈ E(R_H.G.toGraph) then
      let i := (hφE_mem e he).choose
      ψE i ⟨φE e, mem_image_of_mem φE he, (hφE_mem e he).choose_spec⟩
    else φE e
  -- Helper for `v ∈ V(H)` with `Disjoint V(φV v) Z`:
  have hφV_in_piece : ∀ {v : αH} (hv : v ∈ V(R_H.G.toGraph)) (hdisj : Disjoint V(φV v) Z)
      {i : Fin k} (hmeet : (V(φV v) ∩ V(A i.succ)).Nonempty),
      φV v ≤ A i.succ ∧ IsGraphComponent (φV v) (subgraphInter G L (A i.succ)) := by
    intro v hv hdisj i hmeet
    have hle_Ai : φV v ≤ A i.succ :=
      le_piece_of_connected_disjoint_Z (hφ.subgraph_of_mem v hv) (hφ.connected_of_mem v hv)
        hdiv hdisj hmeet
    have hcomp_L : IsGraphComponent (φV v) L := hcomp_φV v hv
    have hle_Li : φV v ≤ subgraphInter G L (A i.succ) :=
      le_subgraphInter hL_le (hdiv.1 i.succ) hcomp_L.1 hle_Ai
    refine ⟨hle_Ai, hle_Li, hφ.connected_of_mem v hv, ?_⟩
    intro C hφv_C hCLi hC_conn
    exact hcomp_L.2.2 C hφv_C (hCLi.trans (subgraphInter_le_left hL_le (hdiv.1 i.succ))) hC_conn
  -- Construct `φV' v` for `v ∈ V(H)` together with its component properties.
  have hex_φV' : ∀ v ∈ V(R_H.G.toGraph), ∃ T : Graph α' β,
      IsGraphComponent T L'_tot ∧
      ((V(φV v) ∩ Z).Nonempty → ∃ z' ∈ Z' ∩ V(T), α_map z' ∈ V(φV v) ∩ Z) ∧
      (Disjoint V(φV v) Z → Disjoint V(T) Z' ∧
        ∀ (i : Fin k) (hP : IsGraphComponent (φV v) (subgraphInter G L (A i.succ))),
          T = ψV i ⟨φV v, hP⟩) := by
    intro v hv
    by_cases hne : (V(φV v) ∩ Z).Nonempty
    · obtain ⟨z, hzv, hzZ⟩ := hne
      have hz_img : z ∈ α_map '' Z' := hα_surj.symm ▸ hzZ
      obtain ⟨z', hz'Z', rfl⟩ := hz_img
      let T := compOf L'_tot z'
      have hz'_tot : z' ∈ V(L'_tot) := hZ'_sub_L'_tot hz'Z'
      refine ⟨T, isGraphComponent_compOf hz'_tot,
        fun _ => ⟨z', ⟨hz'Z', self_mem_reachSet hz'_tot⟩, hzv, hzZ⟩,
        fun hdisj => (disjoint_left.mp hdisj hzv hzZ).elim⟩
    · have hdisj : Disjoint V(φV v) Z :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne)
      let i₀ := (hφV_meets v hv).choose
      have hmeet₀ : (V(φV v) ∩ V(A i₀.succ)).Nonempty := (hφV_meets v hv).choose_spec
      have ⟨hle_Ai₀, hcomp_Li₀⟩ := hφV_in_piece hv hdisj hmeet₀
      let P₀ : ↥{P : Graph α β | IsGraphComponent P (subgraphInter G L (A i₀.succ))} :=
        ⟨φV v, hcomp_Li₀⟩
      let T := ψV i₀ P₀
      have hT_le_A' : T ≤ A' i₀.succ := (hψ i₀).subgraph_of_mem P₀ (hVJ_univ i₀ P₀)
      have hT_disj_Z' : Disjoint V(T) Z' := by
        rw [disjoint_left]
        intro z' hz'T hz'Z'
        have hz'_range : z' ∈ range (π' i₀) := by
          rw [(hπ' i₀).2]; exact ⟨hz'Z', hT_le_A'.vertexSet_mono hz'T⟩
        obtain ⟨j, rfl⟩ := hz'_range
        have hπj_v : π i₀ j ∈ V(φV v) :=
          (lemma_6_3_claim_3_root_iff (hdiv.1 i₀.succ) (hdiv'.1 i₀.succ) (hπ_mem i₀)
            (fun j => (hπ'_mem i₀ j).2) hZ hφ (hψ i₀) P₀ j).mpr hz'T
        exact disjoint_left.mp hdisj hπj_v (hπ_mem i₀ j).1
      have hT_comp_inter : IsGraphComponent T (subgraphInter G' L'_tot (A' i₀.succ)) := by
        rw [← hclaim6_inter i₀.succ]
        exact hcomp_ψV i₀ P₀
      have hT_comp_tot : IsGraphComponent T L'_tot :=
        isGraphComponent_of_component_subgraphInter_disjoint_Z hL'_tot_le hdiv' i₀.succ
          hT_comp_inter hT_disj_Z'
      refine ⟨T, hT_comp_tot, fun h => (hne h).elim, fun _ => ⟨hT_disj_Z', ?_⟩⟩
      intro i hP
      obtain ⟨x₀, hx₀⟩ := (hφ.connected_of_mem v hv).1
      have hx₀_Ai₀ : x₀ ∈ V(A i₀.succ) := hle_Ai₀.vertexSet_mono hx₀
      have hx₀_Ai : x₀ ∈ V(A i.succ) :=
        (subgraphInter_le_right hL_le (hdiv.1 i.succ)).vertexSet_mono (hP.1.vertexSet_mono hx₀)
      have hi_eq : i = i₀ := by
        by_contra hne_i
        have hne_succ : i.succ ≠ i₀.succ := fun h => hne_i (Fin.succ_inj.mp h)
        have hx₀_Z : x₀ ∈ Z := (hdiv.2.2 i.succ i₀.succ hne_succ).2 ⟨hx₀_Ai, hx₀_Ai₀⟩
        exact disjoint_left.mp hdisj hx₀ hx₀_Z
      subst hi_eq
      rfl
  let φV' : αH → Graph α' β := fun v =>
    if hv : v ∈ V(R_H.G.toGraph) then (hex_φV' v hv).choose else ⊥
  have hφV'_spec : ∀ v ∈ V(R_H.G.toGraph),
      IsGraphComponent (φV' v) L'_tot ∧
      ((V(φV v) ∩ Z).Nonempty → ∃ z' ∈ Z' ∩ V(φV' v), α_map z' ∈ V(φV v) ∩ Z) ∧
      (Disjoint V(φV v) Z → Disjoint V(φV' v) Z' ∧
        ∀ (i : Fin k) (hP : IsGraphComponent (φV v) (subgraphInter G L (A i.succ))),
          φV' v = ψV i ⟨φV v, hP⟩) := by
    intro v hv
    simp only [φV', hv, ↓reduceDIte]
    exact (hex_φV' v hv).choose_spec
  -- Claim (7): For `v ∈ V(H)` and `z ∈ Z'`, `z ∈ V(φV' v) ↔ α_map z ∈ V(φV v)`.
  have hclaim7 : ∀ {v : αH} (hv : v ∈ V(R_H.G.toGraph)) {z : α'} (hz : z ∈ Z'),
      z ∈ V(φV' v) ↔ α_map z ∈ V(φV v) := by
    intro v hv z hz
    have ⟨hcomp', hcase_ne, hcase_disj⟩ := hφV'_spec v hv
    constructor
    · intro hz_v'
      have hne_Z : (V(φV v) ∩ Z).Nonempty := by
        by_contra hnot
        have hdisj : Disjoint V(φV v) Z :=
          disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hnot)
        exact disjoint_left.mp (hcase_disj hdisj).1 hz_v' hz
      obtain ⟨z', ⟨hz'Z', hz'_v'⟩, hαz'_v, _⟩ := hcase_ne hne_Z
      have hconn' : AreConnectedIn L'_tot z z' := ⟨φV' v, hcomp', hz_v', hz'_v'⟩
      have hconn_L : AreConnectedIn L (α_map z) (α_map z') :=
        (hclaim6_conn z hz z' hz'Z').mp hconn'
      rcases (hconn_L_iff (α_map z) (α_map z')).mp hconn_L with ⟨_, heq⟩ | ⟨w, hw, hzw, hz'w⟩
      · exact heq.symm ▸ hαz'_v
      · have hvw : v = w := by
          by_contra hne
          exact disjoint_left.mp (hφ.disjoint_V v hv w hw hne).1 hαz'_v hz'w
        exact hvw ▸ hzw
    · intro hαz_v
      have hαz_Z : α_map z ∈ Z := by rw [← hα_surj]; exact mem_image_of_mem α_map hz
      have hne_Z : (V(φV v) ∩ Z).Nonempty := ⟨α_map z, hαz_v, hαz_Z⟩
      obtain ⟨z', ⟨hz'Z', hz'_v'⟩, hαz'_v, _⟩ := hcase_ne hne_Z
      have hconn_L : AreConnectedIn L (α_map z) (α_map z') :=
        (hconn_L_iff (α_map z) (α_map z')).mpr (Or.inr ⟨v, hv, hαz_v, hαz'_v⟩)
      have hconn' : AreConnectedIn L'_tot z z' :=
        (hclaim6_conn z hz z' hz'Z').mpr hconn_L
      rcases hconn' with ⟨C, hC, hzC, hz'C⟩
      have hC_eq : C = φV' v :=
        isGraphComponent_eq_of_mem_inter hC hcomp' ⟨z', hz'C, hz'_v'⟩
      exact hC_eq ▸ hzC
  -- Claim (8): If `v₁, v₂ ∈ V(H)` are distinct then `φV' v₁ ∩ φV' v₂` is null.
  have hclaim8 : ∀ v₁ ∈ V(R_H.G.toGraph), ∀ v₂ ∈ V(R_H.G.toGraph), v₁ ≠ v₂ →
      Disjoint V(φV' v₁) V(φV' v₂) ∧ Disjoint E(φV' v₁) E(φV' v₂) := by
    intro v₁ hv₁ v₂ hv₂ hne
    apply isGraphComponent_disjoint (hφV'_spec v₁ hv₁).1 (hφV'_spec v₂ hv₂).1
    intro heq
    by_cases hne_Z' : (V(φV' v₁) ∩ Z').Nonempty
    · obtain ⟨z, hzv₁', hzZ'⟩ := hne_Z'
      have hzv₂' : z ∈ V(φV' v₂) := heq ▸ hzv₁'
      have hα₁ : α_map z ∈ V(φV v₁) := (hclaim7 hv₁ hzZ').mp hzv₁'
      have hα₂ : α_map z ∈ V(φV v₂) := (hclaim7 hv₂ hzZ').mp hzv₂'
      exact disjoint_left.mp (hφ.disjoint_V v₁ hv₁ v₂ hv₂ hne).1 hα₁ hα₂
    · have hdisj₁' : Disjoint V(φV' v₁) Z' :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne_Z')
      have hdisj₁ : Disjoint V(φV v₁) Z := by
        rw [disjoint_left]
        intro z hzv₁ hzZ
        rw [← hα_surj] at hzZ
        obtain ⟨z', hz'Z', rfl⟩ := hzZ
        exact disjoint_left.mp hdisj₁' ((hclaim7 hv₁ hz'Z').mpr hzv₁) hz'Z'
      have hdisj₂ : Disjoint V(φV v₂) Z := by
        rw [disjoint_left]
        intro z hzv₂ hzZ
        rw [← hα_surj] at hzZ
        obtain ⟨z', hz'Z', rfl⟩ := hzZ
        have hzv₁' : z' ∈ V(φV' v₁) := heq.symm ▸ (hclaim7 hv₂ hz'Z').mpr hzv₂
        exact disjoint_left.mp hdisj₁' hzv₁' hz'Z'
      obtain ⟨i₁, hmeet₁⟩ := hφV_meets v₁ hv₁
      obtain ⟨i₂, hmeet₂⟩ := hφV_meets v₂ hv₂
      have ⟨_, hP₁⟩ := hφV_in_piece hv₁ hdisj₁ hmeet₁
      have ⟨_, hP₂⟩ := hφV_in_piece hv₂ hdisj₂ hmeet₂
      have heq₁ : φV' v₁ = ψV i₁ ⟨φV v₁, hP₁⟩ := ((hφV'_spec v₁ hv₁).2.2 hdisj₁).2 i₁ hP₁
      have heq₂ : φV' v₂ = ψV i₂ ⟨φV v₂, hP₂⟩ := ((hφV'_spec v₂ hv₂).2.2 hdisj₂).2 i₂ hP₂
      obtain ⟨x', hx'⟩ := (hφV'_spec v₁ hv₁).1.2.1.1
      have hx'_A'1 : x' ∈ V(A' i₁.succ) :=
        ((hψ i₁).subgraph_of_mem ⟨φV v₁, hP₁⟩ (hVJ_univ i₁ _)).vertexSet_mono (heq₁ ▸ hx')
      have hx'_A'2 : x' ∈ V(A' i₂.succ) :=
        ((hψ i₂).subgraph_of_mem ⟨φV v₂, hP₂⟩ (hVJ_univ i₂ _)).vertexSet_mono (heq₂ ▸ heq ▸ hx')
      have hi_eq : i₁ = i₂ := by
        by_contra hne_i
        have hne_succ : i₁.succ ≠ i₂.succ := fun h => hne_i (Fin.succ_inj.mp h)
        have hx'_Z' : x' ∈ Z' := (hdiv'.2.2 i₁.succ i₂.succ hne_succ).2 ⟨hx'_A'1, hx'_A'2⟩
        exact disjoint_left.mp hdisj₁' hx' hx'_Z'
      subst hi_eq
      have hψ_eq : ψV i₁ ⟨φV v₁, hP₁⟩ = ψV i₁ ⟨φV v₂, hP₂⟩ := heq₁.symm.trans (heq.trans heq₂)
      have hP_ne : (⟨φV v₁, hP₁⟩ : ↥{P | IsGraphComponent P (subgraphInter G L (A i₁.succ))}) ≠
          ⟨φV v₂, hP₂⟩ := by
        intro hP_eq
        have hv_eq : φV v₁ = φV v₂ := congr_arg Subtype.val hP_eq
        obtain ⟨y, hy⟩ := (hφ.connected_of_mem v₁ hv₁).1
        exact disjoint_left.mp (hφ.disjoint_V v₁ hv₁ v₂ hv₂ hne).1 hy (hv_eq ▸ hy)
      exact disjoint_left.mp
        ((hψ i₁).disjoint_V ⟨φV v₁, hP₁⟩ (hVJ_univ i₁ _) ⟨φV v₂, hP₂⟩ (hVJ_univ i₁ _) hP_ne).1
        (heq₁ ▸ hx') (hψ_eq ▸ heq₁ ▸ hx')
  -- Claim (9): For `1 ≤ r ≤ q`, `u'_r ∈ V(φV' v_r)`.
  have hclaim9 : ∀ r : Fin q, R_G'.roots r ∈ V(φV' (R_H.roots r)) := by
    intro r
    rw [hclaim7 (R_H.roots_mem r) (hroots_Z' r), hα_roots r]
    exact hφ.root_mem r
  -- Claim (10): Unified helper for head and tail of `φE' e`.
  have hclaim10_aux : ∀ {e : βH} (he : e ∈ E(R_H.G.toGraph))
      {v : αH} (hv : v ∈ V(R_H.G.toGraph))
      {u : α} (hu_v : u ∈ V(φV v))
      (hu_Ai : u ∈ V(A (hφE_mem e he).choose.succ))
      {u' : α'}
      (hu'_ψ :
        let i := (hφE_mem e he).choose
        have hu_Li : u ∈ V(subgraphInter G L (A i.succ)) := by
          rw [vertexSet_subgraphInter]
          refine ⟨?_, hu_Ai⟩
          rw [vertexSet_minimalModelSubgraph]
          exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, hu_v⟩)
        u' ∈ V(ψV i ⟨compOf (subgraphInter G L (A i.succ)) u, isGraphComponent_compOf hu_Li⟩)),
      u' ∈ V(φV' v) := by
    intro e he v hv u hu_v hu_Ai u' hu'_ψ
    let i := (hφE_mem e he).choose
    let L_i := subgraphInter G L (A i.succ)
    have hu_Li : u ∈ V(L_i) := by
      rw [vertexSet_subgraphInter]
      refine ⟨?_, hu_Ai⟩
      rw [vertexSet_minimalModelSubgraph]
      exact Or.inr (mem_iUnion₂.mpr ⟨v, hv, hu_v⟩)
    let P : ↥{P : Graph α β | IsGraphComponent P L_i} :=
      ⟨compOf L_i u, isGraphComponent_compOf hu_Li⟩
    have hP_le_L : P.1 ≤ L := P.2.1.trans (subgraphInter_le_left hL_le (hdiv.1 i.succ))
    have hu_P : u ∈ V(P.1) := self_mem_reachSet hu_Li
    have hP_le_φv : P.1 ≤ φV v := by
      have hconn_union := isGraphConnected_subgraphUnion hP_le_L (hcomp_φV v hv).1
        P.2.2.1 (hφ.connected_of_mem v hv) ⟨u, hu_P, hu_v⟩
      have hunion_eq := (hcomp_φV v hv).2.2 _
        (le_subgraphUnion_right hP_le_L (hcomp_φV v hv).1)
        (subgraphUnion_le hP_le_L (hcomp_φV v hv).1) hconn_union
      exact hunion_eq ▸ le_subgraphUnion_left hP_le_L (hcomp_φV v hv).1
    by_cases hPZ : (V(P.1) ∩ Z).Nonempty
    · obtain ⟨z, hzP, hzZ⟩ := hPZ
      have hz_Ai : z ∈ V(A i.succ) :=
        (subgraphInter_le_right hL_le (hdiv.1 i.succ)).vertexSet_mono (P.2.1.vertexSet_mono hzP)
      have hz_range : z ∈ range (π i) := by rw [(hπ i).2]; exact ⟨hzZ, hz_Ai⟩
      obtain ⟨j, rfl⟩ := hz_range
      let z' := π' i j
      have hz'_ψP : z' ∈ V(ψV i P) :=
        (lemma_6_3_claim_3_root_iff (hdiv.1 i.succ) (hdiv'.1 i.succ) (hπ_mem i)
          (fun j => (hπ'_mem i j).2) hZ hφ (hψ i) P j).mp hzP
      have hαz' : α_map z' ∈ V(φV v) := by
        rw [hα_π i j]
        exact hP_le_φv.vertexSet_mono hzP
      have hz'_v' : z' ∈ V(φV' v) := (hclaim7 hv (hπ'_mem i j).1).mpr hαz'
      have hψP_le_tot : ψV i P ≤ L'_tot :=
        (hcomp_ψV i P).1.trans (hL'_piece_le_tot i)
      have hconn_union := isGraphConnected_subgraphUnion hψP_le_tot (hφV'_spec v hv).1.1
        ((hψ i).connected_of_mem P (hVJ_univ i P)) (hφV'_spec v hv).1.2.1 ⟨z', hz'_ψP, hz'_v'⟩
      have hunion_eq := (hφV'_spec v hv).1.2.2 _
        (le_subgraphUnion_right hψP_le_tot (hφV'_spec v hv).1.1)
        (subgraphUnion_le hψP_le_tot (hφV'_spec v hv).1.1) hconn_union
      have hψP_le_v' : ψV i P ≤ φV' v :=
        hunion_eq ▸ le_subgraphUnion_left hψP_le_tot (hφV'_spec v hv).1.1
      exact hψP_le_v'.vertexSet_mono hu'_ψ
    · have hdisj_PZ : Disjoint V(P.1) Z :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hPZ)
      have hP_comp_L : IsGraphComponent P.1 L :=
        isGraphComponent_of_component_subgraphInter_disjoint_Z hL_le hdiv i.succ P.2 hdisj_PZ
      have hP_eq_φv : P.1 = φV v :=
        isGraphComponent_eq_of_mem_inter hP_comp_L (hcomp_φV v hv) ⟨u, hu_P, hu_v⟩
      have hdisj_vZ : Disjoint V(φV v) Z := hP_eq_φv ▸ hdisj_PZ
      have hcomp_v_Li : IsGraphComponent (φV v) L_i := hP_eq_φv ▸ P.2
      have hφv'_eq : φV' v = ψV i ⟨φV v, hcomp_v_Li⟩ :=
        ((hφV'_spec v hv).2.2 hdisj_vZ).2 i hcomp_v_Li
      have hsub_eq : (⟨φV v, hcomp_v_Li⟩ : ↥{P | IsGraphComponent P L_i}) = P :=
        Subtype.ext hP_eq_φv.symm
      rw [hφv'_eq, hsub_eq]
      exact hu'_ψ
  -- Verify `IsRootedDigraphModel R_G' R_H φV' φE'`.
  refine ⟨φV', φE', ⟨?_, ?_, hclaim8, hclaim9, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro v hv
    exact (hφV'_spec v hv).1.1.trans hL'_tot_le
  · intro v hv
    exact (hφV'_spec v hv).1.2.1
  · intro e he
    simp only [φE', he, ↓reduceDIte]
    let i := (hφE_mem e he).choose
    exact (hdiv'.1 i.succ).edgeSet_mono
      ((hψ i).edge_mem ⟨φE e, mem_image_of_mem φE he, (hφE_mem e he).choose_spec⟩ (hEJ_univ i _))
  · intro e₁ he₁ e₂ he₂ heq
    let i₁ := (hφE_mem e₁ he₁).choose
    let i₂ := (hφE_mem e₂ he₂).choose
    have he₁_A' : φE' e₁ ∈ E(A' i₁.succ) := by
      simp only [φE', he₁, ↓reduceDIte]
      exact (hψ i₁).edge_mem ⟨φE e₁, mem_image_of_mem φE he₁, (hφE_mem e₁ he₁).choose_spec⟩
        (hEJ_univ i₁ _)
    have he₂_A' : φE' e₂ ∈ E(A' i₂.succ) := by
      simp only [φE', he₂, ↓reduceDIte]
      exact (hψ i₂).edge_mem ⟨φE e₂, mem_image_of_mem φE he₂, (hφE_mem e₂ he₂).choose_spec⟩
        (hEJ_univ i₂ _)
    have hi_eq : i₁ = i₂ := by
      by_contra hne_i
      have hne_succ : i₁.succ ≠ i₂.succ := fun h => hne_i (Fin.succ_inj.mp h)
      exact disjoint_left.mp (hdiv'.2.2 i₁.succ i₂.succ hne_succ).1 he₁_A' (heq.symm ▸ he₂_A')
    have heq' : ψE i₁ ⟨φE e₁, mem_image_of_mem φE he₁, (hφE_mem e₁ he₁).choose_spec⟩ =
        ψE i₂ ⟨φE e₂, mem_image_of_mem φE he₂, (hφE_mem e₂ he₂).choose_spec⟩ := by
      simpa [φE', he₁, he₂] using heq
    have haux : ∀ (j₁ j₂ : Fin k) (hj : j₁ = j₂)
        (h₁ : φE e₁ ∈ E(A j₁.succ)) (h₂ : φE e₂ ∈ E(A j₂.succ)),
        ψE j₁ ⟨φE e₁, mem_image_of_mem φE he₁, h₁⟩ =
          ψE j₂ ⟨φE e₂, mem_image_of_mem φE he₂, h₂⟩ →
        e₁ = e₂ := by
      rintro j₁ j₂ rfl h₁ h₂ hψ_eq
      have hsub := (hψ j₁).injOn_E (hEJ_univ j₁ _) (hEJ_univ j₁ _) hψ_eq
      exact hφ.injOn_E he₁ he₂ (congr_arg Subtype.val hsub)
    exact haux i₁ i₂ hi_eq (hφE_mem e₁ he₁).choose_spec (hφE_mem e₂ he₂).choose_spec heq'
  · intro e he v hv hmem
    let i := (hφE_mem e he).choose
    let e_J : ↥((φE '' E(R_H.G.toGraph)) ∩ E(A i.succ)) :=
      ⟨φE e, mem_image_of_mem φE he, (hφE_mem e he).choose_spec⟩
    have he'_A'i : φE' e ∈ E(A' i.succ) := by
      simp only [φE', he, ↓reduceDIte]
      exact (hψ i).edge_mem e_J (hEJ_univ i _)
    have he'_tot : φE' e ∈ E(L'_tot) := (hφV'_spec v hv).1.1.edgeSet_mono hmem
    have he'_inter : φE' e ∈ E(subgraphInter G' L'_tot (A' i.succ)) := by
      rw [edgeSet_subgraphInter hL'_tot_le (hdiv'.1 i.succ)]
      exact ⟨he'_tot, he'_A'i⟩
    rw [← hclaim6_inter i.succ] at he'_inter
    change φE' e ∈ E(L'_piece i) at he'_inter
    have hle_ψ : ∀ Q ∈ ψV i '' V((R_J i).G.toGraph), Q ≤ A' i.succ := by
      rintro _ ⟨P, hP, rfl⟩; exact (hψ i).subgraph_of_mem P hP
    rw [edgeSet_subgraphSUnion hle_ψ] at he'_inter
    obtain ⟨_, ⟨P, hP, rfl⟩, he'_P⟩ := mem_iUnion₂.mp he'_inter
    simp only [φE', he, ↓reduceDIte] at he'_P
    exact (hψ i).edge_not_mem_φV e_J (hEJ_univ i _) P hP he'_P
  · intro e he
    let i := (hφE_mem e he).choose
    have hi : φE e ∈ E(A i.succ) := (hφE_mem e he).choose_spec
    have hv : R_H.G.head e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).right_mem
    have hl_Ai : (A i.succ).IsLink (φE e) (R_G.G.tail (φE e)) (R_G.G.head (φE e)) :=
      ((hdiv.1 i.succ).isLink_iff hi).mpr
        (R_G.G.isLink_of_mem _ ((hdiv.1 i.succ).edgeSet_mono hi))
    have hu'_ψ : R_G'.G.head (φE' e) ∈
        V(ψV i ((R_J i).G.head ⟨φE e, mem_image_of_mem φE he, hi⟩)) := by
      simp only [φE', he, ↓reduceDIte]
      exact (hψ i).head_mem ⟨φE e, mem_image_of_mem φE he, hi⟩ (hEJ_univ i _)
    exact hclaim10_aux he hv (hφ.head_mem e he) hl_Ai.right_mem hu'_ψ
  · intro e he
    let i := (hφE_mem e he).choose
    have hi : φE e ∈ E(A i.succ) := (hφE_mem e he).choose_spec
    have hv' : R_H.G.tail e ∈ V(R_H.G.toGraph) := (R_H.G.isLink_of_mem e he).left_mem
    have hl_Ai : (A i.succ).IsLink (φE e) (R_G.G.tail (φE e)) (R_G.G.head (φE e)) :=
      ((hdiv.1 i.succ).isLink_iff hi).mpr
        (R_G.G.isLink_of_mem _ ((hdiv.1 i.succ).edgeSet_mono hi))
    have hu'_ψ : R_G'.G.tail (φE' e) ∈
        V(ψV i ((R_J i).G.tail ⟨φE e, mem_image_of_mem φE he, hi⟩)) := by
      simp only [φE', he, ↓reduceDIte]
      exact (hψ i).tail_mem ⟨φE e, mem_image_of_mem φE he, hi⟩ (hEJ_univ i _)
    exact hclaim10_aux he hv' (hφ.tail_mem e he) hl_Ai.left_mem hu'_ψ
  · intro e he
    let i := (hφE_mem e he).choose
    refine ⟨i, ?_⟩
    simp only [φE', he, ↓reduceDIte]
    exact (hψ i).edge_mem ⟨φE e, mem_image_of_mem φE he, (hφE_mem e he).choose_spec⟩ (hEJ_univ i _)
  · intro v hv
    obtain ⟨i, hmeet⟩ := hφV_meets v hv
    by_cases hne_Z : (V(φV v) ∩ Z).Nonempty
    · obtain ⟨x₀, hx₀v, hx₀A⟩ := hmeet
      obtain ⟨z₀, hz₀v, hz₀Z⟩ := hne_Z
      obtain ⟨W⟩ := (hφ.connected_of_mem v hv).2 x₀ hx₀v z₀ hz₀v
      have hex_Zi : ∃ z ∈ V(φV v), z ∈ Z ∧ z ∈ V(A i.succ) := by
        have hind : ∀ {a b : α} (W₁ : GraphWalk (φV v) a b),
            a ∈ V(A i.succ) → b ∈ Z → ∃ z ∈ W₁.support, z ∈ Z ∧ z ∈ V(A i.succ) := by
          intro a b W₁
          induction W₁ with
          | nil _ =>
            intro ha hb
            exact ⟨_, by simp, hb, ha⟩
          | @cons a₁ m₁ b₁ f hf rest ih =>
            intro ha₁ hb₁
            by_cases ha₁Z : a₁ ∈ Z
            · exact ⟨a₁, by simp, ha₁Z, ha₁⟩
            · have hfG : f ∈ E(G) := (hφ.subgraph_of_mem v hv).edgeSet_mono hf.edge_mem
              rw [← hdiv.edgeSet_iUnion, mem_iUnion] at hfG
              obtain ⟨m, hf_Am⟩ := hfG
              have hl_Am : (A m).IsLink f a₁ m₁ :=
                ((hdiv.1 m).isLink_iff hf_Am).mpr (hf.mono (hφ.subgraph_of_mem v hv))
              have hm_eq : i.succ = m := by
                by_contra hne_m
                exact ha₁Z ((hdiv.2.2 i.succ m hne_m).2 ⟨ha₁, hl_Am.left_mem⟩)
              subst hm_eq
              obtain ⟨z, hz_supp, hzZ, hzA⟩ := ih hl_Am.right_mem hb₁
              exact ⟨z, List.mem_cons_of_mem _ hz_supp, hzZ, hzA⟩
        obtain ⟨z, hz_supp, hzZ, hzA⟩ := hind W hx₀A hz₀Z
        exact ⟨z, W.mem_vertexSet_of_mem_support hz_supp, hzZ, hzA⟩
      obtain ⟨z, hzv, hzZ, hzAi⟩ := hex_Zi
      have hz_range : z ∈ range (π i) := by rw [(hπ i).2]; exact ⟨hzZ, hzAi⟩
      obtain ⟨j, rfl⟩ := hz_range
      refine ⟨i, π' i j, ?_, (hπ'_mem i j).2⟩
      rw [hclaim7 hv (hπ'_mem i j).1, hα_π i j]
      exact hzv
    · have hdisj : Disjoint V(φV v) Z :=
        disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hne_Z)
      have ⟨_, hP⟩ := hφV_in_piece hv hdisj hmeet
      have heq : φV' v = ψV i ⟨φV v, hP⟩ := ((hφV'_spec v hv).2.2 hdisj).2 i hP
      obtain ⟨x', hx'⟩ := (hφV'_spec v hv).1.2.1.1
      refine ⟨i, x', hx', ?_⟩
      exact ((hψ i).subgraph_of_mem ⟨φV v, hP⟩ (hVJ_univ i _)).vertexSet_mono (heq ▸ hx')

private theorem hasRootedDigraphModel_single_noEdge_transfer {b₁ b₂ : Bool}
    {αH βH : Type} {R_H : RootedDigraph αH βH 1} :
    let G_two : Digraph Bool Empty :=
      { toGraph := Graph.noEdge Set.univ Empty
        head := Empty.elim
        tail := Empty.elim
        isLink_of_mem := fun e => Empty.elim e }
    let hle : ∀ b : Bool, Graph.noEdge ({b} : Set Bool) Empty ≤ G_two.toGraph :=
      fun b => ⟨subset_univ {b}, fun _ _ _ h => h.elim⟩
    let R_of : Bool → RootedDigraph Bool Empty 1 :=
      fun b => subRootedDigraph G_two (Graph.noEdge {b} Empty) (hle b) (fun _ => b) (fun _ => rfl)
    HasRootedDigraphModel (R_of b₁) R_H → HasRootedDigraphModel (R_of b₂) R_H := by
  intro G_two hle R_of ⟨φV, φE, hMod⟩
  refine ⟨fun _ => Graph.noEdge {b₂} Empty, φE, ?_⟩
  refine ⟨fun _ _ => le_rfl,
    fun _ _ => ⟨⟨b₂, rfl⟩, fun x hx y hy => by cases hx; cases hy; exact ⟨GraphWalk.nil rfl⟩⟩,
    fun v₁ hv₁ v₂ hv₂ hne => ?_,
    fun _ => rfl,
    fun e he => (hMod.edge_mem e he).elim,
    fun e he => (hMod.edge_mem e he).elim,
    fun e he => (hMod.edge_mem e he).elim,
    fun e he => (hMod.edge_mem e he).elim,
    fun e he => (hMod.edge_mem e he).elim⟩
  obtain ⟨x₁, hx₁⟩ := (hMod.connected_of_mem v₁ hv₁).1
  obtain ⟨x₂, hx₂⟩ := (hMod.connected_of_mem v₂ hv₂).1
  have hx₁_eq : x₁ = b₁ := (hMod.subgraph_of_mem v₁ hv₁).vertexSet_mono hx₁
  have hx₂_eq : x₂ = b₁ := (hMod.subgraph_of_mem v₂ hv₂).vertexSet_mono hx₂
  subst hx₁_eq hx₂_eq
  exact False.elim (disjoint_left.mp (hMod.disjoint_V v₁ hv₁ v₂ hv₂ hne).1 hx₁ hx₂)

/-- Without the root-preservation hypothesis $\alpha(u'_r) = u_r$ ($1 \le r \le q$) used in
Claim (9) on page 545, the statement of **Graph Minors XXII, (6.3)** (page 543) is false:
take $q = 1$, $k = 1$, $\delta = 0$, $G = G' = (\{\text{false}, \text{true}\}, \emptyset)$ with
roots $u_1 = u'_1 = \text{false}$, $H = (\{()\}, \emptyset)$ with root $v_1 = ()$,
$Z = Z' = \{\text{false}, \text{true}\}$, $A_0 = A'_0 = G$,
$A_1 = (\{\text{false}\}, \emptyset)$, $A'_1 = (\{\text{true}\}, \emptyset)$,
$\pi_1 = (\text{false})$, $\pi'_1 = (\text{true})$, $\alpha = \text{not}$,
$\phi(()) = A_1$, and $L'_0 = A'_0$. -/
theorem not_theorem_6_3_without_roots_proof :
    ¬ (∀ {α : Type} {β : Type} {α' : Type}
        {αH : Type} {βH : Type} {q k δ : ℕ}
        {R_G : RootedDigraph α β q} {R_G' : RootedDigraph α' β q}
        {R_H : RootedDigraph αH βH q}
        {Z : Set α} {A : Fin (k + 1) → Graph α β}
        {n : Fin k → ℕ} {π : ∀ i : Fin k, Fin (n i) → α}
        {Z' : Set α'} {A' : Fin (k + 1) → Graph α' β}
        {π' : ∀ i : Fin k, Fin (n i) → α'}
        {α_map : α' → α}
        {φV : αH → Graph α β} {φE : βH → β}
        {L'0 : Graph α' β}
        (hdiv : IsIndexedZDivision R_G.G.toGraph Z A)
        (hπ : ∀ i : Fin k, IsOrderingOf (Z ∩ V(A i.succ)) (π i))
        (hdiv' : IsIndexedZDivision R_G'.G.toGraph Z' A')
        (hπ' : ∀ i : Fin k, IsOrderingOf (Z' ∩ V(A' i.succ)) (π' i)),
        Z ⊆ V(R_G.G.toGraph) →
        (∀ r : Fin q, R_G.roots r ∈ Z) →
        Z ⊆ V(A 0) →
        Z' ⊆ V(R_G'.G.toGraph) →
        (∀ r : Fin q, R_G'.roots r ∈ Z') →
        Z' ⊆ V(A' 0) →
        R_H.HasDetailLE δ →
        (∀ i : Fin k,
          HasSameDeltaFolio
            (subRootedDigraph R_G'.G (A' i.succ) (hdiv'.1 i.succ) (π' i)
              (fun j => ((hπ' i).2 ▸ mem_range_self j).2))
            (subRootedDigraph R_G.G (A i.succ) (hdiv.1 i.succ) (π i)
              (fun j => ((hπ i).2 ▸ mem_range_self j).2))
            δ) →
        α_map '' Z' = Z →
        (∀ i : Fin k, ∀ j : Fin (n i), α_map (π' i j) = π i j) →
        IsRootedDigraphModel R_G R_H φV φE →
        (∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE e ∈ E(A i.succ)) →
        (∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV v) ∩ V(A i.succ)).Nonempty) →
        L'0 ≤ A' 0 →
        (∀ u ∈ Z', ∀ v ∈ Z',
          AreConnectedIn L'0 u v ↔
            AreConnectedIn
              (subgraphInter R_G.G.toGraph (minimalModelSubgraph R_G R_H φV Z) (A 0))
              (α_map u) (α_map v)) →
        ∃ (φV' : αH → Graph α' β) (φE' : βH → β),
          IsRootedDigraphModel R_G' R_H φV' φE' ∧
          (∀ e ∈ E(R_H.G.toGraph), ∃ i : Fin k, φE' e ∈ E(A' i.succ)) ∧
          (∀ v ∈ V(R_H.G.toGraph), ∃ i : Fin k, (V(φV' v) ∩ V(A' i.succ)).Nonempty)) := by
  intro h63_bad
  let G_two : Digraph Bool Empty :=
    { toGraph := Graph.noEdge Set.univ Empty
      head := Empty.elim
      tail := Empty.elim
      isLink_of_mem := fun e => Empty.elim e }
  let G_one : Digraph Unit Empty :=
    { toGraph := Graph.noEdge Set.univ Empty
      head := Empty.elim
      tail := Empty.elim
      isLink_of_mem := fun e => Empty.elim e }
  let R_G : RootedDigraph Bool Empty 1 := ⟨G_two, fun _ => false, fun _ => trivial⟩
  let R_G' : RootedDigraph Bool Empty 1 := ⟨G_two, fun _ => false, fun _ => trivial⟩
  let R_H : RootedDigraph Unit Empty 1 := ⟨G_one, fun _ => (), fun _ => trivial⟩
  let A_of : Bool → Fin 2 → Graph Bool Empty :=
    fun b => Fin.cases (Graph.noEdge Set.univ Empty) (fun _ => Graph.noEdge {b} Empty)
  have hdiv : ∀ b : Bool, IsIndexedZDivision G_two.toGraph Set.univ (A_of b) := by
    intro b
    refine ⟨?_, ?_, ?_⟩
    · intro m
      refine Fin.cases le_rfl (fun _ => ⟨subset_univ _, fun _ _ _ h => h.elim⟩) m
    · refine Graph.ext ?_ fun e => Empty.elim e
      ext x
      simp only [vertexSet_subgraphSUnion, mem_iUnion, mem_range]
      exact ⟨fun _ => trivial, fun _ => ⟨A_of b 0, ⟨0, rfl⟩, trivial⟩⟩
    · intro i j _
      exact ⟨disjoint_left.mpr (fun e => Empty.elim e), subset_univ _⟩
  have hπ : ∀ b : Bool, ∀ i : Fin 1,
      IsOrderingOf (Set.univ ∩ V(A_of b i.succ)) (fun _ : Fin 1 => b) := by
    intro b i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    refine ⟨fun x y _ => Subsingleton.elim x y, ?_⟩
    change Set.range (fun _ : Fin 1 => b) = Set.univ ∩ {b}
    ext x
    simp
  have hDet : R_H.HasDetailLE 0 := by
    refine ⟨finite_univ, finite_empty, by simp [R_H, G_one], ?_⟩
    have hdiff : V(R_H.G.toGraph) \ Set.range R_H.roots = ∅ := by
      ext ⟨⟩
      simp [R_H, G_one]
    simp [hdiff]
  have hfolio : ∀ i : Fin 1,
      HasSameDeltaFolio
        (subRootedDigraph R_G'.G (A_of true i.succ) ((hdiv true).1 i.succ) (fun _ : Fin 1 => true)
          (fun j => ((hπ true i).2 ▸ mem_range_self j).2))
        (subRootedDigraph R_G.G (A_of false i.succ) ((hdiv false).1 i.succ) (fun _ : Fin 1 => false)
          (fun j => ((hπ false i).2 ▸ mem_range_self j).2))
        0 := by
    intro i _ _ R_H' _
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact ⟨hasRootedDigraphModel_single_noEdge_transfer,
      hasRootedDigraphModel_single_noEdge_transfer⟩
  have hα_surj : Bool.not '' (Set.univ : Set Bool) = Set.univ := by
    ext b
    simp only [mem_image, mem_univ, true_and, iff_true]
    exact ⟨!b, Bool.not_not b⟩
  have hφ : IsRootedDigraphModel R_G R_H (fun _ => Graph.noEdge {false} Empty) Empty.elim :=
    ⟨fun _ _ => ⟨subset_univ _, fun _ _ _ h => h.elim⟩,
      fun _ _ => ⟨⟨false, rfl⟩, fun x hx y hy => by cases hx; cases hy; exact ⟨GraphWalk.nil rfl⟩⟩,
      fun v₁ _ v₂ _ hne => (hne (Subsingleton.elim v₁ v₂)).elim,
      fun _ => rfl,
      fun e => Empty.elim e,
      fun e => Empty.elim e,
      fun e => Empty.elim e,
      fun e => Empty.elim e,
      fun e => Empty.elim e⟩
  have hconn_noEdge_univ : ∀ {H : Graph Bool Empty},
      V(H) = Set.univ → ∀ u v : Bool, AreConnectedIn H u v ↔ u = v := by
    intro H hVH u v
    constructor
    · rintro ⟨C, hC, huC, hvC⟩
      obtain ⟨W⟩ := hC.2.1.2 u huC v hvC
      cases W with
      | nil _ => rfl
      | @cons _ _ _ e _ _ => exact Empty.elim e
    · rintro rfl
      rw [areConnectedIn_self_iff, hVH]
      exact trivial
  have hV_inter : V(subgraphInter R_G.G.toGraph
      (minimalModelSubgraph R_G R_H (fun _ => Graph.noEdge {false} Empty) Set.univ)
      (A_of false 0)) = Set.univ := by
    ext b
    simp [subgraphInter, minimalModelSubgraph, subgraphUnion, A_of]
  have hL'0_conn : ∀ u ∈ (Set.univ : Set Bool), ∀ v ∈ (Set.univ : Set Bool),
      AreConnectedIn (A_of true 0) u v ↔
        AreConnectedIn
          (subgraphInter R_G.G.toGraph
            (minimalModelSubgraph R_G R_H (fun _ => Graph.noEdge {false} Empty) Set.univ)
            (A_of false 0))
          (!u) (!v) := by
    intro u _ v _
    rw [hconn_noEdge_univ rfl, hconn_noEdge_univ hV_inter]
    exact ⟨congrArg Bool.not, Bool.not_inj⟩
  obtain ⟨φV', _, hMod', _, hmeets'⟩ :=
    @h63_bad Bool Empty Bool Unit Empty 1 1 0 R_G R_G' R_H
      Set.univ (A_of false) (fun _ => 1) (fun _ _ => false)
      Set.univ (A_of true) (fun _ _ => true) Bool.not
      (fun _ => Graph.noEdge {false} Empty) Empty.elim (A_of true 0)
      (hdiv false) (hπ false) (hdiv true) (hπ true)
      (subset_refl _) (fun _ => trivial) (subset_refl _)
      (subset_refl _) (fun _ => trivial) (subset_refl _)
      hDet hfolio hα_surj (fun _ _ => rfl) hφ (fun e => Empty.elim e)
      (fun _ _ => ⟨0, false, rfl, rfl⟩) le_rfl hL'0_conn
  have hfalse_mem : false ∈ V(φV' ()) := hMod'.root_mem 0
  obtain ⟨i, x, hx_φ, hx_A'⟩ := hmeets' () trivial
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have hx_true : x = true := hx_A'
  subst hx_true
  obtain ⟨W⟩ := (hMod'.connected_of_mem () trivial).2 false hfalse_mem true hx_φ
  cases W with
  | @cons _ _ _ e _ _ => exact Empty.elim e

end GraphMinor.GM22
