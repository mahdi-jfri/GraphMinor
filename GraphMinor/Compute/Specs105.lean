module

public import GraphMinor.GM13.Section7Six
public import GraphMinor.GM13.Section10Free
public import GraphMinor.Compute.BranchDecomp
public import GraphMinor.Compute.Algorithm41Verified
public import GraphMinor.Compute.Algorithm65

/-!
# Interfaces and Bridge Lemmas for Graph Minors XIII, Algorithm (10.5)

This file defines the Word RAM calling conventions and specifications for the three subroutines
called by Algorithm (10.5) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths
Problem*, pages 108–109, together with the bridge lemmas connecting their inputs and outputs to
`GM13`:

1. **`MultiDigraph.deleteVertices` and Step (3) Clique Model Bridge:**
   Deleting a terminal subset `Z : Finset (Fin n)` from `G : MultiDigraph n` by zeroing edge
   multiplicities incident with `Z`, and proving that a model of `K_p` in `G \ Z` is also a model
   of `K_p` in `G` (`MultiDigraph.isCliqueModel_of_deleteVertices`) and yields
   `GM13.HasGraphModel (GM16.completeGraph p)` in both `(G.toGMDigraph.deleteVertices Z.toNatSet).toGraph`
   and `G.toGMDigraph.toGraph`.
2. **Written-Out Branch-Decompositions (`IsWrittenDigraphBD`):**
   Branch-decompositions of `D : ComputeDigraph` of width `≤ B` written out in parent-array and
   leaf-map format (`BranchDecomp.lean`), together with the bridge to `GM13.GraphBranchWidthLE`.
3. **Shared Case (iii) Block Decoder (`Case3BlockDecoder`) and Step (4) Hypothesis C Bridge:**
   The shared decoder for the opaque wall/society/rural-division block passed from Case (iii) of
   Algorithm (9.9) to Algorithm (10.4), and the Step (4) lemma `step4_hypothesisC_of_case3`.
4. **Subroutine Interfaces (`Alg99Spec`, `Alg104Spec`, `Alg41Spec`):**
   Word RAM specifications for Algorithms (9.9) (page 104), (10.4) (page 107), and (4.1) (page 75).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph GraphMinor.Surface GraphMinor.GM09

/-! ### Section 1: Deleting a Vertex Subset `Z` by Zeroing Incident Edge Multiplicities -/

/-- The subdigraph `G \ Z` of `G : MultiDigraph n` represented on the same index set `Fin n` by
retaining only edges whose endpoints both lie outside `Z`. -/
def MultiDigraph.deleteVertices {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    MultiDigraph n where
  edgeMult u v := if u ∉ Z ∧ v ∉ Z then G.edgeMult u v else 0

@[simp]
theorem MultiDigraph.deleteVertices_edgeMult {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (u v : Fin n) :
    (G.deleteVertices Z).edgeMult u v = if u ∉ Z ∧ v ∉ Z then G.edgeMult u v else 0 :=
  rfl

theorem MultiDigraph.deleteVertices_edgeMult_le {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (u v : Fin n) :
    (G.deleteVertices Z).edgeMult u v ≤ G.edgeMult u v := by
  simp only [deleteVertices_edgeMult]
  split_ifs <;> omega

theorem MultiDigraph.toSimpleGraph_deleteVertices_le {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVertices Z).toSimpleGraph ≤ G.toSimpleGraph := by
  intro u v hadj
  rw [MultiDigraph.toSimpleGraph_adj] at hadj ⊢
  have h1 := G.deleteVertices_edgeMult_le Z u v
  have h2 := G.deleteVertices_edgeMult_le Z v u
  omega

/-- Step (3) of GM XIII Algorithm (10.5) (page 109):
"If we obtain a model of $K_p$ in $G_i \setminus Z$ and hence in $G_i$, we apply (6.2) to find a vertex $v$
of $G_i$ irrelevant to the $\delta$-folio of $G_i$ relative to $Z$; we set $G_{i+1} = G_i \setminus v$ and return
for the next iteration." -/
theorem MultiDigraph.isCliqueModel_of_deleteVertices {n p : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) {X : Fin p → Finset (Fin n)}
    (hmodel : IsCliqueModel (G.deleteVertices Z).toSimpleGraph p X) :
    IsCliqueModel G.toSimpleGraph p X := by
  have hle := G.toSimpleGraph_deleteVertices_le Z
  refine ⟨fun i => ⟨(hmodel.1 i).1, induce_connected_of_le (fun _ _ h => hle h) (hmodel.1 i).2⟩,
    hmodel.2.1, fun i j hij => ?_⟩
  rcases hmodel.2.2 i j hij with ⟨u, hu, v, hv, hadj⟩
  exact ⟨u, hu, v, hv, hle hadj⟩

/-- Bridge from `IsCliqueModel G.toSimpleGraph p X` to `GM13.HasGraphModel (GM16.completeGraph p)`
on `G.toGMDigraph.toGraph`. -/
theorem MultiDigraph.hasGraphModel_toGMDigraph_of_isCliqueModel {n p : ℕ}
    (G : MultiDigraph n) {X : Fin p → Finset (Fin n)}
    (hmodel : IsCliqueModel G.toSimpleGraph p X) :
    GM13.HasGraphModel (GM16.completeGraph p) G.toGMDigraph.toGraph := by
  have : Nonempty (ℕ × ℕ × ℕ) := ⟨(0, 0, 0)⟩
  let sub (j : Fin p) : GM13.Digraph ℕ (ℕ × ℕ × ℕ) := G.toGMDigraph.induce (X j).toNatSet
  apply GM13.hasGraphModel_completeGraph_of_connected_subgraphs (sub := sub)
  · intro j
    exact G.toGMDigraph.induce_isSubdigraph _
  · intro j
    exact isConnected_induce_toNatSet G (hmodel.1 j).1 (hmodel.1 j).2
  · intro j₁ j₂ hne
    dsimp [sub]
    rw [vertexSet_induce_toNatSet, vertexSet_induce_toNatSet, Set.disjoint_left]
    intro x hx₁ hx₂
    rcases hx₁ with ⟨u, hu₁, rfl⟩
    have hu₂ : u ∈ X j₂ := (mem_toNatSet_iff (X j₂) u).mp hx₂
    exact Finset.disjoint_left.mp (hmodel.2.1 j₁ j₂ hne) hu₁ hu₂
  · intro j₁ j₂ hlt
    rcases hmodel.2.2 j₁ j₂ (ne_of_lt hlt) with ⟨u, hu, w, hw, hadj_uw⟩
    exact hasEdgeBetween_induce_toNatSet_of_adj G hu hw hadj_uw

theorem MultiDigraph.toGMDigraph_deleteVertices_edgeSet_eq {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVertices Z).toGMDigraph.edgeSet =
      (G.toGMDigraph.deleteVertices Z.toNatSet).edgeSet := by
  ext ⟨u, v, k⟩
  simp only [MultiDigraph.toGMDigraph, MultiDigraph.deleteVertices,
    GM13.Digraph.deleteVertices, GM13.Digraph.induce, Set.mem_sdiff, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu, hv, hk⟩
    split_ifs at hk with hZ
    · refine ⟨⟨hu, hv, hk⟩, ⟨hv, ?_⟩, ⟨hu, ?_⟩⟩
      · intro hvZ
        exact hZ.2 ((mem_toNatSet_iff Z ⟨v, hv⟩).mp hvZ)
      · intro huZ
        exact hZ.1 ((mem_toNatSet_iff Z ⟨u, hu⟩).mp huZ)
    · omega
  · rintro ⟨⟨hu, hv, hk⟩, ⟨_, hvZ⟩, ⟨_, huZ⟩⟩
    refine ⟨hu, hv, ?_⟩
    have huNotZ : (⟨u, hu⟩ : Fin n) ∉ Z := fun h => huZ ((mem_toNatSet_iff Z ⟨u, hu⟩).mpr h)
    have hvNotZ : (⟨v, hv⟩ : Fin n) ∉ Z := fun h => hvZ ((mem_toNatSet_iff Z ⟨v, hv⟩).mpr h)
    rw [ite_eq_left ⟨huNotZ, hvNotZ⟩]
    exact hk

theorem MultiDigraph.isSubdigraph_deleteVertices_toGMDigraph {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.toGMDigraph.deleteVertices Z.toNatSet).IsSubdigraph (G.deleteVertices Z).toGMDigraph where
  vertexSet_subset := by
    intro x hx
    exact hx.1
  edgeSet_subset := by
    rw [G.toGMDigraph_deleteVertices_edgeSet_eq Z]
  head_eq _ _ := rfl
  tail_eq _ _ := rfl

/-- If `X` is a `K_p`-model in `(G.deleteVertices Z).toSimpleGraph` and every branch set `X i` is
disjoint from `Z`, then `(G.toGMDigraph.deleteVertices Z.toNatSet).toGraph` has a model of `K_p`. -/
theorem MultiDigraph.hasGraphModel_deleteVertices_of_isCliqueModel {n p : ℕ}
    (G : MultiDigraph n) (Z : Finset (Fin n)) {X : Fin p → Finset (Fin n)}
    (hX_disj : ∀ j : Fin p, Disjoint (X j) Z)
    (hmodel : IsCliqueModel (G.deleteVertices Z).toSimpleGraph p X) :
    GM13.HasGraphModel (GM16.completeGraph p)
      (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph := by
  have : Nonempty (ℕ × ℕ × ℕ) := ⟨(0, 0, 0)⟩
  let sub (j : Fin p) : GM13.Digraph ℕ (ℕ × ℕ × ℕ) :=
    (G.deleteVertices Z).toGMDigraph.induce (X j).toNatSet
  apply GM13.hasGraphModel_completeGraph_of_connected_subgraphs (sub := sub)
  · intro j
    refine ⟨?_, ?_, fun _ _ => rfl, fun _ _ => rfl⟩
    · intro x hx
      rw [vertexSet_induce_toNatSet] at hx
      rcases hx with ⟨u, huXj, rfl⟩
      exact ⟨u.2, u.2, fun huZ =>
        Finset.disjoint_left.mp (hX_disj j) huXj ((mem_toNatSet_iff Z u).mp huZ)⟩
    · intro e he
      rw [← G.toGMDigraph_deleteVertices_edgeSet_eq Z]
      exact he.1
  · intro j
    exact isConnected_induce_toNatSet (G.deleteVertices Z) (hmodel.1 j).1 (hmodel.1 j).2
  · intro j₁ j₂ hne
    dsimp [sub]
    rw [vertexSet_induce_toNatSet, vertexSet_induce_toNatSet, Set.disjoint_left]
    intro x hx₁ hx₂
    rcases hx₁ with ⟨u, hu₁, rfl⟩
    have hu₂ : u ∈ X j₂ := (mem_toNatSet_iff (X j₂) u).mp hx₂
    exact Finset.disjoint_left.mp (hmodel.2.1 j₁ j₂ hne) hu₁ hu₂
  · intro j₁ j₂ hlt
    rcases hmodel.2.2 j₁ j₂ (ne_of_lt hlt) with ⟨u, hu, w, hw, hadj_uw⟩
    rcases hasEdgeBetween_induce_toNatSet_of_adj (G.deleteVertices Z) hu hw hadj_uw with
      ⟨e, he, hends⟩
    rw [G.toGMDigraph_deleteVertices_edgeSet_eq Z] at he
    exact ⟨e, he, hends⟩

/-! ### Section 2: Written-Out Branch-Decompositions and Bridge to `GM13.GraphBranchWidthLE` -/

@[simp]
theorem mem_digraphTreeEdgeCutVerts_iff {t : ℕ} (G : ComputeDigraph)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.numEdges → Fin t) (f : Sym2 (Fin t)) (w : Fin G.numVerts) :
    w ∈ digraphTreeEdgeCutVerts G T τ f ↔
      ∃ e₁ : Fin G.numEdges, ∃ e₂ : Fin G.numEdges,
        digraphIncident G w e₁ ∧ digraphIncident G w e₂ ∧
        ¬ (T.deleteEdges {f}).Reachable (τ e₁) (τ e₂) := by
  simp [digraphTreeEdgeCutVerts]

/-- A branch-decomposition of `D : ComputeDigraph` of width `≤ B`, written out on the Word RAM as
a tree size `t`, a parent array `p : ℕ → ℕ`, and an edge-to-leaf map `f_tau : ℕ → ℕ` (following the
parent-array format of `BranchDecomp.lean`). When `D.numEdges ≤ 1`, a 1-vertex tree `t = 1`
represents the trivial branch-decomposition of convention (GM XIII, Section 3, page 70). -/
def IsWrittenDigraphBD (B : ℕ) (D : ComputeDigraph) (t : ℕ) (p f_tau : ℕ → ℕ) : Prop :=
  0 < t ∧
  t ≤ 2 * D.numEdges + 1 ∧
  (∀ z, 0 < z → z < t → p z < z) ∧
  (∀ e < D.numEdges, f_tau e < t) ∧
  (D.numEdges ≤ 1 ∨
    ∃ (htau : ∀ e < D.numEdges, f_tau e < t),
      IsDigraphBranchDecompOfWidthLe B D (parentTree t p)
        (fun e : Fin D.numEdges => ⟨f_tau e.1, htau e.1 e.2⟩))

theorem isTernaryTree_of_isCubicOrLeafTree {t : ℕ} {T : SimpleGraph (Fin t)}
    [DecidableRel T.Adj] (hT : IsCubicOrLeafTree T) :
    GM10.IsTernaryTree T where
  isTree := hT.1
  degree_eq_one_or_three v := by
    convert hT.2 v

theorem coe_treeLeaves_eq_leafSet_of_cubic {t : ℕ} {T : SimpleGraph (Fin t)}
    [DecidableRel T.Adj] (hT : IsCubicOrLeafTree T) :
    (treeLeaves T : Set (Fin t)) = GM10.leafSet T := by
  ext v
  simp only [Finset.mem_coe, mem_treeLeaves, GM10.leafSet, Set.mem_ofPred_eq]
  have hleaf : GM10.IsLeaf T v ↔ T.degree v ≤ 1 := by
    unfold GM10.IsLeaf
    congr!
  rw [hleaf]
  rcases hT.2 v with h1 | h3 <;> omega

theorem toGMDigraph_toGraph_inc_iff_getElem {n : ℕ} (G : MultiDigraph n)
    (i : Fin G.directedEdgesList.length) (w : Fin n) :
    G.toGMDigraph.toGraph.Inc (G.edgeEquiv i).1 w.1 ↔
      digraphIncident G.toComputeDigraph w i := by
  have hi : i.1 < G.directedEdgesList.length := i.2
  have hpair := G.getElem_directedEdgeTriples_fst_snd i.1 hi
  have htail : (G.edgeEquiv i).1.1 = (G.toComputeDigraph.tail i).1 := by
    dsimp [MultiDigraph.edgeEquiv, MultiDigraph.edgeToGMTriple, MultiDigraph.toComputeDigraph]
    exact congrArg Prod.fst hpair
  have hhead : (G.edgeEquiv i).1.2.1 = (G.toComputeDigraph.head i).1 := by
    dsimp [MultiDigraph.edgeEquiv, MultiDigraph.edgeToGMTriple, MultiDigraph.toComputeDigraph]
    exact congrArg Prod.snd hpair
  unfold digraphIncident
  constructor
  · rintro ⟨u, _, ⟨heq1, _⟩ | ⟨_, heq1⟩⟩
    · change (G.edgeEquiv i).1.2.1 = w.1 at heq1
      rw [hhead] at heq1
      exact Or.inl (Fin.ext heq1)
    · change (G.edgeEquiv i).1.1 = w.1 at heq1
      rw [htail] at heq1
      exact Or.inr (Fin.ext heq1)
  · intro hinc
    have he_mem : (G.edgeEquiv i).1 ∈ G.toGMDigraph.edgeSet := (G.edgeEquiv i).2
    rcases hinc with hhead_eq | htail_eq
    · refine ⟨(G.edgeEquiv i).1.1, he_mem, Or.inl ⟨?_, rfl⟩⟩
      change (G.edgeEquiv i).1.2.1 = w.1
      rw [hhead, hhead_eq]
    · refine ⟨(G.edgeEquiv i).1.2.1, he_mem, Or.inr ⟨rfl, ?_⟩⟩
      change (G.edgeEquiv i).1.1 = w.1
      rw [htail, htail_eq]

/-- Any `IsDigraphBranchDecompOfWidthLe B G.toComputeDigraph T τ` induces a `GM13` branch-decomposition
of `G.toGMDigraph.toGraph` of width `≤ B`. -/
theorem graphBranchWidthLE_toGMDigraph_of_isDigraphBranchDecompOfWidthLe {n t B : ℕ}
    (G : MultiDigraph n) (ht : 0 < t)
    (T : SimpleGraph (Fin t)) [DecidableRel T.Adj]
    (τ : Fin G.toComputeDigraph.numEdges → Fin t)
    (hbd : IsDigraphBranchDecompOfWidthLe B G.toComputeDigraph T τ) :
    GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B := by
  classical
  right
  let τ_gm (e : ℕ × ℕ × ℕ) : Fin t :=
    if he : e ∈ G.toGMDigraph.edgeSet then
      τ (G.edgeEquiv.symm ⟨e, he⟩)
    else ⟨0, ht⟩
  have hτ_eq : ∀ i : Fin G.directedEdgesList.length, τ_gm (G.edgeEquiv i).1 = τ i := by
    intro i
    have he_mem : (G.edgeEquiv i).1 ∈ G.toGMDigraph.edgeSet := (G.edgeEquiv i).2
    change (if he : (G.edgeEquiv i).1 ∈ G.toGMDigraph.edgeSet then
      τ (G.edgeEquiv.symm ⟨(G.edgeEquiv i).1, he⟩) else ⟨0, ht⟩) = τ i
    rw [dite_eq_left he_mem, Subtype.eta, Equiv.symm_apply_apply]
  refine ⟨Fin t, inferInstance, T, τ_gm, ⟨Or.inr (isTernaryTree_of_isCubicOrLeafTree hbd.1), ?_⟩, ?_⟩
  · rw [← coe_treeLeaves_eq_leafSet_of_cubic hbd.1]
    refine ⟨fun e he => ?_, fun e₁ he₁ e₂ he₂ heq => ?_, fun v hv => ?_⟩
    · change e ∈ G.toGMDigraph.edgeSet at he
      dsimp [τ_gm]
      rw [dite_eq_left he]
      exact hbd.2.1.1 (Set.mem_univ _)
    · change e₁ ∈ G.toGMDigraph.edgeSet at he₁
      change e₂ ∈ G.toGMDigraph.edgeSet at he₂
      dsimp [τ_gm] at heq
      rw [dite_eq_left he₁, dite_eq_left he₂] at heq
      have hinj := hbd.2.1.2.1 (Set.mem_univ _) (Set.mem_univ _) heq
      exact congrArg Subtype.val (G.edgeEquiv.symm.injective hinj)
    · rcases hbd.2.1.2.2 hv with ⟨i, _, rfl⟩
      exact ⟨(G.edgeEquiv i).1, (G.edgeEquiv i).2, hτ_eq i⟩
  · unfold GM13.graphBranchDecompWidth
    by_cases hE_empty : (GM13.graphBranchEdgeOrder G.toGMDigraph.toGraph T τ_gm '' T.edgeSet).Nonempty
    · refine csSup_le hE_empty ?_
      rintro _ ⟨f, hf, rfl⟩
      have hf_fin : f ∈ T.edgeFinset := Set.mem_toFinset.mpr hf
      have hcut_eq :
          {v ∈ V(G.toGMDigraph.toGraph) | ∃ f₁ ∈ E(G.toGMDigraph.toGraph),
            ∃ f₂ ∈ E(G.toGMDigraph.toGraph),
            ¬ (T.deleteEdges {f}).Reachable (τ_gm f₁) (τ_gm f₂) ∧
            G.toGMDigraph.toGraph.Inc f₁ v ∧ G.toGMDigraph.toGraph.Inc f₂ v} =
          (digraphTreeEdgeCutVerts G.toComputeDigraph T τ f).toNatSet := by
        ext x
        simp only [Finset.toNatSet, Set.mem_image, Set.mem_sep_iff]
        constructor
        · rintro ⟨hxV, e₁, he₁, e₂, he₂, hnr, hinc₁, hinc₂⟩
          let w : Fin n := ⟨x, hxV⟩
          let i₁ := G.edgeEquiv.symm ⟨e₁, he₁⟩
          let i₂ := G.edgeEquiv.symm ⟨e₂, he₂⟩
          have he₁_eq : (G.edgeEquiv i₁).1 = e₁ :=
            congrArg Subtype.val (G.edgeEquiv.apply_symm_apply ⟨e₁, he₁⟩)
          have he₂_eq : (G.edgeEquiv i₂).1 = e₂ :=
            congrArg Subtype.val (G.edgeEquiv.apply_symm_apply ⟨e₂, he₂⟩)
          refine ⟨w, Finset.mem_coe.mpr ((mem_digraphTreeEdgeCutVerts_iff G.toComputeDigraph T τ f w).mpr
            ⟨i₁, i₂, ?_, ?_, ?_⟩), rfl⟩
          · rw [← he₁_eq] at hinc₁
            exact (toGMDigraph_toGraph_inc_iff_getElem G i₁ w).mp hinc₁
          · rw [← he₂_eq] at hinc₂
            exact (toGMDigraph_toGraph_inc_iff_getElem G i₂ w).mp hinc₂
          · rw [← hτ_eq i₁, ← hτ_eq i₂, he₁_eq, he₂_eq]
            exact hnr
        · rintro ⟨w, hw_mem, rfl⟩
          rcases (mem_digraphTreeEdgeCutVerts_iff G.toComputeDigraph T τ f w).mp
              (Finset.mem_coe.mp hw_mem) with ⟨i₁, i₂, hinc₁, hinc₂, hnr⟩
          refine ⟨w.2, (G.edgeEquiv i₁).1, (G.edgeEquiv i₁).2,
            (G.edgeEquiv i₂).1, (G.edgeEquiv i₂).2, ?_,
            (toGMDigraph_toGraph_inc_iff_getElem G i₁ w).mpr hinc₁,
            (toGMDigraph_toGraph_inc_iff_getElem G i₂ w).mpr hinc₂⟩
          rw [hτ_eq i₁, hτ_eq i₂]
          exact hnr
      unfold GM13.graphBranchEdgeOrder
      rw [hcut_eq, ncard_toNatSet]
      exact hbd.2.2 f hf_fin
    · simp [Set.not_nonempty_iff_eq_empty.mp hE_empty]

/-- Bridge from `IsWrittenDigraphBD B G.toComputeDigraph t p f_tau` to
`GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B`. -/
theorem IsWrittenDigraphBD.to_graphBranchWidthLE {n B t : ℕ} (G : MultiDigraph n)
    {p f_tau : ℕ → ℕ}
    (hw : IsWrittenDigraphBD B G.toComputeDigraph t p f_tau) :
    GM13.GraphBranchWidthLE G.toGMDigraph.toGraph B := by
  rcases hw with ⟨ht, _, _, _, hle1 | ⟨htau, hbd⟩⟩
  · left
    change G.toGMDigraph.edgeSet.ncard ≤ 1
    rw [G.ncard_edgeSet_toGMDigraph, ← G.length_directedEdgesList]
    exact hle1
  · exact graphBranchWidthLE_toGMDigraph_of_isDigraphBranchDecompOfWidthLe G ht
      (parentTree t p) (fun e => ⟨f_tau e.1, htau e.1 e.2⟩) hbd

/-- Equality of branch-width bounds between `(G.deleteVertices Z).toGMDigraph.toGraph` and
`(G.toGMDigraph.deleteVertices Z.toNatSet).toGraph`. -/
theorem graphBranchWidthLE_deleteVertices_of_deleteVertices {n B : ℕ}
    (G : MultiDigraph n) (Z : Finset (Fin n))
    (hbw : GM13.GraphBranchWidthLE (G.deleteVertices Z).toGMDigraph.toGraph B) :
    GM13.GraphBranchWidthLE (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph B := by
  let G₁ := (G.deleteVertices Z).toGMDigraph.toGraph
  let G₂ := (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph
  have hE_dig : (G.toGMDigraph.deleteVertices Z.toNatSet).edgeSet =
      (G.deleteVertices Z).toGMDigraph.edgeSet :=
    (G.toGMDigraph_deleteVertices_edgeSet_eq Z).symm
  have hE : E(G₂) = E(G₁) := hE_dig
  have hInc : ∀ e w, G₂.Inc e w ↔ G₁.Inc e w := by
    intro e w
    constructor
    · rintro ⟨u, he, hends⟩
      change e ∈ (G.toGMDigraph.deleteVertices Z.toNatSet).edgeSet at he
      rw [hE_dig] at he
      exact ⟨u, he, hends⟩
    · rintro ⟨u, he, hends⟩
      change e ∈ (G.deleteVertices Z).toGMDigraph.edgeSet at he
      rw [← hE_dig] at he
      exact ⟨u, he, hends⟩
  have hV_inc : ∀ e w, G₁.Inc e w → (w ∈ V(G₂) ↔ w ∈ V(G₁)) := by
    intro e w ⟨u, he, hends⟩
    have he₂ : e ∈ (G.toGMDigraph.deleteVertices Z.toNatSet).edgeSet := by
      rw [hE_dig]
      exact he
    rcases hends with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have hw₂ : G.toGMDigraph.head e ∈ (G.toGMDigraph.deleteVertices Z.toNatSet).vertexSet :=
        (G.toGMDigraph.deleteVertices Z.toNatSet).head_mem he₂
      have hw₁ : (G.deleteVertices Z).toGMDigraph.head e ∈ (G.deleteVertices Z).toGMDigraph.vertexSet :=
        (G.deleteVertices Z).toGMDigraph.head_mem he
      exact ⟨fun _ => hw₁, fun _ => hw₂⟩
    · have hw₂ : G.toGMDigraph.tail e ∈ (G.toGMDigraph.deleteVertices Z.toNatSet).vertexSet :=
        (G.toGMDigraph.deleteVertices Z.toNatSet).tail_mem he₂
      have hw₁ : (G.deleteVertices Z).toGMDigraph.tail e ∈ (G.deleteVertices Z).toGMDigraph.vertexSet :=
        (G.deleteVertices Z).toGMDigraph.tail_mem he
      exact ⟨fun _ => hw₁, fun _ => hw₂⟩
  rcases hbw with hle1 | ⟨ι, hfin, T, τ, hbd, hwidth⟩
  · left
    rw [hE]
    exact hle1
  · right
    refine ⟨ι, hfin, T, τ, ⟨hbd.1, ?_⟩, ?_⟩
    · rw [hE]
      exact hbd.2
    · have hord_eq : GM13.graphBranchEdgeOrder G₂ T τ = GM13.graphBranchEdgeOrder G₁ T τ := by
        funext f
        unfold GM13.graphBranchEdgeOrder
        congr 1
        ext w
        simp only [Set.mem_sep_iff, hE, hInc]
        constructor
        · rintro ⟨hw₂, f₁, hf₁, f₂, hf₂, hnr, hinc₁, hinc₂⟩
          exact ⟨(hV_inc f₁ w hinc₁).mp hw₂, f₁, hf₁, f₂, hf₂, hnr, hinc₁, hinc₂⟩
        · rintro ⟨hw₁, f₁, hf₁, f₂, hf₂, hnr, hinc₁, hinc₂⟩
          exact ⟨(hV_inc f₁ w hinc₁).mpr hw₁, f₁, hf₁, f₂, hf₂, hnr, hinc₁, hinc₂⟩
      unfold GM13.graphBranchDecompWidth at hwidth ⊢
      rw [hord_eq]
      exact hwidth

/-- Bridge from `IsWrittenDigraphBD B (G.deleteVertices Z).toComputeDigraph t p f_tau` to
`GM13.GraphBranchWidthLE (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph B`. -/
theorem IsWrittenDigraphBD.to_graphBranchWidthLE_deleteVertices {n B t : ℕ}
    (G : MultiDigraph n) (Z : Finset (Fin n)) {p f_tau : ℕ → ℕ}
    (hw : IsWrittenDigraphBD B (G.deleteVertices Z).toComputeDigraph t p f_tau) :
    GM13.GraphBranchWidthLE (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph B :=
  graphBranchWidthLE_deleteVertices_of_deleteVertices G Z (hw.to_graphBranchWidthLE (G.deleteVertices Z))

/-! ### Section 3: Shared Case (iii) Block Decoder and Step (4) Hypothesis C Lemma -/

/-- Shared pure data decoder for the Case (iii) block `(H, S_H, 𝒜, branch-decompositions)` produced
by Algorithm (9.9) on `G_i \ Z` and passed unchanged (together with `X' = X ∪ Z`) to Algorithm
(10.4) in Step (4) of Algorithm (10.5). -/
structure Case3BlockDecoder where
  /-- Decodes the wall `H` from `(n, G, X', block)`. -/
  wall : ∀ (n : ℕ), MultiDigraph n → Finset (Fin n) → List ℕ → GM13.Wall ℕ (ℕ × ℕ × ℕ)
  /-- Decodes the wall society `S_H` from `(n, G, X', block)`. -/
  society : ∀ (n : ℕ), MultiDigraph n → Finset (Fin n) → List ℕ → GM09.Society ℕ (ℕ × ℕ × ℕ)
  /-- Decodes the rural division `𝒜` from `(n, G, X', block)`. -/
  division : ∀ (n : ℕ), MultiDigraph n → Finset (Fin n) → List ℕ → Set (Graph ℕ (ℕ × ℕ × ℕ))
  /-- Decodes a branch-decomposition `(T, τ)` on `Fin t` for an interior member `A ∈ 𝒜` from
  `(n, G, X', block, A)`. -/
  branchDecomp : ∀ (n : ℕ), MultiDigraph n → Finset (Fin n) → List ℕ →
    Graph ℕ (ℕ × ℕ × ℕ) → Σ (t : ℕ), SimpleGraph (Fin t) × ((ℕ × ℕ × ℕ) → Fin t)

/-- Step (4) of GM XIII Algorithm (10.5) (page 109):
"Otherwise, we obtain $X$, $H$, $\mathcal{A}$ as in Hypothesis C (with $G$ replaced by $G_i \setminus Z$),
where $|X| \le \binom{p}{2} - 1$ and $H$ has height $h$. Put $X' = X \cup Z$; then $G_i$, $X'$, $H$, $\mathcal{A}$
also satisfy Hypothesis C." -/
theorem step4_hypothesisC_of_case3 {n ξ p ω : ℕ}
    (dec : Case3BlockDecoder)
    (G : MultiDigraph n) (Z X : Finset (Fin n)) (block : List ℕ)
    (hZ_card : Z.card ≤ ξ)
    (hdisj : Disjoint X Z)
    (hX_lt : X.card < p.choose 2)
    (hflat : GM13.IsFlatWallIn
      (deleteVertices (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph X.toNatSet)
      (dec.wall n G (X ∪ Z) block))
    (hsoc : GM13.IsWallSociety
      (deleteVertices (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph X.toNatSet)
      (dec.wall n G (X ∪ Z) block) (dec.society n G (X ∪ Z) block))
    (hrural : GM13.IsRuralDivision (dec.society n G (X ∪ Z) block)
      (dec.division n G (X ∪ Z) block))
    (hbd : ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      GM13.IsInteriorMember (dec.wall n G (X ∪ Z) block) (dec.division n G (X ∪ Z) block) A →
        let bd := dec.branchDecomp n G (X ∪ Z) block A
        E(A).ncard ≤ 1 ∨
          (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
            GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)) :
    let X' := X ∪ Z
    let H := dec.wall n G X' block
    let S_H := dec.society n G X' block
    let 𝒜 := dec.division n G X' block
    X'.card ≤ p.choose 2 + ξ - 1 ∧
    GM13.HypothesisC G.toGMDigraph X'.toNatSet.ncard X'.toNatSet H S_H 𝒜 ∧
    GM13.IsFlatWallIn (G.toGMDigraph.deleteVertices X'.toNatSet).toGraph H ∧
    ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      GM13.IsInteriorMember H 𝒜 A →
        let bd := dec.branchDecomp n G X' block A
        E(A).ncard ≤ 1 ∨
          (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
            GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω) := by
  intro X' H S_H 𝒜
  have hX'_eq : X'.toNatSet = X.toNatSet ∪ Z.toNatSet := toNatSet_union X Z
  have hZ_sub : Z.toNatSet ⊆ G.toGMDigraph.vertexSet := toNatSet_subset_lt Z
  have hZ_ncard : Z.toNatSet.ncard ≤ ξ := by
    rw [ncard_toNatSet]; exact hZ_card
  have hX_sub : X.toNatSet ⊆ V((G.toGMDigraph.deleteVertices Z.toNatSet).toGraph) := by
    rintro _ ⟨u, huX, rfl⟩
    exact ⟨u.2, u.2, fun huZ =>
      Finset.disjoint_left.mp hdisj huX ((mem_toNatSet_iff Z u).mp huZ)⟩
  have hX_ncard : X.toNatSet.ncard < p.choose 2 := by
    rw [ncard_toNatSet]; exact hX_lt
  rcases GM13.hypothesisC_union_of_deleteVertices G.isFinite_toGMDigraph hZ_sub hZ_ncard
      hX_sub hX_ncard hflat hsoc hrural with ⟨hXZ_le, hHypC⟩
  rw [← hX'_eq, ncard_toNatSet] at hXZ_le
  rw [← hX'_eq] at hHypC
  have hdel_eq : deleteVertices (G.toGMDigraph.deleteVertices Z.toNatSet).toGraph X.toNatSet =
      (G.toGMDigraph.deleteVertices X'.toNatSet).toGraph := by
    rw [GM13.deleteVertices_toGraph_eq, GM13.Digraph.deleteVertices_deleteVertices, hX'_eq]
  have hflat' : GM13.IsFlatWallIn (G.toGMDigraph.deleteVertices X'.toNatSet).toGraph H :=
    hdel_eq ▸ hflat
  exact ⟨hXZ_le, hHypC, hflat', hbd⟩

/-! ### Section 4: Section 10 Parameters and Subroutine Interfaces `(9.9)`, `(10.4)`, `(4.1)` -/

/-- The wall height parameter `h` in GM XIII Algorithm (10.5) (page 108):
for `p = alg62Param ξ δ` and `q = p.choose 2 + ξ - 1`,
`h = sec10MaxWallHeight GM13.theorem_10_2_proof q δ`. -/
noncomputable def sec105WallHeight
    (ξ δ : ℕ) : ℕ :=
  let p := alg62Param ξ δ
  let q := p.choose 2 + ξ - 1
  GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ

theorem two_le_and_even_sec105WallHeight
    (ξ δ : ℕ) :
    2 ≤ sec105WallHeight ξ δ ∧ Even (sec105WallHeight ξ δ) :=
  GM13.two_le_and_even_sec10MaxWallHeight
    ((alg62Param ξ δ).choose 2 + ξ - 1) δ

/-- The branch-width parameter `ω` in GM XIII Algorithm (10.5) (page 108) provided by (9.8)/(9.9)
for `p = alg62Param ξ δ` and `h = sec105WallHeight ξ δ`. -/
noncomputable def sec105BranchWidth
    (ξ δ : ℕ) : ℕ :=
  let p := alg62Param ξ δ
  let h := sec105WallHeight ξ δ
  let hh := two_le_and_even_sec105WallHeight ξ δ
  (GM13.theorem_9_8_parallel.{0, 0} p h hh.1 hh.2).choose

/-- Base array index `30 + p` for subroutine communication in Algorithm (10.5), chosen strictly
above the working arrays `0 .. 18 + p + 9` used by `(6.2)`, `(6.5)`, and `(10.5)`. -/
def alg105ArrBase (p : ℕ) : ℕ :=
  30 + p

/-- Word RAM interface for **Graph Minors XIII, Algorithm (9.9)** (page 104), as invoked in Step (1)
of the recursion of Algorithm (10.5) (page 108) on `G_i \ Z_i`:

*Input:* In array `alg105ArrBase p`, the encoding `(G_i.deleteVertices Z_i).enc` of `G_i \ Z_i`,
and in array `alg105ArrBase p + 1`, the indicator bitlist `bitSetList Z_i` of `Z_i ⊆ V(G_i)`.
*Output:* A case tag in `s'.regs 51 ∈ {0, 1, 2}`:
- Case (i) (`s'.regs 51 = 0`): a branch-decomposition `(t, par, f_tau)` of `G_i \ Z_i` of width
  `≤ ω` written out (`t = s'.regs 52`, `par` in array `alg105ArrBase p + 2`, `f_tau` in array
  `alg105ArrBase p + 3`);
- Case (ii) (`s'.regs 51 = 1`): a model `X : Fin p → Finset (Fin n_i)` of `K_p` in `G_i \ Z_i`
  written as `encBitSetsUpTo X p` in array `alg105ArrBase p + 2`;
- Case (iii) (`s'.regs 51 = 2`): a vertex subset `X ⊆ V(G_i \ Z_i)` (`Disjoint X Z_i`) with
  `|X| < C(p, 2)` in array `alg105ArrBase p + 2` (`bitSetList X`) and an encoded block `block` in
  array `alg105ArrBase p + 3` whose decoding via `dec` yields a flat wall `H` of height `h` in
  `(G_i \ Z_i) \ X`, its wall society `S_H`, a rural division `𝒜` of `S_H`, and for each interior
  member `A` of `𝒜` a branch-decomposition `dec.branchDecomp n_i G_i X' block A` of `A` of width
  `≤ ω` (or `E(A).ncard ≤ 1`).
*Running time:* `O(vε)` (`C * (n_i + 1) * (n_i + m_del + 1)`). -/
def Alg99Spec (dec : Case3BlockDecoder) (p h ω : ℕ) : Prop :=
  let b := alg105ArrBase p
  ∃ (prog : Cmd) (C c : ℕ), 0 < c ∧ 0 < C ∧
    ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i)) (s : State),
      let D_del := G_i.deleteVertices Z_i
      let N := n_i + D_del.numEdges + 1
      wordSize c N ≤ w →
      s.arrs b = D_del.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      ∃ s' time,
        Exec w prog s s' time ∧
        time ≤ C * (n_i + 1) * N ∧
        (∀ r < 50, s'.regs r = s.regs r) ∧
        (∀ a < b, s'.arrs a = s.arrs a) ∧
        ((s'.regs 51 = 0 ∧
            ∃ (t : ℕ) (par f_tau : ℕ → ℕ),
              s'.regs 52 = t ∧
              (s'.arrs (b + 2)).length = t ∧
              (∀ z < t, (s'.arrs (b + 2)).getD z 0 = par z) ∧
              (s'.arrs (b + 3)).length = D_del.numEdges ∧
              (∀ e < D_del.numEdges, (s'.arrs (b + 3)).getD e 0 = f_tau e) ∧
              IsWrittenDigraphBD ω D_del.toComputeDigraph t par f_tau) ∨
         (s'.regs 51 = 1 ∧
            ∃ X : Fin p → Finset (Fin n_i),
              s'.arrs (b + 2) = encBitSetsUpTo X p ∧
              (∀ j : Fin p, Disjoint (X j) Z_i) ∧
              IsCliqueModel D_del.toSimpleGraph p X) ∨
         (s'.regs 51 = 2 ∧
            ∃ (X : Finset (Fin n_i)) (block : List ℕ),
              s'.arrs (b + 2) = bitSetList X ∧
              s'.arrs (b + 3) = block ∧
              block.length ≤ C * N ∧
              (∀ x ∈ block, x < 2 ^ w) ∧
              Disjoint X Z_i ∧
              X.card < p.choose 2 ∧
              let X' := X ∪ Z_i
              let H := dec.wall n_i G_i X' block
              let S_H := dec.society n_i G_i X' block
              let 𝒜 := dec.division n_i G_i X' block
              H.height = h ∧
              GM13.IsFlatWallIn
                (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph
                  X.toNatSet) H ∧
              GM13.IsWallSociety
                (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph
                  X.toNatSet) H S_H ∧
              GM13.IsRuralDivision S_H 𝒜 ∧
              ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
                GM13.IsInteriorMember H 𝒜 A →
                  let bd := dec.branchDecomp n_i G_i X' block A
                  E(A).ncard ≤ 1 ∨
                    (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
                      GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)))

/-- Word RAM interface for **Graph Minors XIII, Algorithm (10.4)** (page 107), as invoked in Step (4)
of Algorithm (10.5) (page 109):

*Input:* `G_i` in array `alg105ArrBase p` (`G_i.enc`), `X'` in array `alg105ArrBase p + 1`
(`bitSetList X'`), and `block` in array `alg105ArrBase p + 3`, where `|X'| ≤ q` and the decoded
objects `H = dec.wall n_i G_i X' block`, `S_H = dec.society n_i G_i X' block`,
`𝒜 = dec.division n_i G_i X' block` satisfy Hypothesis C, `H.height = h`, and for each interior
member `A` of `𝒜` the decoded decomposition `dec.branchDecomp n_i G_i X' block A` is a
branch-decomposition of `A` of width `≤ ω` (or `E(A).ncard ≤ 1`).
*Output:* In `s'.regs 51`, a vertex `v : Fin n_i` irrelevant to the `δ`-folio of `G_i` relative to
`X'`.
*Running time:* `O(ε²)` (`C * (n_i + m_i + 1)²`). -/
def Alg104Spec (dec : Case3BlockDecoder) (p q δ h ω : ℕ) : Prop :=
  let b := alg105ArrBase p
  ∃ (prog : Cmd) (C c : ℕ), 0 < c ∧ 0 < C ∧
    ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (X' : Finset (Fin n_i)) (block : List ℕ) (s : State),
      let N := n_i + G_i.numEdges + 1
      let H := dec.wall n_i G_i X' block
      let S_H := dec.society n_i G_i X' block
      let 𝒜 := dec.division n_i G_i X' block
      wordSize c (N + block.length) ≤ w →
      X'.card ≤ q →
      GM13.HypothesisC G_i.toGMDigraph X'.toNatSet.ncard X'.toNatSet H S_H 𝒜 →
      H.height = h →
      (∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        GM13.IsInteriorMember H 𝒜 A →
          let bd := dec.branchDecomp n_i G_i X' block A
          E(A).ncard ≤ 1 ∨
            (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
              GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)) →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList X' →
      s.arrs (b + 3) = block →
      ∃ (s' : State) (time : ℕ) (v : Fin n_i),
        Exec w prog s s' time ∧
        time ≤ C * N ^ 2 ∧
        s'.regs 51 = v.1 ∧
        GM13.IsIrrelevantVertex G_i.toGMDigraph δ X'.toNatSet v.1 ∧
        (∀ r < 50, s'.regs r = s.regs r) ∧
        (∀ a < b, s'.arrs a = s.arrs a)

namespace Alg105

/-- Word RAM interface for **Graph Minors XIII, Algorithm (4.1)** (page 75), as invoked in Step (2)
of Algorithm (10.5) (page 109):

*Input:* `G_i` in array `alg105ArrBase p` (`G_i.enc`) with `n_i` in `s.regs 26`, `G_i.numEdges` in
`s.regs 28`, and expanded edge endpoints `tail` in array `alg105ArrBase p + 5` and `head` in array
`alg105ArrBase p + 6`; `Z_i` in array `alg105ArrBase p + 1` (`bitSetList Z_i`) with `|Z_i| ≤ ξ`;
and a written-out branch-decomposition `(t, par, f_tau)` of `G_i` of width `≤ B` (`t` in
`s.regs 52`, `par` in array `alg105ArrBase p + 2`, `f_tau` in array `alg105ArrBase p + 3`).
*Output:* In `outArr`, a word list `s'.arrs outArr` decoded by `decAlg41CodeOut δ x41` (for a valid
branch-decomposition code `x41 : Alg41CodeInput ξ B` of `(G_i, Z_i)`) to a certified output
satisfying `IsValidAlg41ReadCodeOutput δ x41 (decAlg41CodeOut δ x41 (s'.arrs outArr))` (whose
`.toFolioSetRep` represents the `δ`-folio of `G_i` relative to `Z_i` by
`IsValidAlg41CodeOutput.isDeltaFolioRep`, and whose entries carry concrete models in
`rootedDigraphOfZ G_i Z_i`).
*Running time:* `O(v + ε)` (`C * (n_i + m_i + 1)`). -/
def Alg41Spec (p ξ δ B : ℕ) : Prop :=
  let b := alg105ArrBase p
  ∃ (prog : Cmd) (C c : ℕ), 0 < c ∧ 0 < C ∧
    ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
      (t : ℕ) (par f_tau : ℕ → ℕ) (s : State),
      let N := n_i + G_i.numEdges + 1
      wordSize c N ≤ w →
      (hZ : Z_i.card ≤ ξ) →
      IsWrittenDigraphBD B G_i.toComputeDigraph t par f_tau →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      s.regs 26 = n_i →
      s.regs 28 = G_i.numEdges →
      s.regs 52 = t →
      (s.arrs (b + 2)).length = t →
      (∀ z < t, (s.arrs (b + 2)).getD z 0 = par z) →
      (s.arrs (b + 3)).length = G_i.numEdges →
      (∀ e < G_i.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) →
      s.arrs (b + 5) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
      s.arrs (b + 6) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
      ∃ (s' : State) (time : ℕ) (bdCode : List ℕ) (hbd_code : IsValidBranchDecompCode B G_i bdCode),
        let x41 : Alg41CodeInput ξ B := ⟨n_i, G_i, Z_i, hZ, bdCode, hbd_code⟩
        Exec w prog s s' time ∧
        time ≤ C * N ∧
        IsValidAlg41ReadCodeOutput δ x41 (decAlg41CodeOut δ x41 (s'.arrs outArr))

/-- Raw-serialized variant of `Alg41Spec` writing `encFolioSetRep F` directly into `outArr` (as
required by `IsValidFolioOutput` in `FolioStatement.lean`). -/
def Alg41RawSpec (p ξ δ B : ℕ) : Prop :=
  let b := alg105ArrBase p
  ∃ (prog : Cmd) (C c : ℕ), 0 < c ∧ 0 < C ∧
    ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
      (t : ℕ) (par f_tau : ℕ → ℕ) (s : State),
      let N := n_i + G_i.numEdges + 1
      wordSize c N ≤ w →
      Z_i.card ≤ ξ →
      IsWrittenDigraphBD B G_i.toComputeDigraph t par f_tau →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      s.regs 26 = n_i →
      s.regs 28 = G_i.numEdges →
      s.regs 52 = t →
      (s.arrs (b + 2)).length = t →
      (∀ z < t, (s.arrs (b + 2)).getD z 0 = par z) →
      (s.arrs (b + 3)).length = G_i.numEdges →
      (∀ e < G_i.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) →
      s.arrs (b + 5) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
      s.arrs (b + 6) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
      ∃ (s' : State) (time : ℕ) (F : FolioSetRep Z_i.card δ),
        Exec w prog s s' time ∧
        time ≤ C * N ∧
        s'.arrs outArr = encFolioSetRep F ∧
        IsDeltaFolioRep δ G_i Z_i F

end Alg105

/-- Output specification for Algorithm (10.5) on `x : FolioInput ξ` with branch-width bound `B`
when Step (2) invokes `alg41Prog` (`algorithm_4_1_code` in `Algorithm41.lean`):
there is a valid branch-decomposition code `x41 : Alg41CodeInput ξ B` for the terminal subdigraph
`(x41.G, x41.Z)` with `hZ_eq : x41.Z.card = x.Z.card` such that `decAlg41CodeOut δ x41 out` is a
certified output (`hvalid : IsValidAlg41ReadCodeOutput δ x41 (decAlg41CodeOut δ x41 out)`) whose
`δ`-folio representation `hvalid.toFolioSetRep.castCard hZ_eq` represents the `δ`-folio of `x.G`
relative to `x.Z` (`IsDeltaFolioRep δ x.G x.Z`). -/
def IsValidAlg105Output (δ B : ℕ) {ξ : ℕ} (x : FolioInput ξ) (out : List ℕ) : Prop :=
  ∃ (x41 : Alg41CodeInput ξ B) (hZ_eq : x41.Z.card = x.Z.card)
    (hvalid : IsValidAlg41ReadCodeOutput δ x41 (decAlg41CodeOut δ x41 out)),
    IsDeltaFolioRep δ x.G x.Z (hvalid.toFolioSetRep.castCard hZ_eq)

end GraphMinor.Compute
