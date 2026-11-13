module

public import GraphMinor.GM13.Section3
public import GraphMinor.GM13.Section6
public import GraphMinor.GM04.Main
public import GraphMinor.GM05.Main
public import GraphMinor.RST94.Theorem23
public import GraphMinor.Planar.Defs
import GraphMinor.Planar.Grid

@[expose] public section

namespace GraphMinor.GM13

open Set Function
open scoped Classical
open Graph SimpleGraph Hypergraph
open GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM10 GraphMinor.GM16

universe u v w

variable {α : Type u} {β : Type v} {α' : Type*} {β' : Type*}

/-- Every rooted digraph `(G, r)` and integer `δ ≥ 0` admits a modelling of its `δ`-folio
(Graph Minors XIII, Section 4, page 75). -/
lemma exists_isDeltaFolioModelling {k : ℕ} (G : RootedDigraph α β k) (δ : ℕ)
    [Nonempty α] [Nonempty β] :
    ∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
      (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
      IsDeltaFolioModelling G δ vMod eMod := by
  let vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β := fun H =>
    if h : H ∈ G.deltaFolio δ then h.1.2.choose else fun _ => G.digraph
  let eMod : RootedDigraph ℕ ℕ k → ℕ → β := fun H =>
    if h : H ∈ G.deltaFolio δ then h.1.2.choose_spec.choose else fun _ => Classical.arbitrary β
  refine ⟨vMod, eMod, fun H hH => ?_⟩
  dsimp only [vMod, eMod]
  rw [dite_eq_left hH, dite_eq_left hH]
  exact hH.1.2.choose_spec.choose_spec

/-- Set-theoretic inclusions for `Z_i`, `Z_j`, `Z_k` in Step (2) of **Graph Minors XIII,
Algorithm (4.1)** (page 76):
"Since $V(B_j \cap B_k) \subseteq Z_j \cap Z_k$ we can calculate the $\delta$-folio of
$B_j \cup B_k$ relative to $Z_j \cup Z_k$ from this information, by (2.2). Since
$Z_i \subseteq Z_j \cup Z_k$ and $B_j \cup B_k = B_i$, the $\delta$-folio of $B_i$ relative to
$Z_i$ can be calculated by (2.1)." -/
lemma algorithm_4_1_step_2_inclusions {A_i B_i A_j B_j A_k B_k : Digraph α β} {Z : Set α}
    (hsep_jk : B_i.IsSeparation B_j B_k)
    (hAi_sub : A_i.vertexSet ⊆ A_j.vertexSet ∩ A_k.vertexSet)
    (hBk_sub : B_k.vertexSet ⊆ A_j.vertexSet)
    (hBj_sub : B_j.vertexSet ⊆ A_k.vertexSet) :
    let Z_i := (A_i.vertexSet ∪ Z) ∩ B_i.vertexSet
    let Z_j := (A_j.vertexSet ∪ Z) ∩ B_j.vertexSet
    let Z_k := (A_k.vertexSet ∪ Z) ∩ B_k.vertexSet
    B_j.vertexSet ∩ B_k.vertexSet ⊆ Z_j ∩ Z_k ∧ Z_i ⊆ Z_j ∪ Z_k := by
  dsimp only
  refine ⟨?_, ?_⟩
  · rintro x ⟨hxBj, hxBk⟩
    exact ⟨⟨Or.inl (hBk_sub hxBk), hxBj⟩, ⟨Or.inl (hBj_sub hxBj), hxBk⟩⟩
  · rintro x ⟨hxAi | hxZ, hxBi⟩
    · have hxBjBk : x ∈ B_j.vertexSet ∪ B_k.vertexSet := hsep_jk.vertexSet_union ▸ hxBi
      rcases hxBjBk with hxBj | hxBk
      · exact Or.inl ⟨Or.inl (hAi_sub hxAi).1, hxBj⟩
      · exact Or.inr ⟨Or.inl (hAi_sub hxAi).2, hxBk⟩
    · have hxBjBk : x ∈ B_j.vertexSet ∪ B_k.vertexSet := hsep_jk.vertexSet_union ▸ hxBi
      rcases hxBjBk with hxBj | hxBk
      · exact Or.inl ⟨Or.inr hxZ, hxBj⟩
      · exact Or.inr ⟨Or.inr hxZ, hxBk⟩

/-- Dynamic programming combination step in Step (2) of **Graph Minors XIII, Algorithm (4.1)**
(page 76), using (2.2) (`theorem_2_2_proof`) followed by (2.1) (`theorem_2_1_proof`). -/
lemma algorithm_4_1_step_2_combine {B_i B_j B_k B_i' B_j' B_k' : Digraph α β}
    (hVBi : B_i.vertexSet.Finite)
    (hsep : B_i.IsSeparation B_j B_k)
    (hsep' : B_i'.IsSeparation B_j' B_k')
    {Z_i Z_j Z_k : Set α} {δ : ℕ}
    (hZj_eq : Z_j = (Z_j ∪ Z_k) ∩ B_j.vertexSet)
    (hZj'_eq : Z_j = (Z_j ∪ Z_k) ∩ B_j'.vertexSet)
    (hZk_eq : Z_k = (Z_j ∪ Z_k) ∩ B_k.vertexSet)
    (hZk'_eq : Z_k = (Z_j ∪ Z_k) ∩ B_k'.vertexSet)
    (hinter_sub : B_j.vertexSet ∩ B_k.vertexSet ⊆ Z_j ∩ Z_k)
    (hinter'_sub : B_j'.vertexSet ∩ B_k'.vertexSet ⊆ Z_j ∩ Z_k)
    (hZi_sub : Z_i ⊆ Z_j ∪ Z_k)
    (hZj : HasSameDeltaFolioRel B_j B_j' δ Z_j)
    (hZk : HasSameDeltaFolioRel B_k B_k' δ Z_k) :
    HasSameDeltaFolioRel B_i B_i' δ Z_i := by
  have hfin_inter : (B_j.vertexSet ∩ B_k.vertexSet).Finite :=
    (hVBi.subset hsep.sub_left.vertexSet_subset).inter_of_left _
  have hAB : B_j.vertexSet ∩ B_k.vertexSet ⊆ Z_j ∪ Z_k :=
    hinter_sub.trans (inter_subset_left.trans subset_union_left)
  have hAB' : B_j'.vertexSet ∩ B_k'.vertexSet ⊆ Z_j ∪ Z_k :=
    hinter'_sub.trans (inter_subset_left.trans subset_union_left)
  have hZ₁ : Z_j ∪ Z_k ⊆ B_i.vertexSet :=
    union_subset (hZj.1.trans hsep.sub_left.vertexSet_subset)
      (hZk.1.trans hsep.sub_right.vertexSet_subset)
  have hZ₂ : Z_j ∪ Z_k ⊆ B_i'.vertexSet :=
    union_subset (hZj.2.1.trans hsep'.sub_left.vertexSet_subset)
      (hZk.2.1.trans hsep'.sub_right.vertexSet_subset)
  have hZA : (Z_j ∪ Z_k) ∩ B_j.vertexSet = (Z_j ∪ Z_k) ∩ B_j'.vertexSet :=
    hZj_eq.symm.trans hZj'_eq
  have hZB : (Z_j ∪ Z_k) ∩ B_k.vertexSet = (Z_j ∪ Z_k) ∩ B_k'.vertexSet :=
    hZk_eq.symm.trans hZk'_eq
  have hUnion : HasSameDeltaFolioRel B_i B_i' δ (Z_j ∪ Z_k) :=
    theorem_2_2_proof hsep hsep' hfin_inter hAB hAB' hZ₁ hZ₂ hZA hZB
      (hZj_eq ▸ hZj) (hZk_eq ▸ hZk)
  exact theorem_2_1_proof hZi_sub hUnion

/-- Final combination step in Step (3) of **Graph Minors XIII, Algorithm (4.1)** (page 76):
"If $i = m + 1$, the folio of $B_m$ relative to $Z_m$ has been determined. We determine the
$\delta$-folio of $A_m$ relative to $(Z \cup V(B_m)) \cap V(A_m)$ (this is easy, since
$|V(A_m)| \le 2$), and we use (2.1) and (2.2) to determine the $\delta$-folio of $Z$ in
$A_m \cup B_m = G$." -/
lemma algorithm_4_1_step_3_combine {G A_m B_m G' A_m' B_m' : Digraph α β}
    (hVG : G.vertexSet.Finite)
    (hsep : G.IsSeparation A_m B_m)
    (hsep' : G'.IsSeparation A_m' B_m')
    {Z : Set α} (hZ : Z ⊆ G.vertexSet) (_hZ' : Z ⊆ G'.vertexSet) {δ : ℕ}
    (hZA_eq : (Z ∪ B_m.vertexSet) ∩ A_m.vertexSet = (Z ∪ B_m'.vertexSet) ∩ A_m'.vertexSet)
    (hZB_eq : (A_m.vertexSet ∪ Z) ∩ B_m.vertexSet = (A_m'.vertexSet ∪ Z) ∩ B_m'.vertexSet)
    (hAm : HasSameDeltaFolioRel A_m A_m' δ ((Z ∪ B_m.vertexSet) ∩ A_m.vertexSet))
    (hBm : HasSameDeltaFolioRel B_m B_m' δ ((A_m.vertexSet ∪ Z) ∩ B_m.vertexSet)) :
    HasSameDeltaFolioRel G G' δ Z := by
  let Z_A := (Z ∪ B_m.vertexSet) ∩ A_m.vertexSet
  let Z_B := (A_m.vertexSet ∪ Z) ∩ B_m.vertexSet
  have hinter_sub : A_m.vertexSet ∩ B_m.vertexSet ⊆ Z_A ∩ Z_B := by
    rintro x ⟨hxA, hxB⟩
    exact ⟨⟨Or.inr hxB, hxA⟩, ⟨Or.inl hxA, hxB⟩⟩
  have hinter'_sub : A_m'.vertexSet ∩ B_m'.vertexSet ⊆ Z_A ∩ Z_B := by
    rintro x ⟨hxA', hxB'⟩
    have hxZA : x ∈ Z_A := by
      rw [show Z_A = (Z ∪ B_m'.vertexSet) ∩ A_m'.vertexSet from hZA_eq]
      exact ⟨Or.inr hxB', hxA'⟩
    have hxZB : x ∈ Z_B := by
      rw [show Z_B = (A_m'.vertexSet ∪ Z) ∩ B_m'.vertexSet from hZB_eq]
      exact ⟨Or.inl hxA', hxB'⟩
    exact ⟨hxZA, hxZB⟩
  have hZ_sub : Z ⊆ Z_A ∪ Z_B := by
    intro x hxZ
    have hxAB : x ∈ A_m.vertexSet ∪ B_m.vertexSet := hsep.vertexSet_union ▸ hZ hxZ
    rcases hxAB with hxA | hxB
    · exact Or.inl ⟨Or.inl hxZ, hxA⟩
    · exact Or.inr ⟨Or.inr hxZ, hxB⟩
  have hZA_inter : Z_A = (Z_A ∪ Z_B) ∩ A_m.vertexSet := by
    ext x
    simp only [Z_A, Z_B, mem_inter_iff, mem_union]
    refine ⟨fun h => ⟨Or.inl h, h.2⟩, ?_⟩
    rintro ⟨h | ⟨_, hxB⟩, hxA⟩
    · exact h
    · exact ⟨Or.inr hxB, hxA⟩
  have hZA'_inter : Z_A = (Z_A ∪ Z_B) ∩ A_m'.vertexSet := by
    ext x
    rw [show Z_A = (Z ∪ B_m'.vertexSet) ∩ A_m'.vertexSet from hZA_eq]
    rw [show Z_B = (A_m'.vertexSet ∪ Z) ∩ B_m'.vertexSet from hZB_eq]
    simp only [mem_inter_iff, mem_union]
    refine ⟨fun h => ⟨Or.inl h, h.2⟩, ?_⟩
    rintro ⟨h | ⟨_, hxB⟩, hxA⟩
    · exact h
    · exact ⟨Or.inr hxB, hxA⟩
  have hZB_inter : Z_B = (Z_A ∪ Z_B) ∩ B_m.vertexSet := by
    ext x
    simp only [Z_A, Z_B, mem_inter_iff, mem_union]
    refine ⟨fun h => ⟨Or.inr h, h.2⟩, ?_⟩
    rintro ⟨⟨_, hxA⟩ | h, hxB⟩
    · exact ⟨Or.inl hxA, hxB⟩
    · exact h
  have hZB'_inter : Z_B = (Z_A ∪ Z_B) ∩ B_m'.vertexSet := by
    ext x
    rw [show Z_A = (Z ∪ B_m'.vertexSet) ∩ A_m'.vertexSet from hZA_eq]
    rw [show Z_B = (A_m'.vertexSet ∪ Z) ∩ B_m'.vertexSet from hZB_eq]
    simp only [mem_inter_iff, mem_union]
    refine ⟨fun h => ⟨Or.inr h, h.2⟩, ?_⟩
    rintro ⟨⟨_, hxA⟩ | h, hxB⟩
    · exact ⟨Or.inl hxA, hxB⟩
    · exact h
  exact algorithm_4_1_step_2_combine hVG hsep hsep'
    hZA_inter hZA'_inter hZB_inter hZB'_inter hinter_sub hinter'_sub hZ_sub hAm hBm

/-- **Graph Minors XIII, (4.1) Algorithm** (page 75):
"*Input:* A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$, and a
branch-decomposition $(T, \tau)$ of $G$ of width $\le \omega$.
*Output:* The $\delta$-folio of $G$ relative to $Z$, and a modelling of it.
*Running time:* $O(\varepsilon)$."

This is the correctness of the method. The RAM program, a bottom-up dynamic program over the edges
`f₁, …, f_m` of `T` (Steps (1)–(4)), and its `O(\varepsilon)` time bound are `GM13.algorithm_4_1`
in `Results.lean`. -/
theorem algorithm_4_1_correct [Nonempty α] [Nonempty β]
    {k : ℕ} (G : Digraph α β) (hVG : G.vertexSet.Finite)
    (Z : Set α) (hZ : Z ⊆ G.vertexSet)
    (r : Fin k → α) (hr : ∀ i, r i ∈ G.vertexSet)
    (δ : ℕ) :
    (∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
       (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
       IsDeltaFolioModelling (RootedDigraph.mk G r hr) δ vMod eMod) ∧
    (∀ {A_m B_m G' A_m' B_m' : Digraph α β},
      G.IsSeparation A_m B_m →
      G'.IsSeparation A_m' B_m' →
      Z ⊆ G'.vertexSet →
      (Z ∪ B_m.vertexSet) ∩ A_m.vertexSet = (Z ∪ B_m'.vertexSet) ∩ A_m'.vertexSet →
      (A_m.vertexSet ∪ Z) ∩ B_m.vertexSet = (A_m'.vertexSet ∪ Z) ∩ B_m'.vertexSet →
      HasSameDeltaFolioRel A_m A_m' δ ((Z ∪ B_m.vertexSet) ∩ A_m.vertexSet) →
      HasSameDeltaFolioRel B_m B_m' δ ((A_m.vertexSet ∪ Z) ∩ B_m.vertexSet) →
      HasSameDeltaFolioRel G G' δ Z) := by
  refine ⟨exists_isDeltaFolioModelling (RootedDigraph.mk G r hr) δ, ?_⟩
  intro A_m B_m G' A_m' B_m' hsep hsep' hZ' hZA hZB hAm hBm
  exact algorithm_4_1_step_3_combine hVG hsep hsep' hZ hZ' hZA hZB hAm hBm

/-- **Graph Minors XIII, (4.1) Algorithm** (page 75), numbered alias for `algorithm_4_1_correct`. -/
theorem theorem_4_1_proof [Nonempty α] [Nonempty β]
    {k : ℕ} (G : Digraph α β) (hVG : G.vertexSet.Finite)
    (Z : Set α) (hZ : Z ⊆ G.vertexSet)
    (r : Fin k → α) (hr : ∀ i, r i ∈ G.vertexSet)
    (δ : ℕ) :
    (∃ (vMod : RootedDigraph ℕ ℕ k → ℕ → Digraph α β)
       (eMod : RootedDigraph ℕ ℕ k → ℕ → β),
       IsDeltaFolioModelling (RootedDigraph.mk G r hr) δ vMod eMod) ∧
    (∀ {A_m B_m G' A_m' B_m' : Digraph α β},
      G.IsSeparation A_m B_m →
      G'.IsSeparation A_m' B_m' →
      Z ⊆ G'.vertexSet →
      (Z ∪ B_m.vertexSet) ∩ A_m.vertexSet = (Z ∪ B_m'.vertexSet) ∩ A_m'.vertexSet →
      (A_m.vertexSet ∪ Z) ∩ B_m.vertexSet = (A_m'.vertexSet ∪ Z) ∩ B_m'.vertexSet →
      HasSameDeltaFolioRel A_m A_m' δ ((Z ∪ B_m.vertexSet) ∩ A_m.vertexSet) →
      HasSameDeltaFolioRel B_m B_m' δ ((A_m.vertexSet ∪ Z) ∩ B_m.vertexSet) →
      HasSameDeltaFolioRel G G' δ Z) := by
  refine ⟨exists_isDeltaFolioModelling (RootedDigraph.mk G r hr) δ, ?_⟩
  intro A_m B_m G' A_m' B_m' hsep hsep' hZ' hZA hZB hAm hBm
  exact algorithm_4_1_step_3_combine hVG hsep hsep' hZ hZ' hZA hZB hAm hBm

/-- **Graph Minors XIII, (4.2) Theorem** (page 76):
"For every planar graph $H$ there is a number $\omega$ such that every graph with branch-width
$\ge \omega$ has a minor isomorphic to $H$." -/
theorem theorem_4_2_proof (H : Graph α' β') (hPlanar : IsPlanar H) :
    ∃ ω : ℕ, 2 ≤ ω ∧ ∀ (G : Graph α β), V(G).Finite → E(G).Finite →
      ¬ GraphBranchWidthLE G (ω - 1) → IsIsoMinor H G := by
  rcases Planar.exists_even_grid_minor_of_isPlanar hPlanar with ⟨θ, hθ6, _, hH_grid⟩
  let ω := 20 ^ (θ ^ 4 * (2 * θ - 1))
  have hω_pos : 0 < θ ^ 4 * (2 * θ - 1) := by
    refine Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have hω2 : 2 ≤ ω := by
    calc 2 ≤ 20 ^ 1 := by decide
      _ ≤ 20 ^ (θ ^ 4 * (2 * θ - 1)) := Nat.pow_le_pow_right (by decide) hω_pos
  refine ⟨ω, hω2, fun G hVG hEG hnot_bw => ?_⟩
  have hbw_gt : ¬ GM10.branchWidth (graphToHypergraph G hVG hEG) ≤ ω - 1 :=
    fun h => hnot_bw ((graphBranchWidthLE_iff_branchWidth_le G hVG hEG (ω - 1)).mpr h)
  have hθ_le : ω ≤ GM10.tangleNumber (graphToHypergraph G hVG hEG) := by
    have hle := branchWidth_le_tangleNumber (graphToHypergraph G hVG hEG)
    omega
  obtain ⟨𝒯, h𝒯⟩ := GM10.exists_isTangle_of_le_tangleNumber
    (G := graphToHypergraph G hVG hEG) (θ := ω) (by omega) hθ_le
  have hH_eq : graphToHypergraph G hVG hEG = Hypergraph.ofGraph G hVG hEG := rfl
  rw [hH_eq] at h𝒯
  have hGraph : (Hypergraph.ofGraph G hVG hEG).IsGraph := graphToHypergraph_isGraph G hVG hEG
  obtain ⟨W, hW⟩ := RST94.theorem_5_7 hGraph h𝒯 (g := θ) (by omega) le_rfl
  obtain ⟨ηe, hm, _⟩ := RST94.grid_model hW (by omega)
  exact hH_grid.trans
    (isIsoMinor_of_isMinorModel (GM01.gridGraph θ) G
      (Set.toFinite _) (Set.toFinite _) hVG hEG _ ηe hm)

/-- Any finite graph `G` with `GraphBranchWidthLE G ω` satisfies
`GM04.TreeWidthLE (Hypergraph.ofGraph G hVG hEG).toRooted (max (3 * ω / 2) 2)`. -/
lemma treeWidthLE_gm04_of_graphBranchWidthLE {G : Graph α β}
    (hVG : V(G).Finite) (hEG : E(G).Finite) {ω : ℕ} (hbw : GraphBranchWidthLE G ω) :
    GM04.TreeWidthLE (Hypergraph.ofGraph G hVG hEG).toRooted (max (3 * ω / 2) 2) := by
  let H := Hypergraph.ofGraph G hVG hEG
  have hbw_H : GM10.branchWidth H ≤ ω :=
    (graphBranchWidthLE_iff_branchWidth_le G hVG hEG ω).mp hbw
  have hγ_H : GM10.maxEdgeSize H ≤ 2 := maxEdgeSize_graphToHypergraph_le_two G hVG hEG
  have htw_H : GM10.treeWidthPlusOne H ≤ max (3 * ω / 2) 2 := by
    have h51 := (GM10.theorem_5_1_proof H).2
    omega
  obtain ⟨ι, hfin, T, τ, htd, hw_eq⟩ := GM10.exists_treeDecomposition_eq_treeWidthPlusOne H
  let _ : Fintype ι := hfin
  let m := Fintype.card ι
  let e : ι ≃ Fin m := Fintype.equivFin ι
  let K : SimpleGraph (Fin m) := T.map e.toEmbedding
  have htd_K : GM10.IsTreeDecomposition H K (τ ∘ e.symm) := htd.relabel e
  let D : Thomas.TreeDecomp H.skeleton H.vertexSet (Fin m) :=
    { T := K
      isTree := htd_K.isTree
      bag := fun t => (τ (e.symm t)).vertexSet
      iUnion_bag := by
        ext v
        simp [htd.vertex_mem_iff, e.symm.exists_congr_left]
      adj_mem_bag := by
        intro u v _ _ ⟨_, f, hfu, hfv⟩
        have hfH : f ∈ H.edgeSet := H.edge_mem_of_inc hfu
        obtain ⟨t, ht⟩ := htd.edge_mem_iff.mp hfH
        have hends := htd.ends_subset_vertexSet_of_edge_mem ht
        refine ⟨e t, ?_, ?_⟩
        · simp [hends hfu]
        · simp [hends hfv]
      inter_subset_bag := by
        intro t₁ t₂ t₃ hp
        exact (htd_K.inter_le hp).vertexSet_subset }
  have hG_graph : H.IsGraph := graphToHypergraph_isGraph G hVG hEG
  have hD_gm04 : GM04.IsTreeDecomposition H.toRooted (Thomas.rootedTreeOfIsTree D.isTree)
      (Thomas.gm04Bags D hG_graph) :=
    Thomas.isTreeDecomposition_gm04Bags D hG_graph
  have hw_D : D.WidthLE (max (3 * ω / 2) 2) := by
    intro t
    change (τ (e.symm t)).vertexSet.ncard ≤ max (3 * ω / 2) 2 + 1
    have hle : (τ (e.symm t)).vertexSet.ncard ≤ GM10.treeWidthPlusOne H :=
      (GM10.ncard_vertexSet_le_treeDecompWidthPlusOne τ (e.symm t)).trans hw_eq.le
    omega
  exact ⟨Thomas.rootedTreeOfIsTree D.isTree, Thomas.gm04Bags D hG_graph,
    hD_gm04, Thomas.widthLE_gm04Bags D hG_graph hw_D⟩

/-- **Graph Minors IV, (1.4)** (page 229), cited in the proof of **Graph Minors XIII, (4.3)**
(page 76): for any planar graph `H`, the class of all graphs with no minor isomorphic to `H` is
well-quasi-ordered by minors. -/
theorem gm04_theorem_1_4 (H : Graph α' β') (hPlanar : IsPlanar H)
    (G : ℕ → Graph α β) (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hno : ∀ n, ¬ IsIsoMinor H (G n)) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by
  obtain ⟨ω, hω2, h42⟩ := theorem_4_2_proof (α := α) (β := β) H hPlanar
  have hbw : ∀ n, GraphBranchWidthLE (G n) (ω - 1) := by
    intro n
    by_contra hnot
    exact hno n (h42 (G n) (hV n) (hE n) hnot)
  have htw : ∀ n, GM04.TreeWidthLE (Hypergraph.ofGraph (G n) (hV n) (hE n)).toRooted
      (max (3 * (ω - 1) / 2) 2) :=
    fun n => treeWidthLE_gm04_of_graphBranchWidthLE (hV n) (hE n) (hbw n)
  exact GM04.theorem_1_5_proved (max (3 * (ω - 1) / 2) 2) G hV hE htw

/-- If every sequence in `S` has a good pair `i < j` with `r (f i) (f j)`, then every subset
`T ⊆ S` has a finite basis `B : Finset X` with `↑B ⊆ T` such that every `x ∈ T` is `r`-above
some `b ∈ B`. -/
lemma exists_finset_basis_of_forall_seq {X : Type*} {r : X → X → Prop} {S T : Set X}
    (hT : T ⊆ S)
    (hseq : ∀ f : ℕ → X, (∀ n, f n ∈ S) → ∃ i j, i < j ∧ r (f i) (f j)) :
    ∃ B : Finset X, (↑B : Set X) ⊆ T ∧ ∀ x ∈ T, ∃ b ∈ B, r b x := by
  by_contra! hno
  let g : ℕ → {B : Finset X // (↑B : Set X) ⊆ T} :=
    Nat.rec ⟨∅, by simp⟩ (fun n prev =>
      let x := (hno prev.1 prev.2).choose
      have hxT : x ∈ T := (hno prev.1 prev.2).choose_spec.1
      ⟨insert x prev.1, by
        rintro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact hxT
        · exact prev.2 hy'⟩)
  let f : ℕ → X := fun n => (hno (g n).1 (g n).2).choose
  have hfT : ∀ n, f n ∈ T := fun n => (hno (g n).1 (g n).2).choose_spec.1
  have hfS : ∀ n, f n ∈ S := fun n => hT (hfT n)
  have hmem_succ : ∀ n, f n ∈ (g (n + 1)).1 := fun n => Finset.mem_insert_self _ _
  have hmono : ∀ m n, m ≤ n → (g m).1 ⊆ (g n).1 := by
    intro m n hle
    induction hle with
    | refl => exact Finset.Subset.refl _
    | step _ ih => exact ih.trans (Finset.subset_insert _ _)
  obtain ⟨i, j, hij, hrij⟩ := hseq f hfS
  have hfi_in_gj : f i ∈ (g j).1 := hmono (i + 1) j hij (hmem_succ i)
  exact (hno (g j).1 (g j).2).choose_spec.2 (f i) hfi_in_gj hrij

/-- Finite excluded-minor characterization from **Graph Minors IV, (1.4)** used at the start of the
proof of **Graph Minors XIII, (4.3)** (page 76):
"By Theorem (1.4) of [14], there is a finite list of graphs $H_1, \dots, H_k$ such that a graph $G$
is in $\mathcal{F}$ if and only if it has no minor isomorphic to any of $H_1, \dots, H_k$. Since
$\mathcal{F}$ does not contain every planar graph, some $H_i$ (say $H_1$) is planar." -/
theorem exists_finite_excluded_minors_of_planar (ℱ : Set (Graph α β))
    (hclosed : ∀ ⦃G₁ G₂ : Graph α β⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (H₀ : Graph α β) (hVH₀ : V(H₀).Finite) (hEH₀ : E(H₀).Finite)
    (hPlanar₀ : IsPlanar H₀) (hH₀_not : H₀ ∉ ℱ) :
    ∃ B : Finset (Graph α β),
      H₀ ∈ B ∧
      (∃ H₁ ∈ B, IsPlanar H₁) ∧
      (∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ H ∉ ℱ) ∧
      (∀ G : Graph α β, V(G).Finite → E(G).Finite →
        (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G)) := by
  let S : Set (Graph α β) := {G | V(G).Finite ∧ E(G).Finite ∧ ¬ IsIsoMinor H₀ G}
  let T : Set (Graph α β) := {G ∈ S | G ∉ ℱ}
  have hseq : ∀ f : ℕ → Graph α β, (∀ n, f n ∈ S) → ∃ i j, i < j ∧ IsIsoMinor (f i) (f j) := by
    intro f hf
    exact gm04_theorem_1_4 H₀ hPlanar₀ f (fun n => (hf n).1) (fun n => (hf n).2.1)
      (fun n => (hf n).2.2)
  obtain ⟨B₀, hB₀_sub, hB₀_basis⟩ :=
    exists_finset_basis_of_forall_seq (S := S) (T := T) (fun _ h => h.1) hseq
  let B : Finset (Graph α β) := insert H₀ B₀
  have hH₀_mem : H₀ ∈ B := Finset.mem_insert_self H₀ B₀
  have hB_props : ∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ H ∉ ℱ := by
    intro H hH
    rcases Finset.mem_insert.mp hH with rfl | hH₀
    · exact ⟨hVH₀, hEH₀, hH₀_not⟩
    · have hHT : H ∈ T := hB₀_sub hH₀
      exact ⟨hHT.1.1, hHT.1.2.1, hHT.2⟩
  refine ⟨B, hH₀_mem, ⟨H₀, hH₀_mem, hPlanar₀⟩, hB_props, fun G hVG hEG => ⟨?_, ?_⟩⟩
  · intro hGℱ H hHB hminor
    have hH := hB_props H hHB
    exact hH.2.2 (hclosed hH.1 hH.2.1 hVG hEG hminor hGℱ)
  · intro hall
    by_contra hG_not
    by_cases hminor₀ : IsIsoMinor H₀ G
    · exact hall H₀ hH₀_mem hminor₀
    · have hGT : G ∈ T := ⟨⟨hVG, hEG, hminor₀⟩, hG_not⟩
      obtain ⟨b, hbB₀, hminor_b⟩ := hB₀_basis G hGT
      exact hall b (Finset.mem_insert_of_mem hbB₀) hminor_b

/-- Convert `Relation.ReflTransGen G.Adj x y` into a `GraphWalk G x y`. -/
lemma graphWalk_nonempty_of_reflTransGen_adj {G : Graph α β} {x y : α}
    (hx : x ∈ V(G)) (h : Relation.ReflTransGen G.Adj x y) :
    Nonempty (GraphWalk G x y) := by
  induction h with
  | refl => exact ⟨GraphWalk.nil hx⟩
  | @tail b c _ hbc ih =>
    rcases ih with ⟨W⟩
    rcases hbc with ⟨e, hlink⟩
    exact ⟨W.append (GraphWalk.cons hlink (GraphWalk.nil hlink.right_mem))⟩

/-- Convert a `GraphWalk G x y` into `Relation.ReflTransGen G.Adj x y`. -/
lemma reflTransGen_adj_of_graphWalk {G : Graph α β} {x y : α}
    (W : GraphWalk G x y) : Relation.ReflTransGen G.Adj x y := by
  induction W with
  | nil _ => exact Relation.ReflTransGen.refl
  | cons hlink _ ih => exact Relation.ReflTransGen.head ⟨_, hlink⟩ ih

/-- In a minor model `IsMinorModel H D.toGraph ηv ηe`, each edge `e ∈ E(H)` has ends `u, v ∈ V(H)`
such that `D.head (ηe e) ∈ ηv u` and `D.tail (ηe e) ∈ ηv v`. -/
lemma exists_ends_in_minorModel_of_digraph {D : Digraph α β} {H : Graph α' β'}
    {ηv : α' → Set α} {ηe : β' → β} (hm : IsMinorModel H D.toGraph ηv ηe)
    {e : β'} (he : e ∈ E(H)) :
    ∃ u ∈ V(H), ∃ v ∈ V(H), H.IsLink e u v ∧
      D.head (ηe e) ∈ ηv u ∧ D.tail (ηe e) ∈ ηv v := by
  obtain ⟨u, v, huv⟩ := (H.edge_mem_iff_exists_isLink e).mp he
  have hu : u ∈ V(H) := huv.left_mem
  have hv : v ∈ V(H) := huv.right_mem
  have heD : ηe e ∈ D.edgeSet := hm.edge_mem e he
  have hinc_head : D.toGraph.Inc (ηe e) (D.head (ηe e)) :=
    ⟨D.tail (ηe e), heD, Or.inl ⟨rfl, rfl⟩⟩
  have hinc_tail : D.toGraph.Inc (ηe e) (D.tail (ηe e)) :=
    ⟨D.head (ηe e), heD, Or.inr ⟨rfl, rfl⟩⟩
  by_cases huv_eq : u = v
  · subst huv_eq
    have hloop := (hm.isLoopAt_iff u hu e he).mp huv
    exact ⟨u, hu, u, hu, huv, hloop _ hinc_head, hloop _ hinc_tail⟩
  · obtain ⟨x, hx, hinc_x⟩ := (hm.inc_iff u hu e he).mp huv.inc_left
    obtain ⟨y, hy, hinc_y⟩ := (hm.inc_iff v hv e he).mp huv.inc_right
    have hdisj : Disjoint (ηv u) (ηv v) := hm.vertex_disjoint u hu v hv huv_eq
    have hx_ht : x = D.head (ηe e) ∨ x = D.tail (ηe e) := by
      rcases hinc_x with ⟨z, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
    have hy_ht : y = D.head (ηe e) ∨ y = D.tail (ηe e) := by
      rcases hinc_y with ⟨z, _, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm
    rcases hx_ht with rfl | rfl <;> rcases hy_ht with hy_eq | hy_eq
    · exfalso
      exact disjoint_left.mp hdisj hx (hy_eq ▸ hy)
    · exact ⟨u, hu, v, hv, huv, hx, hy_eq ▸ hy⟩
    · exact ⟨v, hv, u, hu, huv.symm, hy_eq ▸ hy, hx⟩
    · exfalso
      exact disjoint_left.mp hdisj hx (hy_eq ▸ hy)

/-- If `HasSameDeltaFolioRel D D' δ ∅`, then any finite graph `H` with `V(H).ncard ≤ δ` and
`E(H).ncard ≤ δ` that is isomorphic to a minor of `D.toGraph` is also isomorphic to a minor of
`D'.toGraph`. -/
lemma isIsoMinor_of_hasSameDeltaFolioRel_empty [Nonempty β]
    {D D' : Digraph α β} (hfin : D.IsFinite) (hfin' : D'.IsFinite) {δ : ℕ}
    (hfolio : HasSameDeltaFolioRel D D' δ ∅)
    {H : Graph α' β'} (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hV_le : V(H).ncard ≤ δ) (hE_le : E(H).ncard ≤ δ)
    (hminor : IsIsoMinor H D.toGraph) :
    IsIsoMinor H D'.toGraph := by
  obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor hfin.finite_V hfin.finite_E hminor
  let nV := V(H).ncard
  let nE := E(H).ncard
  let eV : V(H) ≃ Fin nV := hVH.equivFin
  let eE : E(H) ≃ Fin nE := hEH.equivFin
  have hends (j : Fin nE) := exists_ends_in_minorModel_of_digraph hm (eE.symm j).2
  let uOf (j : Fin nE) : V(H) := ⟨(hends j).choose, (hends j).choose_spec.1⟩
  let vOf (j : Fin nE) : V(H) :=
    ⟨(hends j).choose_spec.2.choose, (hends j).choose_spec.2.choose_spec.1⟩
  have hlinkOf (j : Fin nE) : H.IsLink (eE.symm j).1 (uOf j).1 (vOf j).1 :=
    (hends j).choose_spec.2.choose_spec.2.1
  have hheadOf (j : Fin nE) : D.head (ηe (eE.symm j).1) ∈ ηv (uOf j).1 :=
    (hends j).choose_spec.2.choose_spec.2.2.1
  have htailOf (j : Fin nE) : D.tail (ηe (eE.symm j).1) ∈ ηv (vOf j).1 :=
    (hends j).choose_spec.2.choose_spec.2.2.2
  let H_nat : RootedDigraph ℕ ℕ 0 :=
    { digraph :=
        { vertexSet := ↑(Finset.range nV)
          edgeSet := ↑(Finset.range nE)
          head := fun j => if hj : j < nE then (eV (uOf ⟨j, hj⟩)).1 else 0
          tail := fun j => if hj : j < nE then (eV (vOf ⟨j, hj⟩)).1 else 0
          head_mem := fun j hj => by
            have hj' : j < nE := Finset.mem_range.mp hj
            simp only [Finset.mem_coe, Finset.mem_range, dite_eq_left hj', Fin.is_lt]
          tail_mem := fun j hj => by
            have hj' : j < nE := Finset.mem_range.mp hj
            simp only [Finset.mem_coe, Finset.mem_range, dite_eq_left hj', Fin.is_lt] }
      roots := Fin.elim0
      roots_mem := fun i => i.elim0 }
  have hK (u : V(H)) := hm.connected u.1 u.2
  let KOf (u : V(H)) : Graph α β := (hK u).choose
  have hK_le (u : V(H)) : KOf u ≤ D.toGraph.deleteEdges (ηe '' E(H)) :=
    (hK u).choose_spec.1
  have hK_V (u : V(H)) : V(KOf u) = ηv u.1 := (hK u).choose_spec.2.1
  have hK_conn (u : V(H)) : GraphConnected (KOf u) := (hK u).choose_spec.2.2
  let vMap (i : ℕ) : Digraph α β :=
    if hi : i < nV then
      let u := eV.symm ⟨i, hi⟩
      D.subdigraphOf V(KOf u) E(KOf u)
    else D
  let eMap (j : ℕ) : β :=
    if hj : j < nE then ηe (eE.symm ⟨j, hj⟩).1 else Classical.arbitrary β
  have hvMap_V {i : ℕ} (hi : i < nV) : (vMap i).vertexSet = ηv (eV.symm ⟨i, hi⟩).1 := by
    dsimp [vMap]
    rw [dite_eq_left hi]
    have hsub : V(KOf (eV.symm ⟨i, hi⟩)) ⊆ D.vertexSet := by
      rw [hK_V]
      exact hm.vertex_subset _ (eV.symm ⟨i, hi⟩).2
    exact (inter_eq_self_of_subset_right hsub).trans (hK_V _)
  have hvMap_toGraph {i : ℕ} (hi : i < nV) : (vMap i).toGraph = KOf (eV.symm ⟨i, hi⟩) := by
    let u := eV.symm ⟨i, hi⟩
    have hle : KOf u ≤ D.toGraph := (hK_le u).trans Graph.deleteEdges_le
    refine Graph.ext ((hvMap_V hi).trans (hK_V u).symm) (fun e x y => ?_)
    dsimp [vMap]
    rw [dite_eq_left hi]
    simp only [Digraph.toGraph, Digraph.subdigraphOf, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨heD, heK⟩, _, _⟩, h⟩
      exact (hle.isLink_iff heK).mpr ⟨heD, h⟩
    · intro hlinkK
      have hlinkD : D.toGraph.IsLink e x y := hlinkK.mono hle
      have heK : e ∈ E(KOf u) := hlinkK.edge_mem
      have hxK : x ∈ V(KOf u) := hlinkK.left_mem
      have hyK : y ∈ V(KOf u) := hlinkK.right_mem
      refine ⟨⟨⟨hlinkD.1, heK⟩, ?_⟩, hlinkD.2⟩
      rcases hlinkD.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1.symm ▸ hxK, h2.symm ▸ hyK⟩
      · exact ⟨h1.symm ▸ hyK, h2.symm ▸ hxK⟩
  let R : RootedDigraph α β 0 := RootedDigraph.mk D Fin.elim0 (fun i => i.elim0)
  let R' : RootedDigraph α β 0 := RootedDigraph.mk D' Fin.elim0 (fun i => i.elim0)
  have hMod : IsRootedDigraphModel H_nat R vMap eMap := by
    refine
      { sub_of_mem := fun i hi => by
          have hi' : i < nV := Finset.mem_range.mp hi
          dsimp [vMap]; rw [dite_eq_left hi']
          exact D.subdigraphOf_isSubdigraph _ _
        connected_of_mem := fun i hi => by
          have hi' : i < nV := Finset.mem_range.mp hi
          refine ⟨(hvMap_V hi').symm ▸ hm.vertex_nonempty _ (eV.symm ⟨i, hi'⟩).2, fun x hx y hy => ?_⟩
          rw [hvMap_toGraph hi']
          have hxK : x ∈ V(KOf (eV.symm ⟨i, hi'⟩)) := by
            rw [hK_V, ← hvMap_V hi']; exact hx
          have hyK : y ∈ V(KOf (eV.symm ⟨i, hi'⟩)) := by
            rw [hK_V, ← hvMap_V hi']; exact hy
          exact graphWalk_nonempty_of_reflTransGen_adj hxK ((hK_conn _).2 x hxK y hyK)
        disjoint_of_ne := fun i₁ i₂ hi₁ hi₂ hne => by
          have hi₁' : i₁ < nV := Finset.mem_range.mp hi₁
          have hi₂' : i₂ < nV := Finset.mem_range.mp hi₂
          rw [hvMap_V hi₁', hvMap_V hi₂']
          have hne_u : (eV.symm ⟨i₁, hi₁'⟩).1 ≠ (eV.symm ⟨i₂, hi₂'⟩).1 := by
            intro heq
            have hsub_eq : eV.symm ⟨i₁, hi₁'⟩ = eV.symm ⟨i₂, hi₂'⟩ := Subtype.ext heq
            have hfin_eq : (⟨i₁, hi₁'⟩ : Fin nV) = ⟨i₂, hi₂'⟩ := eV.symm.injective hsub_eq
            exact hne (Fin.ext_iff.mp hfin_eq)
          exact hm.vertex_disjoint _ (eV.symm ⟨i₁, hi₁'⟩).2 _ (eV.symm ⟨i₂, hi₂'⟩).2 hne_u
        edge_mem := fun j hj => by
          have hj' : j < nE := Finset.mem_range.mp hj
          dsimp [eMap]; rw [dite_eq_left hj']
          exact hm.edge_mem _ (eE.symm ⟨j, hj'⟩).2
        head_tail_mem := fun j hj => by
          have hj' : j < nE := Finset.mem_range.mp hj
          have hhead_j : H_nat.digraph.head j = (eV (uOf ⟨j, hj'⟩)).1 := dite_eq_left hj'
          have htail_j : H_nat.digraph.tail j = (eV (vOf ⟨j, hj'⟩)).1 := dite_eq_left hj'
          have heMap_j : eMap j = ηe (eE.symm ⟨j, hj'⟩).1 := dite_eq_left hj'
          rw [hhead_j, htail_j, heMap_j]
          rw [hvMap_V (eV (uOf ⟨j, hj'⟩)).2, hvMap_V (eV (vOf ⟨j, hj'⟩)).2]
          simp only [Fin.eta, Equiv.symm_apply_apply]
          exact ⟨hheadOf ⟨j, hj'⟩, htailOf ⟨j, hj'⟩⟩
        loop_not_mem := fun j hj _ he_in => by
          have hj' : j < nE := Finset.mem_range.mp hj
          have hhead_lt : H_nat.digraph.head j < nV :=
            Finset.mem_range.mp (H_nat.digraph.head_mem hj)
          have he_in_K : eMap j ∈ E(KOf (eV.symm ⟨H_nat.digraph.head j, hhead_lt⟩)) := by
            have hE_eq : (vMap (H_nat.digraph.head j)).edgeSet =
                E(KOf (eV.symm ⟨H_nat.digraph.head j, hhead_lt⟩)) :=
              congrArg Graph.edgeSet (hvMap_toGraph hhead_lt)
            exact hE_eq ▸ he_in
          have he_del := (hK_le (eV.symm ⟨H_nat.digraph.head j, hhead_lt⟩)).edgeSet_mono he_in_K
          rw [Graph.edgeSet_deleteEdges] at he_del
          apply he_del.2
          dsimp [eMap]; rw [dite_eq_left hj']
          exact ⟨(eE.symm ⟨j, hj'⟩).1, (eE.symm ⟨j, hj'⟩).2, rfl⟩
        eMap_injOn := fun j₁ hj₁ j₂ hj₂ heq => by
          have hj₁' : j₁ < nE := Finset.mem_range.mp hj₁
          have hj₂' : j₂ < nE := Finset.mem_range.mp hj₂
          dsimp [eMap] at heq
          rw [dite_eq_left hj₁', dite_eq_left hj₂'] at heq
          have he_eq := hm.edge_injOn (eE.symm ⟨j₁, hj₁'⟩).2 (eE.symm ⟨j₂, hj₂'⟩).2 heq
          have hsub_eq : eE.symm ⟨j₁, hj₁'⟩ = eE.symm ⟨j₂, hj₂'⟩ := Subtype.ext he_eq
          exact Fin.ext_iff.mp (eE.symm.injective hsub_eq)
        root_mem := fun i => i.elim0 }
  have hH_nat_in : H_nat ∈ R.deltaFolio δ := by
    refine ⟨⟨⟨Finset.finite_toSet _, Finset.finite_toSet _⟩, vMap, eMap, hMod⟩, ?_⟩
    dsimp [RootedDigraph.detail, H_nat]
    rw [ncard_coe_finset, Finset.card_range]
    have hV_diff : ((↑(Finset.range nV) : Set ℕ) \ range Fin.elim0).ncard ≤ nV := by
      calc ((↑(Finset.range nV) : Set ℕ) \ range Fin.elim0).ncard
          ≤ (↑(Finset.range nV) : Set ℕ).ncard := ncard_le_ncard sdiff_subset (Finset.finite_toSet _)
        _ = nV := by rw [ncard_coe_finset, Finset.card_range]
    exact max_le hE_le (hV_diff.trans hV_le)
  have hsame_R : R.deltaFolio δ = R'.deltaFolio δ :=
    hfolio.2.2 0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0)
      (injective_of_subsingleton _) (by simp)
  have hH_nat_in' : H_nat ∈ R'.deltaFolio δ := hsame_R ▸ hH_nat_in
  rcases hH_nat_in' with ⟨⟨_, vMap', eMap', hMod'⟩, _⟩
  let ηv' (u : α') : Set α :=
    if hu : u ∈ V(H) then (vMap' (eV ⟨u, hu⟩).1).vertexSet else ∅
  let ηe' (e : β') : β :=
    if he : e ∈ E(H) then eMap' (eE ⟨e, he⟩).1 else Classical.arbitrary β
  have hm' : IsMinorModel H D'.toGraph ηv' ηe' := by
    refine
      { vertex_nonempty := fun u hu => by
          dsimp [ηv']; rw [dite_eq_left hu]
          have hi : (eV ⟨u, hu⟩).1 ∈ H_nat.digraph.vertexSet :=
            Finset.mem_range.mpr (eV ⟨u, hu⟩).2
          exact (hMod'.connected_of_mem hi).1
        vertex_subset := fun u hu => by
          dsimp [ηv']; rw [dite_eq_left hu]
          have hi : (eV ⟨u, hu⟩).1 ∈ H_nat.digraph.vertexSet :=
            Finset.mem_range.mpr (eV ⟨u, hu⟩).2
          exact (hMod'.sub_of_mem hi).vertexSet_subset
        edge_mem := fun e he => by
          dsimp [ηe']; rw [dite_eq_left he]
          have hj : (eE ⟨e, he⟩).1 ∈ H_nat.digraph.edgeSet :=
            Finset.mem_range.mpr (eE ⟨e, he⟩).2
          exact hMod'.edge_mem hj
        vertex_disjoint := fun u₁ hu₁ u₂ hu₂ hne => by
          dsimp [ηv']; rw [dite_eq_left hu₁, dite_eq_left hu₂]
          have hi₁ : (eV ⟨u₁, hu₁⟩).1 ∈ H_nat.digraph.vertexSet :=
            Finset.mem_range.mpr (eV ⟨u₁, hu₁⟩).2
          have hi₂ : (eV ⟨u₂, hu₂⟩).1 ∈ H_nat.digraph.vertexSet :=
            Finset.mem_range.mpr (eV ⟨u₂, hu₂⟩).2
          have hne_i : (eV ⟨u₁, hu₁⟩).1 ≠ (eV ⟨u₂, hu₂⟩).1 := by
            intro heq
            have hfin_eq : eV ⟨u₁, hu₁⟩ = eV ⟨u₂, hu₂⟩ := Fin.ext heq
            exact hne (Subtype.ext_iff.mp (eV.injective hfin_eq))
          exact hMod'.disjoint_of_ne hi₁ hi₂ hne_i
        edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
          dsimp [ηe'] at heq; rw [dite_eq_left he₁, dite_eq_left he₂] at heq
          have hj₁ : (eE ⟨e₁, he₁⟩).1 ∈ H_nat.digraph.edgeSet :=
            Finset.mem_range.mpr (eE ⟨e₁, he₁⟩).2
          have hj₂ : (eE ⟨e₂, he₂⟩).1 ∈ H_nat.digraph.edgeSet :=
            Finset.mem_range.mpr (eE ⟨e₂, he₂⟩).2
          have hj_eq := hMod'.eMap_injOn hj₁ hj₂ heq
          exact Subtype.ext_iff.mp (eE.injective (Fin.ext hj_eq))
        inc_iff := fun w hw e he => by
          dsimp [ηv', ηe']; rw [dite_eq_left hw, dite_eq_left he]
          let j := eE ⟨e, he⟩
          have hj : j.1 ∈ H_nat.digraph.edgeSet := Finset.mem_range.mpr j.2
          have hht := hMod'.head_tail_mem hj
          have hhead_eq : H_nat.digraph.head j.1 = (eV (uOf j)).1 := dite_eq_left j.2
          have htail_eq : H_nat.digraph.tail j.1 = (eV (vOf j)).1 := dite_eq_left j.2
          rw [hhead_eq, htail_eq] at hht
          have he_eq : (eE.symm j).1 = e := congrArg Subtype.val (eE.symm_apply_apply ⟨e, he⟩)
          have hlink_j : H.IsLink e (uOf j).1 (vOf j).1 := he_eq ▸ hlinkOf j
          have heD' : eMap' j.1 ∈ D'.edgeSet := hMod'.edge_mem hj
          constructor
          · intro hinc
            have hw_eq : w = (uOf j).1 ∨ w = (vOf j).1 := by
              rcases hinc with ⟨z, hz⟩
              rcases hz.eq_and_eq_or_eq_and_eq hlink_j with ⟨rfl, _⟩ | ⟨rfl, _⟩
              · exact Or.inl rfl
              · exact Or.inr rfl
            rcases hw_eq with rfl | rfl
            · exact ⟨D'.head (eMap' j.1), hht.1, D'.tail (eMap' j.1), heD', Or.inl ⟨rfl, rfl⟩⟩
            · exact ⟨D'.tail (eMap' j.1), hht.2, D'.head (eMap' j.1), heD', Or.inr ⟨rfl, rfl⟩⟩
          · rintro ⟨x, hx, z, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
            · have hw_eq : (⟨w, hw⟩ : V(H)) = uOf j := by
                by_contra hne
                have hne_i : (eV ⟨w, hw⟩).1 ≠ (eV (uOf j)).1 :=
                  fun h => hne (eV.injective (Fin.ext h))
                exact disjoint_left.mp
                  (hMod'.disjoint_of_ne (Finset.mem_range.mpr (eV ⟨w, hw⟩).2)
                    (Finset.mem_range.mpr (eV (uOf j)).2) hne_i)
                  hx hht.1
              have hw_val : w = (uOf j).1 := congrArg Subtype.val hw_eq
              exact hw_val ▸ hlink_j.inc_left
            · have hw_eq : (⟨w, hw⟩ : V(H)) = vOf j := by
                by_contra hne
                have hne_i : (eV ⟨w, hw⟩).1 ≠ (eV (vOf j)).1 :=
                  fun h => hne (eV.injective (Fin.ext h))
                exact disjoint_left.mp
                  (hMod'.disjoint_of_ne (Finset.mem_range.mpr (eV ⟨w, hw⟩).2)
                    (Finset.mem_range.mpr (eV (vOf j)).2) hne_i)
                  hx hht.2
              have hw_val : w = (vOf j).1 := congrArg Subtype.val hw_eq
              exact hw_val ▸ hlink_j.inc_right
        isLoopAt_iff := fun w hw e he => by
          dsimp [ηv', ηe']; rw [dite_eq_left hw, dite_eq_left he]
          let j := eE ⟨e, he⟩
          have hj : j.1 ∈ H_nat.digraph.edgeSet := Finset.mem_range.mpr j.2
          have hht := hMod'.head_tail_mem hj
          have hhead_eq : H_nat.digraph.head j.1 = (eV (uOf j)).1 := dite_eq_left j.2
          have htail_eq : H_nat.digraph.tail j.1 = (eV (vOf j)).1 := dite_eq_left j.2
          rw [hhead_eq, htail_eq] at hht
          have he_eq : (eE.symm j).1 = e := congrArg Subtype.val (eE.symm_apply_apply ⟨e, he⟩)
          have hlink_j : H.IsLink e (uOf j).1 (vOf j).1 := he_eq ▸ hlinkOf j
          have heD' : eMap' j.1 ∈ D'.edgeSet := hMod'.edge_mem hj
          constructor
          · intro hloop x hinc_x
            rcases hloop.eq_and_eq_or_eq_and_eq hlink_j with ⟨hu_eq, hv_eq⟩ | ⟨hv_eq, hu_eq⟩
            all_goals
              have hu_sub : (⟨w, hw⟩ : V(H)) = uOf j := Subtype.ext hu_eq
              have hv_sub : (⟨w, hw⟩ : V(H)) = vOf j := Subtype.ext hv_eq
              rcases hinc_x with ⟨z, _, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
              · rw [hu_sub]; exact hht.1
              · rw [hv_sub]; exact hht.2
          · intro hall
            have hh_in : D'.head (eMap' j.1) ∈ (vMap' (eV ⟨w, hw⟩).1).vertexSet :=
              hall _ ⟨D'.tail (eMap' j.1), heD', Or.inl ⟨rfl, rfl⟩⟩
            have ht_in : D'.tail (eMap' j.1) ∈ (vMap' (eV ⟨w, hw⟩).1).vertexSet :=
              hall _ ⟨D'.head (eMap' j.1), heD', Or.inr ⟨rfl, rfl⟩⟩
            have hu_eq : (⟨w, hw⟩ : V(H)) = uOf j := by
              by_contra hne
              have hne_i : (eV ⟨w, hw⟩).1 ≠ (eV (uOf j)).1 :=
                fun h => hne (eV.injective (Fin.ext h))
              exact disjoint_left.mp
                (hMod'.disjoint_of_ne (Finset.mem_range.mpr (eV ⟨w, hw⟩).2)
                  (Finset.mem_range.mpr (eV (uOf j)).2) hne_i)
                hh_in hht.1
            have hv_eq : (⟨w, hw⟩ : V(H)) = vOf j := by
              by_contra hne
              have hne_i : (eV ⟨w, hw⟩).1 ≠ (eV (vOf j)).1 :=
                fun h => hne (eV.injective (Fin.ext h))
              exact disjoint_left.mp
                (hMod'.disjoint_of_ne (Finset.mem_range.mpr (eV ⟨w, hw⟩).2)
                  (Finset.mem_range.mpr (eV (vOf j)).2) hne_i)
                ht_in hht.2
            have hu_val : (uOf j).1 = w := congrArg Subtype.val hu_eq.symm
            have hv_val : (vOf j).1 = w := congrArg Subtype.val hv_eq.symm
            rw [hu_val, hv_val] at hlink_j
            exact hlink_j
        connected := fun u hu => by
          dsimp [ηv']; rw [dite_eq_left hu]
          let i := eV ⟨u, hu⟩
          have hi : i.1 ∈ H_nat.digraph.vertexSet := Finset.mem_range.mpr i.2
          refine ⟨(vMap' i.1).toGraph, ?_, rfl, ?_⟩
          · refine ⟨(hMod'.sub_of_mem hi).vertexSet_subset, fun f x y hlink => ?_⟩
            rw [Graph.deleteEdges_isLink]
            refine ⟨(hMod'.sub_of_mem hi).toGraph_le.isLink_mono hlink, ?_⟩
            rintro ⟨e, he, rfl⟩
            have hf : ηe' e ∈ (vMap' i.1).edgeSet := hlink.edge_mem
            dsimp [ηe'] at hf; rw [dite_eq_left he] at hf
            have hj : (eE ⟨e, he⟩).1 ∈ H_nat.digraph.edgeSet :=
              Finset.mem_range.mpr (eE ⟨e, he⟩).2
            exact hMod'.toIsDigraphModel.edge_not_mem_vMap hj hi hf
          · rcases hMod'.connected_of_mem hi with ⟨hne, hconn⟩
            refine ⟨hne, fun x hx y hy => ?_⟩
            rcases hconn x hx y hy with ⟨W⟩
            exact reflTransGen_adj_of_graphWalk W }
  exact isIsoMinor_of_isMinorModel H D'.toGraph hVH hEH hfin'.finite_V hfin'.finite_E ηv' ηe' hm'

/-- If `HasSameDeltaFolioRel D D' δ ∅`, then for every finite graph `H` with `V(H).ncard ≤ δ` and
`E(H).ncard ≤ δ`, `IsIsoMinor H D.toGraph ↔ IsIsoMinor H D'.toGraph`. -/
lemma isIsoMinor_iff_of_hasSameDeltaFolioRel_empty [Nonempty β]
    {D D' : Digraph α β} (hfin : D.IsFinite) (hfin' : D'.IsFinite) {δ : ℕ}
    (hfolio : HasSameDeltaFolioRel D D' δ ∅)
    {H : Graph α' β'} (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hV_le : V(H).ncard ≤ δ) (hE_le : E(H).ncard ≤ δ) :
    IsIsoMinor H D.toGraph ↔ IsIsoMinor H D'.toGraph :=
  ⟨isIsoMinor_of_hasSameDeltaFolioRel_empty hfin hfin' hfolio hVH hEH hV_le hE_le,
   isIsoMinor_of_hasSameDeltaFolioRel_empty hfin' hfin hfolio.symm hVH hEH hV_le hE_le⟩

/-- **Graph Minors XIII, (4.3)** (page 76):
"Let $\mathcal{F}$ be a minor-closed class of graphs such that some planar graph is not in
$\mathcal{F}$. Then there is an algorithm to determine whether $G \in \mathcal{F}$ with running
time $O(v^2)$."

This theorem gives the data fixed at the start of the proof: the finite excluded-minor list `B`
(from Graph Minors IV, (1.4), via `exists_finite_excluded_minors_of_planar`), the number `ω` of
(4.2), and `δ`, the largest number of vertices or edges of a graph in `B`. The four steps of the
algorithm are the program `Compute.alg43Prog`; Step (1) is proved in
`GraphMinor/Compute/GM13PairCapMinor.lean`. -/
theorem theorem_4_3_proof [Nonempty β] (ℱ : Set (Graph α β))
    (hclosed : ∀ ⦃G₁ G₂ : Graph α β⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (H₀ : Graph α β) (hVH₀ : V(H₀).Finite) (hEH₀ : E(H₀).Finite)
    (hPlanar₀ : IsPlanar H₀) (hH₀_not : H₀ ∉ ℱ) :
    ∃ (B : Finset (Graph α β)) (ω δ : ℕ),
      H₀ ∈ B ∧
      2 ≤ ω ∧
      (∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ ∧ H ∉ ℱ) ∧
      (∀ G : Graph α β, V(G).Finite → E(G).Finite →
        (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G)) ∧
      (∀ G : Graph α β, V(G).Finite → E(G).Finite →
        ¬ GraphBranchWidthLE G (ω - 1) → G ∉ ℱ) := by
  obtain ⟨B, hH₀_B, _, hB_props, hB_iff⟩ :=
    exists_finite_excluded_minors_of_planar ℱ hclosed H₀ hVH₀ hEH₀ hPlanar₀ hH₀_not
  obtain ⟨ω, hω2, h42⟩ := theorem_4_2_proof (α := α) (β := β) H₀ hPlanar₀
  let δ : ℕ := B.sup (fun H => max V(H).ncard E(H).ncard)
  have hB_δ : ∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ ∧ H ∉ ℱ := by
    intro H hHB
    have hp := hB_props H hHB
    have hle_sup : max V(H).ncard E(H).ncard ≤ δ :=
      Finset.le_sup (f := fun K => max V(K).ncard E(K).ncard) hHB
    exact ⟨hp.1, hp.2.1, (le_max_left _ _).trans hle_sup, (le_max_right _ _).trans hle_sup, hp.2.2⟩
  refine ⟨B, ω, δ, hH₀_B, hω2, hB_δ, hB_iff, ?_⟩
  intro G hVG hEG hnot_bw hGℱ
  have hminor₀ : IsIsoMinor H₀ G := h42 G hVG hEG hnot_bw
  exact (hB_iff G hVG hEG).mp hGℱ H₀ hH₀_B hminor₀

/-- **Graph Minors XIII, (4.4) Algorithm** (page 77):
"*Input:* A graph $G$.
*Output:* Decides if there is a model of $H$ in $G$, and outputs such a model if one exists.
*Running time:* $O(v^2)$."

This is the correctness of the method. The RAM program for Steps (1)–(3) and its `O(v^2)` time
bound are `GM13.algorithm_4_4` in `Results.lean`. -/
theorem algorithm_4_4_correct [Nonempty β]
    (H : Graph α' β') (hVH : V(H).Finite) (hEH : E(H).Finite) (hPlanar : IsPlanar H) :
    ∃ ω : ℕ, 2 ≤ ω ∧
      (∀ G : Graph α β, V(G).Finite → E(G).Finite →
        ¬ GraphBranchWidthLE G (ω - 1) → IsIsoMinor H G) ∧
      (∀ D : Digraph α β, D.IsFinite →
        let δ := max V(H).ncard E(H).ncard
        ∃ D₁ : Digraph α β, D₁.IsSubdigraph D ∧ D₁.vertexSet = D.vertexSet ∧
          HasSameDeltaFolioRel D D₁ δ ∅ ∧
          D₁.HasBoundedMultiplicity δ ∧
          (IsIsoMinor H D.toGraph ↔ IsIsoMinor H D₁.toGraph) ∧
          (2 ≤ E(D₁.toGraph).ncard →
            ∃ (G₂ : Graph α β) (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
              G₂ ≤ D₁.toGraph ∧
              2 ≤ E(G₂).ncard ∧
              IsGraphBranchDecomposition G₂ T τ ∧
              graphBranchDecompWidth G₂ T τ ≤ 3 * ω ∧
              (G₂ = D₁.toGraph ∨ IsIsoMinor H G₂) ∧
              (IsIsoMinor H D₁.toGraph ↔ IsIsoMinor H G₂))) := by
  obtain ⟨ω, hω2, h42⟩ := theorem_4_2_proof (α := α) (β := β) H hPlanar
  refine ⟨ω, hω2, h42, fun D hD_fin => ?_⟩
  dsimp only
  let δ := max V(H).ncard E(H).ncard
  obtain ⟨D₁, hsub₁, hVD₁_eq, hfolio₁, hbm₁⟩ :=
    exists_boundedMultiplicity_subdigraph (δ := δ) hD_fin (empty_subset _)
  have hD₁_fin : D₁.IsFinite :=
    ⟨hD_fin.finite_V.subset hsub₁.vertexSet_subset, hD_fin.finite_E.subset hsub₁.edgeSet_subset⟩
  have hiso₁ : IsIsoMinor H D.toGraph ↔ IsIsoMinor H D₁.toGraph :=
    isIsoMinor_iff_of_hasSameDeltaFolioRel_empty hD_fin hD₁_fin hfolio₁ hVH hEH
      (le_max_left _ _) (le_max_right _ _)
  refine ⟨D₁, hsub₁, hVD₁_eq, hfolio₁, hbm₁, hiso₁, fun hE2 => ?_⟩
  obtain ⟨G₂, ι, hfin, T, τ, hG₂_le, hE2_G₂, hbd, hw, _, hnot_bw_sub1⟩ :=
    algorithm_3_3_correct D₁.toGraph hD₁_fin.finite_V hD₁_fin.finite_E hE2 ω hω2
  have hVG₂ : V(G₂).Finite := hD₁_fin.finite_V.subset hG₂_le.vertexSet_mono
  have hEG₂ : E(G₂).Finite := hD₁_fin.finite_E.subset hG₂_le.edgeSet_mono
  have hcase : G₂ = D₁.toGraph ∨ IsIsoMinor H G₂ := by
    rcases hnot_bw_sub1 with rfl | hnot_bw
    · exact Or.inl rfl
    · exact Or.inr (h42 G₂ hVG₂ hEG₂ hnot_bw)
  have hiso₂ : IsIsoMinor H D₁.toGraph ↔ IsIsoMinor H G₂ := by
    rcases hcase with rfl | hminor_G₂
    · exact Iff.rfl
    · refine ⟨fun _ => hminor_G₂, fun ⟨G', hG'_le, C, hC, hφ⟩ => ?_⟩
      exact ⟨G', hG'_le.trans hG₂_le, C, hC, hφ⟩
  exact ⟨G₂, ι, hfin, T, τ, hG₂_le, hE2_G₂, hbd, hw, hcase, hiso₂⟩

/-- **Graph Minors XIII, (4.4) Algorithm** (page 77), numbered alias for `algorithm_4_4_correct`. -/
theorem theorem_4_4_proof [Nonempty β]
    (H : Graph α' β') (hVH : V(H).Finite) (hEH : E(H).Finite) (hPlanar : IsPlanar H) :
    ∃ ω : ℕ, 2 ≤ ω ∧
      (∀ G : Graph α β, V(G).Finite → E(G).Finite →
        ¬ GraphBranchWidthLE G (ω - 1) → IsIsoMinor H G) ∧
      (∀ D : Digraph α β, D.IsFinite →
        let δ := max V(H).ncard E(H).ncard
        ∃ D₁ : Digraph α β, D₁.IsSubdigraph D ∧ D₁.vertexSet = D.vertexSet ∧
          HasSameDeltaFolioRel D D₁ δ ∅ ∧
          D₁.HasBoundedMultiplicity δ ∧
          (IsIsoMinor H D.toGraph ↔ IsIsoMinor H D₁.toGraph) ∧
          (2 ≤ E(D₁.toGraph).ncard →
            ∃ (G₂ : Graph α β) (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : β → ι),
              G₂ ≤ D₁.toGraph ∧
              2 ≤ E(G₂).ncard ∧
              IsGraphBranchDecomposition G₂ T τ ∧
              graphBranchDecompWidth G₂ T τ ≤ 3 * ω ∧
              (G₂ = D₁.toGraph ∨ IsIsoMinor H G₂) ∧
              (IsIsoMinor H D₁.toGraph ↔ IsIsoMinor H G₂))) := by
  obtain ⟨ω, hω2, h42, hstep⟩ := algorithm_4_4_correct (α := α) (β := β) H hVH hEH hPlanar
  exact ⟨ω, hω2, h42, hstep⟩

end GraphMinor.GM13
