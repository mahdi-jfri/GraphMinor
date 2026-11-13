module

public import GraphMinor.GM16.Defs

/-!
# Small examples for Graph Minors XVI definitions

This file tests `IsCompleteGraphOn`, `IsCliqueSum`, `HasTreeStructureOver`, and `HasTreeWidthLE`
from `GraphMinor/GM16/Defs.lean` on concrete small graphs:

1. The edgeless graph on two vertices is not a clique-sum of itself with itself
   (`not_isCliqueSum_edgelessTwo_self`).
2. A four-cycle is a clique-sum of two triangles (`isCliqueSum_cycleFour_triangles`).
3. A triangle is not a tree-structure over the class of graphs with at most 2 vertices
   (`not_hasTreeStructureOver_completeGraph_three` and `not_hasTreeWidthLE_completeGraph_three_one`).
4. The sentence on page 48 claiming that every torso of a member of `𝒟^n` is a `(≤ n)`-vertex
   extension of a torso of a member of `𝒟` is false with the paper's definition `IsVertexExtension`:
   for `d = (edgelessTwo, ∅)` and `d' = (edgelessTwo, {univ})` (`n = 2`, `Z = univ`), `completeGraph 2`
   is a torso of `d' ∈ 𝒟^2`, but is not a vertex extension of any torso of a member of `𝒟 = {d}`
   (`completeGraph_two_mem_torsosOfClass_enlargement` and
   `not_exists_torso_isVertexExtension_completeGraph_two`).
-/

public section

namespace GraphMinor.GM16.Examples

open Set Graph GraphMinor.GM06 GraphMinor.GM09 GraphMinor.GM16

/-! ## 1. The edgeless graph on two vertices is not a clique-sum of itself with itself -/

/-- The edgeless graph on `Fin 2`, obtained by deleting all edges from `completeGraph 2`. -/
abbrev edgelessTwo : Graph (Fin 2) (Sym2 (Fin 2)) :=
  (completeGraph 2).deleteEdges Set.univ

/-- The edgeless graph on two vertices is not a clique-sum of itself with itself. -/
theorem not_isCliqueSum_edgelessTwo_self :
    ¬ IsCliqueSum edgelessTwo edgelessTwo edgelessTwo := by
  rintro ⟨H₁, H₂, K, _, hK, hsep₁, hsep₂⟩
  have hVK_sub₁ : V(K) ⊆ V(H₁) := hK.1.trans_subset inter_subset_left
  have hVK_sub₂ : V(K) ⊆ V(H₂) := hK.1.trans_subset inter_subset_right
  have hVH₁ : V(H₁) = V(edgelessTwo) := by
    have h := hsep₁.2.2.1
    rw [union_eq_self_of_subset_right hVK_sub₁] at h
    exact h
  have hVH₂ : V(H₂) = V(edgelessTwo) := by
    have h := hsep₂.2.2.1
    rw [union_eq_self_of_subset_right hVK_sub₂] at h
    exact h
  have h0 : (0 : Fin 2) ∈ V(H₁) ∩ V(H₂) := by
    rw [hVH₁, hVH₂, inter_self]
    exact mem_univ _
  have h1 : (1 : Fin 2) ∈ V(H₁) ∩ V(H₂) := by
    rw [hVH₁, hVH₂, inter_self]
    exact mem_univ _
  obtain ⟨e, he, _⟩ := hK.2.2 0 h0 1 h1 (by decide)
  have he_mem : e ∈ E(edgelessTwo) := hsep₁.2.1.edgeSet_mono he.edge_mem
  simp [edgelessTwo] at he_mem

/-! ## 2. A four-cycle is a clique-sum of two triangles -/

/-- The edge set of the 4-cycle `0 - 1 - 2 - 3 - 0` inside `completeGraph 4`. -/
def cycleFourEdges : Set (Sym2 (Fin 4)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}

/-- The edge set of the path `0 - 1 - 2`. -/
def leftPathEdges : Set (Sym2 (Fin 4)) :=
  {s(0, 1), s(1, 2)}

/-- The edge set of the path `2 - 3 - 0`. -/
def rightPathEdges : Set (Sym2 (Fin 4)) :=
  {s(2, 3), s(3, 0)}

/-- The diagonal edge `{0, 2}`. -/
def diagEdges : Set (Sym2 (Fin 4)) :=
  {s(0, 2)}

/-- The 4-cycle `0 - 1 - 2 - 3 - 0` as a subgraph of `completeGraph 4`. -/
def cycleFour : Graph (Fin 4) (Sym2 (Fin 4)) :=
  (completeGraph 4).restrict cycleFourEdges

/-- The triangle on `{0, 1, 2}` as a subgraph of `completeGraph 4`. -/
def triangleLeft : Graph (Fin 4) (Sym2 (Fin 4)) :=
  ((completeGraph 4).induce ({0, 1, 2} : Set (Fin 4))).restrict (leftPathEdges ∪ diagEdges)

/-- The triangle on `{0, 2, 3}` as a subgraph of `completeGraph 4`. -/
def triangleRight : Graph (Fin 4) (Sym2 (Fin 4)) :=
  ((completeGraph 4).induce ({0, 2, 3} : Set (Fin 4))).restrict (rightPathEdges ∪ diagEdges)

/-- The four-cycle `cycleFour` is a clique-sum of the two triangles `triangleLeft` and
`triangleRight`. -/
theorem isCliqueSum_cycleFour_triangles :
    IsCliqueSum cycleFour triangleLeft triangleRight := by
  let H₁ : Graph (Fin 4) (Sym2 (Fin 4)) :=
    ((completeGraph 4).induce ({0, 1, 2} : Set (Fin 4))).restrict leftPathEdges
  let H₂ : Graph (Fin 4) (Sym2 (Fin 4)) :=
    ((completeGraph 4).induce ({0, 2, 3} : Set (Fin 4))).restrict rightPathEdges
  let K : Graph (Fin 4) (Sym2 (Fin 4)) :=
    ((completeGraph 4).induce ({0, 2} : Set (Fin 4))).restrict diagEdges
  have hC_le : cycleFour ≤ completeGraph 4 := restrict_le
  have hT₁_le : triangleLeft ≤ completeGraph 4 :=
    restrict_le.trans ((completeGraph 4).induce_le (subset_univ _))
  have hT₂_le : triangleRight ≤ completeGraph 4 :=
    restrict_le.trans ((completeGraph 4).induce_le (subset_univ _))
  have hH₁_le : H₁ ≤ completeGraph 4 :=
    restrict_le.trans ((completeGraph 4).induce_le (subset_univ _))
  have hH₂_le : H₂ ≤ completeGraph 4 :=
    restrict_le.trans ((completeGraph 4).induce_le (subset_univ _))
  have hK_le : K ≤ completeGraph 4 :=
    restrict_le.trans ((completeGraph 4).induce_le (subset_univ _))
  have hVH₁ : V(H₁) = ({0, 1, 2} : Set (Fin 4)) := rfl
  have hVH₂ : V(H₂) = ({0, 2, 3} : Set (Fin 4)) := rfl
  have hVK : V(K) = ({0, 2} : Set (Fin 4)) := rfl
  have hVT₁ : V(triangleLeft) = ({0, 1, 2} : Set (Fin 4)) := rfl
  have hVT₂ : V(triangleRight) = ({0, 2, 3} : Set (Fin 4)) := rfl
  have hVC : V(cycleFour) = Set.univ := rfl
  have hEC : E(cycleFour) = cycleFourEdges := by
    ext e
    simp only [cycleFour, edgeSet_restrict, mem_inter_iff, and_iff_right_iff_imp]
    intro he
    rcases he with rfl | rfl | rfl | rfl
    · exact ⟨0, 1, by decide, rfl⟩
    · exact ⟨1, 2, by decide, rfl⟩
    · exact ⟨2, 3, by decide, rfl⟩
    · exact ⟨3, 0, by decide, rfl⟩
  have hEH₁ : E(H₁) = leftPathEdges := by
    ext e
    simp only [H₁, edgeSet_restrict, edgeSet_induce, mem_inter_iff, Set.mem_ofPred_eq,
      and_iff_right_iff_imp]
    intro he
    rcases he with rfl | rfl
    · exact ⟨0, 1, ⟨by decide, rfl⟩, by decide, by decide⟩
    · exact ⟨1, 2, ⟨by decide, rfl⟩, by decide, by decide⟩
  have hEH₂ : E(H₂) = rightPathEdges := by
    ext e
    simp only [H₂, edgeSet_restrict, edgeSet_induce, mem_inter_iff, Set.mem_ofPred_eq,
      and_iff_right_iff_imp]
    intro he
    rcases he with rfl | rfl
    · exact ⟨2, 3, ⟨by decide, rfl⟩, by decide, by decide⟩
    · exact ⟨3, 0, ⟨by decide, rfl⟩, by decide, by decide⟩
  have hEK : E(K) = diagEdges := by
    ext e
    simp only [K, edgeSet_restrict, edgeSet_induce, mem_inter_iff, Set.mem_ofPred_eq,
      and_iff_right_iff_imp]
    intro he
    rcases he with rfl
    exact ⟨0, 2, ⟨by decide, rfl⟩, by decide, by decide⟩
  have hET₁ : E(triangleLeft) = leftPathEdges ∪ diagEdges := by
    ext e
    simp only [triangleLeft, edgeSet_restrict, edgeSet_induce, mem_inter_iff, Set.mem_ofPred_eq,
      and_iff_right_iff_imp]
    rintro ((rfl | rfl) | rfl)
    · exact ⟨0, 1, ⟨by decide, rfl⟩, by decide, by decide⟩
    · exact ⟨1, 2, ⟨by decide, rfl⟩, by decide, by decide⟩
    · exact ⟨0, 2, ⟨by decide, rfl⟩, by decide, by decide⟩
  have hET₂ : E(triangleRight) = rightPathEdges ∪ diagEdges := by
    ext e
    simp only [triangleRight, edgeSet_restrict, edgeSet_induce, mem_inter_iff, Set.mem_ofPred_eq,
      and_iff_right_iff_imp]
    rintro ((rfl | rfl) | rfl)
    · exact ⟨2, 3, ⟨by decide, rfl⟩, by decide, by decide⟩
    · exact ⟨3, 0, ⟨by decide, rfl⟩, by decide, by decide⟩
    · exact ⟨0, 2, ⟨by decide, rfl⟩, by decide, by decide⟩
  refine ⟨H₁, H₂, K, ?_, ?_, ?_, ?_⟩
  · refine ⟨(Compatible.of_le_le hH₁_le hC_le).le_iff.mpr ⟨subset_univ _, ?_⟩,
      (Compatible.of_le_le hH₂_le hC_le).le_iff.mpr ⟨subset_univ _, ?_⟩, ?_, ?_, ?_⟩
    · rw [hEH₁, hEC]
      rintro e (rfl | rfl) <;> simp [cycleFourEdges]
    · rw [hEH₂, hEC]
      rintro e (rfl | rfl) <;> simp [cycleFourEdges]
    · rw [hVC, hVH₁, hVH₂]
      ext x
      fin_cases x <;> simp
    · rw [hEC, hEH₁, hEH₂]
      ext e
      simp only [cycleFourEdges, leftPathEdges, rightPathEdges, mem_union, mem_insert_iff,
        mem_singleton_iff]
      tauto
    · rw [hEH₁, hEH₂, Set.disjoint_left]
      rintro e (rfl | rfl) (h | h) <;> revert h <;> decide
  · have hV_inter : V(H₁) ∩ V(H₂) = ({0, 2} : Set (Fin 4)) := by
      rw [hVH₁, hVH₂]
      ext x
      fin_cases x <;> decide
    rw [hV_inter]
    refine ⟨hVK, ?_, ?_⟩
    · intro e x hloop
      have hlink := (hK_le.isLink_iff hloop.edge_mem).mp hloop
      exact hlink.1 rfl
    · intro x hx y hy hne
      refine ⟨s(x, y), ?_, ?_⟩
      · have hlink_comp : (completeGraph 4).IsLink s(x, y) x y := ⟨hne, rfl⟩
        have heK : s(x, y) ∈ E(K) := by
          rw [hEK, diagEdges, mem_singleton_iff]
          rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
          · exact (hne rfl).elim
          · rfl
          · exact Sym2.eq_swap
          · exact (hne rfl).elim
        exact (hK_le.isLink_iff heK).mpr hlink_comp
      · intro e he
        exact ((hK_le.isLink_iff he.edge_mem).mp he).2
  · refine ⟨(Compatible.of_le_le hH₁_le hT₁_le).le_iff.mpr
        ⟨le_rfl, by rw [hEH₁, hET₁]; exact subset_union_left⟩,
      (Compatible.of_le_le hK_le hT₁_le).le_iff.mpr
        ⟨by rw [hVK, hVT₁]; rintro x (rfl | rfl) <;> simp,
         by rw [hEK, hET₁]; exact subset_union_right⟩,
      by rw [hVT₁, hVH₁, hVK]; ext x; fin_cases x <;> simp,
      by rw [hET₁, hEH₁, hEK],
      by rw [hEH₁, hEK, diagEdges, Set.disjoint_left]; rintro e (rfl | rfl) h <;> revert h <;> decide⟩
  · refine ⟨(Compatible.of_le_le hH₂_le hT₂_le).le_iff.mpr
        ⟨le_rfl, by rw [hEH₂, hET₂]; exact subset_union_left⟩,
      (Compatible.of_le_le hK_le hT₂_le).le_iff.mpr
        ⟨by rw [hVK, hVT₂]; rintro x (rfl | rfl) <;> simp,
         by rw [hEK, hET₂]; exact subset_union_right⟩,
      by rw [hVT₂, hVH₂, hVK]; ext x; fin_cases x <;> simp,
      by rw [hET₂, hEH₂, hEK],
      by rw [hEH₂, hEK, diagEdges, Set.disjoint_left]; rintro e (rfl | rfl) h <;> revert h <;> decide⟩

/-! ## 3. A triangle is not a tree-structure over the class of graphs with at most 2 vertices -/

/-- `G` contains a triangle on the three vertices `0, 1, 2 : Fin 3`. -/
def HasTriangleOnFin3 {β : Type*} (G : Graph (Fin 3) β) : Prop :=
  (0 : Fin 3) ∈ V(G) ∧ (1 : Fin 3) ∈ V(G) ∧ (2 : Fin 3) ∈ V(G) ∧
    (∃ e, G.IsLink e 0 1) ∧ (∃ e, G.IsLink e 1 2) ∧ (∃ e, G.IsLink e 0 2)

private lemma exists_link_in_piece {β : Type*} {G H₁ H₂ K G₁ : Graph (Fin 3) β}
    (hsepG : IsGraphSeparation G H₁ H₂)
    (hK : IsCompleteGraphOn K (V(H₁) ∩ V(H₂)))
    (hsep₁ : IsGraphSeparation G₁ H₁ K)
    {x y : Fin 3} (hxy : x ≠ y) (hx : x ∈ V(H₁)) (hy : y ∈ V(H₁))
    (he : ∃ e, G.IsLink e x y) :
    ∃ e, G₁.IsLink e x y := by
  obtain ⟨e, hlink⟩ := he
  have he_union : e ∈ E(H₁) ∪ E(H₂) := hsepG.2.2.2.1 ▸ hlink.edge_mem
  rcases he_union with he₁ | he₂
  · exact ⟨e, ((hsepG.1.isLink_iff he₁).mpr hlink).mono hsep₁.1⟩
  · have hlink₂ := (hsepG.2.1.isLink_iff he₂).mpr hlink
    obtain ⟨eK, heK, _⟩ := hK.2.2 x ⟨hx, hlink₂.left_mem⟩ y ⟨hy, hlink₂.right_mem⟩ hxy
    exact ⟨eK, heK.mono hsep₁.2.1⟩

private lemma hasTriangleOnFin3_of_isCliqueSum {β : Type*} {G G₁ G₂ : Graph (Fin 3) β}
    (hsum : IsCliqueSum G G₁ G₂) (htri : HasTriangleOnFin3 G) :
    HasTriangleOnFin3 G₁ ∨ HasTriangleOnFin3 G₂ := by
  rcases hsum with ⟨H₁, H₂, K, hsepG, hK, hsep₁, hsep₂⟩
  rcases htri with ⟨h0, h1, h2, he01, he12, he02⟩
  have hVG₁ : V(H₁) ⊆ V(G₁) := hsep₁.1.vertexSet_mono
  have hVG₂ : V(H₂) ⊆ V(G₂) := hsep₂.1.vertexSet_mono
  by_cases hH₁_all : (0 : Fin 3) ∈ V(H₁) ∧ (1 : Fin 3) ∈ V(H₁) ∧ (2 : Fin 3) ∈ V(H₁)
  · rcases hH₁_all with ⟨h0₁, h1₁, h2₁⟩
    left
    exact ⟨hVG₁ h0₁, hVG₁ h1₁, hVG₁ h2₁,
      exists_link_in_piece hsepG hK hsep₁ (by decide) h0₁ h1₁ he01,
      exists_link_in_piece hsepG hK hsep₁ (by decide) h1₁ h2₁ he12,
      exists_link_in_piece hsepG hK hsep₁ (by decide) h0₁ h2₁ he02⟩
  · right
    have hedge_in_H₂ : ∀ {x y : Fin 3}, x ∉ V(H₁) → (∃ e, G.IsLink e x y) →
        x ∈ V(H₂) ∧ y ∈ V(H₂) := by
      intro x y hx ⟨e, hlink⟩
      have he_union : e ∈ E(H₁) ∪ E(H₂) := hsepG.2.2.2.1 ▸ hlink.edge_mem
      rcases he_union with he₁ | he₂
      · exact (hx ((hsepG.1.isLink_iff he₁).mpr hlink).left_mem).elim
      · have hlink₂ := (hsepG.2.1.isLink_iff he₂).mpr hlink
        exact ⟨hlink₂.left_mem, hlink₂.right_mem⟩
    have hH₂_all : (0 : Fin 3) ∈ V(H₂) ∧ (1 : Fin 3) ∈ V(H₂) ∧ (2 : Fin 3) ∈ V(H₂) := by
      by_cases h0₁ : (0 : Fin 3) ∈ V(H₁)
      · by_cases h1₁ : (1 : Fin 3) ∈ V(H₁)
        · have h2₁ : (2 : Fin 3) ∉ V(H₁) := fun h2₁ => hH₁_all ⟨h0₁, h1₁, h2₁⟩
          obtain ⟨e02, hl02⟩ := he02
          obtain ⟨e12, hl12⟩ := he12
          exact ⟨(hedge_in_H₂ h2₁ ⟨e02, hl02.symm⟩).2,
            (hedge_in_H₂ h2₁ ⟨e12, hl12.symm⟩).2,
            (hedge_in_H₂ h2₁ ⟨e02, hl02.symm⟩).1⟩
        · obtain ⟨e01, hl01⟩ := he01
          exact ⟨(hedge_in_H₂ h1₁ ⟨e01, hl01.symm⟩).2,
            (hedge_in_H₂ h1₁ ⟨e01, hl01.symm⟩).1,
            (hedge_in_H₂ h1₁ he12).2⟩
      · exact ⟨(hedge_in_H₂ h0₁ he01).1, (hedge_in_H₂ h0₁ he01).2, (hedge_in_H₂ h0₁ he02).2⟩
    rcases hH₂_all with ⟨h0₂, h1₂, h2₂⟩
    have hsepG_symm : IsGraphSeparation G H₂ H₁ :=
      ⟨hsepG.2.1, hsepG.1, (union_comm _ _).trans hsepG.2.2.1,
        (union_comm _ _).trans hsepG.2.2.2.1, hsepG.2.2.2.2.symm⟩
    have hK_symm : IsCompleteGraphOn K (V(H₂) ∩ V(H₁)) := by
      rwa [inter_comm]
    exact ⟨hVG₂ h0₂, hVG₂ h1₂, hVG₂ h2₂,
      exists_link_in_piece hsepG_symm hK_symm hsep₂ (by decide) h0₂ h1₂ he01,
      exists_link_in_piece hsepG_symm hK_symm hsep₂ (by decide) h1₂ h2₂ he12,
      exists_link_in_piece hsepG_symm hK_symm hsep₂ (by decide) h0₂ h2₂ he02⟩

/-- No graph in `HasTreeStructureOver {H | V(H).ncard ≤ 2}` contains a triangle on `Fin 3`. -/
theorem not_hasTriangleOnFin3_of_hasTreeStructureOver {β : Type*} {G : Graph (Fin 3) β}
    (h : HasTreeStructureOver {H : Graph (Fin 3) β | V(H).ncard ≤ 2} G) :
    ¬ HasTriangleOnFin3 G := by
  induction h with
  | @base H hH =>
    rintro ⟨h0, h1, h2, _⟩
    have hV : V(H) = Set.univ := by
      ext x
      fin_cases x <;> simp [h0, h1, h2]
    have hcard : V(H).ncard = 3 := by
      rw [hV]
      simp
    change V(H).ncard ≤ 2 at hH
    omega
  | cliqueSum hsum _ _ ih₁ ih₂ =>
    intro htri
    rcases hasTriangleOnFin3_of_isCliqueSum hsum htri with h₁ | h₂
    · exact ih₁ h₁
    · exact ih₂ h₂

/-- A triangle (`completeGraph 3`) is not a tree-structure over the class of graphs with at most
2 vertices. -/
theorem not_hasTreeStructureOver_completeGraph_three :
    ¬ HasTreeStructureOver {H : Graph (Fin 3) (Sym2 (Fin 3)) | V(H).ncard ≤ 2}
        (completeGraph 3) := by
  intro h
  refine not_hasTriangleOnFin3_of_hasTreeStructureOver h
    ⟨mem_univ _, mem_univ _, mem_univ _, ?_, ?_, ?_⟩
  · exact ⟨s(0, 1), by decide, rfl⟩
  · exact ⟨s(1, 2), by decide, rfl⟩
  · exact ⟨s(0, 2), by decide, rfl⟩

/-- A triangle (`completeGraph 3`) does not have tree-width at most 1 (`HasTreeWidthLE`). -/
theorem not_hasTreeWidthLE_completeGraph_three_one :
    ¬ HasTreeWidthLE (completeGraph 3) 1 := by
  intro h
  refine not_hasTriangleOnFin3_of_hasTreeStructureOver h
    ⟨mem_univ _, mem_univ _, mem_univ _, ?_, ?_, ?_⟩
  · exact ⟨Sum.inl s(0, 1), liftEdgeInl_isLink_inl.mpr ⟨by decide, rfl⟩⟩
  · exact ⟨Sum.inl s(1, 2), liftEdgeInl_isLink_inl.mpr ⟨by decide, rfl⟩⟩
  · exact ⟨Sum.inl s(0, 2), liftEdgeInl_isLink_inl.mpr ⟨by decide, rfl⟩⟩

/-! ## 4. Counterexample to the page 48 torso-enlargement sentence for `IsVertexExtension` -/

/-- The design `(H, M) = (edgelessTwo, ∅)` on two vertices with no edges and no attachment sets. -/
def baseDesignTwo : GraphDesign (Fin 2) (Sym2 (Fin 2)) :=
  (edgelessTwo, ∅)

/-- The `2`-enlargement `(H', M') = (edgelessTwo, {univ})` of `baseDesignTwo` via `Z = univ`. -/
def enlargedDesignTwo : GraphDesign (Fin 2) (Sym2 (Fin 2)) :=
  (edgelessTwo, {Set.univ})

/-- `enlargedDesignTwo` is a `2`-enlargement of `baseDesignTwo`. -/
theorem isGraphEnlargement_two_baseDesignTwo :
    IsGraphEnlargement 2 baseDesignTwo enlargedDesignTwo := by
  refine ⟨Set.univ, by simp, ?_⟩
  refine ⟨⟨Set.toFinite _, Set.toFinite _, fun _ h => False.elim h⟩,
    ⟨Set.toFinite _, Set.toFinite _, fun _ _ => subset_univ _⟩,
    subset_univ _, le_rfl, fun _ h => mem_univ _, subset_rfl, ?_⟩
  intro X hX hne
  exact (hne (mem_singleton_iff.mp hX)).elim

/-- `completeGraph 2` (the single edge on `{0, 1}`) is a torso of the `2`-enlargement
`enlargedDesignTwo ∈ ({baseDesignTwo} : Set _)^2`. -/
theorem completeGraph_two_mem_torsosOfClass_enlargement :
    completeGraph 2 ∈ torsosOfClass (graphEnlargementClass {baseDesignTwo} 2) := by
  refine ⟨enlargedDesignTwo, ⟨baseDesignTwo, mem_singleton _, isGraphEnlargement_two_baseDesignTwo⟩,
    rfl, deleteEdges_le, ?_⟩
  intro e _
  exact ⟨Set.univ, mem_singleton _, fun _ _ => mem_univ _⟩

/-- Every torso of `baseDesignTwo` has an empty edge set. -/
theorem edgeSet_eq_empty_of_isTorsoOfDesign_baseDesignTwo
    {G' : Graph (Fin 2) (Sym2 (Fin 2))} (h : IsTorsoOfDesign baseDesignTwo G') :
    E(G') = ∅ := by
  ext e
  simp only [mem_empty_iff_false, iff_false]
  intro he
  have hed : e ∉ E(edgelessTwo) := by simp [edgelessTwo]
  obtain ⟨_, hX, _⟩ := h.2.2 e ⟨he, hed⟩
  exact hX

/-- Counterexample to the sentence on page 48 of Graph Minors XVI with the paper's definition of
`IsVertexExtension`: `completeGraph 2` is a torso of a member of `𝒟^2` for `𝒟 = {baseDesignTwo}`,
but there is no torso `G'` of a member of `𝒟` such that `IsVertexExtension n (completeGraph 2) G'`. -/
theorem not_exists_torso_isVertexExtension_completeGraph_two (n : ℕ) :
    ¬ ∃ G' ∈ torsosOfClass ({baseDesignTwo} : Set (GraphDesign (Fin 2) (Sym2 (Fin 2)))),
        IsVertexExtension n (completeGraph 2) G' := by
  rintro ⟨G', ⟨d, hd_mem, htorso⟩, Z, _, _, hdel⟩
  rw [mem_singleton_iff] at hd_mem
  subst hd_mem
  have hVG' : V(G') = Set.univ := htorso.1.symm
  have hEG' : E(G') = ∅ := edgeSet_eq_empty_of_isTorsoOfDesign_baseDesignTwo htorso
  have hV_del : V(GM09.deleteVertices (completeGraph 2) Z) = Set.univ := by
    rw [hdel, hVG']
  have h0_mem : (0 : Fin 2) ∈ V(completeGraph 2) \ Z := by
    change (0 : Fin 2) ∈ V(GM09.deleteVertices (completeGraph 2) Z)
    rw [hV_del]
    exact mem_univ _
  have h1_mem : (1 : Fin 2) ∈ V(completeGraph 2) \ Z := by
    change (1 : Fin 2) ∈ V(GM09.deleteVertices (completeGraph 2) Z)
    rw [hV_del]
    exact mem_univ _
  have he_mem : s(0, 1) ∈ E(GM09.deleteVertices (completeGraph 2) Z) := by
    simp only [GM09.deleteVertices, edgeSet_induce, Set.mem_ofPred_eq]
    exact ⟨0, 1, ⟨by decide, rfl⟩, h0_mem, h1_mem⟩
  rw [hdel, hEG'] at he_mem
  exact he_mem

end GraphMinor.GM16.Examples
