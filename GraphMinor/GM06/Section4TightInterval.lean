module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4ShrinkInterval
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.Surface.DiscGrow

/-!
# Excluding vertices beyond the chosen component

In the minimum candidate of VI (4.2), claim (2), an extra vertex cannot
lie before every retained boundary vertex, or after every retained
boundary vertex. Shrink the interval on that side, preserve the path
homotopies, and obtain a strict decrease in the number of vertices of
`H` in the interval.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Shrink an interval past a point on one side of all retained points,
preserving the specified component's path homotopies. -/
theorem exists_smaller_interval_of_one_sided_point
    {H : Drawing ClosedCylinder} {K : Graph ClosedCylinder (Set ClosedCylinder)}
    (W : Set ClosedCylinder) (hWf : W.Finite)
    {C A : Set ClosedCylinder} (hC : IsOArc C) {s t : ClosedCylinder}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (f : Curve ClosedCylinder) (hf : ParametrizesSet f (closure A) s t)
    (hKA : W ⊆ A)
    (hWne : W.Nonempty)
    (hpaths : ∀ a ∈ Graph.vertexSet K ∩ A, ∀ b ∈ Graph.vertexSet K ∩ A, a ≠ b →
      ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
        PathHomotopicToArc P a b (cuffSubArc C A a b))
    {z : unitInterval} (hz : f z ∈ H.V ∩ A)
    (hside : (∀ u ∈ f ⁻¹' W, z < u) ∨
      (∀ u ∈ f ⁻¹' W, u < z)) :
    ∃ s' ∈ C \ H.V, ∃ t' ∈ C \ H.V, s' ≠ t' ∧
      ∃ B ∈ componentsIn (C \ {s', t'}),
        W ⊆ B ∧ B ⊆ A ∧
        (∀ a ∈ Graph.vertexSet K ∩ B, ∀ b ∈ Graph.vertexSet K ∩ B, a ≠ b →
          ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
            PathHomotopicToArc P a b (cuffSubArc C B a b)) ∧
        (B ∩ H.V).ncard < (A ∩ H.V).ncard := by
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  have hWin : f ⁻¹' W ⊆ Ioo (0 : unitInterval) 1 := by
    intro u hu
    rw [← hpre]
    exact hKA hu
  have hcuts : ∃ l r : unitInterval,
      f ⁻¹' W ⊆ Ioo l r ∧ z ∉ Ioo l r := by
    rcases hside with hleft | hright
    · exact ⟨z, 1, fun u hu => ⟨hleft u hu, (hWin hu).2⟩,
        fun h => (lt_irrefl z) h.1⟩
    · exact ⟨0, z, fun u hu => ⟨(hWin hu).1, hright u hu⟩,
        fun h => (lt_irrefl z) h.2⟩
  obtain ⟨l, r, hWlr, hzlr⟩ := hcuts
  obtain ⟨s', hs', t', ht', hst', B, hB, hKB, hBA, hBcut, hlineB⟩ :=
    exists_restricted_cuff_interval hC hA f hf H.finite_V hWf hWne hKA hWlr
  have hAC : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hlineA : IsLineWithEnds (closure A) s t := by
    simpa only [hf.2.1, hf.2.2.1, hf.2.2.2] using
      IsArcMap.isLineWithEnds ⟨f.continuous, hf.1⟩
  have hzB : f z ∉ B := by
    intro hzB
    obtain ⟨u, hu, he⟩ := hBcut hzB
    exact hzlr ((hf.1 he) ▸ hu)
  refine ⟨s', ⟨hAC hs'.1, hs'.2⟩, t', ⟨hAC ht'.1, ht'.2⟩, hst', B, hB, hKB, hBA, ?_, ?_⟩
  · intro a ha b hb hab
    obtain ⟨P, hP, hPA⟩ := hpaths a ⟨ha.1, hBA ha.2⟩ b ⟨hb.1, hBA hb.2⟩ hab
    have hcl := closure_cuffSubArc_eq_of_nested_intervals hC hA hlineA hB hlineB hBA
      ha.2 hb.2 hab
    exact ⟨P, hP, by simpa only [PathHomotopicToArc, hcl] using hPA⟩
  · have hproper : B ∩ H.V ⊂ A ∩ H.V := by
      refine ssubset_iff_subset_ne.mpr ⟨inter_subset_inter_left _ hBA, ?_⟩
      intro heq
      have hzA : f z ∈ A ∩ H.V := ⟨hz.2, hz.1⟩
      have hzB' : f z ∈ B ∩ H.V := heq.symm ▸ hzA
      exact hzB hzB'.1
    exact ncard_lt_ncard hproper (H.finite_V.inter_of_right A)

/-- A candidate containing a vertex on one side of all its retained
component vertices has a strictly smaller candidate. This is the first
part of the minimum-size argument in VI (4.2), claim (2), page 126. -/
theorem exists_smaller_initial_interval_of_one_sided_point
    {H : Drawing ClosedCylinder} {K : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K H.toGraph)
    {C A : Set ClosedCylinder} (hC : IsOArc C) {s t : ClosedCylinder}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (f : Curve ClosedCylinder) (hf : ParametrizesSet f (closure A) s t)
    (hKA : Graph.vertexSet K ∩ bd ClosedCylinder ⊆ A)
    (hWne : (Graph.vertexSet K ∩ bd ClosedCylinder).Nonempty)
    (hpaths : ∀ a ∈ Graph.vertexSet K ∩ A, ∀ b ∈ Graph.vertexSet K ∩ A, a ≠ b →
      ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
        PathHomotopicToArc P a b (cuffSubArc C A a b))
    {z : unitInterval} (hz : f z ∈ H.V ∩ A)
    (hside : (∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ bd ClosedCylinder), z < u) ∨
      (∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ bd ClosedCylinder), u < z)) :
    ∃ s' ∈ C \ H.V, ∃ t' ∈ C \ H.V, s' ≠ t' ∧
      ∃ B ∈ componentsIn (C \ {s', t'}),
        Graph.vertexSet K ∩ bd ClosedCylinder ⊆ B ∧ B ⊆ A ∧
        (∀ a ∈ Graph.vertexSet K ∩ B, ∀ b ∈ Graph.vertexSet K ∩ B, a ≠ b →
          ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
            PathHomotopicToArc P a b (cuffSubArc C B a b)) ∧
        (B ∩ H.V).ncard < (A ∩ H.V).ncard := by
  exact exists_smaller_interval_of_one_sided_point
    (Graph.vertexSet K ∩ bd ClosedCylinder)
    (H.finite_V.subset (inter_subset_left.trans hK.1.vertexSet_mono))
    hC hA f hf hKA hWne hpaths hz hside

end GraphMinor.GM06
