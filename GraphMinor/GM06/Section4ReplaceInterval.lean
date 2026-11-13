module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4Claim1
import GraphMinor.GM06.Section4InitialInterval
import GraphMinor.GM06.Section4NestedComponents
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM06.Section4ShrinkInterval
import GraphMinor.Surface.DiscGrow

/-!
# Replacing the chosen component in VI (4.2), claim (2)

If a foreign component has a vertex inside the subarc between two
vertices of the chosen component, all its boundary vertices stay there.
Claim (1) supplies their subarc homotopies. Choose a smaller interval
around them, excluding an original end vertex. This strictly decreases
the number of vertices of `H` in the interval, as required by the
paper's minimum argument on page 126.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Replace the chosen component by a distinct component nested inside
its homotopic cuff path, obtaining a strictly smaller initial candidate.
This is the interior case of the minimum argument in VI (4.2)(2). -/
theorem exists_smaller_initial_interval_of_nested_component
    {H P : Drawing ClosedCylinder} (hH : IsGraphForest H.toGraph)
    {K L : Graph ClosedCylinder (Set ClosedCylinder)}
    (hK : IsGraphComponent K H.toGraph) (hL : IsGraphComponent L H.toGraph) (hne : K ≠ L)
    {C A S : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder) (hAS : A ⊆ S)
    {a b x : ClosedCylinder} (hab : a ≠ b)
    (ha : a ∈ Graph.vertexSet K ∩ C) (hb : b ∈ Graph.vertexSet K ∩ C) (haS : a ∈ S)
    (hA : A ∈ componentsIn (C \ {a, b}))
    (hP : IsSubpathOf H P a b) (hPA : PathHomotopicToArc P a b A)
    (hx : x ∈ Graph.vertexSet L ∩ A) :
    ∃ s' ∈ C \ H.V, ∃ t' ∈ C \ H.V, s' ≠ t' ∧
      ∃ B ∈ componentsIn (C \ {s', t'}),
        Graph.vertexSet L ∩ bd ClosedCylinder ⊆ B ∧ B ⊆ S ∧
        (∀ c ∈ Graph.vertexSet L ∩ B, ∀ d ∈ Graph.vertexSet L ∩ B, c ≠ d →
          ∃ Q : Drawing ClosedCylinder, IsSubpathOf H Q c d ∧
            PathHomotopicToArc Q c d (cuffSubArc C B c d)) ∧
        (B ∩ H.V).ncard < (S ∩ H.V).ncard := by
  have hCO : IsOArc C := by
    rw [cuffs_closedCylinder] at hC
    rcases hC with rfl | rfl
    · exact isOArc_cylinderCuff1
    · exact isOArc_cylinderCuff2
  have hAcut : A ⊆ C \ {a, b} := by
    obtain ⟨o, _, rfl⟩ := hA
    exact connectedComponentIn_subset _ o
  have hCbd : C ⊆ bd ClosedCylinder := by
    obtain ⟨o, _, rfl⟩ := hC
    exact connectedComponentIn_subset _ o
  have hWA := component_boundary_subset_arc_of_mem hK hL hne hC hab ha hb hA hP hPA hx
  have hWne : (Graph.vertexSet L ∩ bd ClosedCylinder).Nonempty :=
    ⟨x, hx.1, hCbd (hAcut hx.2).1⟩
  have hWf : (Graph.vertexSet L ∩ bd ClosedCylinder).Finite :=
    H.finite_V.subset (inter_subset_left.trans hL.1.vertexSet_mono)
  have hlineA : IsLineWithEnds (closure A) a b := by
    obtain ⟨f, k, hf, hk, hhom⟩ := hPA
    simpa only [hk.2.1, hk.2.2.1, hk.2.2.2] using
      IsArcMap.isLineWithEnds ⟨k.continuous, hk.1⟩
  obtain ⟨f, hf⟩ := exists_parametrizesSet_of_isLineWithEnds hlineA
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  have hWin : f ⁻¹' (Graph.vertexSet L ∩ bd ClosedCylinder) ⊆ Ioo (0 : unitInterval) 1 := by
    intro v hv
    rw [← hpre]
    exact hWA hv
  obtain ⟨s', hs', t', ht', hst', B, hB, hWB, hBA, _, hlineB⟩ :=
    exists_restricted_cuff_interval hCO hA f hf H.finite_V hWf hWne hWA hWin
  have hBS : B ⊆ S := hBA.trans hAS
  have haB : a ∉ B := by
    intro haB
    exact (hAcut (hBA haB)).2 (Or.inl rfl)
  refine ⟨s', ⟨(hAcut hs'.1).1, hs'.2⟩, t', ⟨(hAcut ht'.1).1, ht'.2⟩,
    hst', B, hB, hWB, hBS, ?_, ?_⟩
  · intro c hc d hd hcd
    obtain ⟨Q, hQ⟩ := exists_subpath_of_mem_component hL hc.1 hd.1 hcd
    have hQA := lemma_4_2_claim_1_of_mem_arc hH hC hab hA hP hPA hQ
      (hBA hc.2) (hBA hd.2) hcd
    have hcl := closure_cuffSubArc_eq_of_nested_intervals hCO hA hlineA hB hlineB hBA
      hc.2 hd.2 hcd
    exact ⟨Q, hQ, by simpa only [PathHomotopicToArc, hcl] using hQA⟩
  · have hproper : B ∩ H.V ⊂ S ∩ H.V := by
      refine ssubset_iff_subset_ne.mpr ⟨inter_subset_inter_left _ hBS, ?_⟩
      intro heq
      have haSH : a ∈ S ∩ H.V := ⟨haS, hK.1.vertexSet_mono ha.1⟩
      have haBH : a ∈ B ∩ H.V := heq.symm ▸ haSH
      exact haB haBH.1
    exact ncard_lt_ncard hproper (H.finite_V.inter_of_right S)

end GraphMinor.GM06
