module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4Components
import GraphMinor.GM06.Section4MinimumInterval
import GraphMinor.GM06.Section4TightInterval
import GraphMinor.GM06.Section4ReplaceInterval
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM06.Section4Subarc

/-!
# The minimum candidate is a cuff base

Graph Minors VI (4.2), claim (2), page 126, chooses a minimum initial
interval. If it contained a vertex of another component, either that
vertex lies outside the range of retained parameters, and we shrink
the same interval, or it lies between two retained vertices. In the
latter case we replace the component by the nested one. Both cases
strictly reduce the number of vertices in the interval. Thus no foreign
vertex remains, and the interval is a cuff base.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- The minimum choice in the one-cuff case of Graph Minors VI (4.2),
claim (2), is a cuff base. Excluding Reduction 1 ensures that the chosen
component has at least two boundary vertices. -/
theorem exists_cuffBase_of_component_on_one_cuff
    {G H : Drawing ClosedCylinder} (hH : H.IsProper)
    (hforest : IsGraphForest H.toGraph)
    (hbd : H.V ∩ bd ClosedCylinder = G.V ∩ bd ClosedCylinder)
    (hno : ¬ Section4Reduction1Applies G H)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    (hex : ∃ K : Graph ClosedCylinder (Set ClosedCylinder),
      IsGraphComponent K H.toGraph ∧ Graph.vertexSet K ∩ bd ClosedCylinder ⊆ C) :
    ∃ (K : Graph ClosedCylinder (Set ClosedCylinder)) (A : Set ClosedCylinder),
      IsCuffBase H K C A ∧ Graph.vertexSet K ∩ bd ClosedCylinder ⊆ C ∧
        2 ≤ (Graph.vertexSet K ∩ C).ncard := by
  classical
  obtain ⟨K, hK, s, hs, t, ht, hst, A, hA, hKA, hpaths, hmin⟩ :=
    exists_minimum_initial_interval_on_cuff hforest hC hex
  have hCO : IsOArc C := by
    rw [cuffs_closedCylinder] at hC
    rcases hC with rfl | rfl
    · exact isOArc_cylinderCuff1
    · exact isOArc_cylinderCuff2
  have hCbd : C ⊆ bd ClosedCylinder := by
    obtain ⟨o, _, rfl⟩ := hC
    exact connectedComponentIn_subset _ o
  have hAC : A ⊆ C := by
    obtain ⟨o, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ o).trans sdiff_subset
  have hline := isLineWithEnds_closure_component_of_oArc hCO hs.1 ht.1 hst hA
  obtain ⟨f, hf⟩ := exists_parametrizesSet_of_isLineWithEnds hline
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  have hWcard := component_boundary_two_le_of_not_reduction1 hH hforest hbd hno hK
  have hWfin : (Graph.vertexSet K ∩ bd ClosedCylinder).Finite :=
    H.finite_V.subset (inter_subset_left.trans hK.1.vertexSet_mono)
  have hWne : (Graph.vertexSet K ∩ bd ClosedCylinder).Nonempty :=
    (ncard_pos (s := Graph.vertexSet K ∩ bd ClosedCylinder) hWfin).mp
      ((by decide : 0 < 2).trans_le hWcard)
  have hforeign : H.V ∩ A ⊆ Graph.vertexSet K := by
    intro x hx
    by_contra hxK
    have hxr : x ∈ range f := hf.2.1.symm ▸ subset_closure hx.2
    obtain ⟨z, hz⟩ := hxr
    have hzHA : f z ∈ H.V ∩ A := by rw [hz]; exact hx
    by_cases hside :
        (∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ bd ClosedCylinder), z < u) ∨
        (∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ bd ClosedCylinder), u < z)
    · obtain ⟨s', hs', t', ht', hst', B, hB, hKB, _, hBpaths, hsmall⟩ :=
        exists_smaller_initial_interval_of_one_sided_point hK hCO hA f hf hKA hWne
          hpaths hzHA hside
      have hlarge := hmin K hK s' hs' t' ht' hst' B hB hKB hBpaths
      exact (not_lt_of_ge hlarge) hsmall
    · have hneq (u : unitInterval)
          (hu : u ∈ f ⁻¹' (Graph.vertexSet K ∩ bd ClosedCylinder)) : u ≠ z := by
        intro he
        have huK : f u ∈ Graph.vertexSet K := hu.1
        rw [he, hz] at huK
        exact hxK huK
      have hleft : ¬ ∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ bd ClosedCylinder), z < u :=
        fun h => hside (Or.inl h)
      have hright : ¬ ∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ bd ClosedCylinder), u < z :=
        fun h => hside (Or.inr h)
      push Not at hleft hright
      obtain ⟨p, hp, hpz⟩ := hleft
      obtain ⟨q, hq, hzq⟩ := hright
      have hpz' : p < z := lt_of_le_of_ne hpz (hneq p hp)
      have hzq' : z < q := lt_of_le_of_ne hzq (Ne.symm (hneq q hq))
      have hpq : p < q := hpz'.trans hzq'
      have hpA : f p ∈ A := hKA hp
      have hqA : f q ∈ A := hKA hq
      have hp01 : p ∈ Ioo (0 : unitInterval) 1 := by rw [← hpre]; exact hpA
      have hq01 : q ∈ Ioo (0 : unitInterval) 1 := by rw [← hpre]; exact hqA
      have hpqf : f p ≠ f q := hf.1.ne hpq.ne
      let I := cuffSubArc C A (f p) (f q)
      have hIcomp : I ∈ componentsIn (C \ {f p, f q}) :=
        cuffSubArc_mem_componentsIn_of_interval hCO hA hline hpA hqA hpqf
      have hIA : I ⊆ A := sUnion_subset fun T hT => hT.2
      have hxI : x ∈ I := by
        rw [show I = cuffSubArc C A (f p) (f q) from rfl,
          cuffSubArc_eq_image_Ioo_of_parametrizes_closure hCO hA f hf hp01 hq01 hpq]
        exact ⟨z, ⟨hpz', hzq'⟩, hz⟩
      obtain ⟨P, hP, hPI⟩ := hpaths (f p) ⟨hp.1, hpA⟩ (f q) ⟨hq.1, hqA⟩ hpqf
      let L := compOf H.toGraph x
      have hL : IsGraphComponent L H.toGraph := isGraphComponent_compOf hx.1
      have hxL : x ∈ Graph.vertexSet L := self_mem_reachSet hx.1
      have hKL : K ≠ L := by
        intro he
        apply hxK
        rw [he]
        exact hxL
      obtain ⟨s', hs', t', ht', hst', B, hB, hLB, _, hBpaths, hsmall⟩ :=
        exists_smaller_initial_interval_of_nested_component hforest hK hL hKL hC hIA hpqf
          ⟨hp.1, hAC hpA⟩ ⟨hq.1, hAC hqA⟩ hpA hIcomp hP hPI ⟨hxL, hxI⟩
      have hlarge := hmin L hL s' hs' t' ht' hst' B hB hLB hBpaths
      exact (not_lt_of_ge hlarge) hsmall
  have hEq : Graph.vertexSet K ∩ C = H.V ∩ A := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hK.1.vertexSet_mono hx.1, hKA ⟨hx.1, hCbd hx.2⟩⟩
    · intro x hx
      exact ⟨hforeign hx, hAC hx.2⟩
  have hbase : IsCuffBase H K C A := by
    refine ⟨hC, hK, ⟨s, hs, t, ht, hst, hA⟩, hEq, ?_⟩
    intro a ha b hb hab
    exact hpaths a ⟨hforeign ha, ha.2⟩ b ⟨hforeign hb, hb.2⟩ hab
  have honly : Graph.vertexSet K ∩ bd ClosedCylinder ⊆ C := hKA.trans hAC
  have hW_eq : Graph.vertexSet K ∩ bd ClosedCylinder = Graph.vertexSet K ∩ C := by
    ext x
    exact ⟨fun hx => ⟨hx.1, honly hx⟩, fun hx => ⟨hx.1, hCbd hx.2⟩⟩
  refine ⟨K, A, hbase, honly, ?_⟩
  rw [← hW_eq]
  exact hWcard

end GraphMinor.GM06
