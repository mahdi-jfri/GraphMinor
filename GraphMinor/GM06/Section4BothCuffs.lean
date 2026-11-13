module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.Cylinder
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4InitialInterval
import GraphMinor.GM06.Section4TightInterval
import GraphMinor.GM06.Section4NestedComponents
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM06.Section4Subarc

/-!
# Components meeting both cuffs are interval-based

The first case of Graph Minors VI (4.2), claim (2), says that if every
component meets both cuffs, each is interval-based on both. For a fixed
component and cuff, minimize an interval around its vertices. A foreign
vertex outside their parameter range permits shrinking. One inside
would belong to a component confined to this cuff by separation, which
contradicts the assumption that it meets the other cuff.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

/-- Graph Minors VI (4.2), claim (2), first case, page 126: if every
component meets both cuffs, every component is interval-based on each
cuff. This supplies the proof omitted after the word “clearly”. -/
theorem isIntervalBasedOn_of_all_components_meet_both_cuffs
    {H : Drawing ClosedCylinder} (hforest : IsGraphForest H.toGraph)
    (hall : ∀ L : Graph ClosedCylinder (Set ClosedCylinder), IsGraphComponent L H.toGraph →
      (Graph.vertexSet L ∩ cylinderCuff1).Nonempty ∧
      (Graph.vertexSet L ∩ cylinderCuff2).Nonempty)
    {K : Graph ClosedCylinder (Set ClosedCylinder)} (hK : IsGraphComponent K H.toGraph)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder) : IsIntervalBasedOn H K C := by
  classical
  let Q : ℕ → Prop := fun n =>
    ∃ s ∈ C \ H.V, ∃ t ∈ C \ H.V, s ≠ t ∧
      ∃ A ∈ componentsIn (C \ {s, t}), Graph.vertexSet K ∩ C ⊆ A ∧
        (∀ a ∈ Graph.vertexSet K ∩ A, ∀ b ∈ Graph.vertexSet K ∩ A, a ≠ b →
          ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
            PathHomotopicToArc P a b (cuffSubArc C A a b)) ∧ (A ∩ H.V).ncard = n
  have hQ : ∃ n, Q n := by
    obtain ⟨s, hs, t, ht, hst, A, hA, hKA, hpaths⟩ := exists_initial_interval_on_cuff hforest hK hC
    exact ⟨(A ∩ H.V).ncard, s, hs, t, ht, hst, A, hA, hKA, hpaths, rfl⟩
  obtain ⟨s, hs, t, ht, hst, A, hA, hKA, hpaths, hn⟩ := Nat.find_spec hQ
  have hmin {s' t' : ClosedCylinder} {B : Set ClosedCylinder}
      (hs' : s' ∈ C \ H.V) (ht' : t' ∈ C \ H.V) (hst' : s' ≠ t')
      (hB : B ∈ componentsIn (C \ {s', t'})) (hKB : Graph.vertexSet K ∩ C ⊆ B)
      (hBpaths : ∀ a ∈ Graph.vertexSet K ∩ B, ∀ b ∈ Graph.vertexSet K ∩ B, a ≠ b →
        ∃ P : Drawing ClosedCylinder, IsSubpathOf H P a b ∧
          PathHomotopicToArc P a b (cuffSubArc C B a b)) :
      (A ∩ H.V).ncard ≤ (B ∩ H.V).ncard := by
    rw [hn]
    exact Nat.find_min' hQ ⟨s', hs', t', ht', hst', B, hB, hKB, hBpaths, rfl⟩
  have hcases : C = cylinderCuff1 ∨ C = cylinderCuff2 := by rw [cuffs_closedCylinder] at hC; exact hC
  have hCO : IsOArc C := hcases.elim
    (fun h => h ▸ isOArc_cylinderCuff1) (fun h => h ▸ isOArc_cylinderCuff2)
  have hAC : A ⊆ C := by
    obtain ⟨o, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ o).trans sdiff_subset
  have hline := isLineWithEnds_closure_component_of_oArc hCO hs.1 ht.1 hst hA
  obtain ⟨f, hf⟩ := exists_parametrizesSet_of_isLineWithEnds hline
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  have hWfin : (Graph.vertexSet K ∩ C).Finite :=
    H.finite_V.subset (inter_subset_left.trans hK.1.vertexSet_mono)
  have hWne : (Graph.vertexSet K ∩ C).Nonempty := by
    rcases hcases with h | h
    · rw [h]; exact (hall K hK).1
    · rw [h]; exact (hall K hK).2
  have hforeign : H.V ∩ A ⊆ Graph.vertexSet K := by
    intro x hx
    by_contra hxK
    have hxr : x ∈ range f := hf.2.1.symm ▸ subset_closure hx.2
    obtain ⟨z, hz⟩ := hxr
    have hzHA : f z ∈ H.V ∩ A := by rw [hz]; exact hx
    by_cases hside :
        (∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ C), z < u) ∨
        (∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ C), u < z)
    · obtain ⟨s', hs', t', ht', hst', B, hB, hKB, _, hBpaths, hsmall⟩ :=
        exists_smaller_interval_of_one_sided_point (Graph.vertexSet K ∩ C) hWfin
          hCO hA f hf hKA hWne
          hpaths hzHA hside
      have hlarge := hmin hs' ht' hst' hB hKB hBpaths
      exact (not_lt_of_ge hlarge) hsmall
    · have hneq (u : unitInterval)
          (hu : u ∈ f ⁻¹' (Graph.vertexSet K ∩ C)) : u ≠ z := by
        intro he
        have huK : f u ∈ Graph.vertexSet K := hu.1
        rw [he, hz] at huK
        exact hxK huK
      have hleft : ¬ ∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ C), z < u :=
        fun h => hside (Or.inl h)
      have hright : ¬ ∀ u ∈ f ⁻¹' (Graph.vertexSet K ∩ C), u < z :=
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
      have hLOnly : Graph.vertexSet L ∩ bd ClosedCylinder ⊆ C :=
        (component_boundary_subset_arc_of_mem hK hL hKL hC hpqf
          ⟨hp.1, hAC hpA⟩ ⟨hq.1, hAC hqA⟩ hIcomp hP hPI ⟨hxL, hxI⟩).trans
          (hIA.trans hAC)
      rcases hcases with hC1 | hC2
      · obtain ⟨y, hyL, hy2⟩ := (hall L hL).2
        have hybd : y ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inr hy2
        have hy1 : y ∈ cylinderCuff1 := by rw [← hC1]; exact hLOnly ⟨hyL, hybd⟩
        change y.1.1 = 1 at hy1
        change y.1.1 = 2 at hy2
        linarith only [hy1, hy2]
      · obtain ⟨y, hyL, hy1⟩ := (hall L hL).1
        have hybd : y ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl hy1
        have hy2 : y ∈ cylinderCuff2 := by rw [← hC2]; exact hLOnly ⟨hyL, hybd⟩
        change y.1.1 = 1 at hy1
        change y.1.1 = 2 at hy2
        linarith only [hy1, hy2]
  have hEq : Graph.vertexSet K ∩ C = H.V ∩ A := by
    apply Subset.antisymm
    · intro x hx
      exact ⟨hK.1.vertexSet_mono hx.1, hKA hx⟩
    · intro x hx
      exact ⟨hforeign hx, hAC hx.2⟩
  refine ⟨A, hC, hK, ⟨s, hs, t, ht, hst, hA⟩, hEq, ?_⟩
  intro a ha b hb hab
  exact hpaths a ⟨hforeign ha, ha.2⟩ b ⟨hforeign hb, hb.2⟩ hab

end GraphMinor.GM06
