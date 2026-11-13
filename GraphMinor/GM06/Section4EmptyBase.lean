module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4Subarc
import GraphMinor.Surface.DiscGrow

/-!
# Empty bases on a cuff

In Graph Minors VI (4.2), claim (2), a component meeting only one cuff
is also interval-based on the other cuff. A small open cuff arc misses
the finite vertex set, and serves as an empty base. We construct that
arc inside a segment of the circle avoiding the vertices.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- A cuff contains an open arc, with distinct ends, whose closure avoids
any prescribed finite set. -/
theorem exists_cuff_arc_disjoint_finite
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C W : Set S} (hC : IsOArc C) (hW : W.Finite) :
    ∃ s ∈ C \ W, ∃ t ∈ C \ W, s ≠ t ∧
      ∃ A ∈ componentsIn (C \ {s, t}), A ⊆ C \ W := by
  obtain ⟨φ⟩ := hC
  let j := oArcMap φ
  have hji : Function.Injective j := injective_oArcMap φ
  let V : Set Circle := insert 1 (j ⁻¹' W)
  have hV : V.Finite :=
    (Set.Finite.preimage hji.injOn hW).insert 1
  obtain ⟨e⟩ := nonempty_homeomorph_Ioo_nextSegment hV (mem_insert 1 _)
  let q : unitInterval → Ioo (0 : ℝ) 1 := fun t =>
    ⟨1 / 3 + (t : ℝ) / 3, by constructor <;> linarith only [t.2.1, t.2.2]⟩
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqi : Function.Injective q := by
    intro s t he
    apply Subtype.ext
    have hv := congrArg Subtype.val he
    dsimp [q] at hv
    linarith only [hv]
  let f : Curve S :=
    ⟨fun t => j (e (q t)).1, by
      exact (continuous_subtype_val.comp φ.continuous).comp
        (continuous_subtype_val.comp (e.continuous.comp hqc))⟩
  have hfi : Function.Injective f :=
    hji.comp (Subtype.val_injective.comp (e.injective.comp hqi))
  have hfCW : range f ⊆ C \ W := by
    rintro x ⟨t, rfl⟩
    refine ⟨(φ (e (q t)).1).2, ?_⟩
    intro hw
    have hv : (e (q t)).1 ∈ V := Or.inr hw
    exact nextSegment_subset_compl (e (q t)).2 hv
  have hL : IsLineWithEnds (range f) (f 0) (f 1) :=
    IsArcMap.isLineWithEnds ⟨f.continuous, hfi⟩
  have hline : IsLine (range f) := by
    obtain ⟨d, _, _⟩ := hL
    exact ⟨d⟩
  have hcl : closure (cuffSubArc C (range f) (f 0) (f 1)) = range f :=
    closure_cuffSubArc_eq_of_line ⟨φ⟩ hline (hfCW.trans sdiff_subset) hL Subset.rfl
  have hne : (cuffSubArc C (range f) (f 0) (f 1)).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, closure_empty] at hcl
    exact (hcl.symm ▸ mem_range_self 0 : f 0 ∈ (∅ : Set S))
  obtain ⟨x, hx⟩ := hne
  obtain ⟨A, ⟨hA, hAf⟩, _⟩ := mem_sUnion.mp hx
  exact ⟨f 0, hfCW (mem_range_self 0), f 1, hfCW (mem_range_self 1),
    hfi.ne zero_ne_one, A, hA, hAf.trans hfCW⟩

/-- The cuff missed by a component has an empty base. This is the empty
base case used in Graph Minors VI (4.2), claim (2), page 126. -/
theorem isIntervalBasedOn_of_component_disjoint_cuff
    {H : Drawing ClosedCylinder} {H' : Graph ClosedCylinder (Set ClosedCylinder)}
    (hH' : IsGraphComponent H' H.toGraph)
    {C : Set ClosedCylinder} (hC : C ∈ cuffs ClosedCylinder)
    (hmiss : Disjoint (Graph.vertexSet H') C) : IsIntervalBasedOn H H' C := by
  have hCO : IsOArc C := by
    rw [cuffs_closedCylinder] at hC
    rcases hC with rfl | rfl
    · exact isOArc_cylinderCuff1
    · exact isOArc_cylinderCuff2
  obtain ⟨s, hs, t, ht, hst, A, hA, hAC⟩ :=
    exists_cuff_arc_disjoint_finite hCO H.finite_V
  have hempty : H.V ∩ A = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (hAC hx.2).2 hx.1
  refine ⟨A, hC, hH', ⟨s, hs, t, ht, hst, hA⟩, ?_, ?_⟩
  · rw [hempty]
    exact disjoint_iff_inter_eq_empty.mp hmiss
  · intro a ha
    rw [hempty] at ha
    exact False.elim ha

end GraphMinor.GM06
