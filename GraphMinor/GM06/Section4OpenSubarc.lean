module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Subarc
import GraphMinor.GM06.Section4Segment
import GraphMinor.GM06.Section4IntervalRestriction

/-!
# Parameterizing subarcs inside an open cuff interval

Two points inside a cuff interval determine a closed subarc still inside
that interval. We restrict a parameterization of its closure, then use
the two-arc characterization of `cuffSubArc`. This gives the cuff curves
needed in Graph Minors VI (4.2), claim (2).
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- A line with specified ends has an injective curve parameterization
with those ends. -/
theorem exists_parametrizesSet_of_isLineWithEnds
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {L : Set S} {s t : S} (hL : IsLineWithEnds L s t) :
    ∃ f : Curve S, ParametrizesSet f L s t := by
  obtain ⟨f, hf, hR, h0, h1⟩ := hL.exists_arc
  exact ⟨⟨f, hf.1⟩, hf.2, hR, h0, h1⟩

/-- A parameterization of the closure of a cuff component takes the
open unit interval precisely onto that component. -/
theorem preimage_component_of_parametrizes_closure
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} {s t : S} (hA : A ∈ componentsIn (C \ {s, t}))
    (f : Curve S) (hf : ParametrizesSet f (closure A) s t) :
    f ⁻¹' A = Ioo (0 : unitInterval) 1 := by
  have hAsub : A ⊆ C \ {s, t} := by
    obtain ⟨x, _, rfl⟩ := hA
    exact connectedComponentIn_subset _ x
  have hAconn : IsPreconnected A := by
    obtain ⟨x, _, rfl⟩ := hA
    exact isPreconnected_connectedComponentIn
  ext v
  constructor
  · intro hv
    refine ⟨unitInterval.pos_iff_ne_zero.mpr ?_, unitInterval.lt_one_iff_ne_one.mpr ?_⟩
    · intro he
      exact (hAsub hv).2 (Or.inl (by rw [he]; exact hf.2.2.1))
    · intro he
      exact (hAsub hv).2 (Or.inr (by rw [he]; exact hf.2.2.2))
  · intro hv
    have hcl := closure_arc_subset_of_isPreconnected hAconn f hf.1 hf.2.1
    rcases hcl (hf.2.1 ▸ mem_range_self v) with hvA | hvends
    · exact hvA
    · rcases hvends with he | he
      · exact ((ne_of_gt hv.1) (hf.1 he)).elim
      · exact ((ne_of_lt hv.2) (hf.1 he)).elim

/-- A subarc between two points inside an open cuff interval has an
injective parameterization whose range stays inside the interval. -/
theorem exists_parametrizesSet_cuffSubArc
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} (hC : IsOArc C) {s t a b : S}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (hline : IsLineWithEnds (closure A) s t)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    ∃ k : Curve S, ParametrizesSet k (closure (cuffSubArc C A a b)) a b ∧ range k ⊆ A := by
  have hAsub : A ⊆ C \ {s, t} := by
    obtain ⟨x, _, rfl⟩ := hA
    exact connectedComponentIn_subset _ x
  have hAconn : IsPreconnected A := by
    obtain ⟨x, _, rfl⟩ := hA
    exact isPreconnected_connectedComponentIn
  obtain ⟨f, hf, hfR, hf0, hf1⟩ := hline.exists_arc
  let g : Curve S := ⟨f, hf.1⟩
  have hgR : range g = closure A := hfR
  have hga : a ∈ range g := hgR.symm ▸ subset_closure ha
  have hgb : b ∈ range g := hgR.symm ▸ subset_closure hb
  obtain ⟨p, hp⟩ := hga
  obtain ⟨q, hq⟩ := hgb
  have hpq : p ≠ q := fun he => hab (hp.symm.trans ((congrArg g he).trans hq))
  have hpre (v : unitInterval) (hv : g v ∈ A) : (v : ℝ) ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · apply lt_of_le_of_ne v.2.1
      intro h0
      have hv0 : v = 0 := Subtype.ext h0.symm
      exact (hAsub hv).2 (Or.inl (by rw [hv0]; exact hf0))
    · apply lt_of_le_of_ne v.2.2
      intro h1
      have hv1 : v = 1 := Subtype.ext h1
      exact (hAsub hv).2 (Or.inr (by rw [hv1]; exact hf1))
  have hpint := hpre p (hp.symm ▸ ha)
  have hqint := hpre q (hq.symm ▸ hb)
  have hginterior (v : unitInterval) (hv : (v : ℝ) ∈ Ioo (0 : ℝ) 1) : g v ∈ A := by
    have hend := closure_arc_subset_of_isPreconnected hAconn g hf.2 hgR
    rcases hend (hgR ▸ mem_range_self v) with hvA | hvend
    · exact hvA
    · rcases hvend with hv0 | hv1
      · have he : v = 0 := hf.2 hv0
        have hvz := congrArg Subtype.val he
        exact (ne_of_gt hv.1 hvz).elim
      · have he : v = 1 := hf.2 hv1
        have hvo := congrArg Subtype.val he
        exact (ne_of_lt hv.2 hvo).elim
  let k := GM07.subPathSeg g p q
  have hki : Function.Injective k := injective_subPathSeg_of_ne hf.2 hpq
  have hkA : range k ⊆ A := by
    rintro x ⟨u, rfl⟩
    apply hginterior
    change (1 - (u : ℝ)) * (p : ℝ) + (u : ℝ) * (q : ℝ) ∈ Ioo (0 : ℝ) 1
    exact (convex_Ioo (𝕜 := ℝ) (0 : ℝ) 1) hpint hqint (sub_nonneg.mpr u.2.2) u.2.1 (by ring)
  have hk0 : k 0 = a := (GM07.subPathSeg_zero g p q).trans hp
  have hk1 : k 1 = b := (GM07.subPathSeg_one g p q).trans hq
  have hkline : IsLineWithEnds (range k) a b := by
    simpa only [hk0, hk1] using IsArcMap.isLineWithEnds ⟨k.continuous, hki⟩
  have hclosedline : IsLine (closure A) := by obtain ⟨e, _, _⟩ := hline; exact ⟨e⟩
  have hclC : closure A ⊆ C :=
    closure_minimal (hAsub.trans sdiff_subset) hC.isCompact.isClosed
  have hclosure : closure (cuffSubArc C A a b) = range k :=
    closure_cuffSubArc_eq_of_subset_line hC hclosedline hclC subset_closure hkline hkA
  exact ⟨k, ⟨hki, hclosure.symm, hk0, hk1⟩, hkA⟩

/-- In an interval parameterization of a cuff component, the cuff subarc
between two interior parameters is the image of their open interval. -/
theorem cuffSubArc_eq_image_Ioo_of_parametrizes_closure
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} (hC : IsOArc C) {s t : S}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (f : Curve S) (hf : ParametrizesSet f (closure A) s t)
    {p q : unitInterval} (hp : p ∈ Ioo (0 : unitInterval) 1)
    (hq : q ∈ Ioo (0 : unitInterval) 1) (hpq : p < q) :
    cuffSubArc C A (f p) (f q) = f '' Ioo p q := by
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  let k := GM07.subPathSeg f p q
  have hki : Function.Injective k := injective_subPathSeg_of_ne hf.1 hpq.ne
  have hL : IsLineWithEnds (range k) (f p) (f q) := by
    simpa only [k, GM07.subPathSeg_zero, GM07.subPathSeg_one] using
      IsArcMap.isLineWithEnds ⟨k.continuous, hki⟩
  have hkA : range k ⊆ A := by
    rw [show range k = range (GM07.subPathSeg f p q) from rfl,
      range_subPathSeg_eq_image_uIcc, uIcc_of_le hpq.le]
    rintro x ⟨v, hv, rfl⟩
    change v ∈ f ⁻¹' A
    rw [hpre]
    exact ⟨hp.1.trans_le hv.1, hv.2.trans_lt hq.2⟩
  have hM : IsLine (closure A) := by
    obtain ⟨e, _, _⟩ := IsArcMap.isLineWithEnds ⟨f.continuous, hf.1⟩
    exact ⟨hf.2.1 ▸ e⟩
  have hAsub : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hclA : closure A ⊆ C := closure_minimal hAsub hC.isCompact.isClosed
  rw [cuffSubArc_eq_line_sdiff_ends_of_subset_line hC hM hclA subset_closure hL hkA]
  exact range_subPathSeg_sdiff_ends_eq_image_Ioo hf.1 hpq

/-- The closure of a cuff component with a line parameterization is
that component together with its two ends. -/
theorem closure_component_eq_union_pair
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} {s t : S} (hA : A ∈ componentsIn (C \ {s, t}))
    (hline : IsLineWithEnds (closure A) s t) : closure A = A ∪ {s, t} := by
  obtain ⟨f, hf⟩ := exists_parametrizesSet_of_isLineWithEnds hline
  have hconn : IsPreconnected A := by
    obtain ⟨x, _, rfl⟩ := hA
    exact isPreconnected_connectedComponentIn
  apply Subset.antisymm
  · simpa only [hf.2.2.1, hf.2.2.2] using
      closure_arc_subset_of_isPreconnected hconn f hf.1 hf.2.1
  · refine union_subset subset_closure ?_
    rintro x (rfl | rfl)
    · rw [← hf.2.1, ← hf.2.2.1]; exact mem_range_self 0
    · rw [← hf.2.1, ← hf.2.2.2]; exact mem_range_self 1

/-- Closing the base cuff interval does not change a subarc between two
of its interior points. -/
theorem closure_cuffSubArc_closure_base_eq
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} (hC : IsOArc C) {s t a b : S}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (hline : IsLineWithEnds (closure A) s t)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    closure (cuffSubArc C (closure A) a b) = closure (cuffSubArc C A a b) := by
  obtain ⟨k, hk, hkA⟩ := exists_parametrizesSet_cuffSubArc hC hA hline ha hb hab
  have hL : IsLineWithEnds (range k) a b := by
    simpa only [hk.2.2.1, hk.2.2.2] using IsArcMap.isLineWithEnds ⟨k.continuous, hk.1⟩
  have hM : IsLine (closure A) := by obtain ⟨e, _, _⟩ := hline; exact ⟨e⟩
  have hAsub : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hclA : closure A ⊆ C := closure_minimal hAsub hC.isCompact.isClosed
  exact (closure_cuffSubArc_eq_of_subset_line hC hM hclA Subset.rfl hL
    (hkA.trans subset_closure)).trans hk.2.1

/-- A cuff subarc inside an open cuff interval is itself a component
obtained by removing its two ends. -/
theorem cuffSubArc_mem_componentsIn_of_interval
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A : Set S} (hC : IsOArc C) {s t a b : S}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (hline : IsLineWithEnds (closure A) s t)
    (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    cuffSubArc C A a b ∈ componentsIn (C \ {a, b}) := by
  obtain ⟨k, hk, hkA⟩ := exists_parametrizesSet_cuffSubArc hC hA hline ha hb hab
  have hL : IsLineWithEnds (range k) a b := by
    simpa only [hk.2.2.1, hk.2.2.2] using IsArcMap.isLineWithEnds ⟨k.continuous, hk.1⟩
  have hM : IsLine (closure A) := by obtain ⟨e, _, _⟩ := hline; exact ⟨e⟩
  have hAsub : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hclA : closure A ⊆ C := closure_minimal hAsub hC.isCompact.isClosed
  rw [cuffSubArc_eq_line_sdiff_ends_of_subset_line hC hM hclA subset_closure hL hkA]
  exact cuff_line_sdiff_ends_mem_componentsIn hC hL (hkA.trans hAsub)

/-- Shrinking an open cuff interval does not change the subarc between
two of its retained points. The closures agree, which is the form needed
for the path homotopies in VI (4.2), claim (2). -/
theorem closure_cuffSubArc_eq_of_nested_intervals
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A B : Set S} (hC : IsOArc C) {s t u v a b : S}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (hlineA : IsLineWithEnds (closure A) s t)
    (hB : B ∈ componentsIn (C \ {u, v}))
    (hlineB : IsLineWithEnds (closure B) u v) (hBA : B ⊆ A)
    (ha : a ∈ B) (hb : b ∈ B) (hab : a ≠ b) :
    closure (cuffSubArc C A a b) = closure (cuffSubArc C B a b) := by
  obtain ⟨k, hk, hkB⟩ := exists_parametrizesSet_cuffSubArc hC hB hlineB ha hb hab
  have hL : IsLineWithEnds (range k) a b := by
    simpa only [hk.2.2.1, hk.2.2.2] using IsArcMap.isLineWithEnds ⟨k.continuous, hk.1⟩
  have hM : IsLine (closure A) := by obtain ⟨e, _, _⟩ := hlineA; exact ⟨e⟩
  have hAsub : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hclA : closure A ⊆ C := closure_minimal hAsub hC.isCompact.isClosed
  exact (closure_cuffSubArc_eq_of_subset_line hC hM hclA subset_closure hL
    (hkB.trans hBA)).trans hk.2.1

end GraphMinor.GM06
