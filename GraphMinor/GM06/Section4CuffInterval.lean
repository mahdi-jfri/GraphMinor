module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4Subarc
import GraphMinor.GM06.Section2Dual
import GraphMinor.Surface.SurfaceGraph
import GraphMinor.Surface.DiscGrow

/-!
# Choosing a cuff interval from an open region

For Graph Minors VI (4.2), claim (2), choose two nearby points of a cuff
inside the selected region. A small closed cuff line between them stays
in that region. Its complementary open arc contains all prescribed
points of the cuff that miss the region.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface Real Metric

universe u

/-- A point of an open part of a cuff lies in the interior of a closed
line contained in that open part. -/
theorem exists_cuff_line_around_point
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C O : Set S} (hC : IsOArc C) (hO : IsOpen O)
    {x : S} (hxC : x ∈ C) (hxO : x ∈ O) :
    ∃ (L : Set S) (s t : S), s ≠ t ∧ IsLineWithEnds L s t ∧
      L ⊆ C ∩ O ∧ x ∈ L \ {s, t} := by
  obtain ⟨φ⟩ := hC
  let z := φ.symm ⟨x, hxC⟩
  let j : ℝ → S := fun θ => oArcMap φ (Circle.exp θ * z)
  have hj : Continuous j := by dsimp [j, oArcMap]; fun_prop
  have hj0 : j 0 = x := by simp [j, z, oArcMap]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp (hO.preimage hj) 0 (by simpa [hj0] using hxO)
  let δ : ℝ := min ε π / 2
  have hδ : 0 < δ := div_pos (lt_min hε pi_pos) (by norm_num)
  have hδε : δ < ε := by
    have hm : min ε π ≤ ε := min_le_left _ _
    dsimp [δ]
    linarith only [hm, hε]
  have hδπ : 2 * δ < 2 * π := by
    have hm : min ε π ≤ π := min_le_right _ _
    dsimp [δ]
    linarith only [hm, pi_pos]
  let θ : unitInterval → ℝ := fun t => δ * (2 * (t : ℝ) - 1)
  have hθ (t : unitInterval) : θ t ∈ Icc (-δ) δ := by
    dsimp [θ]
    constructor <;> nlinarith only [hδ, t.2.1, t.2.2]
  let f : Curve S := ⟨fun t => j (θ t), by dsimp [θ]; fun_prop⟩
  have hfi : Function.Injective f := by
    intro s t he
    have he' : Circle.exp (θ s) * z = Circle.exp (θ t) * z :=
      injective_oArcMap φ he
    have hθeq := Circle.exp_injOn_Icc (by linarith only [hδπ]) (hθ s) (hθ t) (mul_right_cancel he')
    apply Subtype.ext
    dsimp [θ] at hθeq
    nlinarith only [hθeq, hδ]
  have hsub : range f ⊆ C ∩ O := by
    rintro y ⟨t, rfl⟩
    refine ⟨(φ (Circle.exp (θ t) * z)).2, hball ?_⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨(neg_lt_neg hδε).trans_le (hθ t).1, (hθ t).2.trans_lt hδε⟩
  let m : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hfm : f m = x := by
    change j (δ * (2 * (1 / 2 : ℝ) - 1)) = x
    norm_num
    exact hj0
  refine ⟨range f, f 0, f 1, hfi.ne zero_ne_one,
    IsArcMap.isLineWithEnds ⟨f.continuous, hfi⟩, hsub, ⟨m, hfm⟩, ?_⟩
  rintro (he | he)
  · have hm := congrArg Subtype.val (hfi (hfm.trans he))
    norm_num [m] at hm
  · have hm := congrArg Subtype.val (hfi (hfm.trans he))
    norm_num [m] at hm

/-- A nonempty relatively open part of a cuff contains a closed line. -/
theorem exists_cuff_line_in_open
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C O : Set S} (hC : IsOArc C) (hO : IsOpen O) (hCO : (C ∩ O).Nonempty) :
    ∃ (L : Set S) (s t : S), s ≠ t ∧ IsLineWithEnds L s t ∧ L ⊆ C ∩ O := by
  obtain ⟨x, hxC, hxO⟩ := hCO
  obtain ⟨L, s, t, hst, hL, hsub, _⟩ := exists_cuff_line_around_point hC hO hxC hxO
  exact ⟨L, s, t, hst, hL, hsub⟩

/-- Cutting out a short cuff line inside an open region gives a cuff
interval containing every prescribed point outside that region. This is
the interval choice in Graph Minors VI (4.2), claim (2), page 126. -/
theorem exists_cuff_interval_cover_outside_open
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C O W : Set S} (hC : IsOArc C) (hO : IsOpen O)
    (hCO : (C ∩ O).Nonempty) (hWC : W ⊆ C) (hWO : Disjoint W O) :
    ∃ s ∈ C ∩ O, ∃ t ∈ C ∩ O, s ≠ t ∧
      ∃ A ∈ componentsIn (C \ {s, t}), W ⊆ A := by
  obtain ⟨L, s, t, hst, hL, hsub⟩ := exists_cuff_line_in_open hC hO hCO
  have hs : s ∈ L := hL.left_mem
  have ht : t ∈ L := hL.right_mem
  refine ⟨s, hsub hs, t, hsub ht, hst, C \ L,
    cuff_sdiff_line_mem_componentsIn hC hL (hsub.trans inter_subset_left), ?_⟩
  intro x hx
  exact ⟨hWC hx, fun hxL => disjoint_left.mp hWO hx (hsub hxL).2⟩

/-- The complementary interval can be chosen with its closure avoiding a
specified point of the open region. This lets that point serve as the cut
for the homotopy assertion in VI (4.2), claim (2). -/
theorem exists_cuff_interval_cover_avoiding_point
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C O W : Set S} (hC : IsOArc C) (hO : IsOpen O)
    {x : S} (hxC : x ∈ C) (hxO : x ∈ O)
    (hWC : W ⊆ C) (hWO : Disjoint W O) :
    ∃ s ∈ C ∩ O, ∃ t ∈ C ∩ O, s ≠ t ∧
      ∃ A ∈ componentsIn (C \ {s, t}), W ⊆ A ∧ x ∉ closure A ∧
        IsLineWithEnds (closure A) s t := by
  obtain ⟨L, s, t, hst, hL, hsub, hxL, hxends⟩ :=
    exists_cuff_line_around_point hC hO hxC hxO
  refine ⟨s, hsub hL.left_mem, t, hsub hL.right_mem, hst, C \ L,
    cuff_sdiff_line_mem_componentsIn hC hL (hsub.trans inter_subset_left), ?_, ?_,
    isLineWithEnds_closure_cuff_sdiff_line hC hL (hsub.trans inter_subset_left)⟩
  · intro w hw
    exact ⟨hWC hw, fun hwL => disjoint_left.mp hWO hw (hsub hwL).2⟩
  · intro hxcl
    exact hxends (closure_cuff_sdiff_line_inter_subset_ends hC hL
      (hsub.trans inter_subset_left) ⟨hxcl, hxL⟩)

end GraphMinor.GM06
