module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18CircleGraph
import GraphMinor.GM08.Section18GraphUnion
import GraphMinor.GM08.Section18GraphArcEuler
import GraphMinor.GM08.Section18GraphUnionEuler
import Lean.Elab.Tactic.Omega

/-!
# Euler sums of the two-loop schism shapes

Two circles meeting once have Euler sum minus one. Two disjoint circles
have sum zero, and adding their joining line lowers it to minus one.
Inclusion-exclusion makes these values independent of subdivision, as
needed for type (iv) in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

private theorem graph_on_circle {S : Type} [TopologicalSpace S] [T2Space S]
    {A : Set S} (hA : IsOArc A) :
    ∃ V E, IsGraph V E ∧ gr V E = A ∧ (V.ncard : ℤ) - E.ncard = 0 := by
  obtain ⟨V, E, hg, _, hgr, _⟩ := exists_graph_oArc_with_finite_marks hA finite_empty (empty_subset _)
  exact ⟨V, E, hg, hgr, graph_euler_oArc hg (hgr.symm ▸ hA)⟩

/-- A two-loop graph whose circles meet once has Euler sum minus one.
This is the `X₂` case of type (iv) in VIII (18.2), page 286. -/
theorem graph_euler_x2 {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) (hX : GM07.IsX2Arc (gr V E)) :
    (V.ncard : ℤ) - E.ncard = -1 := by
  obtain ⟨A, B, u, hA, hB, hAB, hF⟩ := hX
  obtain ⟨VA, EA, hGA, hgrA, hχA⟩ := graph_on_circle hA
  obtain ⟨VB, EB, hGB, hgrB, hχB⟩ := graph_on_circle hB
  have hfin : (gr VA EA ∩ gr VB EB).Finite := by rw [hgrA, hgrB, hAB]; exact finite_singleton u
  have hχ := graph_euler_union hg hGA hGB (by rw [hF, hgrA, hgrB]) hfin
  rw [hχA, hχB, hgrA, hgrB, hAB, ncard_singleton] at hχ
  exact hχ

/-- A barbell graph has Euler sum minus one. This is the `X₁` case of
type (iv) in VIII (18.2), page 286. -/
theorem graph_euler_x1 {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) (hX : GM07.IsX1Arc (gr V E)) :
    (V.ncard : ℤ) - E.ncard = -1 := by
  obtain ⟨A, B, P, u, v, hA, hB, hAB, hP, hu, hv, hPA, hPB, hF⟩ := hX
  obtain ⟨VA, EA, hGA, hgrA, hχA⟩ := graph_on_circle hA
  obtain ⟨VB, EB, hGB, hgrB, hχB⟩ := graph_on_circle hB
  have hABempty : A ∩ B = ∅ := disjoint_iff_inter_eq_empty.mp hAB
  have hinter : gr VA EA ∩ gr VB EB ⊆ VA ∩ VB := by
    rw [hgrA, hgrB, hABempty]
    exact empty_subset _
  have hGAB := isGraph_union_of_inter_subset_vertices hGA hGB hinter
  have hgrAB : gr (VA ∪ VB) (EA ∪ EB) = A ∪ B := by
    have hh : gr (VA ∪ VB) (EA ∪ EB) = gr VA EA ∪ gr VB EB := by
      simp only [gr, sUnion_union]
      ac_rfl
    rw [hh, hgrA, hgrB]
  have hχAB : ((VA ∪ VB).ncard : ℤ) - (EA ∪ EB).ncard = 0 := by
    have hfin : (gr VA EA ∩ gr VB EB).Finite := by rw [hgrA, hgrB, hABempty]; exact finite_empty
    have hh := graph_euler_union hGAB hGA hGB (by rw [hgrAB, hgrA, hgrB]) hfin
    rw [hχA, hχB, hgrA, hgrB, hABempty, ncard_empty] at hh
    exact hh
  have huv : u ≠ v := fun heq => disjoint_left.mp hAB hu (heq ▸ hv)
  obtain ⟨hGP, hgrP⟩ := isGraph_single_line huv hP
  have hχP := graph_euler_line hGP huv (hgrP.symm ▸ hP)
  have hmeet : (A ∪ B) ∩ P = {u, v} := by
    rw [union_inter_distrib_right, inter_comm A P, inter_comm B P, hPA, hPB]
    ext x
    simp only [mem_union, mem_singleton_iff, mem_insert_iff]
  have hfin : (gr (VA ∪ VB) (EA ∪ EB) ∩ gr {u, v} {P}).Finite := by
    rw [hgrAB, hgrP, hmeet]
    exact (finite_singleton v).insert u
  have hχ := graph_euler_union hg hGAB hGP (by rw [hF, hgrAB, hgrP]) hfin
  rw [hχAB, hχP, hgrAB, hgrP, hmeet, ncard_pair huv] at hχ
  exact hχ

end GraphMinor.GM08
