module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18CircleGraph
import GraphMinor.GM08.Section18GraphArcEuler
import GraphMinor.GM08.Section18GraphUnionEuler
import GraphMinor.Surface.CutLoop

/-!
# Euler sums of the theta and whiskered-circle shapes

A theta is a circle together with a line meeting it at both ends, so
its Euler sum is minus one. A whiskered circle adds a line at one end,
so its sum is zero. These are types (v) and (vi) in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- A theta graph has Euler sum minus one, the graph count for type (v)
in VIII (18.2), page 286. -/
theorem graph_euler_x3 {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) (hX : GM07.IsX3Arc (gr V E)) :
    (V.ncard : ℤ) - E.ncard = -1 := by
  obtain ⟨P, Q, R, u, v, huv, hP, hQ, hR, hPQ, hPR, hQR, hF⟩ := hX
  have hA : IsOArc (P ∪ Q) := oArc_of_lines hP hQ hPQ
  obtain ⟨VA, EA, hGA, _, hgrA, _⟩ :=
    exists_graph_oArc_with_finite_marks hA finite_empty (empty_subset _)
  have hχA := graph_euler_oArc hGA (hgrA.symm ▸ hA)
  obtain ⟨hGR, hgrR⟩ := isGraph_single_line huv hR
  have hχR := graph_euler_line hGR huv (hgrR.symm ▸ hR)
  have hmeet : (P ∪ Q) ∩ R = {u, v} := by
    rw [union_inter_distrib_right, hPR, hQR, union_self]
  have hfin : (gr VA EA ∩ gr {u, v} {R}).Finite := by
    rw [hgrA, hgrR, hmeet]
    exact (finite_singleton v).insert u
  have hχ := graph_euler_union hg hGA hGR (by rw [hF, hgrA, hgrR]) hfin
  rw [hχA, hχR, hgrA, hgrR, hmeet, ncard_pair huv] at hχ
  exact hχ

/-- A whiskered-circle graph has Euler sum zero, the graph count for
type (vi) in VIII (18.2), page 286. -/
theorem graph_euler_x4 {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) (hX : GM07.IsX4Arc (gr V E)) :
    (V.ncard : ℤ) - E.ncard = 0 := by
  obtain ⟨w, A, P, u, hA, hP, huw, hPA, hF⟩ := hX
  obtain ⟨VA, EA, hGA, _, hgrA, _⟩ :=
    exists_graph_oArc_with_finite_marks hA finite_empty (empty_subset _)
  have hχA := graph_euler_oArc hGA (hgrA.symm ▸ hA)
  obtain ⟨hGP, hgrP⟩ := isGraph_single_line huw hP
  have hχP := graph_euler_line hGP huw (hgrP.symm ▸ hP)
  have hmeet : A ∩ P = {u} := (inter_comm A P).trans hPA
  have hfin : (gr VA EA ∩ gr {u, w} {P}).Finite := by
    rw [hgrA, hgrP, hmeet]
    exact finite_singleton u
  have hχ := graph_euler_union hg hGA hGP (by rw [hF, hgrA, hgrP]) hfin
  rw [hχA, hχP, hgrA, hgrP, hmeet, ncard_singleton] at hχ
  exact hχ

end GraphMinor.GM08
