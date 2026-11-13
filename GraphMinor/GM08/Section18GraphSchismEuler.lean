module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18GraphArcEuler
import GraphMinor.GM08.Section18GraphLoopEuler
import GraphMinor.GM08.Section18GraphBranchEuler
import Lean.Elab.Tactic.Omega

/-!
# The graph contribution to the cut Euler characteristic

For every schism except a circle off the boundary, the number of cut
edges minus cut vertices plus old boundary contacts is one. For a
boundary-disjoint circle it is zero. These are the graph counts in the
case analysis of VIII (18.2), before counting the new cuffs.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

/-- The graph Euler change in VIII (18.2), page 286, for all six schism
types. A zero change occurs only for a boundary-disjoint circle; every
other case has change one. -/
theorem schism_graph_euler_jump {S : Type} [TopologicalSpace S] [T2Space S]
    {V : Set S} {E : Set (Set S)} (hg : IsGraph V E) (hF : GM07.IsSchism (gr V E)) :
    (IsOArc (gr V E) ∧ gr V E ∩ bd S = ∅ ∧
      (E.ncard : ℤ) - V.ncard + (gr V E ∩ bd S).ncard = 0) ∨
      (E.ncard : ℤ) - V.ncard + (gr V E ∩ bd S).ncard = 1 := by
  rcases hF with hi | hii | hiii | hiv | hv | hvi
  · have hχ := graph_euler_oArc hg hi.1
    by_cases hoff : gr V E ∩ bd S = ∅
    · refine Or.inl ⟨hi.1, hoff, ?_⟩
      rw [hoff, ncard_empty]
      omega
    · have hpos : 0 < (gr V E ∩ bd S).ncard :=
        (ncard_pos hi.2.2.1).mpr (nonempty_iff_ne_empty.mpr hoff)
      have hle := hi.2.2.2
      right
      omega
  · obtain ⟨u, v, huv, hbd, hline⟩ := hii.1
    have hχ := graph_euler_line hg huv hline
    right
    rw [hbd, ncard_pair huv]
    omega
  · obtain ⟨u, v, huv, hbd, hline⟩ := hiii.1
    have hχ := graph_euler_line hg huv hline
    right
    rw [hbd, ncard_pair huv]
    omega
  · have hχ : (V.ncard : ℤ) - E.ncard = -1 := by
      rcases hiv.1 with hbar | hwedge
      · exact graph_euler_x1 hg hbar
      · exact graph_euler_x2 hg hwedge
    right
    rw [hiv.2.1, ncard_empty]
    omega
  · have hχ := graph_euler_x3 hg hv.1
    right
    rw [hv.2.1, ncard_empty]
    omega
  · obtain ⟨w, A, P, C, D, u, hA, hP, huw, hPA, hF, _, _, _, _, _, hbd⟩ := hvi
    have hχ := graph_euler_x4 hg ⟨w, A, P, u, hA, hP, huw, hPA, hF⟩
    right
    rw [hbd, ncard_singleton]
    omega

end GraphMinor.GM08
