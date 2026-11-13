module

public import GraphMinor.GM08.Section18Complexity
import GraphMinor.Surface.CutIArc

/-!
# Cutting an arc between distinct cuffs

For schisms of type (ii) in VIII Section 18, cutting joins two cuffs and
leaves the handle and crosscap counts fixed. The proved arc-cut theorem
therefore gives a drop of one in the measure `4a + 2b + c`. This is the
corresponding case of VIII (18.2), page 286.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

private theorem component_eq_cuff_of_mem {S : Type w} [TopologicalSpace S]
    {C : Set S} (hC : C ∈ cuffs S) {x : S} (hx : x ∈ C) :
    connectedComponentIn (bd S) x = C := by
  obtain ⟨y, hy, rfl⟩ := hC
  exact (connectedComponentIn_eq hx).symm

/-- The distinct-cuff arc case of VIII (18.2), page 286: there is a cut
surface with strictly smaller measure. The arc-cut construction preserves
handles and crosscaps and removes one cuff. -/
theorem exists_cut_complexity_lt_of_distinct_cuffs {S : Type w} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {F C D : Set S} {u v : S}
    (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    (hu : u ∈ C) (hv : v ∈ D) (hF : IsLineWithEnds F u v)
    (hbd : F ∩ bd S = {u, v}) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsCutting ψ F ∧ surfaceComplexity T < surfaceComplexity S := by
  have huv : u ≠ v := fun heq => disjoint_left.mp (cuffs_disjoint hC hD hCD) hu (heq ▸ hv)
  obtain ⟨T, tT, ψ, hT, hcut, hdiff, _, _⟩ := cutIArc S F u v hS inferInstance huv hbd hF
  let := tT
  have hneq : connectedComponentIn (bd S) u ≠ connectedComponentIn (bd S) v := by
    rw [component_eq_cuff_of_mem hC hu, component_eq_cuff_of_mem hD hv]
    exact hCD
  obtain ⟨hconn, a, b, c, hmodelS, hmodelT⟩ := hdiff hneq
  let := hconn
  refine ⟨T, tT, ψ, hT, hcut, ?_⟩
  rw [surfaceComplexity_eq_connected (S := T), surfaceComplexity_eq_connected (S := S),
    connectedSurfaceComplexity_eq hmodelT, connectedSurfaceComplexity_eq hmodelS]
  omega

end GraphMinor.GM08
