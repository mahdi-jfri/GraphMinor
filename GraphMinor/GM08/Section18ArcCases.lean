module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18CutArc
import GraphMinor.GM08.Section18SameCuffCut
import GraphMinor.GM07.CuffCollar

/-!
# The two proper arc types of a schism

The schism definition describes ends using the set `lineEnds`. The proper
arc cut lemmas use named endpoints. The ends of a line are precisely those
two endpoints, so the printed conditions for types (ii) and (iii) give the
hypotheses of the two cut lemmas. Both proper arc types therefore decrease
the surface measure in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- The exact type (ii) conditions from VIII Section 18, page 285, imply
the cut decrease in (18.2), page 286. -/
theorem exists_cut_complexity_lt_of_schism_type_ii {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsProperIArc F) {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S)
    (hCD : C ≠ D) (hmC : (lineEnds F ∩ C).Nonempty) (hmD : (lineEnds F ∩ D).Nonempty) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsCutting ψ F ∧ surfaceComplexity T < surfaceComplexity S := by
  have : T2Space S := hS.2.1
  obtain ⟨u, v, _, hbd, hline⟩ := hF
  obtain ⟨x, hx, hxC⟩ := hmC
  obtain ⟨y, hy, hyD⟩ := hmD
  have hxy : x ≠ y := fun he => disjoint_left.mp (cuffs_disjoint hC hD hCD) hxC (he.symm ▸ hyD)
  rcases GM07.lineEnds_subset hline hx with rfl | rfl
  · rcases GM07.lineEnds_subset hline hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact exists_cut_complexity_lt_of_distinct_cuffs hS hC hD hCD hxC hyD hline hbd
  · rcases GM07.lineEnds_subset hline hy with rfl | rfl
    · exact exists_cut_complexity_lt_of_distinct_cuffs hS hD hC hCD.symm hyD hxC hline hbd
    · exact (hxy rfl).elim

/-- The exact type (iii) conditions from VIII Section 18, page 285, imply
the cut decrease in (18.2), page 286. -/
theorem exists_cut_complexity_lt_of_schism_type_iii {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S) {F C : Set S}
    (hF : IsProperIArc F) (hC : C ∈ cuffs S) (hends : lineEnds F ⊆ C)
    (hnp : ¬ GM07.IsNearPlanar (F ∪ C)) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsCutting ψ F ∧ surfaceComplexity T < surfaceComplexity S := by
  obtain ⟨u, v, hne, hbd, hline⟩ := hF
  exact exists_cut_complexity_lt_of_same_cuff_arc hS hC
    (hends ⟨v, hline⟩) (hends ⟨u, hline.symm⟩) hne hline hbd hnp

end GraphMinor.GM08
