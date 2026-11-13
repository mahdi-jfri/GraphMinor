module

public import GraphMinor.GM06.Alg34GapDisc
public import GraphMinor.Compute.GM06Alg34GapDiscLayout
import GraphMinor.Compute.GM06Alg34DiscRep

/-!
# Every represented disc has matching cuff and gap lists

The disc has one cuff, and the augmented representation has one gap
group for that cuff. The gap region function's finite domain proves
that the two supplied lists have the same length. Thus the finite
layout required by the RAM deletion phases follows from the input
interpretation, including for an empty cuff list.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- Every augmented input representing a disc has the matching finite
single-cuff layout required by the internal gap array. -/
theorem disc_layout (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S) :
    ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length := by
  obtain ⟨L, hL⟩ := h.drawing.exists_cuff_list hS
  obtain ⟨R, hR⟩ := h.disc_gapRegions_singleton hS
  let c : Fin X.drawing.cuffs.length := ⟨0, by rw [hL]; simp only [List.length_cons, List.length_nil]; omega⟩
  have hh := congrArg List.length (h.gap c).region_list
  simp only [List.length_ofFn, Fin.getElem_fin, c, hL, hR, List.getElem_cons_zero] at hh
  exact ⟨L, R, hL, hR, hh.symm⟩

end GraphMinor.Compute.GM06GapInputRep
