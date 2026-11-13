module

public import GraphMinor.GM06.Alg34GapInputRep
public import GraphMinor.Compute.GM06Alg34GapInputWords
public import GraphMinor.Compute.GM06Alg34Array

/-!
# Feasibility is determined by the augmented array

Reading the base section recovers the supplied graph and division.
The existing array-determination theorem therefore applies to the
augmented input. The gap representation also proves the numeric list
lengths and direct label reads needed by its RAM parser.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06

universe u v

/-- Each gap incidence list has exactly one label per supplied cuff position. -/
theorem GM06CuffGapRep.region_length {x : GM06DrawingData} {S : Type u}
    [TopologicalSpace S] {G : Drawing S} {Δ : Set (Set S)}
    {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
    {R : List (Fin x.regions.length)} (hg : GM06CuffGapRep h c R) :
    R.length = x.cuffs[c].length := by
  rw [← hg.region_list, List.length_ofFn]

/-- A supplied gap label is read directly from its finite incidence list. -/
theorem GM06CuffGapRep.region_get {x : GM06DrawingData} {S : Type u}
    [TopologicalSpace S] {G : Drawing S} {Δ : Set (Set S)}
    {h : GM06DrawingRep x G Δ} {c : Fin x.cuffs.length}
    {R : List (Fin x.regions.length)} (hg : GM06CuffGapRep h c R)
    (i : Fin x.cuffs[c].length) :
    R[i.val]'(by rw [hg.region_length]; exact i.isLt) = hg.region i := by
  simp only [← hg.region_list, List.getElem_ofFn]

/-- The augmented array describes a drawing, its division, and its plain
cuff gap region incidence through representation bijections and cyclic orders. -/
@[expose] def GM06GapRepresentsArray (w : List ℕ) {S : Type u} [TopologicalSpace S]
    (G : Drawing S) (Δ : Set (Set S)) : Prop :=
  ∃ x : GM06GapInput, x.words = w ∧ Nonempty (GM06GapInputRep x G Δ)

/-- Two instances represented by the same augmented array have the same
feasibility answer. No gap label or program output is selected from a proof. -/
theorem GM06GapRepresentsArray.feasible_iff {w : List ℕ} {S : Type u} {T : Type v}
    [TopologicalSpace S] [TopologicalSpace T] {G : Drawing S} {H : Drawing T}
    {Δ : Set (Set S)} {Ε : Set (Set T)}
    (hG : GM06GapRepresentsArray w G Δ) (hH : GM06GapRepresentsArray w H Ε)
    (hΔ : IsDivision Δ) (hΕ : IsDivision Ε) :
    IsFeasible G.toGraph Δ ↔ IsFeasible H.toGraph Ε := by
  obtain ⟨x, hx, ⟨hG⟩⟩ := hG
  obtain ⟨y, hy, ⟨hH⟩⟩ := hH
  have hd := GM06GapInput.drawing_eq_of_words_eq (hx.trans hy.symm)
  exact hG.drawing.feasible_iff_of_same_words hH.drawing
    (congrArg GM06DrawingData.words hd) hΔ hΕ

end GraphMinor.Compute
