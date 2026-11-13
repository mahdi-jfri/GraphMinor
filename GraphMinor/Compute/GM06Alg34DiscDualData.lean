module

public import GraphMinor.Compute.GM06Alg34DualGapInput
import GraphMinor.Compute.GM06Alg34GapPositionCast

/-!
# The plain finite dual operation on augmented disc inputs

Read the first supplied cuff and gap lists. When their lengths match
and the supplied region range is nonempty, use list lookup to compute
the augmented dual. The checks and every output label are finite
operations on the input data. No geometric interpretation is queried.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06GapInput

/-- The finite dual update, using only supplied cuff and gap-region lists.
Malformed list layouts retain their original finite data. -/
def discDualFromLists (X : GM06GapInput) (L : List (Fin X.drawing.n))
    (R : List (Fin X.drawing.regions.length)) : GM06GapInput :=
  if hR : 0 < X.drawing.regions.length then
    if hlen : R.length = L.length then
      X.drawing.dualGapInput L hR (fun i => R.get (Fin.cast hlen.symm i))
    else X
  else X

/-- Read the supplied first cuff and gap lists to form the finite dual. -/
def discDualData (X : GM06GapInput) : GM06GapInput :=
  X.discDualFromLists (X.drawing.cuffs.headD []) (X.gapRegions.headD [])

/-- On matching supplied disc lists, the finite update is the explicitly
labelled augmented dual. -/
theorem discDualData_eq (X : GM06GapInput) (L : List (Fin X.drawing.n))
    (R : List (Fin X.drawing.regions.length)) (hL : X.drawing.cuffs = [L])
    (hgroups : X.gapRegions = [R]) (hR : 0 < X.drawing.regions.length)
    (hlen : R.length = L.length) (g : Fin L.length → Fin X.drawing.regions.length)
    (hg : List.ofFn g = R) : X.discDualData = X.drawing.dualGapInput L hR g := by
  let f : Fin L.length → Fin X.drawing.regions.length := fun i => R.get (Fin.cast hlen.symm i)
  have hf : List.ofFn f = R := (gm06OfFn_cast hlen.symm R.get).trans (List.ofFn_get R)
  have hfg : f = g := List.ofFn_injective (hf.trans hg.symm)
  have hl : X.drawing.cuffs.headD [] = L := congrArg (fun ls => ls.headD []) hL
  have hr : X.gapRegions.headD [] = R := congrArg (fun ls => ls.headD []) hgroups
  rw [discDualData, hl, hr]
  simp only [discDualFromLists, dite_eq_left hR, dite_eq_left hlen]
  exact congrArg (X.drawing.dualGapInput L hR) hfg

/-- The finite disc dual update again has matching single cuff and gap lists. -/
theorem discDualData_disc_layout (X : GM06GapInput)
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length)
    (hR : 0 < X.drawing.regions.length) :
    ∃ L' R', X.discDualData.drawing.cuffs = [L'] ∧
      X.discDualData.gapRegions = [R'] ∧ R'.length = L'.length := by
  obtain ⟨L, R, hL, hgroups, hlen⟩ := hshape
  let g : Fin L.length → Fin X.drawing.regions.length := fun i => R.get (Fin.cast hlen.symm i)
  have hg : List.ofFn g = R := (gm06OfFn_cast hlen.symm R.get).trans (List.ofFn_get R)
  rw [X.discDualData_eq L R hL hgroups hR hlen g hg]
  exact X.drawing.dualGapInput_disc_layout L hR g

end GraphMinor.Compute.GM06GapInput
