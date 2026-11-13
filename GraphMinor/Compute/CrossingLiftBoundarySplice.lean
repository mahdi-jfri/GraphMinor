module

public import GraphMinor.Compute.CrossingLiftSplice
public import GraphMinor.Compute.CrossingLiftCutEnds
import GraphMinor.Compute.CrossingLiftReplacementMath

/-!
# Splicing the reverse-search path at the boundary cuts

The first cut and the cut just after the last boundary visit delimit the segment replaced
in Lemma 1. The general slice-splice program writes exactly `spliceBetween` at those cuts.
Its work is bounded by the old path and the returned search path lengths.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- The existing splice program at the computed boundary cuts writes Lemma 1's splice.
The assumptions describe the stored path, patch and cuts, the boundary visits, distinct
output memory and word bounds. -/
theorem liftSpliceProg_exec_boundary {w N : ℕ} (src patch dst r_lo r_hi R : ℕ)
    (hsd : src ≠ dst) (hpd : patch ≠ dst) (hloR : r_lo < R) (hhiR : r_hi < R)
    (B L Y : List (Fin N)) (S : Finset (Fin N)) (hB : ∀ x, x ∈ B ↔ x ∈ S)
    (p q : Fin N) (hp : firstIn S L = some p) (hq : lastIn S L = some q)
    (s : State) (hs : s.arrs src = L.map Fin.val) (hy : s.arrs patch = Y.map Fin.val)
    (hlo : s.regs r_lo = liftFirstBoundaryIndex B L)
    (hhi : s.regs r_hi = liftAfterLastBoundaryIndex B L)
    (hw : 16 * (N + L.length + Y.length + 1) < 2 ^ w) :
    ∃ s' t, Exec w (liftSpliceProg src patch dst r_lo r_hi R) s s' t ∧
      t ≤ 21 * (L.length + Y.length) + 53 ∧
      s'.arrs dst = (spliceBetween S L Y).map Fin.val ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧ (∀ k < R, s'.regs k = s.regs k) := by
  let f := liftFirstBoundaryIndex B L
  let a := liftAfterLastBoundaryIndex B L
  have hfL : f ≤ L.length := (liftBoundaryIndices_le_length B L).1
  have haL : a ≤ L.length := (liftBoundaryIndices_le_length B L).2
  obtain ⟨_, ha0, _, hqpos⟩ := liftBoundaryCuts_endpoints B L S hB p q hp hq
  have hqB : q ∈ B := (hB q).mpr (liftBoundaryEnds_mem hp hq).2
  have haidx : a - 1 < L.length := by dsimp [a] at *; omega
  have hqget : L[a - 1] = q := (List.getElem?_eq_some_iff.mp hqpos).2
  have hfirst : f ≤ a - 1 := liftFirstBoundaryIndex_le_of_mem B L haidx (hqget.symm ▸ hqB)
  have hfa : f ≤ a := by omega
  let A := L.take f
  let X := (L.drop f).take (a - f)
  let C := L.drop a
  have hsplit : A ++ X ++ C = L := by
    dsimp [A, X, C]
    rw [← List.take_add]
    have heq : f + (a - f) = a := by omega
    rw [heq, List.take_append_drop]
  have hAl : A.length = f := List.length_take_of_le hfL
  have hXl : X.length = a - f := by
    dsimp [X]
    rw [List.length_take, List.length_drop, min_eq_left (by omega)]
  have hCl : C.length = L.length - a := List.length_drop
  have hwords : ∀ x ∈ A.map Fin.val ++ Y.map Fin.val ++ C.map Fin.val, x < 2 ^ w := by
    intro x hx
    have hx' : x ∈ (A ++ Y ++ C).map Fin.val := by simpa only [List.map_append] using hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hx'
    exact v.isLt.trans (by omega)
  obtain ⟨s', t, hex, ht, ho, ha, hr⟩ := liftSpliceProg_exec (w := w)
    src patch dst r_lo r_hi R hsd hpd hloR hhiR
    (A.map Fin.val) (X.map Fin.val) (Y.map Fin.val) (C.map Fin.val) s
    (by rw [← List.map_append, ← List.map_append, hsplit]; exact hs) hy
    (by simpa only [List.length_map, hAl] using hlo)
    (by simpa only [List.length_map, hAl, hXl, Nat.add_sub_of_le hfa] using hhi)
    hwords (by simp only [List.length_map, hAl, hXl, hCl]; omega)
  refine ⟨s', t, hex, ?_, ?_, ha, hr⟩
  · simp only [List.length_map, hAl, hCl] at ht; omega
  · rw [← List.map_append, ← List.map_append] at ho
    exact ho.trans (congrArg (List.map Fin.val) (liftBoundaryCuts_spliceBetween B L Y S hB))

end GraphMinor.Compute.Crossing
