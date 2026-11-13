module

public import GraphMinor.Compute.GM06Alg34DualSelect
public import GraphMinor.Compute.GM06Alg34DualGapClassWords
public import GraphMinor.Compute.GM06Alg34DualGapRowLoop

/-!
# Selecting a dual division block from its computed relation row

The row in array 43 marks the class of one gap. Scan every supplied
gap index and copy its supplied region label from array 47 exactly
when that mark is set. The resulting padded buffer is the finite dual
division block, with its exact live length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Select one class row and map positions to supplied region words. -/
def gm06DualGapClassSelectProg : Cmd :=
  gm06DualSelectProg 53 (.read 43 (.reg 7603)) (.read 47 (.reg 7603))

/-- A prepared class row yields exactly the corresponding finite dual
block in linear time, preserving the row and supplied gap labels. -/
theorem gm06DualGapClassSelectProg_exec {w : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (g : Fin L.length → Fin x.regions.length) (i : Fin L.length)
    {s : State} (hw : 1 < 2 ^ w) (hspan : L.length + 2 < 2 ^ w)
    (hrw : x.regions.length < 2 ^ w) (hrow : s.arrs 43 = gm06GapRow x L i)
    (hregions : s.arrs 47 = List.ofFn (fun j => (g j).val))
    (hsource : s.arrs 53 = List.range L.length) :
    ∃ s' t, Exec w gm06DualGapClassSelectProg s s' t ∧ t ≤ 100 * (L.length + 1) ∧
      s'.arrs 54 = gm06DualGapClassWords x L g i ++
        List.replicate (L.length - (gm06DualGapClassWords x L g i).length) 0 ∧
      s'.regs 7604 = (gm06DualGapClassWords x L g i).length ∧
      (∀ A : ℕ, A ≠ 54 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7601 ∨ 7605 < r → s'.regs r = s.regs r) := by
  have hkw : L.length < 2 ^ w := by omega
  have hwords : ∀ y ∈ List.range L.length, y < 2 ^ w :=
    fun y hy => (List.mem_range.mp hy).trans hkw
  obtain ⟨s', t, he, ht, hb, hc, ha, hr⟩ := gm06DualSelectProg_exec
    (.read 43 (.reg 7603)) (.read 47 (.reg 7603)) (gm06DualGapClassKeep x L i) (gm06DualGapLabel g)
    (by decide : 53 ≠ 54) hw hsource (by simpa only [List.length_range] using hspan) hwords
    (fun z y hy ha _ hry => by
      have hyk : y < L.length := List.mem_range.mp hy
      have hzrow : z.arrs 43 = gm06GapRow x L i := (ha 43 (by decide)).trans hrow
      cases hh : x.dualGapRelated L i ⟨y, hyk⟩ <;>
        simp [Expr.eval, checkWord, hry, hwords y hy, hzrow, gm06GapRow, hyk,
          gm06DualGapClassKeep, hh, hw, Nat.zero_lt_of_lt hw])
    (fun z y hy _ ha _ hry => by
      have hyk : y < L.length := List.mem_range.mp hy
      have hzreg : z.arrs 47 = List.ofFn (fun j => (g j).val) := (ha 47 (by decide)).trans hregions
      have hgw := (g ⟨y, hyk⟩).isLt.trans hrw
      simp [Expr.eval, checkWord, hry, hwords y hy, hzreg, hyk, gm06DualGapLabel, hgw])
  simp only [List.length_range, Expr.cost] at ht
  refine ⟨s', t, he, by omega, ?_, ?_, ha, hr⟩
  · simpa only [gm06DualGapClassWords_scan, List.length_range] using hb
  · simpa only [gm06DualGapClassWords_scan] using hc

end GraphMinor.Compute
