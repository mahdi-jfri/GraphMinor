module

public import GraphMinor.Compute.GM06Alg34DualRegionsLoop
public import GraphMinor.Compute.GM06Alg34DualData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# The complete dual region section

Initialize the old vertex scan with the supplied vertex count. Its
records are exactly the region section of the finite dual drawing,
since dual regions keep the old vertex order and transpose the two
supplied incidence lists.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Emit every transposed dual region in old vertex order. -/
def gm06DualRegionsProg : Cmd :=
  .seq (.assign 7701 (.const 0))
    (.seq (.assign 7702 (.reg 100)) gm06DualRegionsLoopProg)

private theorem regionWords_flatMap (rs : List (List ℕ × List ℕ)) :
    gm06RegionWords rs = rs.flatMap (fun r =>
      GM06DrawingData.listWords r.1 ++ GM06DrawingData.listWords r.2) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [gm06RegionWords, List.flatMap_cons, ih]

/-- The complete transposed record list is exactly the finite dual region section. -/
theorem gm06DualRegionWords_eq (x : GM06DrawingData) (hR : 0 < x.regions.length)
    (L : List (Fin x.n)) (g : Fin L.length → Fin x.regions.length) :
    gm06DualRegionWords x (List.finRange x.n) = (x.dualData L hR g).regionWords := by
  simp only [gm06DualRegionWords, gm06DualRegionRecordWords, GM06DrawingData.regionWords,
    GM06DrawingData.raw, GM06DrawingData.dualData, regionWords_flatMap,
    List.ofFn_eq_map, List.flatMap_map, GM06DrawingData.dualRegionBoundary,
    List.map_map, Function.comp_def, Fin.val_cast]
  apply congrArg (fun f : Fin x.n → List ℕ => (List.finRange x.n).flatMap f)
  funext a
  rfl

/-- The complete region serializer appends precisely the transposed
finite dual region records and preserves the outer memory frame. -/
theorem gm06DualRegionsProg_exec {w cap : ℕ} (x : GM06DrawingData)
    {pre : List ℕ} {s : State} (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hRspan : x.regions.length + 2 < 2 ^ w) (hEspan : x.ends.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hregions : s.arrs 52 = List.range x.regions.length) (hedges : s.arrs 51 = List.range x.ends.length)
    (hbuf : IsPrefixBuffer 55 pre ((gm06DualRegionWords x (List.finRange x.n)).length + cap) s)
    (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + (gm06DualRegionWords x (List.finRange x.n)).length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualRegionsProg s s' t ∧
      t ≤ (200 * (x.regions.length + x.ends.length + 2) + 13) * x.n + 5 ∧
      IsPrefixBuffer 55 (pre ++ gm06DualRegionWords x (List.finRange x.n)) cap s' ∧
      s'.regs 7804 = (pre ++ gm06DualRegionWords x (List.finRange x.n)).length ∧
      (∀ A : ℕ, A ≠ 54 → A ≠ 55 → A ≠ 56 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7600 → s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by
    have hh : x.n ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
    exact hh.trans_lt hN
  let s₁ := s.setReg 7701 0
  let s₂ := s₁.setReg 7702 x.n
  have he₁ : Exec w (.assign 7701 (.const 0)) s s₁ 2 := .assign (eval_const (Nat.zero_lt_of_lt hw))
  have he₂ : Exec w (.assign 7702 (.reg 100)) s₁ s₂ 2 := .assign (eval_reg hn hnw)
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, _, _, ha₃, hg₃⟩ :=
    gm06DualRegionsLoopProg_exec (s := s₂) x (List.finRange x.n)
      (i := 0) (by simp [List.range_eq_range']) (by simp) hw hN hsquare hRspan hEspan
      hmat hstride hn hm hregions hedges (by simp [s₂, s₁]) (by simp [s₂])
      (hbuf.of_arr_eq rfl) (by simpa [s₂, s₁] using hpos) hfit
  refine ⟨s₃, 2 + (2 + t₃), .seq he₁ (.seq he₂ he₃),
    by simp only [List.length_finRange] at ht₃; omega, hb₃, hp₃, ha₃, ?_⟩
  intro r hr
  exact (hg₃ r hr).trans (by simp [s₂, s₁, State.setReg,
    show r ≠ 7701 by omega, show r ≠ 7702 by omega])

end GraphMinor.Compute
