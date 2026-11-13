module

public import GraphMinor.Compute.GM06Alg34DualEndsLoop
public import GraphMinor.Compute.GM06Alg34DualData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# The complete endpoint section of a computed dual

Start the edge scan at zero with the supplied edge count. Each edge
keeps its original slot in the dual endpoint list. The exact finite
output agrees with the endpoint section of the assembled dual drawing.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Write the dual endpoint pair for every supplied primal edge. -/
def gm06DualEndsProg : Cmd :=
  .seq (.assign 7701 (.const 0))
    (.seq (.assign 7702 (.reg 101)) gm06DualEndsLoopProg)

/-- The canonical complete edge scan is exactly the endpoint section
of the assembled finite dual. -/
theorem gm06DualEndpointWords_eq (x : GM06DrawingData) (hR : 0 < x.regions.length)
    (L : List (Fin x.n)) (g : Fin L.length → Fin x.regions.length) :
    gm06DualEndpointWords x hR (List.finRange x.ends.length) =
      (x.dualData L hR g).endpointWords := by
  simp only [gm06DualEndpointWords, GM06DrawingData.endpointWords,
    GM06DrawingData.dualData, GM06DrawingData.raw, GM06DrawingData.dualEndsOfNonempty,
    List.flatMap_map]

/-- The complete endpoint serializer appends all supplied-edge dual
pairs, retaining the old payload prefix and the outer memory frame. -/
theorem gm06DualEndsProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (hR : 0 < x.regions.length) {pre : List ℕ} {s : State}
    (hw : 2 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hspan : x.regions.length + 2 < 2 ^ w)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hstride : s.regs 170 = x.cellCount)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hsource : s.arrs 52 = List.range x.regions.length)
    (hbuf : IsBuf 55 7804 pre cap s) (hcap : 2 * x.ends.length ≤ cap)
    (hfit : pre.length + 2 * x.ends.length < 2 ^ w) :
    ∃ s' t, Exec w gm06DualEndsProg s s' t ∧
      t ≤ (100 * (x.regions.length + 1) + 37) * x.ends.length + 5 ∧
      IsBuf 55 7804 (pre ++ gm06DualEndpointWords x hR (List.finRange x.ends.length))
        (cap - 2 * x.ends.length) s' ∧
      (∀ A : ℕ, A ≠ 54 → A ≠ 55 → s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r < 7600 ∨ 7702 < r → r ≠ 7804 → s'.regs r = s.regs r) := by
  have hmw : x.ends.length < 2 ^ w := by
    have hh : x.ends.length ≤ x.cellCount := by dsimp only [GM06DrawingData.cellCount]; omega
    exact hh.trans_lt hN
  let s₁ := s.setReg 7701 0
  let s₂ := s₁.setReg 7702 x.ends.length
  have he₁ : Exec w (.assign 7701 (.const 0)) s s₁ 2 :=
    .assign (eval_const (Nat.zero_lt_of_lt hw))
  have he₂ : Exec w (.assign 7702 (.reg 101)) s₁ s₂ 2 := .assign (eval_reg hm hmw)
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, _, _, ha₃, hg₃⟩ :=
    gm06DualEndsLoopProg_exec (s := s₂) x hR (List.finRange x.ends.length)
      (i := 0) (by simp [List.range_eq_range']) (by simp)
      hw hN hsquare hspan hmat hstride hn hm hsource
      (by simp [s₂, s₁]) (by simp [s₂])
      (by simpa [IsBuf, s₂, s₁] using hbuf)
      (by simpa only [List.length_finRange] using hcap)
      (by simpa only [List.length_finRange] using hfit)
  refine ⟨s₃, 2 + (2 + t₃), .seq he₁ (.seq he₂ he₃),
    by simp only [List.length_finRange] at ht₃; omega,
    by simpa only [List.length_finRange] using hb₃, ha₃, ?_⟩
  intro r hr h7804
  have h1 : r ≠ 7701 := by omega
  have h2 : r ≠ 7702 := by omega
  exact (hg₃ r hr h7804).trans (by simp [s₂, s₁, State.setReg, h1, h2])

end GraphMinor.Compute
