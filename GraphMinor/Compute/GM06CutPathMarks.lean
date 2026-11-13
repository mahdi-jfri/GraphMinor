module

public import GraphMinor.Compute.GM06CutTables
public import GraphMinor.Compute.GM06FaceSuccessors

/-!
# Computing incoming and outgoing linkage ends on the RAM

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) locates both
path ends at every linkage vertex. Scan a supplied path row. For each dart,
store its label plus one at its origin and store its reverse plus one
at the reverse's origin. Zero then means no corresponding path end.
The invariant is the exact fold of these two independent table writes.
The row program reads only darts and original endpoint labels.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- One paired path-end update: incoming reverse first, outgoing dart second. -/
def gm06CutPathMarkStep (origins : List ℕ) (tables : List ℕ × List ℕ) (d : ℕ) : List ℕ × List ℕ :=
  let mate := gm06DartMate d
  (tables.1.set (origins[mate]?.getD 0) (mate + 1),
    tables.2.set (origins[d]?.getD 0) (d + 1))

/-- Exact pure path-marking fold for one row. -/
def gm06CutPathMarkScan (origins row incoming outgoing : List ℕ) : List ℕ × List ℕ :=
  row.foldl (gm06CutPathMarkStep origins) (incoming, outgoing)

/-- Both endpoint tables retain their original sizes during the scan. -/
theorem gm06CutPathMarkScan_lengths (origins row incoming outgoing : List ℕ) :
    (gm06CutPathMarkScan origins row incoming outgoing).1.length = incoming.length ∧
    (gm06CutPathMarkScan origins row incoming outgoing).2.length = outgoing.length := by
  induction row generalizing incoming outgoing with
  | nil => exact ⟨rfl, rfl⟩
  | cons d ds ih =>
    simpa only [gm06CutPathMarkScan, List.foldl_cons, gm06CutPathMarkStep,
      List.length_set] using ih
        (incoming.set (origins[gm06DartMate d]?.getD 0) (gm06DartMate d + 1))
        (outgoing.set (origins[d]?.getD 0) (d + 1))

/-- The two folds are exactly the input-derived predecessor and successor writes. -/
theorem gm06CutPathMarkScan_eq_scatter (origins row incoming outgoing : List ℕ) :
    gm06CutPathMarkScan origins row incoming outgoing =
      (gm06Scatter (gm06CutPathEndPairs origins row true) incoming,
        gm06Scatter (gm06CutPathEndPairs origins row false) outgoing) := by
  induction row generalizing incoming outgoing with
  | nil => rfl
  | cons d ds ih =>
    simpa only [gm06CutPathMarkScan, List.foldl_cons, gm06CutPathMarkStep,
      gm06CutPathEndPairs, List.map_cons, Bool.false_eq_true, ↓reduceIte, gm06Scatter] using ih
        (incoming.set (origins[gm06DartMate d]?.getD 0) (gm06DartMate d + 1))
        (outgoing.set (origins[d]?.getD 0) (d + 1))

/-- One RAM path-end step. Original origins are in 601, path darts
in 611, incoming marks in 620 and outgoing marks in 621. -/
def gm06CutPathMarkBody : Cmd :=
  .seq (.assign 651 (.read 611 (.reg 650)))
    (.seq (.assign 652 (gm06DartMateExpr (.reg 651)))
      (.seq (.write 621 (.read 601 (.reg 651)) (.op .add (.reg 651) (.const 1)))
        (.write 620 (.read 601 (.reg 652)) (.op .add (.reg 652) (.const 1)))))

/-- Mark the ends of every dart in the current path row. -/
def gm06CutPathMarkRowProg : Cmd :=
  .seq (.assign 650 (.const 0)) (forUp 650 (.len 611) gm06CutPathMarkBody)

/-- The row program computes both exact endpoint-table folds in
linear time. No membership or path-position table is supplied. -/
theorem gm06CutPathMarkRowProg_exec {w n m : ℕ}
    (origins row incoming outgoing : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hl : row.length < 2 ^ w) (horig : origins.length = 2 * m)
    (hin : incoming.length = n) (hout : outgoing.length = n)
    (hd : ∀ d ∈ row, d < 2 * m) (hv : ∀ v ∈ origins, v < n)
    (h601 : s.arrs 601 = origins) (h611 : s.arrs 611 = row)
    (h620 : s.arrs 620 = incoming) (h621 : s.arrs 621 = outgoing) :
    ∃ sf t, Exec w gm06CutPathMarkRowProg s sf t ∧
      t ≤ 5 + 34 * row.length ∧ Keeps [650, 651, 652] [620, 621] s sf ∧
      sf.arrs 620 = gm06Scatter (gm06CutPathEndPairs origins row true) incoming ∧
      sf.arrs 621 = gm06Scatter (gm06CutPathEndPairs origins row false) outgoing := by
  have hw1 : 1 < 2 ^ w := by omega
  let scan := fun i => gm06CutPathMarkScan origins (row.take i) incoming outgoing
  let Inv := fun i st => st.regs 650 = i ∧ Keeps [650, 651, 652] [620, 621] s st ∧
    st.arrs 620 = (scan i).1 ∧ st.arrs 621 = (scan i).2
  let s₀ := s.setReg 650 0
  have hI₀ : Inv 0 s₀ := ⟨by simp [s₀], (Keeps.refl _ _ s).setReg (by simp) _, h620, h621⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 650) (hi := .len 611) (body := gm06CutPathMarkBody) Inv row.length 27 hw1 hl
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 611 (by decide)).trans h611) hl⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, harrIn, harrOut⟩ := h
      have hsrc : st.arrs 611 = row := (hk.2 611 (by decide)).trans h611
      have horg : st.arrs 601 = origins := (hk.2 601 (by decide)).trans h601
      have hdi : row[i] < 2 * m := hd _ (List.getElem_mem hi)
      have hmate : gm06DartMate row[i] < 2 * m := gm06DartMate_lt hdi
      have hdi' : row[i] < origins.length := horig ▸ hdi
      have hmate' : gm06DartMate row[i] < origins.length := horig ▸ hmate
      have hu : origins[row[i]] < n := hv _ (List.getElem_mem hdi')
      have hv' : origins[gm06DartMate row[i]] < n := hv _ (List.getElem_mem hmate')
      have hread : (Expr.read 611 (.reg 650)).eval w st = some row[i] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 611)
          (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hl))
          (by simpa [hsrc] using hi) (by simpa [hsrc] using hdi.trans hm)
        simpa only [hsrc] using he
      let st₁ := st.setReg 651 row[i]
      let st₂ := st₁.setReg 652 (gm06DartMate row[i])
      let st₃ := st₂.writeArr 621 origins[row[i]] (row[i] + 1)
      let st₄ := st₃.writeArr 620 origins[gm06DartMate row[i]] (gm06DartMate row[i] + 1)
      have he₁ : Exec w (.assign 651 (.read 611 (.reg 650))) st st₁ 3 := .assign hread
      have he₂ : Exec w (.assign 652 (gm06DartMateExpr (.reg 651))) st₁ st₂ 12 :=
        .assign (gm06DartMateExpr_eval hw hm hdi
          (GraphMinor.Compute.Crossing.eval_reg (by simp [st₁]) (hdi.trans hm)))
      have hreadOut : (Expr.read 601 (.reg 651)).eval w st₂ = some origins[row[i]] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 601) (s := st₂)
          (GraphMinor.Compute.Crossing.eval_reg (r := 651) (by simp [st₂, st₁]) (hdi.trans hm))
          (by simpa [st₂, st₁, horg] using hdi') (by simpa [st₂, st₁, horg] using hu.trans hn)
        simpa only [st₂, st₁, State.setReg_arrs, horg] using he
      have hreadIn : (Expr.read 601 (.reg 652)).eval w st₃ = some origins[gm06DartMate row[i]] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 601) (s := st₃)
          (GraphMinor.Compute.Crossing.eval_reg (r := 652) (by simp [st₃, st₂]) (hmate.trans hm))
          (by simpa [st₃, st₂, st₁, State.writeArr, horg] using hmate')
          (by simpa [st₃, st₂, st₁, State.writeArr, horg] using hv'.trans hn)
        simpa only [st₃, st₂, st₁, State.writeArr, State.setArr_arrs_ne _ _ (by decide : 601 ≠ 621),
          State.setReg_arrs, horg] using he
      have hlenOut : (st₂.arrs 621).length = n := by
        simp only [st₂, st₁, State.setReg_arrs, harrOut]
        exact (gm06CutPathMarkScan_lengths _ _ _ _).2.trans hout
      have hlenIn : (st₃.arrs 620).length = n := by
        simp only [st₃, State.writeArr, State.setArr_arrs_ne _ _ (by decide : 620 ≠ 621),
          st₂, st₁, State.setReg_arrs, harrIn]
        exact (gm06CutPathMarkScan_lengths _ _ _ _).1.trans hin
      have he₃ : Exec w (.write 621 (.read 601 (.reg 651)) (.op .add (.reg 651) (.const 1))) st₂ st₃ 6 :=
        .write hreadOut (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg (r := 651) (by simp [st₂, st₁]) (hdi.trans hm))
          (GraphMinor.Compute.Crossing.eval_const hw1) (by omega)) (by rw [hlenOut]; exact hu)
      have he₄ : Exec w (.write 620 (.read 601 (.reg 652)) (.op .add (.reg 652) (.const 1))) st₃ st₄ 6 :=
        .write hreadIn (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg (r := 652) (by simp [st₃, st₂]) (hmate.trans hm))
          (GraphMinor.Compute.Crossing.eval_const hw1) (by omega)) (by rw [hlenIn]; exact hv')
      have hnext : scan (i + 1) = gm06CutPathMarkStep origins (scan i) row[i] := by
        dsimp only [scan, gm06CutPathMarkScan]
        rw [List.take_succ_eq_append_getElem hi, List.foldl_append]
        rfl
      refine ⟨st₄, 27, .seq he₁ (.seq he₂ (.seq he₃ he₄)), le_rfl, ⟨by simp, ?_, ?_, ?_⟩, ?_⟩
      · exact ((((hk.setReg (by simp) _).setReg (by simp) _).writeArr
          (by simp) _ _).writeArr (by simp) _ _).setReg (by simp) _
      · change ((st.arrs 620).set origins[gm06DartMate row[i]] (gm06DartMate row[i] + 1)) = _
        rw [harrIn, hnext]
        simp only [gm06CutPathMarkStep, List.getElem?_eq_getElem hmate', Option.getD_some]
      · change ((st.arrs 621).set origins[row[i]] (row[i] + 1)) = _
        rw [harrOut, hnext]
        simp only [gm06CutPathMarkStep, List.getElem?_eq_getElem hdi', Option.getD_some]
      · simpa [st₄, st₃, st₂, st₁, State.writeArr] using hidx) s₀ hI₀
  refine ⟨sf, 2 + tf, .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) hef,
    ?_, hIf.2.1, ?_, ?_⟩
  · simp only [Expr.cost] at htf
    omega
  · simpa only [scan, List.take_length, gm06CutPathMarkScan_eq_scatter] using hIf.2.2.1
  · simpa only [scan, List.take_length, gm06CutPathMarkScan_eq_scatter] using hIf.2.2.2

end GraphMinor.Compute
