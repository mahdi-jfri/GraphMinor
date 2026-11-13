module

public import GraphMinor.Compute.GM06RotationPredecessors
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning one rotation into the predecessor table

The first pass of FACE_ROWS in Section 5 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) writes the cyclic predecessor of each dart. Start with the
row's last dart as the previous dart, then scan the row from its first entry. Each step writes that
previous dart and makes the current dart the new previous dart. A fold invariant
proves the exact table update, with a linear instruction bound.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- One predecessor write and the new previous dart. -/
def gm06PredecessorStep (state : List ℕ × ℕ) (d : ℕ) : List ℕ × ℕ :=
  (state.1.set d state.2, d)

/-- Pure predecessor scan with a supplied initial previous dart. -/
def gm06PredecessorScan (row table : List ℕ) (previous : ℕ) : List ℕ × ℕ :=
  row.foldl gm06PredecessorStep (table, previous)

/-- Scanning a row preserves the predecessor table's size. -/
theorem gm06PredecessorScan_length (row table : List ℕ) (previous : ℕ) :
    (gm06PredecessorScan row table previous).1.length = table.length := by
  induction row generalizing table previous with
  | nil => rfl
  | cons d ds ih => simpa only [gm06PredecessorScan, List.foldl_cons, gm06PredecessorStep,
      List.length_set] using ih (table.set d previous) d

/-- The previous dart is always the initial dart or a scanned entry. -/
theorem gm06PredecessorScan_previous (row table : List ℕ) (previous : ℕ) :
    (gm06PredecessorScan row table previous).2 ∈ previous :: row := by
  induction row generalizing table previous with
  | nil => exact List.mem_cons_self
  | cons d ds ih =>
    have h := ih (table.set d previous) d
    change (gm06PredecessorScan (d :: ds) table previous).2 ∈ d :: ds at h
    exact List.mem_cons_of_mem previous h

/-- Extending the scanned prefix performs one table write. -/
theorem gm06PredecessorScan_append_one (row table : List ℕ) (previous d : ℕ) :
    gm06PredecessorScan (row ++ [d]) table previous =
      gm06PredecessorStep (gm06PredecessorScan row table previous) d := by
  simp only [gm06PredecessorScan, List.foldl_append, List.foldl_cons, List.foldl_nil]

private theorem zip_previous_dropLast (row : List ℕ) (previous : ℕ) :
    row.zip (previous :: row) = row.zip (previous :: row.dropLast) := by
  induction row generalizing previous with
  | nil => rfl
  | cons d ds ih =>
    cases ds with
    | nil => rfl
    | cons e es => simpa only [List.dropLast_cons_cons, List.zip_cons_cons] using
        (congrArg (List.cons (d, previous)) (ih d))

private theorem scan_table_eq_scatter (row table : List ℕ) (previous : ℕ) :
    (gm06PredecessorScan row table previous).1 = gm06Scatter (row.zip (previous :: row)) table := by
  induction row generalizing table previous with
  | nil => rfl
  | cons d ds ih =>
    simpa only [gm06PredecessorScan, List.foldl_cons, gm06PredecessorStep,
      List.zip_cons_cons, gm06Scatter] using ih (table.set d previous) d

/-- With the last dart as its initial value, the scan writes exactly
the cyclic predecessor pairs used in the pure rotation function. -/
theorem gm06PredecessorScan_cyclic (row table : List ℕ) :
    (gm06PredecessorScan row table (row.getLast?.getD 0)).1 =
      gm06Scatter (gm06RotationPredecessorPairs row) table := by
  rw [scan_table_eq_scatter, zip_previous_dropLast]
  cases row with
  | nil => rfl
  | cons d ds =>
    simp only [gm06RotationPredecessorPairs, List.getLast?_eq_some_getLast (by simp : d :: ds ≠ []),
      Option.getD_some, Option.toList_some, List.singleton_append]

/-- Scan a supplied row into a predecessor array. Register 651 holds
the previous dart. Only registers 650--652 and the table change. -/
def gm06PredecessorScanProg (src dst : Arr) : Cmd :=
  .seq (.assign 650 (.const 0))
    (forUp 650 (.len src)
      (.seq (.assign 652 (.read src (.reg 650)))
        (.seq (.write dst (.reg 652) (.reg 651)) (.assign 651 (.reg 652)))))

/-- Exact RAM execution of the row fold, in linear time. -/
theorem gm06PredecessorScanProg_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (row table : List ℕ) (previous : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hl : row.length < 2 ^ w) (hn : table.length < 2 ^ w)
    (hd : ∀ d ∈ row, d < table.length) (hp : previous < 2 ^ w)
    (hsrc : s.arrs src = row) (hdst : s.arrs dst = table) (hprev : s.regs 651 = previous) :
    ∃ s' t, Exec w (gm06PredecessorScanProg src dst) s s' t ∧
      t ≤ 5 + 15 * row.length ∧ Keeps [650, 651, 652] [dst] s s' ∧
      s'.arrs dst = (gm06PredecessorScan row table previous).1 ∧
      s'.regs 651 = (gm06PredecessorScan row table previous).2 := by
  let scan := fun i => gm06PredecessorScan (row.take i) table previous
  let Inv := fun i st => st.regs 650 = i ∧ Keeps [650, 651, 652] [dst] s st ∧
    st.arrs dst = (scan i).1 ∧ st.regs 651 = (scan i).2
  let s₀ := s.setReg 650 0
  have hI₀ : Inv 0 s₀ := by
    exact ⟨by simp [s₀], (Keeps.refl _ _ s).setReg (by simp) _, hdst,
      by simpa [s₀, scan, gm06PredecessorScan] using hprev⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 650) (hi := .len src)
    (body := .seq (.assign 652 (.read src (.reg 650)))
      (.seq (.write dst (.reg 652) (.reg 651)) (.assign 651 (.reg 652))))
    Inv row.length 8 hw hl
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len
      ((h.2.1.2 src (by simpa using hne)).trans hsrc) hl⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, harr, hprevious⟩ := h
      have hsrc' : st.arrs src = row := (hk.2 src (by simpa using hne)).trans hsrc
      have hlen : (st.arrs dst).length = table.length := by
        rw [harr]
        exact gm06PredecessorScan_length _ _ _
      have hiw : i < 2 ^ w := hi.trans hl
      have hdi : row[i] < table.length := hd _ (List.getElem_mem hi)
      have hdw : row[i] < 2 ^ w := hdi.trans hn
      have hpw : (scan i).2 < 2 ^ w := by
        have hmem := gm06PredecessorScan_previous (row.take i) table previous
        rcases List.mem_cons.mp hmem with h | h
        · exact h ▸ hp
        · exact (hd _ (List.mem_of_mem_take h)).trans hn
      have hread : (Expr.read src (.reg 650)).eval w st = some row[i] := by
        have hh := GraphMinor.Compute.Crossing.eval_read (a := src)
          (GraphMinor.Compute.Crossing.eval_reg hidx hiw)
          (by simpa only [hsrc'] using hi) (by simpa only [hsrc'] using hdw)
        simpa only [hsrc'] using hh
      let st₁ := st.setReg 652 row[i]
      let st₂ := st₁.writeArr dst row[i] (scan i).2
      let st₃ := st₂.setReg 651 row[i]
      have he₁ : Exec w (.assign 652 (.read src (.reg 650))) st st₁ 3 := .assign hread
      have he₂ : Exec w (.write dst (.reg 652) (.reg 651)) st₁ st₂ 3 :=
        .write (GraphMinor.Compute.Crossing.eval_reg (by simp [st₁]) hdw)
          (GraphMinor.Compute.Crossing.eval_reg (by simpa [st₁] using hprevious) hpw)
          (by simpa [st₁, hlen] using hdi)
      have he₃ : Exec w (.assign 651 (.reg 652)) st₂ st₃ 2 :=
        .assign (GraphMinor.Compute.Crossing.eval_reg (by simp [st₂, st₁]) hdw)
      have hnext : scan (i + 1) = gm06PredecessorStep (scan i) row[i] := by
        dsimp only [scan]
        rw [List.take_succ_eq_append_getElem hi, gm06PredecessorScan_append_one]
      refine ⟨st₃, 8, .seq he₁ (.seq he₂ he₃), le_rfl, ⟨by simp, ?_, ?_, ?_⟩, ?_⟩
      · exact (((hk.setReg (by simp) _).writeArr (by simp) _ _).setReg
          (by simp) _).setReg (by simp) _
      · simp only [State.setReg_arrs, st₃, st₂, st₁, State.writeArr, State.setArr_arrs_self]
        rw [harr, hnext]
        rfl
      · simp [st₃, hnext, gm06PredecessorStep]
      · simpa [st₃, st₂, st₁] using hidx) s₀ hI₀
  refine ⟨sf, 2 + tf, .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) hef,
    ?_, hIf.2.1, ?_, ?_⟩
  · simp only [Expr.cost] at htf
    omega
  · simpa only [scan, List.take_length] using hIf.2.2.1
  · simpa only [scan, List.take_length] using hIf.2.2.2

/-- Initialize the previous dart from the last entry, then scan the
row. An empty rotation performs no predecessor write. -/
def gm06PredecessorRowProg (src dst : Arr) : Cmd :=
  .ite (.len src)
    (.seq (.assign 651 (.read src (.op .sub (.len src) (.const 1))))
      (gm06PredecessorScanProg src dst)) .skip

/-- The RAM cyclic row pass computes exactly the pure predecessor-pair
update, preserving every other array and using linear time. -/
theorem gm06PredecessorRowProg_exec {w : ℕ} (src dst : ℕ) (hne : src ≠ dst)
    (row table : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hl : row.length < 2 ^ w) (hn : table.length < 2 ^ w)
    (hd : ∀ d ∈ row, d < table.length) (hsrc : s.arrs src = row) (hdst : s.arrs dst = table) :
    ∃ s' t, Exec w (gm06PredecessorRowProg src dst) s s' t ∧
      t ≤ 11 + 15 * row.length ∧ Keeps [650, 651, 652] [dst] s s' ∧
      s'.arrs dst = gm06Scatter (gm06RotationPredecessorPairs row) table := by
  cases row with
  | nil =>
    exact ⟨s, 2, .ite_false (GraphMinor.Compute.Crossing.eval_len hsrc hl) (.skip s),
      by simp, Keeps.refl _ _ _, hdst⟩
  | cons d ds =>
    let row := d :: ds
    let last := row.getLast (by simp [row])
    have hlast : last < table.length := hd _ (List.getLast_mem (by simp : d :: ds ≠ []))
    have hi : row.length - 1 < row.length := by
      change ds.length < ds.length + 1
      exact Nat.lt_succ_self _
    have hread : (Expr.read src (.op .sub (.len src) (.const 1))).eval w s = some last := by
      have he := GraphMinor.Compute.Crossing.eval_read (a := src)
        (GraphMinor.Compute.Crossing.eval_sub (GraphMinor.Compute.Crossing.eval_len hsrc hl)
          (GraphMinor.Compute.Crossing.eval_const hw)) (by simp [hsrc])
        (by simpa only [hsrc, ← List.getLast_eq_getElem (by simp : d :: ds ≠ [])] using hlast.trans hn)
      simpa only [hsrc, ← List.getLast_eq_getElem (by simp : d :: ds ≠ [])] using he
    let s₁ := s.setReg 651 last
    obtain ⟨sf, tf, hef, htf, hkf, hdf, _⟩ := gm06PredecessorScanProg_exec src dst hne row table
      last s₁ hw hl hn hd (hlast.trans hn) hsrc hdst (by simp [s₁])
    refine ⟨sf, 1 + (5 + tf), .ite_true (GraphMinor.Compute.Crossing.eval_len hsrc hl)
      (Nat.succ_ne_zero _) (.seq (.assign hread) hef), by dsimp only [row] at htf; omega,
      ((Keeps.refl _ _ s).setReg (by simp) _).trans hkf (fun _ h => h) (fun _ h => h), ?_⟩
    have hlast' : row.getLast?.getD 0 = last := by
      simp only [List.getLast?_eq_some_getLast (l := row) (by simp [row]), Option.getD_some, last]
    rw [← gm06PredecessorScan_cyclic]
    exact hlast' ▸ hdf

end GraphMinor.Compute
