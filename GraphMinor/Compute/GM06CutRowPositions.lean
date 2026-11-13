module

public import GraphMinor.Compute.GM06PredecessorProgram

/-!
# Computing positions in each original rotation row

The interval table in Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) compares the cyclic positions of directed ends. Build an
index table from a row before splitting it. Unlisted labels receive the row length. A scatter of the
row's indexed entries then gives exactly List.idxOf for a row without repetitions.
The RAM scan writes these positions directly from the row.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Position table for a rotation row, with row length for absent ends. -/
def gm06RowPositions (n : ℕ) (row : List ℕ) : List ℕ :=
  gm06Scatter row.zipIdx (List.replicate n row.length)

/-- The position table retains its complete permanent dart-label space. -/
theorem gm06RowPositions_length (n : ℕ) (row : List ℕ) :
    (gm06RowPositions n row).length = n := by simp [gm06RowPositions, gm06Scatter_length]

/-- In a row with distinct ends the position table is exactly idxOf,
including the row-length sentinel for an absent end. -/
theorem gm06RowPositions_getElem? (n : ℕ) (row : List ℕ) (hn : row.Nodup)
    (d : ℕ) (hd : d < n) : (gm06RowPositions n row)[d]? = some (row.idxOf d) := by
  by_cases hm : d ∈ row
  · have hi := List.idxOf_lt_length_of_mem hm
    apply gm06Scatter_getElem?_of_mem row.zipIdx (List.replicate n row.length)
      (by simpa using hn) (d, row.idxOf d)
    · apply List.mem_iff_getElem.mpr
      refine ⟨row.idxOf d, by simpa using hi, ?_⟩
      simp only [List.getElem_zipIdx, Nat.zero_add, List.getElem_idxOf hi]
    · simpa using hd
  · rw [gm06RowPositions, gm06Scatter_getElem?_of_not_mem _ _ d (by simpa using hm),
      List.getElem?_replicate, ite_eq_left hd, List.idxOf_eq_length hm]

/-- Append one indexed row entry to its scatter pass. -/
theorem gm06IndexScatter_take_succ (row table : List ℕ) (i : ℕ) (hi : i < row.length) :
    gm06Scatter (row.zipIdx.take (i + 1)) table =
      (gm06Scatter (row.zipIdx.take i) table).set row[i] i := by
  rw [List.take_succ_eq_append_getElem (by simpa using hi), gm06Scatter_append]
  simp only [List.getElem_zipIdx, Nat.zero_add, gm06Scatter]

/-- Write each source dart's index into a supplied table. -/
def gm06IndexScatterProg (src dst : ℕ) : Cmd :=
  .seq (.assign 650 (.const 0))
    (forUp 650 (.len src) (.write dst (.read src (.reg 650)) (.reg 650)))

/-- Indexed scattering reads the row itself and costs linear time. -/
theorem gm06IndexScatterProg_exec {w src dst : ℕ} (hsd : src ≠ dst)
    (row table : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hl : row.length < 2 ^ w) (ht : table.length < 2 ^ w)
    (hkeys : ∀ d ∈ row, d < table.length) (ha : s.arrs src = row) (hb : s.arrs dst = table) :
    ∃ sf t, Exec w (gm06IndexScatterProg src dst) s sf t ∧ t ≤ 5 + 11 * row.length ∧
      Keeps [650] [dst] s sf ∧ sf.arrs dst = gm06Scatter row.zipIdx table := by
  let scan := fun i => gm06Scatter (row.zipIdx.take i) table
  let Inv := fun i st => st.regs 650 = i ∧ Keeps [650] [dst] s st ∧ st.arrs dst = scan i
  let s₀ := s.setReg 650 0
  have hI₀ : Inv 0 s₀ := ⟨by simp [s₀], (Keeps.refl _ _ s).setReg (by simp) _, hb⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 650) (hi := .len src) (body := .write dst (.read src (.reg 650)) (.reg 650))
    Inv row.length 4 hw hl
    (fun _ _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len
      ((h.2.1.2 src (by simpa using hsd)).trans ha) hl⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, htab⟩ := h
      have hsrc : st.arrs src = row := (hk.2 src (by simpa using hsd)).trans ha
      have hdi : row[i] < table.length := hkeys _ (List.getElem_mem hi)
      have hread : (Expr.read src (.reg 650)).eval w st = some row[i] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := src)
          (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hl))
          (by simpa [hsrc] using hi) (by simpa [hsrc] using hdi.trans ht)
        simpa only [hsrc] using he
      have hbound : row[i] < (st.arrs dst).length := by
        simpa only [htab, scan, gm06Scatter_length] using hdi
      let st' := st.writeArr dst row[i] i
      refine ⟨st', 4, .write hread (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hl)) hbound,
        le_rfl, ⟨by simp, (hk.writeArr (by simp) _ _).setReg (by simp) _, ?_⟩, ?_⟩
      · simp only [State.setReg_arrs, st', State.writeArr, State.setArr_arrs_self]
        rw [htab]
        exact (gm06IndexScatter_take_succ row table i hi).symm
      · simpa [st', State.writeArr] using hidx) s₀ hI₀
  refine ⟨sf, 2 + tf, .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) hef,
    ?_, hIf.2.1, ?_⟩
  · simp only [Expr.cost] at htf
    omega
  · simpa only [scan, ← List.length_zipIdx (l := row) (i := 0), List.take_length] using hIf.2.2

/-- Initialize positions in 614 and scatter the current row in 611.
Register 647 holds the permanent dart-label-space size. -/
def gm06RowPositionsProg : Cmd :=
  .seq (gm13TabulateProg 650 (.reg 647) (.len 611) 614) (gm06IndexScatterProg 611 614)

/-- The complete row-position pass returns the exact pure table.
Only the current row, its label-space size and word bounds are inputs. -/
theorem gm06RowPositionsProg_exec {w n : ℕ} (row : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hl : row.length < 2 ^ w)
    (hkeys : ∀ d ∈ row, d < n) (ha : s.arrs 611 = row) (h647 : s.regs 647 = n) :
    ∃ sf t, Exec w gm06RowPositionsProg s sf t ∧ t ≤ 11 + 13 * n + 11 * row.length ∧
      Keeps [650] [614] s sf ∧ sf.arrs 614 = gm06RowPositions n row := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm13TabulateProg_exec
    650 (.reg 647) (.len 611) 614 (List.replicate n row.length) s hw (by simpa using hn)
    (fun st hk => by
      simpa only [List.length_replicate] using GraphMinor.Compute.Crossing.eval_reg
        ((hk.1 647 (by decide)).trans h647) hn)
    (fun st i hi hk _ => by
      simpa only [List.getElem_replicate] using GraphMinor.Compute.Crossing.eval_len
        ((hk.2 611 (by decide)).trans ha) hl)
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06IndexScatterProg_exec (by decide : 611 ≠ 614)
    row (List.replicate n row.length) s₁ hw hl (by simpa using hn)
    (fun d hd => by simpa using hkeys d hd) ((hk₁.2 611 (by decide)).trans ha) hd₁
  refine ⟨sf, t₁ + tf, .seq he₁ hef, ?_, hk₁.trans hkf (fun _ h => h) (fun _ h => h), hdf⟩
  simp only [Expr.cost, List.length_replicate] at ht₁
  omega

end GraphMinor.Compute
