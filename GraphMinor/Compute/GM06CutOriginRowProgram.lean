module

public import GraphMinor.Compute.GM06CutOriginFacts

/-!
# Writing copied origins and active ends from a rotation row

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) connects
every copied outgoing end to the vertex of its induced rotation. This
scan reads one such row, writes its vertex index into the origin
table and sets the active-end bit. The paired scatter invariant
records every processed end. Repeated writes are allowed, although
valid copied rotations have no repeated end.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Appending one source dart appends its constant-value table write. -/
theorem gm06ConstantScatter_take_succ (row table : List ℕ) (value i : ℕ) (hi : i < row.length) :
    gm06Scatter ((row.take (i + 1)).map (fun d => (d, value))) table =
      (gm06Scatter ((row.take i).map (fun d => (d, value))) table).set row[i] value := by
  rw [List.take_succ_eq_append_getElem hi, List.map_append, gm06Scatter_append]
  rfl

/-- Read a copied end and install its origin and active bit. -/
def gm06CutOriginRowBody : Cmd :=
  .seq (.assign 651 (.read 611 (.reg 650)))
    (.seq (.write 626 (.reg 651) (.reg 666)) (.write 627 (.reg 651) (.const 1)))

/-- Process one induced rotation row. Register 666 is its copied vertex index. -/
def gm06CutOriginRowProg : Cmd :=
  .seq (.assign 650 (.const 0)) (forUp 650 (.len 611) gm06CutOriginRowBody)

/-- Each copied end receives exactly its row's vertex and active bit.
The scan takes linear time and preserves the row and vertex index. -/
theorem gm06CutOriginRowProg_exec {w q v : ℕ} (row origins active : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hq : q < 2 ^ w) (hv : v < 2 ^ w) (hl : row.length < 2 ^ w)
    (hkeys : ∀ d ∈ row, d < q) (hlenOrg : origins.length = q) (hlenAct : active.length = q)
    (h611 : s.arrs 611 = row) (h626 : s.arrs 626 = origins) (h627 : s.arrs 627 = active)
    (h666 : s.regs 666 = v) :
    ∃ sf t, Exec w gm06CutOriginRowProg s sf t ∧ t ≤ 5 + 16 * row.length ∧
      Keeps [650, 651] [626, 627] s sf ∧
      sf.arrs 626 = gm06Scatter (row.map (fun d => (d, v))) origins ∧
      sf.arrs 627 = gm06Scatter (row.map (fun d => (d, 1))) active := by
  let oscan := fun i => gm06Scatter ((row.take i).map (fun d => (d, v))) origins
  let ascan := fun i => gm06Scatter ((row.take i).map (fun d => (d, 1))) active
  let Inv := fun i st => st.regs 650 = i ∧ Keeps [650, 651] [626, 627] s st ∧
    st.arrs 626 = oscan i ∧ st.arrs 627 = ascan i
  let s₀ := s.setReg 650 0
  have hI₀ : Inv 0 s₀ := ⟨by simp [s₀], (Keeps.refl _ _ s).setReg (by simp) _, h626, h627⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 650) (hi := .len 611) (body := gm06CutOriginRowBody) Inv row.length 9 hw hl
    (fun _ _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 611 (by decide)).trans h611) hl⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, ho, ha⟩ := h
      have hsrc : st.arrs 611 = row := (hk.2 611 (by decide)).trans h611
      have hvertex : st.regs 666 = v := (hk.1 666 (by decide)).trans h666
      have hdi : row[i] < q := hkeys _ (List.getElem_mem hi)
      have hread : (Expr.read 611 (.reg 650)).eval w st = some row[i] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 611)
          (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hl))
          (by simpa [hsrc] using hi) (by simpa [hsrc] using hdi.trans hq)
        simpa only [hsrc] using he
      let st₁ := st.setReg 651 row[i]
      let st₂ := st₁.writeArr 626 row[i] v
      let st₃ := st₂.writeArr 627 row[i] 1
      have he₁ : Exec w (.assign 651 (.read 611 (.reg 650))) st st₁ 3 := .assign hread
      have he₂ : Exec w (.write 626 (.reg 651) (.reg 666)) st₁ st₂ 3 :=
        .write (GraphMinor.Compute.Crossing.eval_reg (by simp [st₁]) (hdi.trans hq))
          (GraphMinor.Compute.Crossing.eval_reg (by simpa [st₁] using hvertex) hv)
          (by simpa [st₁, ho, oscan, gm06Scatter_length, hlenOrg] using hdi)
      have he₃ : Exec w (.write 627 (.reg 651) (.const 1)) st₂ st₃ 3 :=
        .write (GraphMinor.Compute.Crossing.eval_reg (by simp [st₂, st₁]) (hdi.trans hq))
          (GraphMinor.Compute.Crossing.eval_const hw)
          (by simpa [st₂, st₁, State.writeArr, ha, ascan, gm06Scatter_length, hlenAct] using hdi)
      refine ⟨st₃, 9, .seq he₁ (.seq he₂ he₃), le_rfl, ⟨by simp, ?_, ?_, ?_⟩, ?_⟩
      · exact (((hk.setReg (by simp) _).writeArr (by simp) _ _).writeArr (by simp) _ _).setReg (by simp) _
      · change (st.arrs 626).set row[i] v = oscan (i + 1)
        rw [ho]
        exact (gm06ConstantScatter_take_succ row origins v i hi).symm
      · change (st.arrs 627).set row[i] 1 = ascan (i + 1)
        rw [ha]
        exact (gm06ConstantScatter_take_succ row active 1 i hi).symm
      · simpa [st₃, st₂, st₁, State.writeArr] using hidx) s₀ hI₀
  refine ⟨sf, 2 + tf, .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) hef,
    ?_, hIf.2.1, ?_, ?_⟩
  · simp only [Expr.cost] at htf
    omega
  · simpa only [oscan, List.take_length] using hIf.2.2.1
  · simpa only [ascan, List.take_length] using hIf.2.2.2

end GraphMinor.Compute
