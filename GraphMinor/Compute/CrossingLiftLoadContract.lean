module

public import GraphMinor.Compute.CrossingLiftRead
public import GraphMinor.Compute.CrossingLiftSlice

/-!
# Loading an encoded contraction record

The contraction record stores its tag, two old endpoints, two cycle flags and the old
neighbours of the retained endpoint. This file reads those fields at a runtime record
start and copies the recorded neighbour list to a scratch array. It reads no free buffer
entries and preserves the record array.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Load the four fixed contraction fields, then copy its neighbour slice. -/
def liftLoadContractionProg (a_rec neighbours r_start r_u r_v r_uOn r_vOn R : ℕ) : Cmd :=
  .seq (.assign r_u (.read a_rec (.op .add (.reg r_start) (.const 1))))
    (.seq (.assign r_v (.read a_rec (.op .add (.reg r_start) (.const 2))))
      (.seq (.assign r_uOn (.read a_rec (.op .add (.reg r_start) (.const 3))))
        (.seq (.assign r_vOn (.read a_rec (.op .add (.reg r_start) (.const 4))))
          (.seq (.alloc neighbours (.read a_rec (.op .add (.reg r_start) (.const 5))))
            (liftSliceAtProg a_rec neighbours (.op .add (.reg r_start) (.const 6)) (.const 0)
            (.read a_rec (.op .add (.reg r_start) (.const 5))) R)))))

private theorem load_contraction_layout (r_start r_u r_v r_uOn r_vOn : ℕ)
    (h : [r_start, r_u, r_v, r_uOn, r_vOn].Nodup) :
    r_start ≠ r_u ∧ r_start ≠ r_v ∧ r_start ≠ r_uOn ∧ r_start ≠ r_vOn ∧
    r_u ≠ r_v ∧ r_u ≠ r_uOn ∧ r_u ≠ r_vOn ∧
    r_v ≠ r_uOn ∧ r_v ≠ r_vOn ∧ r_uOn ≠ r_vOn := by
  simpa only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    not_false_eq_true, List.nodup_nil, and_true, and_assoc] using h

/-- Loading a contraction record takes time linear in its encoded neighbour list. Hypotheses
state the exact encoding at the known start, distinct destination registers below scratch,
and the word bound. Record validity is not needed to decode these fields. -/
theorem liftLoadContractionProg_exec {w N : ℕ} (r : ContractRecord (Fin N)) (Nv : List (Fin N))
    (a_rec neighbours r_start r_u r_v r_uOn r_vOn R : ℕ)
    (hne : a_rec ≠ neighbours) (hregs : [r_start, r_u, r_v, r_uOn, r_vOn].Nodup)
    (hbelow : ∀ q ∈ [r_start, r_u, r_v, r_uOn, r_vOn], q < R)
    (pre spare : List ℕ) (s : State)
    (hrec : s.arrs a_rec = pre ++ withLength
      ([1, r.u.val, r.v.val, if r.u ∈ r.cycle then 1 else 0,
        if r.v ∈ r.cycle then 1 else 0, Nv.length] ++ Nv.map Fin.val) ++ spare)
    (hstart : s.regs r_start = pre.length)
    (hw : N + pre.length + Nv.length + 8 < 2 ^ w) :
    ∃ s' t, Exec w (liftLoadContractionProg a_rec neighbours r_start r_u r_v r_uOn r_vOn R) s s' t ∧
      t ≤ 21 * Nv.length + 43 ∧ s'.arrs neighbours = Nv.map Fin.val ∧
      s'.regs r_u = r.u.val ∧ s'.regs r_v = r.v.val ∧
      s'.regs r_uOn = (if r.u ∈ r.cycle then 1 else 0) ∧
      s'.regs r_vOn = (if r.v ∈ r.cycle then 1 else 0) ∧
      (∀ a, a ≠ neighbours → s'.arrs a = s.arrs a) ∧
      (∀ q < R, q ∉ [r_u, r_v, r_uOn, r_vOn] → s'.regs q = s.regs q) := by
  obtain ⟨hsu, hsv, hsuO, hsvO, huv, huuO, huvO, hvuO, hvvO, huOvO⟩ :=
    load_contraction_layout r_start r_u r_v r_uOn r_vOn hregs
  have hsR : r_start < R := hbelow _ (by simp)
  have huR : r_u < R := hbelow _ (by simp)
  have hvR : r_v < R := hbelow _ (by simp)
  have huOR : r_uOn < R := hbelow _ (by simp)
  have hvOR : r_vOn < R := hbelow _ (by simp)
  let fu := if r.u ∈ r.cycle then 1 else 0
  let fv := if r.v ∈ r.cycle then 1 else 0
  let header := [1, r.u.val, r.v.val, fu, fv, Nv.length]
  let tail := Nv.map Fin.val ++ [(header ++ Nv.map Fin.val).length] ++ spare
  have hflat : s.arrs a_rec = pre ++ header ++ tail := by
    simpa only [withLength, header, tail, fu, fv, List.append_assoc] using hrec
  have hh : header.length = 6 := rfl
  have hfu : fu < 2 ^ w := by dsimp [fu]; split_ifs <;> omega
  have hfv : fv < 2 ^ w := by dsimp [fv]; split_ifs <;> omega
  have hwords : ∀ x ∈ Nv.map Fin.val, x < 2 ^ w := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
    exact y.isLt.trans (by omega)
  have hfield : ∀ (st : State) (j value : ℕ), st.arrs a_rec = s.arrs a_rec →
      st.regs r_start = pre.length → header[j]? = some value → value < 2 ^ w →
      (Expr.read a_rec (.op .add (.reg r_start) (.const j))).eval w st = some value := by
    intro st j value ha hs hj hvw
    exact eval_lift_record_field (ha.trans hflat) hs hj hvw (by rw [hh]; omega)
  let s1 := s.setReg r_u r.u.val
  let s2 := s1.setReg r_v r.v.val
  let s3 := s2.setReg r_uOn fu
  let s4 := s3.setReg r_vOn fv
  have hs1 : s1.regs r_start = pre.length := by simp [s1, hsu, hstart]
  have hs2 : s2.regs r_start = pre.length := by simp [s2, hsv, hs1]
  have hs3 : s3.regs r_start = pre.length := by simp [s3, hsuO, hs2]
  have hs4 : s4.regs r_start = pre.length := by simp [s4, hsvO, hs3]
  have he1 : Exec w (.assign r_u (.read a_rec (.op .add (.reg r_start) (.const 1)))) s s1 5 :=
    .assign (hfield s 1 r.u.val rfl hstart (by rfl) (r.u.isLt.trans (by omega)))
  have he2 : Exec w (.assign r_v (.read a_rec (.op .add (.reg r_start) (.const 2)))) s1 s2 5 :=
    .assign (hfield s1 2 r.v.val rfl hs1 (by rfl) (r.v.isLt.trans (by omega)))
  have he3 : Exec w (.assign r_uOn (.read a_rec (.op .add (.reg r_start) (.const 3)))) s2 s3 5 :=
    .assign (hfield s2 3 fu rfl hs2 (by rfl) hfu)
  have he4 : Exec w (.assign r_vOn (.read a_rec (.op .add (.reg r_start) (.const 4)))) s3 s4 5 :=
    .assign (hfield s3 4 fv rfl hs3 (by rfl) hfv)
  have hsliced : s4.arrs a_rec = (pre ++ header) ++ Nv.map Fin.val ++
      ([(header ++ Nv.map Fin.val).length] ++ spare) := by
    change s.arrs a_rec = _
    simpa only [withLength, header, fu, fv, List.append_assoc] using hrec
  let s5 := s4.setArr neighbours (List.replicate Nv.length 0)
  have he5 : Exec w (.alloc neighbours (.read a_rec (.op .add (.reg r_start) (.const 5))))
      s4 s5 (4 + Nv.length) :=
    .alloc (hfield s4 5 Nv.length rfl hs4 (by rfl) (by omega))
  have hs5 : s5.regs r_start = pre.length := hs4
  obtain ⟨s6, t6, he6, ht6, ho6, ha6, hr6⟩ := liftSliceAtProg_exec
    a_rec neighbours R (.op .add (.reg r_start) (.const 6)) (.const 0)
    (.read a_rec (.op .add (.reg r_start) (.const 5))) hne
    (pre ++ header) (Nv.map Fin.val) ([(header ++ Nv.map Fin.val).length] ++ spare) [] [] s5
    (by simpa only [s5, State.setArr_arrs_ne _ _ hne] using hsliced) (by simp [s5])
    (by simpa only [List.length_append, hh] using
      eval_add (w := w) (eval_reg hs5 (by omega)) (eval_const (by omega)) (by omega))
    (eval_const (by omega))
    (by
      have he := hfield ((s5.setReg R (pre ++ header).length).setReg (R + 1) 0)
        5 Nv.length (by simp [s5, s4, s3, s2, s1, hne])
        (by simp [hsR.ne, show r_start ≠ R + 1 by omega, hs5]) (by rfl) (by omega)
      simpa only [List.length_map, List.length_nil] using he)
    hwords (by simp only [List.length_append, List.length_map, List.length_nil, hh]; omega)
  refine ⟨s6, 5 + (5 + (5 + (5 + ((4 + Nv.length) + t6)))), .seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5 he6)))),
    ?_, by simpa using ho6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost, List.length_map] at ht6; omega
  · rw [hr6 r_u huR]; simp [s5, s4, s3, s2, s1, huvO, huuO, huv]
  · rw [hr6 r_v hvR]; simp [s5, s4, s3, s2, hvvO, hvuO]
  · rw [hr6 r_uOn huOR]; simp [s5, s4, s3, huOvO, fu]
  · rw [hr6 r_vOn hvOR]; simp [s5, s4, fv]
  · intro a ha
    exact (ha6 a ha).trans (State.setArr_arrs_ne _ _ ha)
  · intro q hq hn
    simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hn
    rw [hr6 q hq]
    simp [s5, s4, s3, s2, s1, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2]

end GraphMinor.Compute.Crossing
