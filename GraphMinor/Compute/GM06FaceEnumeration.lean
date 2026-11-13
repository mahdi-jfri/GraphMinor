module

public import GraphMinor.Compute.GM06AppendFaceRow

/-!
# The outer RAM scan of face orbits

FACE_ROWS, Section 5 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`)
scans active darts in label order and starts a row only at an unseen dart.
The owner table detects completed orbits. A new row is disjoint from
all completed rows because its start was unseen. This maintains a
repetition-free list of complete orbits and provides enough buffer
space for the next traversal. The execution theorem proves the exact
pure enumeration, including its owner table and encoded row output.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Registers changed by the face-enumeration scan. -/
def gm06FaceEnumerationRegs : List ℕ := [650, 651, 652, 654, 655, 656, 657]

/-- Inspect one active dart. Owner zero starts a new row; a positive
owner means its row has already been completed. -/
def gm06FaceEnumerationStep : Cmd :=
  .seq (.assign 652 (.read 604 (.reg 650)))
    (.seq (.ite (.readMin 605 (.reg 652) (.const 1)) .skip gm06AppendFaceRowProg)
      (.assign 650 (.op .add (.reg 650) (.const 1))))

/-- Enumerate the remaining active dart labels stored in 604. -/
def gm06FaceEnumerationLoop : Cmd :=
  .while (.op .lt (.reg 650) (.len 604)) gm06FaceEnumerationStep

private theorem nat_rows_mem_iff {n : ℕ} (rows : List (List (Fin n))) (d : Fin n) :
    d.val ∈ (rows.map (List.map Fin.val)).flatten ↔ d ∈ rows.flatten := by
  rw [← List.map_flatten]
  constructor
  · intro hm
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hm
    exact (Fin.ext heq) ▸ ha
  · intro hd
    exact List.mem_map.mpr ⟨d, hd, rfl⟩

private theorem orbit_rows_nonempty {n : ℕ} (next : Equiv.Perm (Fin n))
    (rows : List (List (Fin n)))
    (hr : ∀ row ∈ rows, ∃ d, row = gm06OrbitTrace next d n) :
    ∀ row ∈ rows, row ≠ [] := by
  intro row hrow
  obtain ⟨d, rfl⟩ := hr row hrow
  exact gm06OrbitTrace_ne_nil next d n (by simp)

/-- The outer scan computes the same rows as the pure enumerator.
The completed rows in its invariant are disjoint full orbits, not
extra input data required by the complete program. -/
theorem gm06FaceEnumerationLoop_exec {w n : ℕ} (next : Equiv.Perm (Fin n))
    (done labels : List (Fin n)) (rows : List (List (Fin n))) (s : State)
    (hw : 1 < 2 ^ w) (hcap : 1 + 2 * n < 2 ^ w)
    (hl : (done ++ labels).length < 2 ^ w)
    (hnd : rows.flatten.Nodup)
    (hr : ∀ row ∈ rows, ∃ d, row = gm06OrbitTrace next d n)
    (h603 : s.arrs 603 = List.ofFn (fun d => (next d).val))
    (h604 : s.arrs 604 = (done ++ labels).map Fin.val)
    (h605 : s.arrs 605 = gm06FaceOwners n (rows.map (List.map Fin.val)))
    (h606 : s.arrs 606 = gm06FaceBuffer (1 + 2 * n) (rows.map (List.map Fin.val)))
    (h650 : s.regs 650 = done.length) (h655 : s.regs 655 = rows.length)
    (h656 : s.regs 656 = (gm06EncodeRows (rows.map (List.map Fin.val))).length) :
    let result := gm06FaceRowsAux next n labels rows
    ∃ sf t, Exec w gm06FaceEnumerationLoop s sf t ∧
      t ≤ 3 + labels.length * (40 + 18 * n) ∧
      Keeps gm06FaceEnumerationRegs [605, 606] s sf ∧
      sf.arrs 605 = gm06FaceOwners n (result.map (List.map Fin.val)) ∧
      sf.arrs 606 = gm06FaceBuffer (1 + 2 * n) (result.map (List.map Fin.val)) ∧
      sf.regs 650 = (done ++ labels).length ∧ sf.regs 655 = result.length ∧
      sf.regs 656 = (gm06EncodeRows (result.map (List.map Fin.val))).length := by
  have hn : n < 2 ^ w := by omega
  induction labels generalizing done rows s with
  | nil =>
    have heval := GraphMinor.Compute.Crossing.eval_lt
      (GraphMinor.Compute.Crossing.eval_reg h650 (by simpa using hl))
      (GraphMinor.Compute.Crossing.eval_len h604 (by simpa using hl)) hw
    refine ⟨s, 3, .while_false ?_, by simp, Keeps.refl _ _ _, h605, h606,
      by simpa using h650, h655, h656⟩
    simpa only [List.append_nil, List.length_map, lt_self_iff_false, ↓reduceIte] using heval
  | cons d labels ih =>
    have hi : done.length < (done ++ d :: labels).length := by simp
    have hiw : done.length < 2 ^ w := hi.trans hl
    have hdw : d.val < 2 ^ w := d.isLt.trans hn
    have hindex : done.length < (s.arrs 604).length := by simpa only [h604, List.length_map] using hi
    have hget : (s.arrs 604)[done.length] = d.val := by
      have hh : (s.arrs 604)[done.length]? = some d.val := by
        rw [h604, List.map_append, List.getElem?_append_right (by simp)]
        simp
      exact Option.some.inj ((List.getElem?_eq_getElem hindex).symm.trans hh)
    let s₁ := s.setReg 652 d.val
    have he₁ : Exec w (.assign 652 (.read 604 (.reg 650))) s s₁ 3 :=
      .assign (by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 604)
          (GraphMinor.Compute.Crossing.eval_reg h650 hiw) hindex (by rw [hget]; exact hdw)
        simpa only [hget] using he)
    have hk₁ : Keeps gm06FaceEnumerationRegs [605, 606] s s₁ :=
      (Keeps.refl _ _ s).setReg (by simp [gm06FaceEnumerationRegs]) _
    have ho : d.val < (s₁.arrs 605).length := by simp [s₁, h605, gm06FaceOwners_length, d.isLt]
    have howner := GraphMinor.Compute.Crossing.eval_readMin (a := 605)
      (GraphMinor.Compute.Crossing.eval_reg (show s₁.regs 652 = d.val by simp [s₁]) hdw)
      (GraphMinor.Compute.Crossing.eval_const hw) ho
    have hzero : (s₁.arrs 605)[d.val] = 0 ↔ d ∉ rows.flatten := by
      have hh := gm06FaceOwners_zero_iff n (rows.map (List.map Fin.val)) d.val d.isLt
      have hob : d.val < (gm06FaceOwners n (rows.map (List.map Fin.val))).length := by
        simpa only [gm06FaceOwners_length] using d.isLt
      rw [List.getElem?_eq_getElem hob, Option.some.injEq] at hh
      simpa only [s₁, State.setReg_arrs, h605, nat_rows_mem_iff] using hh
    have hcond := GraphMinor.Compute.Crossing.eval_lt
      (GraphMinor.Compute.Crossing.eval_reg h650 hiw)
      (GraphMinor.Compute.Crossing.eval_len h604 (by simpa only [List.length_map] using hl)) hw
    have hcond' : (Expr.op .lt (.reg 650) (.len 604)).eval w s = some 1 := by
      simpa only [List.length_map, hi, ↓reduceIte] using hcond
    by_cases hseen : d ∈ rows.flatten
    · have hnonzero : (s₁.arrs 605)[d.val] ≠ 0 := by
        intro hz
        exact hzero.mp hz hseen
      have hmin : min (s₁.arrs 605)[d.val] 1 = 1 := by omega
      have he₂ : Exec w (.ite (.readMin 605 (.reg 652) (.const 1)) .skip gm06AppendFaceRowProg) s₁ s₁ 5 :=
        .ite_true (by simpa only [hmin] using howner) (by decide) (.skip s₁)
      let s₂ := s₁.setReg 650 (done.length + 1)
      have he₃ : Exec w (.assign 650 (.op .add (.reg 650) (.const 1))) s₁ s₂ 4 :=
        .assign (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁] using h650) hiw)
          (GraphMinor.Compute.Crossing.eval_const hw) (by simp only [List.length_append, List.length_cons] at hl; omega))
      have hk₂ : Keeps gm06FaceEnumerationRegs [605, 606] s s₂ := hk₁.setReg (by simp [gm06FaceEnumerationRegs]) _
      obtain ⟨sf, tf, hef, htf, hkf, hdf, hbf, hif, hcf, hpf⟩ := ih (done ++ [d]) rows s₂
        (by simpa only [List.append_assoc, List.singleton_append] using hl) hnd hr
        ((hk₂.2 603 (by decide)).trans h603)
        (by simpa only [List.append_assoc, List.singleton_append] using (hk₂.2 604 (by decide)).trans h604)
        (by simpa [s₂, s₁] using h605) (by simpa [s₂, s₁] using h606)
        (by simp [s₂]) (by simpa [s₂, s₁] using h655)
        (by simpa [s₂, s₁] using h656)
      refine ⟨sf, 3 + (3 + (5 + 4)) + tf,
        .while_true hcond' (by decide) (.seq he₁ (.seq he₂ he₃)) hef, ?_,
        hk₂.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte] using hdf
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte] using hbf
      · simpa only [List.append_assoc, List.singleton_append] using hif
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte] using hcf
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte] using hpf
    · let orbit := gm06OrbitTrace next d n
      let rows' := rows ++ [orbit]
      have hnd' : rows'.flatten.Nodup := gm06FaceRows_append_orbit_nodup next n (by simp) rows hnd hr d hseen
      have hr' : ∀ row ∈ rows', ∃ a, row = gm06OrbitTrace next a n := by
        intro row hrow
        rcases List.mem_append.mp hrow with hrow | hrow
        · exact hr row hrow
        · exact ⟨d, List.mem_singleton.mp hrow⟩
      obtain ⟨rest, horbit, hnot, hchain, hlength⟩ := gm06OrbitTrace_nat_row next d
      have hrows' : rows'.map (List.map Fin.val) = rows.map (List.map Fin.val) ++ [d.val :: rest] := by
        simp only [rows', List.map_append, List.map_cons, List.map_nil, orbit, horbit]
      have hrest : ∀ x ∈ rest, x < n := by
        intro x hx
        have hm : x ∈ orbit.map Fin.val := by rw [horbit]; exact List.mem_cons_of_mem _ hx
        obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
        exact a.isLt
      have hroom := gm06FaceCode_capacity rows' hnd' (orbit_rows_nonempty next rows' hr')
      rw [hrows'] at hroom
      obtain ⟨sm, tm, hem, htm, hkm, hdm, hbm, hcm, hpm⟩ := gm06AppendFaceRowProg_exec
        (List.ofFn (fun a => (next a).val)) (rows.map (List.map Fin.val)) d.val rest
        (1 + 2 * n) s₁ hw (by simpa using hn) (by simp)
        (by simpa using hrest) hnot hchain hroom hcap h603 (by simpa [s₁] using h605) h606
        (by simp [s₁]) (by simpa [s₁] using h655) (by simpa [s₁] using h656)
      have hmin : min (s₁.arrs 605)[d.val] 1 = 0 := by rw [hzero.mpr hseen]; rfl
      have he₂ : Exec w (.ite (.readMin 605 (.reg 652) (.const 1)) .skip gm06AppendFaceRowProg) s₁ sm (4 + tm) :=
        .ite_false (by simpa only [hmin] using howner) hem
      have hk₂ : Keeps gm06FaceEnumerationRegs [605, 606] s sm :=
        hk₁.trans hkm (by simp [gm06FaceEnumerationRegs]) (fun _ h => h)
      have hidx : sm.regs 650 = done.length := (hkm.1 650 (by decide)).trans (by simpa [s₁] using h650)
      let s₂ := sm.setReg 650 (done.length + 1)
      have he₃ : Exec w (.assign 650 (.op .add (.reg 650) (.const 1))) sm s₂ 4 :=
        .assign (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg hidx hiw)
          (GraphMinor.Compute.Crossing.eval_const hw) (by simp only [List.length_append, List.length_cons] at hl; omega))
      have hk₃ := hk₂.setReg (by simp [gm06FaceEnumerationRegs] : 650 ∈ gm06FaceEnumerationRegs) (done.length + 1)
      obtain ⟨sf, tf, hef, htf, hkf, hdf, hbf, hif, hcf, hpf⟩ := ih (done ++ [d]) rows' s₂
        (by simpa only [List.append_assoc, List.singleton_append] using hl) hnd' hr'
        ((hk₃.2 603 (by decide)).trans h603)
        (by simpa only [List.append_assoc, List.singleton_append] using (hk₃.2 604 (by decide)).trans h604)
        (by simpa only [s₂, State.setReg_arrs, List.length_ofFn, hrows'] using hdm)
        (by simpa only [s₂, State.setReg_arrs, hrows'] using hbm)
        (by simp [s₂]) (by simpa [s₂, rows'] using hcm)
        (by simpa only [s₂, State.setReg_regs_ne _ _ (by decide : 656 ≠ 650), hrows'] using hpm)
      refine ⟨sf, 3 + (3 + ((4 + tm) + 4)) + tf,
        .while_true hcond' (by decide) (.seq he₁ (.seq he₂ he₃)) hef, ?_,
        hk₃.trans hkf (fun _ h => h) (fun _ h => h), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte, rows', orbit] using hdf
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte, rows', orbit] using hbf
      · simpa only [List.append_assoc, List.singleton_append] using hif
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte, rows', orbit] using hcf
      · simpa only [gm06FaceRowsAux, hseen, ↓reduceIte, rows', orbit] using hpf

end GraphMinor.Compute
