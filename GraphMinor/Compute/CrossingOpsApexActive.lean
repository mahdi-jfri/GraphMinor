module

public import GraphMinor.Compute.CrossingOpsApexSize
public import GraphMinor.Compute.CrossingOpsRecord

/-!
# Preparing active marks for the apex graph

The old active array is copied and followed by a final one for the apex. A one-entry
array supplies that last mark to the existing bounded concatenation program.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Copy active marks and append one new active vertex. -/
def appendMarkProg (src dst one R : ℕ) : Cmd :=
  .seq (.alloc one (.const 1))
    (.seq (.write one (.const 0) (.const 1))
      (.seq (.assign (R + 11) (.const 1))
        (concatProg src one dst (R + 11) (R + 12) (R + 13) (R + 14))))

/-- Appending the apex mark preserves all arrays except the destination and its one-entry
scratch array, and takes linear time in the old marks. -/
theorem appendMarkProg_exec {w : ℕ} (src dst one R : ℕ) {s : State} {l : List ℕ}
    (hsd : src ≠ dst) (hso : src ≠ one) (hod : one ≠ dst)
    (hl : s.arrs src = l) (hbits : ∀ x ∈ l, x ≤ 1)
    (hlen : l.length + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (appendMarkProg src dst one R) s s' t ∧
      t ≤ 55 + 17 * l.length ∧ s'.arrs dst = l ++ [1] ∧
      (∀ a, a ≠ dst → a ≠ one → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 11 → r ≠ R + 12 → r ≠ R + 13 → r ≠ R + 14 → s'.regs r = s.regs r) := by
  let s1 := s.setArr one [0]
  let s2 := s1.writeArr one 0 1
  let s3 := s2.setReg (R + 11) 1
  have he1 : Exec w (.alloc one (.const 1)) s s1 2 := .alloc (eval_const hw)
  have he2 : Exec w (.write one (.const 0) (.const 1)) s1 s2 3 :=
    .write (eval_const (by omega)) (eval_const hw) (by simp [s1])
  have he3 : Exec w (.assign (R + 11) (.const 1)) s2 s3 2 := .assign (eval_const hw)
  have hsrc : s3.arrs src = l := by
    simp [s3, s2, s1, State.writeArr_arrs_ne, State.setArr_arrs_ne, hso, hl]
  have hone : s3.arrs one = [1] := by simp [s3, s2, s1]
  obtain ⟨s4, t4, he4, ht4, harr4, ha4, hr4⟩ := concatProg_exec (w := w)
    src one dst (R + 11) (R + 12) (R + 13) (R + 14) hsd hod
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (s := s3) (B := 1) (by simp [s3]) hw hw (by simp [hsrc, hone]; omega)
  have hex := Exec.seq he1 (.seq he2 (.seq he3 he4))
  refine ⟨s4, _, hex, by rw [hsrc, hone] at ht4; simp only [List.length_singleton] at ht4; omega,
    ?_, ?_, ?_⟩
  · rw [harr4, hsrc, hone]
    exact map_min_of_le (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact hbits x hx
      · have heq : x = 1 := List.mem_singleton.mp hx
        exact heq ▸ Nat.le_refl 1)
  · intro a had hao
    exact (ha4 a had).trans (by simp [s3, s2, s1, State.writeArr_arrs_ne, State.setArr_arrs_ne, hao])
  · intro r h11 h12 h13 h14
    exact (hr4 r h12 h13 h14).trans (by simp [s3, s2, s1, State.setReg_regs, h11])

/-- The active-array program produces precisely the active marks of the numerical apex graph. -/
theorem apexActiveProg_exec {w N : ℕ} (src dst one R : ℕ) (S : Finset (Fin N)) {s : State}
    (hsd : src ≠ dst) (hso : src ≠ one) (hod : one ≠ dst)
    (hl : s.arrs src = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hlen : N + 1 < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (appendMarkProg src dst one R) s s' t ∧ t ≤ 55 + 17 * N ∧
      s'.arrs dst = List.ofFn (fun u : Fin (N + 1) => if u ∈ apexFinVerts S then 1 else 0) ∧
      (∀ a, a ≠ dst → a ≠ one → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 11 → r ≠ R + 12 → r ≠ R + 13 → r ≠ R + 14 → s'.regs r = s.regs r) := by
  obtain ⟨s', t, he, ht, ha, haf, hr⟩ := appendMarkProg_exec src dst one R hsd hso hod hl
    (fun x hx => by obtain ⟨u, rfl⟩ := List.mem_ofFn.mp hx; split <;> omega)
    (by simpa only [List.length_ofFn] using hlen) hw
  exact ⟨s', t, he, by simpa only [List.length_ofFn] using ht,
    ha.trans (apex_activeList S).symm, haf, hr⟩

end GraphMinor.Compute.Crossing
