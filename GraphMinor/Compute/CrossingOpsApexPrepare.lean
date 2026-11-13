module

public import GraphMinor.Compute.CrossingOpsApexRebuild
public import GraphMinor.Compute.CrossingOpsApexActive
public import GraphMinor.Compute.CrossingOpsReplMark

/-!
# Preparing the entire apex search input

The program reads the old size, marks the cycle vertices, and computes the new size.
It builds the numerical apex CSR arrays and appends the active apex mark. All arrays
below the source block remain unchanged.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Prepare the apex graph and active marks in a fresh block. -/
def apexPrepareProg (a_D A B R : ℕ) : Cmd :=
  .seq (.assign (R + 8) (.len (A + 6)))
    (.seq (.assign (R + 9) (.reg (R + 8)))
      (.seq (markArrayProg a_D (A + 3) R)
        (.seq (.assign (R + 8) (.op .add (.reg (R + 9)) (.const 1)))
          (.seq (apexRebuildProg a_D A B R)
            (appendMarkProg (A + 6) (B + 6) (B + 7) R)))))

/-- Complete apex preparation reads its sizes from memory and yields a valid input for
BFS. It assumes only the old CSR encoding, active marks, distinct cycle vertices, and
the word bound. -/
theorem apexPrepareProg_exec {w N : ℕ} (a_D A B R : ℕ)
    {G : SimpleGraph (Fin N)} (S : Finset (Fin N)) {lists : Fin N → List ℕ}
    {D : List (Fin N)} {s : State} (hDA : a_D < A) (hAB : A + 7 ≤ B)
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hentries : (s.arrs (A + 2)).length = 2 * G.edgeSet.ncard)
    (hD : s.arrs a_D = D.map Fin.val) (hDnd : D.Nodup)
    (hactive : s.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0))
    (hw : 10 * (N + G.edgeSet.ncard + 1) < 2 ^ w) :
    ∃ s' t, Exec w (apexPrepareProg a_D A B R) s s' t ∧
      t ≤ 300 * (N + G.edgeSet.ncard + 1) ∧
      IsAdjList (apexFinGraph G D) B (B + 1) (B + 2) (fun u => apexList lists D u.val) s' ∧
      (s'.arrs (B + 2)).length = 2 * (apexFinGraph G D).edgeSet.ncard ∧
      s'.arrs (B + 6) = List.ofFn (fun u : Fin (N + 1) => if u ∈ apexFinVerts S then 1 else 0) ∧
      (∀ a, a < A → s'.arrs a = s.arrs a) := by
  have hDlen : D.length ≤ N := by simpa using hDnd.length_le_card
  let s1 := s.setReg (R + 8) N
  let s2 := s1.setReg (R + 9) N
  have he1 : Exec w (.assign (R + 8) (.len (A + 6))) s s1 2 :=
    .assign (by simp [Expr.eval, checkWord, hactive, show N < 2 ^ w by omega])
  have he2 : Exec w (.assign (R + 9) (.reg (R + 8))) s1 s2 2 :=
    .assign (eval_reg (by simp [s1]) (by omega))
  obtain ⟨s3, t3, he3, ht3, hm3, ha3, hr3⟩ := markArrayProg_exec (w := w) (N := N)
    a_D (A + 3) R (s := s2) (l := D.map Fin.val) (by omega) hD (by simp [s2, s1])
    (fun x hx => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hx; exact v.isLt)
    (by simp only [List.length_map]; omega) (by omega) (by omega)
  have hr9 : s3.regs (R + 9) = N :=
    (hr3 _ (by omega) (by omega) (by omega)).trans (by simp [s2])
  let s4 := s3.setReg (R + 8) (N + 1)
  have he4 : Exec w (.assign (R + 8) (.op .add (.reg (R + 9)) (.const 1))) s3 s4 4 :=
    .assign (eval_add (eval_reg hr9 (by omega)) (eval_const (by omega)) (by omega))
  have ha4 : ∀ a, a ≠ A + 3 → s4.arrs a = s.arrs a := fun a hh => ha3 a hh
  have hadj4 := hadj.of_arrs_eq (ha4 _ (by omega)) (ha4 _ (by omega)) (ha4 _ (by omega))
  have hent4 : (s4.arrs (A + 2)).length = 2 * G.edgeSet.ncard := by
    rw [ha4 _ (by omega)]; exact hentries
  obtain ⟨s5, t5, he5, ht5, hadj5, hent5, ha5⟩ := apexRebuildProg_exec (w := w)
    a_D A B R hDA hAB hadj4 hent4 ((ha4 _ (by omega)).trans hD) hDnd hm3
    (by simp [s4]) (by simp [s4, hr9]) (by omega)
  have hal5 : s5.arrs (A + 6) = List.ofFn (fun u : Fin N => if u ∈ S then 1 else 0) :=
    (ha5 _ (by omega) (by omega) (by omega) (by omega)).trans ((ha4 _ (by omega)).trans hactive)
  obtain ⟨s6, t6, he6, ht6, hal6, ha6, hr6⟩ := apexActiveProg_exec (w := w)
    (A + 6) (B + 6) (B + 7) R S (by omega) (by omega) (by omega) hal5 (by omega) (by omega)
  refine ⟨s6, _, .seq he1 (.seq he2 (.seq he3 (.seq he4 (.seq he5 he6)))),
    by simp only [List.length_map] at ht3; omega, ?_, ?_, hal6, ?_⟩
  · exact hadj5.of_arrs_eq (ha6 _ (by omega) (by omega))
      (ha6 _ (by omega) (by omega)) (ha6 _ (by omega) (by omega))
  · rw [ha6 _ (by omega) (by omega)]; exact hent5
  · intro a hh
    exact (ha6 a (by omega) (by omega)).trans
      ((ha5 a (by omega) (by omega) (by omega) (by omega)).trans (ha4 a (by omega)))

end GraphMinor.Compute.Crossing
