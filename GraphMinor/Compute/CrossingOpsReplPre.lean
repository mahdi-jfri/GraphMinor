module

public import GraphMinor.Compute.CrossingOpsReplMark

/-!
# Preparing a replacement

The first phase copies the instance, stores its number of vertices, marks the deleted and
boundary vertices, concatenates the recorded component and boundary, and marks that union.
All input arrays are preserved.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Copy the instance and prepare the three membership arrays and recorded-vertex array. -/
def replPreProg (a : InstArrs) (a_del a_bd a_rep A R : ℕ) : Cmd :=
  .seq (copyInstanceProg a (bArrs A) (R + 15))
    (.seq (.assign (R + 8) (.len (A + 5)))
      (.seq (markArrayProg a_del (A + 3) R)
        (.seq (markArrayProg a_bd (A + 9) R)
          (.seq (.assign (R + 11) (.reg (R + 8)))
            (.seq (concatProg a_rep a_bd (A + 11) (R + 11) (R + 12) (R + 13) (R + 14))
              (markArrayProg (A + 11) (A + 10) R))))))

local macro "pre_simp" : tactic => `(tactic| simp [markArrayProg, writeAllProg,
  forArrProg, forUp, concatProg, copyAtProg, Cmd.writtenArrs, Cmd.writtenRegs])

/-- The preparation copies the instance and produces the required marks and union array.
The input lists are distinct-vertex lists below `N`; no graph operation is performed yet. -/
theorem replPreProg_exec {w N : ℕ} (a : InstArrs) (a_del a_bd a_rep A R : ℕ)
    (hok : ArrsOk a.list A) (hdelA : a_del < A) (hbdA : a_bd < A) (hrepA : a_rep < A)
    {G : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {dl bl rep : List ℕ} {s : State}
    (hinst : IsInstanceAt a G S D s) (hDN : D.length ≤ N)
    (hdel : s.arrs a_del = dl) (hbd : s.arrs a_bd = bl) (hrep : s.arrs a_rep = rep)
    (hdnd : dl.Nodup) (hbnd : bl.Nodup) (hrnd : rep.Nodup)
    (hdlt : ∀ x ∈ dl, x < N) (hblt : ∀ x ∈ bl, x < N) (hrlt : ∀ x ∈ rep, x < N)
    (hw : 10 * instSize N G < 2 ^ w) :
    ∃ s' t, Exec w (replPreProg a a_del a_bd a_rep A R) s s' t ∧
      t ≤ 300 * instSize N G ∧ IsInstanceAt (bArrs A) G S D s' ∧
      s'.regs (R + 8) = N ∧
      s'.arrs (A + 3) = setAt (List.replicate N 0) dl 1 ∧
      s'.arrs (A + 9) = setAt (List.replicate N 0) bl 1 ∧
      s'.arrs (A + 11) = rep ++ bl ∧
      s'.arrs (A + 10) = setAt (List.replicate N 0) (rep ++ bl) 1 ∧
      (∀ x, x < A → s'.arrs x = s.arrs x) := by
  have hsz : instSize N G = N + G.edgeSet.ncard + 1 := rfl
  have hdlen := length_le_of_nodup_lt hdnd hdlt
  have hblen := length_le_of_nodup_lt hbnd hblt
  have hrlen := length_le_of_nodup_lt hrnd hrlt
  have hok' : ArrsOk (a.list ++ (bArrs A).list) (A + 7) := by
    constructor
    · rw [List.nodup_append]
      refine ⟨hok.1, by simp [bArrs, InstArrs.list] <;> omega, ?_⟩
      intro x hx y hy
      have := hok.2 x hx
      simp [bArrs, InstArrs.list] at hy
      omega
    · intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · have := hok.2 x hx; omega
      · simp [bArrs, InstArrs.list] at hx; omega
  obtain ⟨s1, t1, hex1, ht1, hf1, hi1⟩ := copyInstanceProg_exec (w := w) a (bArrs A) (A + 7) (R + 15)
    hok' hinst hDN (by omega)
  have ha1 : ∀ x, x < A → s1.arrs x = s.arrs x := by
    intro x hx
    exact hf1.2 x (by omega) (by simp [bArrs, InstArrs.list]; omega)
  let s2 := s1.setReg (R + 8) N
  have hlen : (s1.arrs (A + 5)).length = N := by
    have h := hi1.2.1
    change s1.arrs (A + 5) = _ at h
    simp [h]
  have hex2 : Exec w (.assign (R + 8) (.len (A + 5))) s1 s2 2 :=
    .assign (by simpa only [hlen] using eval_len (w := w) (a := A + 5) (s := s1) rfl (by omega))
  obtain ⟨s3, t3, hex3, ht3, hm3, ha3, hr3⟩ := markArrayProg_exec (w := w)
    a_del (A + 3) R (s := s2) (by omega) ((ha1 a_del hdelA).trans hdel) (by simp [s2]) hdlt
    (by omega) (by omega) (by omega)
  have hN3 : s3.regs (R + 8) = N := by
    rw [hr3 (R + 8) (by omega) (by omega) (by omega)]; simp [s2]
  obtain ⟨s4, t4, hex4, ht4, hm4, ha4, hr4⟩ := markArrayProg_exec (w := w)
    a_bd (A + 9) R (by omega)
    ((ha3 a_bd (by omega)).trans ((ha1 a_bd hbdA).trans hbd)) hN3 hblt
    (by omega) (by omega) (by omega)
  have hN4 : s4.regs (R + 8) = N :=
    (hr4 (R + 8) (by omega) (by omega) (by omega)).trans hN3
  let s5 := s4.setReg (R + 11) N
  have hex5 : Exec w (.assign (R + 11) (.reg (R + 8))) s4 s5 2 := .assign (eval_reg hN4 (by omega))
  have hrep5 : s5.arrs a_rep = rep := (ha4 a_rep (by omega)).trans
    ((ha3 a_rep (by omega)).trans ((ha1 a_rep hrepA).trans hrep))
  have hbd5 : s5.arrs a_bd = bl := (ha4 a_bd (by omega)).trans
    ((ha3 a_bd (by omega)).trans ((ha1 a_bd hbdA).trans hbd))
  obtain ⟨s6, t6, hex6, ht6, hcat6, ha6, hr6⟩ := concatProg_exec (w := w)
    a_rep a_bd (A + 11) (R + 11) (R + 12) (R + 13) (R + 14) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (s := s5) (B := N) (by simp [s5]) (by omega) (by omega) (by rw [hrep5, hbd5]; omega)
  have hcat : s6.arrs (A + 11) = rep ++ bl := by
    rw [hcat6, hrep5, hbd5]
    exact map_min_of_le (fun x hx => by
      rcases List.mem_append.mp hx with hx | hx
      · exact (hrlt x hx).le
      · exact (hblt x hx).le)
  have hN6 : s6.regs (R + 8) = N := by
    rw [hr6 (R + 8) (by omega) (by omega) (by omega)]
    simpa [s5] using hN4
  obtain ⟨s7, t7, hex7, ht7, hm7, ha7, hr7⟩ := markArrayProg_exec (w := w)
    (A + 11) (A + 10) R (by omega) hcat hN6
    (fun x hx => by rcases List.mem_append.mp hx with hx | hx; exact hrlt x hx; exact hblt x hx)
    (by simp only [List.length_append]; omega) (by omega) (by omega)
  have htail : Exec w
      (.seq (.assign (R + 8) (.len (A + 5)))
        (.seq (markArrayProg a_del (A + 3) R) (.seq (markArrayProg a_bd (A + 9) R)
          (.seq (.assign (R + 11) (.reg (R + 8)))
            (.seq (concatProg a_rep a_bd (A + 11) (R + 11) (R + 12) (R + 13) (R + 14))
              (markArrayProg (A + 11) (A + 10) R)))))) s1 s7 (2 + (t3 + (t4 + (2 + (t6 + t7))))) :=
    .seq hex2 (.seq hex3 (.seq hex4 (.seq hex5 (.seq hex6 hex7))))
  refine ⟨s7, _, .seq hex1 htail, ?_, ?_, ?_, ?_, ?_, ?_, hm7, ?_⟩
  · rw [hrep5, hbd5] at ht6
    simp only [List.length_append] at ht7
    omega
  · apply hi1.of_arrs_eq
    intro x hx
    exact htail.arrs_eq_of_not_mem_writtenArrs (by
      simp only [bArrs, InstArrs.list, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;> pre_simp)
  · exact (hr7 (R + 8) (by omega) (by omega) (by omega)).trans hN6
  · rw [ha7 (A + 3) (by omega), ha6 (A + 3) (by omega)]
    change s4.arrs (A + 3) = _
    rw [ha4 (A + 3) (by omega)]; exact hm3
  · rw [ha7 (A + 9) (by omega), ha6 (A + 9) (by omega)]
    exact hm4
  · rw [ha7 (A + 11) (by omega)]; exact hcat
  · intro x hx
    rw [htail.arrs_eq_of_not_mem_writtenArrs (by pre_simp <;> dsimp only [Arr, Reg] at * <;> omega)]
    exact ha1 x hx

end GraphMinor.Compute.Crossing
