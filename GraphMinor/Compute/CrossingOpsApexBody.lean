module

public import GraphMinor.Compute.CrossingOpsApexSize
public import GraphMinor.Compute.CrossingOpsFilter
public import GraphMinor.Compute.CrossingOpsReplEnc
public import GraphMinor.Compute.CrossingOpsReplFilter

/-!
# Emitting one apex adjacency list

For an old vertex, the program copies its old neighbours and appends the apex index
when the vertex belongs to the cycle. For the final vertex it emits the cycle list.
The original vertex count is stored separately from the new count.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Emit the apex list of the vertex in `R`, with the old count in `R+9`. -/
def apexBody (a_D a_mark A buf R : ℕ) : Cmd :=
  .ite (.op .lt (.reg R) (.reg (R + 9)))
    (.seq (filterListProg A (A + 1) (A + 2) buf R (.const 1))
      (.ite (.read a_mark (.reg R)) (emitProg buf (R + 4) (.reg (R + 9))) .skip))
    (emitArrayProg a_D buf R)

/-- A single body emits exactly the numerical apex list, in linear time in its input list. -/
theorem apexBody_exec {w N : ℕ} (a_D a_mark A buf R : ℕ)
    {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ} {D : List (Fin N)}
    {pre : List ℕ} {s : State} {x k : ℕ}
    (hent : A + 2 ≠ buf) (hDne : a_D ≠ buf) (hmne : a_mark ≠ buf)
    (hadj : IsAdjList G A (A + 1) (A + 2) lists s)
    (hD : s.arrs a_D = D.map Fin.val) (hDnd : D.Nodup)
    (hm : s.arrs a_mark = setAt (List.replicate N 0) (D.map Fin.val) 1)
    (hx : s.regs R = x) (hxN : x < N + 1) (hN : s.regs (R + 9) = N)
    (hb : IsBuf buf (R + 4) pre k s) (hk : (apexList lists D x).length ≤ k)
    (hw : N + (s.arrs (A + 2)).length + pre.length + k + 2 < 2 ^ w) :
    ∃ s' t, Exec w (apexBody a_D a_mark A buf R) s s' t ∧
      t ≤ 25 + 18 * (if x < N then (listOf lists x).length else D.length) ∧
      IsBuf buf (R + 4) (pre ++ apexList lists D x) (k - (apexList lists D x).length) s' ∧
      (∀ a, a ≠ buf → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ R + 1 → r ≠ R + 2 → r ≠ R + 3 → r ≠ R + 4 →
        r ≠ R + 5 → r ≠ R + 6 → s'.regs r = s.regs r) := by
  have hc := eval_lt (eval_reg hx (by omega)) (eval_reg hN (by omega)) (show 1 < 2 ^ w by omega)
  have hrun : ∃ s' t, Exec w (apexBody a_D a_mark A buf R) s s' t ∧
      t ≤ 25 + 18 * (if x < N then (listOf lists x).length else D.length) ∧
      IsBuf buf (R + 4) (pre ++ apexList lists D x) (k - (apexList lists D x).length) s' := by
    by_cases hxl : x < N
    · obtain ⟨st, en, hl⟩ := hadj.1.2.2 ⟨x, hxl⟩
      have hll : IsListAt A (A + 1) (A + 2) x st en (listOf lists x) s := by
        simpa only [listOf, dif_pos hxl] using hl
      have hlenlo : (listOf lists x).length = (lists ⟨x, hxl⟩).length := by
        simp only [listOf, dif_pos hxl]
      have hkeep : ((listOf lists x).filter (fun _ => true)).length ≤ k := by
        simp only [List.filter_true]
        have hh := hk
        simp only [apexList, hxl, dite_true, List.length_append] at hh
        omega
      obtain ⟨s1, t1, he1, ht1, hb1, ha1, hr1⟩ := filterListProg_exec (w := w)
        A (A + 1) (A + 2) buf R (.const 1) (fun _ => true) hent hll hx hb hkeep
        (fun y hy => by have hh := (hadj.2 ⟨x, hxl⟩).1 y (by simpa [listOf, hxl] using hy); omega)
        (by omega) (by have hh := hl.2.2.1; omega) (by omega) (by omega)
        (fun _ _ _ _ _ _ => eval_const (by omega))
      simp only [List.filter_true] at hb1
      have hroot : s1.regs R = x := (hr1 R (by omega) (by omega) (by omega) (by omega)).trans hx
      have hsize : s1.regs (R + 9) = N :=
        (hr1 (R + 9) (by omega) (by omega) (by omega) (by omega)).trans hN
      have htest := eval_membershipMark a_mark R ((ha1 _ hmne).trans hm) hroot hxl
        (show N < 2 ^ w by omega) (show 1 < 2 ^ w by omega)
      have hmem : x ∈ D.map Fin.val ↔ (⟨x, hxl⟩ : Fin N) ∈ D := by
        simp only [List.mem_map]
        constructor
        · rintro ⟨v, hv, he⟩
          have hh : v = ⟨x, hxl⟩ := Fin.ext he
          exact hh ▸ hv
        · intro hh; exact ⟨⟨x, hxl⟩, hh, rfl⟩
      by_cases hxd : (⟨x, hxl⟩ : Fin N) ∈ D
      · have htest1 : (Expr.read a_mark (.reg R)).eval w s1 = some 1 := by
          simpa only [hmem, hxd, ite_true] using htest
        have hk1 : k - (listOf lists x).length = (k - (listOf lists x).length - 1) + 1 := by
          simp only [apexList, hxl, dite_true, hxd, ite_true, List.length_append, List.length_singleton] at hk
          omega
        obtain ⟨s2, he2, hb2, -, -⟩ := emitReg_exec (w := w) buf (R + 4) (R + 9)
          (by rw [← hk1]; exact hb1) hsize (by omega) (by
            simp only [List.length_append]; omega)
        refine ⟨s2, 3 + (t1 + (2 + 7)), .ite_true (by simpa [hxl] using hc) (by decide)
          (.seq he1 (.ite_true htest1 (by decide) he2)), ?_, ?_⟩
        · simp only [Expr.cost] at ht1; simp only [hxl, ite_true]; omega
        · simpa only [apexList, hxl, dite_true, hxd, ite_true, listOf, dif_pos hxl,
            List.append_assoc, List.length_append, List.length_singleton, Nat.sub_sub] using hb2
      · have htest0 : (Expr.read a_mark (.reg R)).eval w s1 = some 0 := by
          simpa only [hmem, hxd, ite_false] using htest
        refine ⟨s1, 3 + (t1 + 3), .ite_true (by simpa [hxl] using hc) (by decide)
          (.seq he1 (.ite_false htest0 (.skip s1))), ?_, ?_⟩
        · simp only [Expr.cost] at ht1; simp only [hxl, ite_true]; omega
        · simpa only [apexList, hxl, dite_true, hxd, ite_false, List.append_nil,
            listOf, dif_pos hxl] using hb1
    · have heq : x = N := by omega
      have hlen : D.length ≤ N := by simpa using hDnd.length_le_card
      obtain ⟨s1, t1, he1, ht1, hb1, -, -⟩ := emitArrayProg_exec (w := w) a_D buf R hDne hD hb
        (by simpa [apexList, hxl, heq] using hk)
        (fun y hy => by obtain ⟨v, -, rfl⟩ := List.mem_map.mp hy; have := v.isLt; omega)
        (by simp only [List.length_map]; omega) (by omega)
      refine ⟨s1, 3 + t1, .ite_false (by simpa [hxl] using hc) he1, ?_, ?_⟩
      · simp only [hxl, ite_false, List.length_map] at ht1 ⊢; omega
      · simpa [apexList, hxl, heq] using hb1
  obtain ⟨s', t, he, ht, hb'⟩ := hrun
  refine ⟨s', t, he, ht, hb', ?_, ?_⟩
  · intro a hh
    exact he.arrs_eq_of_not_mem_writtenArrs (by
      simp [apexBody, filterListProg, emitWhenProg, emitArrayProg, forArrProg, forList,
        forUp, emitProg, Cmd.writtenArrs, hh])
  · intro r h1 h2 h3 h4 h5 h6
    exact he.regs_eq_of_not_mem_writtenRegs (by
      simp [apexBody, filterListProg, emitWhenProg, emitArrayProg, forArrProg, forList,
        forUp, emitProg, Cmd.writtenRegs, h1, h2, h3, h4, h5, h6])

end GraphMinor.Compute.Crossing
