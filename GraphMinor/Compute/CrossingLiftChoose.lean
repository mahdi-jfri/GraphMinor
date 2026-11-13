module

public import GraphMinor.Compute.CrossingLiftFind

/-!
# Choosing an old endpoint for an incident path edge

In Section 11 the lift keeps `v` when the old graph joins `v` to the next path vertex.
Otherwise it uses `u`. The contraction encoding holds the neighbours of `v`, so the
choice is a scan of that list. It does not search the graph.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Choose `r_v` when `r_y` occurs in `neighbours`, and `r_u` otherwise. The choice is written
in `r_out`. Registers starting at `R` are scratch registers. -/
def liftChooseProg (neighbours r_u r_v r_y r_out R : ℕ) : Cmd :=
  .seq (liftFindVertexProg neighbours r_y R (R + 1))
    (.ite (.op .lt (.reg R) (.len neighbours))
      (.assign r_out (.reg r_v)) (.assign r_out (.reg r_u)))

/-- The endpoint choice from Section 11 costs linear time in the recorded neighbour list.
Only the output register and scratch registers change. -/
theorem liftChooseProg_exec {w : ℕ} (neighbours r_u r_v r_y r_out R : ℕ)
    (huR : r_u < R) (hvR : r_v < R) (hyR : r_y < R)
    (Nv : List ℕ) (u v y : ℕ) (s : State)
    (hNv : s.arrs neighbours = Nv) (hnd : Nv.Nodup)
    (hu : s.regs r_u = u) (hv : s.regs r_v = v) (hy : s.regs r_y = y)
    (hwords : ∀ x ∈ Nv, x < 2 ^ w) (huw : u < 2 ^ w) (hvw : v < 2 ^ w)
    (hyw : y < 2 ^ w) (hw : Nv.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (liftChooseProg neighbours r_u r_v r_y r_out R) s s' t ∧
      t ≤ 16 * (Nv.length + 1) + 5 ∧
      s'.regs r_out = (if y ∈ Nv then v else u) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r < R, r ≠ r_out → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s1, t1, he1, ht1, hp1, ha1, hr1⟩ := liftFindVertexProg_exec
    neighbours r_y R (R + 1) (by omega) (by omega) (by omega)
    Nv y s hNv hy hnd hwords hyw hw
  have hc := eval_lt (eval_reg hp1 (Nat.lt_of_le_of_lt List.idxOf_le_length (by omega)))
    (eval_len ((ha1 neighbours).trans hNv) (by omega)) hw1
  have hu1 : s1.regs r_u = u := (hr1 r_u (by omega) (by omega)).trans hu
  have hv1 : s1.regs r_v = v := (hr1 r_v (by omega) (by omega)).trans hv
  by_cases hym : y ∈ Nv
  · have hlt : Nv.idxOf y < Nv.length := List.idxOf_lt_length_iff.mpr hym
    have hcond : (Expr.op .lt (.reg R) (.len neighbours)).eval w s1 = some 1 := by
      simpa only [hlt, ↓reduceIte] using hc
    refine ⟨s1.setReg r_out v, t1 + 5,
      .seq he1 (.ite_true hcond (by omega) (.assign (eval_reg hv1 hvw))), by omega,
      by simp [hym], ha1, ?_⟩
    intro r hr hro
    simp only [State.setReg_regs_ne _ _ hro]
    exact hr1 r (by omega) (by omega)
  · have hlt : ¬ Nv.idxOf y < Nv.length := by
      rw [List.idxOf_eq_length hym]; omega
    have hcond : (Expr.op .lt (.reg R) (.len neighbours)).eval w s1 = some 0 := by
      simpa only [hlt, ↓reduceIte] using hc
    refine ⟨s1.setReg r_out u, t1 + 5,
      .seq he1 (.ite_false hcond (.assign (eval_reg hu1 huw))), by omega,
      by simp [hym], ha1, ?_⟩
    intro r hr hro
    simp only [State.setReg_regs_ne _ _ hro]
    exact hr1 r (by omega) (by omega)

end GraphMinor.Compute.Crossing
