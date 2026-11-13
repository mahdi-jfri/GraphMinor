module

public import GraphMinor.Compute.Basic

/-!
# Array length charged to RAM time

Allocation pays for every allocated word, and writes preserve length.
Consequently a supplied member program starting with an empty output
cannot return more words than its running time. This also pays for the
subsequent copying of a returned wall.
-/

public section

namespace GraphMinor.Compute

/-- An array can grow by at most the execution time. -/
theorem case3Exec_array_length_le_time {w : ℕ} {P : Cmd} {s s' : State} {t : ℕ}
    (hex : Exec w P s s' t) (a : ℕ) :
    (s'.arrs a).length ≤ (s.arrs a).length + t := by
  induction hex with
  | skip => omega
  | assign => simp only [State.setReg_arrs]; omega
  | @write b idx val st j v hi hv hb =>
    by_cases ha : a = b
    · subst b
      simp only [State.writeArr_arrs_self, List.length_set]
      omega
    · rw [State.writeArr_arrs_ne _ _ _ ha]
      omega
  | @alloc b len st m hm =>
    by_cases ha : a = b
    · subst b
      simp only [State.setArr_arrs_self, List.length_replicate]
      omega
    · rw [State.setArr_arrs_ne _ _ ha]
      omega
  | seq _ _ ih₁ ih₂ => omega
  | ite_true _ _ _ ih => omega
  | ite_false _ _ ih => omega
  | while_false => omega
  | while_true _ _ _ _ ih₁ ih₂ => omega

end GraphMinor.Compute
