module

public import GraphMinor.Compute.Basic

/-!
# Array bounds preserved by checked RAM execution

Writes retain array length and store checked words. Allocations use a checked
length and initialize zeroes. An initially bounded array therefore retains
both its length bound and its word bounds through any execution. Clearing an
output array before a supplied program lets its result use these bounds.
-/

public section

namespace GraphMinor.Compute

/-- Every array remains shorter than the word range when it starts so: writes
preserve length and allocations check their length word. -/
theorem case3Exec_array_length_lt {w : ℕ} {P : Cmd} {s s' : State} {t : ℕ}
    (hex : Exec w P s s' t) (a : ℕ) (hlen : (s.arrs a).length < 2 ^ w) :
    (s'.arrs a).length < 2 ^ w := by
  induction hex with
  | skip => exact hlen
  | assign => exact hlen
  | @write b idx val st j v hi hv hb =>
    by_cases ha : a = b
    · subst b
      simpa only [State.writeArr_arrs_self, List.length_set] using hlen
    · simpa only [State.writeArr_arrs_ne _ _ _ ha] using hlen
  | @alloc b len st m hm =>
    by_cases ha : a = b
    · subst b
      simpa only [State.setArr_arrs_self, List.length_replicate] using Expr.eval_lt hm
    · simpa only [State.setArr_arrs_ne _ _ ha] using hlen
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hlen)
  | ite_true _ _ _ ih => exact ih hlen
  | ite_false _ _ ih => exact ih hlen
  | while_false => exact hlen
  | while_true _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hlen)

/-- An array whose words fit the word range retains that property through
checked RAM execution. -/
theorem case3Exec_array_words_lt {w : ℕ} {P : Cmd} {s s' : State} {t : ℕ}
    (hex : Exec w P s s' t) (a : ℕ) (hwords : ∀ z ∈ s.arrs a, z < 2 ^ w) :
    ∀ z ∈ s'.arrs a, z < 2 ^ w := by
  induction hex with
  | skip => exact hwords
  | assign => exact hwords
  | @write b idx val st j v hi hv hb =>
    by_cases ha : a = b
    · subst b
      intro z hz
      rw [State.writeArr_arrs_self] at hz
      rcases List.mem_or_eq_of_mem_set hz with hz | rfl
      · exact hwords z hz
      · exact Expr.eval_lt hv
    · simpa only [State.writeArr_arrs_ne _ _ _ ha] using hwords
  | @alloc b len st m hm =>
    by_cases ha : a = b
    · subst b
      intro z hz
      rw [State.setArr_arrs_self] at hz
      have hz0 := (List.mem_replicate.mp hz).2
      subst z
      exact Nat.two_pow_pos _
    · simpa only [State.setArr_arrs_ne _ _ ha] using hwords
  | seq _ _ ih₁ ih₂ => exact ih₂ (ih₁ hwords)
  | ite_true _ _ _ ih => exact ih hwords
  | ite_false _ _ ih => exact ih hwords
  | while_false => exact hwords
  | while_true _ _ _ _ ih₁ ih₂ => exact ih₂ (ih₁ hwords)

end GraphMinor.Compute
