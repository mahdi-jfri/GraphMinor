module

public import GraphMinor.Compute.Case3StepsBoundaryMembership
public import GraphMinor.Compute.Case3StepsBoolExpr

/-!
# A constant-size RAM test for boundary membership

Each slot is tested only when the key's size word marks it as occupied.
Combining the three guarded tests gives the exact boundary-membership bit,
including boundaries containing vertex zero.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Test whether one occupied slot holds the selected vertex. -/
def case3BoundarySlotExpr (a_key r_v : ℕ) (j : Fin 3) : Expr :=
  case3AndExpr (.op .lt (.const j.1) (.read a_key (.const 0)))
    (.op .eq (.read a_key (.const (j.1 + 1))) (.reg r_v))

/-- Test all three possible boundary slots. -/
def case3BoundaryContainsExpr (a_key r_v : ℕ) : Expr :=
  case3OrExpr (case3BoundarySlotExpr a_key r_v 0)
    (case3OrExpr (case3BoundarySlotExpr a_key r_v 1) (case3BoundarySlotExpr a_key r_v 2))

/-- An occupied-slot expression computes the exact guarded comparison. -/
theorem case3BoundarySlotExpr_eval {n w : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (v : Fin n) (j : Fin 3) (a_key r_v : ℕ) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    {s : State} (hkey : s.arrs a_key = case3BoundaryKey S) (hrv : s.regs r_v = v.1) :
    (case3BoundarySlotExpr a_key r_v j).eval w s =
      some (if j.1 < S.card ∧ (case3BoundaryKey S).getD (j.1 + 1) 0 = v.1 then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hjw : j.1 < 2 ^ w := by have := j.2; omega
  have hj1w : j.1 + 1 < 2 ^ w := by have := j.2; omega
  have hvw : v.1 < 2 ^ w := v.2.trans hn
  have hcw : S.card < 2 ^ w := by omega
  have hlen : (s.arrs a_key).length = 4 := by rw [hkey, case3BoundaryKey_length S hS]
  have hi0 : 0 < (s.arrs a_key).length := by omega
  have hij : j.1 + 1 < (s.arrs a_key).length := by rw [hlen]; have := j.2; omega
  have hget0 : (s.arrs a_key)[0]'hi0 = S.card := by
    rw [← List.getD_eq_getElem _ 0 hi0, hkey, case3BoundaryKey_getD_zero]
  have hgetj : (s.arrs a_key)[j.1 + 1]'hij = (case3BoundaryKey S).getD (j.1 + 1) 0 := by
    rw [← List.getD_eq_getElem _ 0 hij, hkey]
  have hslotw := case3BoundaryKey_getD_lt S hS hw hn (j.1 + 1)
  have hhead : (Expr.read a_key (.const 0)).eval w s = some S.card := by
    simp only [Expr.eval, checkWord, h0, ↓reduceIte, hi0, hget0, hcw, ↓reduceDIte]
  have hslot : (Expr.read a_key (.const (j.1 + 1))).eval w s =
      some ((case3BoundaryKey S).getD (j.1 + 1) 0) := by
    simp only [Expr.eval, checkWord, hj1w, ↓reduceIte, hij, hgetj, hslotw, ↓reduceDIte]
  have hindex : (Expr.const j.1).eval w s = some j.1 := by
    simp only [Expr.eval, checkWord, hjw, ↓reduceIte]
  have hvert : (Expr.reg r_v).eval w s = some v.1 := by
    simp only [Expr.eval, checkWord, hrv, hvw, ↓reduceIte]
  have hguard := case3LtExpr_eval (.const j.1) (.read a_key (.const 0)) h1 hindex hhead
  have hvalue := case3EqExpr_eval (.read a_key (.const (j.1 + 1))) (.reg r_v) h1 hslot hvert
  exact case3AndExpr_eval _ _ _ _ h1 hguard hvalue

/-- The complete expression returns one exactly for vertices in the boundary. -/
theorem case3BoundaryContainsExpr_eval {n w : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (v : Fin n) (a_key r_v : ℕ) (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    {s : State} (hkey : s.arrs a_key = case3BoundaryKey S) (hrv : s.regs r_v = v.1) :
    (case3BoundaryContainsExpr a_key r_v).eval w s = some (if v ∈ S then 1 else 0) := by
  let P (j : Fin 3) : Prop := j.1 < S.card ∧ (case3BoundaryKey S).getD (j.1 + 1) 0 = v.1
  let e := case3BoundarySlotExpr a_key r_v
  have he : ∀ j, (e j).eval w s = some (if P j then 1 else 0) := fun j =>
    case3BoundarySlotExpr_eval S hS v j a_key r_v hw hn hkey hrv
  have hw2 : 2 < 2 ^ w := by omega
  have h12 := case3OrExpr_eval (e 1) (e 2) (P 1) (P 2) hw2 (he 1) (he 2)
  have h012 := case3OrExpr_eval (e 0) (case3OrExpr (e 1) (e 2)) (P 0) (P 1 ∨ P 2) hw2 (he 0) h12
  have hmem : (P 0 ∨ P 1 ∨ P 2) ↔ v ∈ S := (case3BoundaryKey_mem_iff_three_slots S hS v).symm
  simpa only [case3BoundaryContainsExpr, e, hmem] using h012

/-- The boundary test has constant expression cost. -/
theorem case3BoundaryContainsExpr_cost (a_key r_v : ℕ) :
    (case3BoundaryContainsExpr a_key r_v).cost = 33 := rfl

end GraphMinor.Compute
