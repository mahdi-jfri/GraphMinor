module

public import GraphMinor.Compute.Case3StepsAttachmentKeyAccess

/-!
# Comparing a boundary-key word on the RAM

Each comparison reads one word of a selected component key and one word of
the target key. Row-major indices and key entries fit the common word bound.
Four such comparisons suffice to test equality of the attachment sets.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Compare one slot of the selected component key to the target key. -/
def case3KeyWordEqExpr (a_keys a_target r_seed : ℕ) (j : Fin 4) : Expr :=
  .op .eq
    (.read a_keys (.op .add (.op .mul (.reg r_seed) (.const 4)) (.const j.1)))
    (.read a_target (.const j.1))

private theorem keyWord_lt {n w : ℕ} (S : Finset (Fin n)) (hS : S.card ≤ 3)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (j : Fin 4) :
    (case3BoundaryKey S).getD j.1 0 < 2 ^ w := by
  have hj : j.1 < (case3BoundaryKey S).length := by rw [case3BoundaryKey_length S hS]; exact j.2
  rw [List.getD_eq_getElem _ 0 hj]
  exact case3BoundaryKey_words S hS hw hn _ (List.getElem_mem hj)

/-- A key-slot comparison returns its exact Boolean indicator. -/
theorem case3KeyWordEqExpr_eval {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (bd : Finset (Fin x.n)) (hbd : bd.card ≤ 3) (u : Fin x.n) (j : Fin 4)
    (a_keys a_target r_seed : ℕ) (hw : 4 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) {s : State}
    (htab : s.arrs a_keys = case3AttachmentKeys x d.core.Z)
    (htarget : s.arrs a_target = case3BoundaryKey bd) (hseed : s.regs r_seed = u.1) :
    (case3KeyWordEqExpr a_keys a_target r_seed j).eval w s =
      some (if (case3BoundaryKey (case3AttachmentRowSet x d.core.Z u)).getD j.1 0 =
        (case3BoundaryKey bd).getD j.1 0 then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hn
  have hjw : j.1 < 2 ^ w := j.2.trans hw
  have hmulw : u.1 * 4 < 2 ^ w := by omega
  have hoffw : u.1 * 4 + j.1 < 2 ^ w := by omega
  have htablen : (s.arrs a_keys).length = x.n * 4 := by
    rw [htab]
    have hp := case3AttachmentKeys_prefix_length x d hd x.n le_rfl
    rw [List.take_of_length_le (by simp only [List.length_finRange]; exact le_rfl)] at hp
    exact hp
  have hidx : u.1 * 4 + j.1 < (s.arrs a_keys).length := by rw [htablen]; omega
  have htidx : j.1 < (s.arrs a_target).length := by
    rw [htarget, case3BoundaryKey_length bd hbd]
    exact j.2
  have hsrc : (s.arrs a_keys)[u.1 * 4 + j.1]'hidx =
      (case3BoundaryKey (case3AttachmentRowSet x d.core.Z u)).getD j.1 0 := by
    rw [← List.getD_eq_getElem _ 0 hidx, htab, case3AttachmentKeys_getD x d hd u j]
  have htgt : (s.arrs a_target)[j.1]'htidx = (case3BoundaryKey bd).getD j.1 0 := by
    rw [← List.getD_eq_getElem _ 0 htidx, htarget]
  have hsrcw := keyWord_lt _ (case3AttachmentRowSet_card_le_three x d hd u) hw hn j
  have htgtw := keyWord_lt bd hbd hw hn j
  simp only [List.getD_eq_getElem?_getD] at hsrcw htgtw
  by_cases heq : (case3BoundaryKey (case3AttachmentRowSet x d.core.Z u)).getD j.1 0 =
      (case3BoundaryKey bd).getD j.1 0 <;>
    simp only [List.getD_eq_getElem?_getD] at heq <;>
    simp [case3KeyWordEqExpr, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hseed, huw, hjw, hw, hmulw, hoffw, hidx, htidx, hsrc, htgt, hsrcw, htgtw, heq, h0, h1]

/-- Compare all four words of a component key with a target key. -/
def case3BoundaryEqExpr (a_keys a_target r_seed : ℕ) : Expr :=
  .op .mul (case3KeyWordEqExpr a_keys a_target r_seed 0)
    (.op .mul (case3KeyWordEqExpr a_keys a_target r_seed 1)
      (.op .mul (case3KeyWordEqExpr a_keys a_target r_seed 2)
        (case3KeyWordEqExpr a_keys a_target r_seed 3)))

private theorem mulIndicators_eval {w : ℕ} {s : State} (e f : Expr)
    (P Q : Prop) [Decidable P] [Decidable Q] (hw : 1 < 2 ^ w)
    (he : e.eval w s = some (if P then 1 else 0))
    (hf : f.eval w s = some (if Q then 1 else 0)) :
    (Expr.op .mul e f).eval w s = some (if P ∧ Q then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  by_cases hP : P <;> by_cases hQ : Q <;>
    simp [Expr.eval, he, hf, BinOp.eval, BinOp.raw, checkWord, hP, hQ, hw, h0]

/-- The four comparisons together test equality of the attachment sets. -/
theorem case3BoundaryEqExpr_eval {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (bd : Finset (Fin x.n)) (hbd : bd.card ≤ 3) (u : Fin x.n)
    (a_keys a_target r_seed : ℕ) (hw : 4 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) {s : State}
    (htab : s.arrs a_keys = case3AttachmentKeys x d.core.Z)
    (htarget : s.arrs a_target = case3BoundaryKey bd) (hseed : s.regs r_seed = u.1) :
    (case3BoundaryEqExpr a_keys a_target r_seed).eval w s =
      some (if case3AttachmentRowSet x d.core.Z u = bd then 1 else 0) := by
  classical
  let P (j : Fin 4) : Prop :=
    (case3BoundaryKey (case3AttachmentRowSet x d.core.Z u)).getD j.1 0 =
      (case3BoundaryKey bd).getD j.1 0
  let e := case3KeyWordEqExpr a_keys a_target r_seed
  have he : ∀ j, (e j).eval w s = some (if P j then 1 else 0) := fun j =>
    case3KeyWordEqExpr_eval x d hd bd hbd u j a_keys a_target r_seed hw hn hkeys htab htarget hseed
  have hw1 : 1 < 2 ^ w := by omega
  have h23 := mulIndicators_eval (e 2) (e 3) (P 2) (P 3) hw1 (he 2) (he 3)
  have h123 := mulIndicators_eval (e 1) (.op .mul (e 2) (e 3)) (P 1) (P 2 ∧ P 3) hw1 (he 1) h23
  have h0123 := mulIndicators_eval (e 0) (.op .mul (e 1) (.op .mul (e 2) (e 3)))
    (P 0) (P 1 ∧ P 2 ∧ P 3) hw1 (he 0) h123
  have hforall : (P 0 ∧ P 1 ∧ P 2 ∧ P 3) ↔ ∀ j, P j := by
    constructor
    · rintro ⟨h0, h1, h2, h3⟩ j
      fin_cases j
      · exact h0
      · exact h1
      · exact h2
      · exact h3
    · intro h
      exact ⟨h 0, h 1, h 2, h 3⟩
  have heq : (∀ j, P j) ↔ case3AttachmentRowSet x d.core.Z u = bd := by
    have h := case3AttachmentKeys_words_eq_iff x d hd u bd hbd
    simpa only [P, case3AttachmentKeys_getD x d hd u] using h
  simpa only [case3BoundaryEqExpr, e, hforall, heq] using h0123

/-- A matching seed must lie outside the core and have the target boundary. -/
def case3BoundaryMatchExpr (a_Z a_keys a_target r_seed : ℕ) : Expr :=
  .op .mul (.op .eq (.read a_Z (.reg r_seed)) (.const 0))
    (case3BoundaryEqExpr a_keys a_target r_seed)

/-- The matching test ignores core rows and compares exactly the attachment
set of an outside component. -/
theorem case3BoundaryMatchExpr_eval {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (bd : Finset (Fin x.n)) (hbd : bd.card ≤ 3) (u : Fin x.n)
    (a_Z a_keys a_target r_seed : ℕ) (hw : 4 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) {s : State} (hZ : IsBitSet d.core.Z a_Z s)
    (htab : s.arrs a_keys = case3AttachmentKeys x d.core.Z)
    (htarget : s.arrs a_target = case3BoundaryKey bd) (hseed : s.regs r_seed = u.1) :
    (case3BoundaryMatchExpr a_Z a_keys a_target r_seed).eval w s =
      some (if u ∉ d.core.Z ∧ case3AttachmentRowSet x d.core.Z u = bd then 1 else 0) := by
  classical
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hn
  have hidx : u.1 < (s.arrs a_Z).length := by rw [hZ.1]; exact u.2
  have hbit : (s.arrs a_Z)[u.1]'hidx = if u ∈ d.core.Z then 1 else 0 := by
    simpa only [hZ.arr_eq_bitSetList] using getElem_bitSetList d.core.Z u.1 u.2
  have hcore : (Expr.op .eq (.read a_Z (.reg r_seed)) (.const 0)).eval w s =
      some (if u ∉ d.core.Z then 1 else 0) := by
    by_cases hu : u ∈ d.core.Z <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hseed, huw, hidx, hbit, hu, h0, h1]
  exact mulIndicators_eval _ _ _ _ h1 hcore
    (case3BoundaryEqExpr_eval x d hd bd hbd u a_keys a_target r_seed hw hn hkeys htab htarget hseed)

end GraphMinor.Compute
