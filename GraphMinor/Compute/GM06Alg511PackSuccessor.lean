module

public import GraphMinor.Compute.GM06SuccessorInput
public import GraphMinor.Compute.Algorithm101Stream
public import GraphMinor.Compute.GM06Alg511CopyRow
import GraphMinor.Compute.GM06Alg511SelectField
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Packing computed successor fields

Each call of VI (5.7) within (5.11), page 134, receives the original
drawing fields and the current computed linkage rows. Pack these
array fields with their length prefixes. The program reads their
actual lengths and words, allocates the exact output length and
copies the completed code to the input array. It retains every
source field and every scalar used by the winding comparison.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Append the source arrays as successive length-prefixed fields. -/
def gm06Alg511PackFieldsProg : List ℕ → Cmd
  | [] => .skip
  | a :: rest => .seq (.assign 1701 (.len a))
      (.seq (appendLengthPrefixedProg a 1600 1701 1700 1800)
        (gm06Alg511PackFieldsProg rest))

/-- Exact space needed for a count word followed by the field arrays. -/
def gm06Alg511PackLengthExpr : List ℕ → Expr
  | [] => .const 1
  | a :: rest => .op .add (.op .add (.const 1) (.len a)) (gm06Alg511PackLengthExpr rest)

/-- Pack the source fields and copy the resulting input code to
array zero. Source arrays must differ from zero and scratch 1600. -/
def gm06Alg511PackSuccessorProg (sources : List ℕ) : Cmd :=
  .seq (.assign 1702 (gm06Alg511PackLengthExpr sources))
    (.seq (.alloc 1600 (.reg 1702))
      (.seq (.write 1600 (.const 0) (.const sources.length))
        (.seq (.assign 1700 (.const 1))
          (.seq (gm06Alg511PackFieldsProg sources) (gm06Alg511CopyRowProg 1600 0)))))

private theorem payload_cons (row : List ℕ) (rows : List (List ℕ)) :
    gm06EncodeRowsPayload (row :: rows) = (row.length :: row) ++ gm06EncodeRowsPayload rows := by
  rfl

private theorem pack_fields_exec {w : ℕ} (sources : List ℕ) (rows : List (List ℕ))
    (hsame : sources.length = rows.length) (hsrc : ∀ a ∈ sources, a ≠ 1600)
    (hw : 1 < 2 ^ w) (hwords : ∀ row ∈ rows, ∀ d ∈ row, d < 2 ^ w)
    (pfx : List ℕ) (cap : ℕ) (s : State)
    (hfit : pfx.length + (gm06EncodeRowsPayload rows).length < 2 ^ w)
    (harr : ∀ i (hi : i < sources.length), s.arrs sources[i] = rows[i]'(by omega))
    (hbuf : IsPrefixBuffer 1600 pfx ((gm06EncodeRowsPayload rows).length + cap) s)
    (hpos : s.regs 1700 = pfx.length) :
    ∃ s' t, Exec w (gm06Alg511PackFieldsProg sources) s s' t ∧
      t ≤ 1 + 31 * (gm06EncodeRowsPayload rows).length ∧
      IsPrefixBuffer 1600 (pfx ++ gm06EncodeRowsPayload rows) cap s' ∧
      s'.regs 1700 = (pfx ++ gm06EncodeRowsPayload rows).length ∧
      (∀ a : ℕ, a ≠ 1600 → s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < 1800 → r ≠ 1700 → r ≠ 1701 → s'.regs r = s.regs r) := by
  induction sources generalizing rows pfx s with
  | nil =>
    have hr : rows = [] := List.eq_nil_of_length_eq_zero (by simpa only [List.length_nil] using hsame.symm)
    subst rows
    exact ⟨s, 1, .skip s, by simp [gm06EncodeRowsPayload],
      by simpa [gm06EncodeRowsPayload] using hbuf,
      by simpa [gm06EncodeRowsPayload] using hpos, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | cons a sources ih =>
    cases rows with
    | nil => simp at hsame
    | cons row rows =>
      have hl : row.length < 2 ^ w := by
        simp only [payload_cons, List.length_append, List.length_cons] at hfit
        omega
      have ha : s.arrs a = row := by
        have hh := harr 0 (by simp)
        change s.arrs a = row at hh
        exact hh
      let s₁ := s.setReg 1701 row.length
      have he₁ : Exec w (.assign 1701 (.len a)) s s₁ 2 := .assign (Crossing.eval_len ha hl)
      obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, _, ha₂, hr₂⟩ :=
        appendLengthPrefixedProg_exec (s := s₁) (pfx := pfx) (chunk := row) (cap := (gm06EncodeRowsPayload rows).length + cap)
          a 1600 1701 1700 1800 (hsrc a (by simp)) (by decide) (by decide) (by decide)
          (hwords row (by simp)) hw (by
            simp only [payload_cons, List.length_append, List.length_cons] at hfit
            omega)
          (by simpa only [s₁, State.setReg_arrs] using ha)
          (by
            have hh : (gm06EncodeRowsPayload (row :: rows)).length + cap =
                1 + row.length + ((gm06EncodeRowsPayload rows).length + cap) := by
              simp only [payload_cons, List.length_append, List.length_cons]
              omega
            simpa only [s₁, State.setReg_arrs, IsPrefixBuffer, hh] using hbuf)
          (by simp [s₁]) (by simpa [s₁] using hpos)
      obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, ha₃, hr₃⟩ := ih rows (by simpa using hsame)
        (fun a ha => hsrc a (by simp [ha])) (fun row hr => hwords row (by simp [hr]))
        (pfx ++ (row.length :: row)) s₂ (by
          simpa only [payload_cons, List.length_append, List.length_cons, Nat.add_assoc] using hfit)
        (by
          intro i hi
          exact (ha₂ _ (hsrc _ (by simp [List.getElem_mem hi]))).trans
            (by
              have hh := harr (i + 1) (by simpa using hi)
              have hirows : i < rows.length := by simp only [List.length_cons] at hsame; omega
              change s.arrs sources[i] = rows[i]'hirows at hh
              simpa only [s₁, State.setReg_arrs] using hh))
        hb₂ hp₂
      refine ⟨s₃, 2 + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [payload_cons, List.length_append, List.length_cons]
        omega
      · simpa only [payload_cons, List.append_assoc] using hb₃
      · simpa only [payload_cons, List.append_assoc] using hp₃
      · intro b hb
        exact (ha₃ b hb).trans (ha₂ b hb)
      · intro r hr h0 h1
        exact (hr₃ r hr h0 h1).trans ((hr₂ r hr h0).trans (State.setReg_regs_ne _ _ h1))

private theorem pack_length_eval {w : ℕ} (sources : List ℕ) (rows : List (List ℕ))
    (hsame : sources.length = rows.length) (s : State)
    (harr : ∀ i (hi : i < sources.length), s.arrs sources[i] = rows[i]'(by omega))
    (hfit : 1 + (gm06EncodeRowsPayload rows).length < 2 ^ w) :
    Expr.eval w s (gm06Alg511PackLengthExpr sources) = some (1 + (gm06EncodeRowsPayload rows).length) := by
  induction sources generalizing rows with
  | nil =>
    have hr : rows = [] := List.eq_nil_of_length_eq_zero (by simpa only [List.length_nil] using hsame.symm)
    subst rows
    simpa only [gm06Alg511PackLengthExpr, gm06EncodeRowsPayload, List.flatMap_nil, List.length_nil, Nat.add_zero] using Crossing.eval_const hfit
  | cons a sources ih =>
    cases rows with
    | nil => simp at hsame
    | cons row rows =>
      have hfit' : 1 + row.length + (1 + (gm06EncodeRowsPayload rows).length) < 2 ^ w := by
        simp only [payload_cons, List.length_append, List.length_cons] at hfit
        omega
      have ha : s.arrs a = row := by
        have hh := harr 0 (by simp)
        change s.arrs a = row at hh
        exact hh
      have ht := ih rows (by simpa using hsame) (fun i hi => by
        have hh := harr (i + 1) (by simpa using hi)
        have hirows : i < rows.length := by simp only [List.length_cons] at hsame; omega
        change s.arrs sources[i] = rows[i]'hirows at hh
        exact hh) (by omega)
      have h := Crossing.eval_add (Crossing.eval_add (Crossing.eval_const (by omega : 1 < 2 ^ w))
        (Crossing.eval_len ha (by omega)) (by omega)) ht hfit'
      simpa only [gm06Alg511PackLengthExpr, payload_cons, List.length_append, List.length_cons,
        Nat.add_assoc] using h

/-- The field packer produces the exact plain code from the actual
source arrays. Its time is linear in the code length. Source fields
and all comparison registers are retained. -/
theorem gm06Alg511PackSuccessorProg_exec {w : ℕ}
    (sources : List ℕ) (rows : List (List ℕ))
    (hsame : sources.length = rows.length)
    (hsrc : ∀ a ∈ sources, a ≠ 0 ∧ a ≠ 1600)
    (s : State) (hw : 1 < 2 ^ w)
    (hfit : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeRows rows, d < 2 ^ w)
    (harr : ∀ i (hi : i < sources.length), s.arrs sources[i] = rows[i]'(by omega)) :
    ∃ s' t, Exec w (gm06Alg511PackSuccessorProg sources) s s' t ∧
      t ≤ 20 + (gm06Alg511PackLengthExpr sources).cost + 44 * (gm06EncodeRows rows).length ∧
      s'.arrs 0 = gm06EncodeRows rows ∧
      (∀ a : ℕ, a ≠ 0 → a ≠ 1600 → s'.arrs a = s.arrs a) ∧
      (∀ (r : ℕ), r < 1700 → r ≠ 20 → s'.regs r = s.regs r) := by
  let N := (gm06EncodeRows rows).length
  have hN : N < 2 ^ w := hfit
  have hNpos : 0 < N := by simp [N, gm06EncodeRows]
  have hpay : N = 1 + (gm06EncodeRowsPayload rows).length := by simp [N, gm06EncodeRows, Nat.add_comm]
  have hcount : sources.length < 2 ^ w := by
    rw [hsame]
    exact hwords _ (by simp [gm06EncodeRows])
  let s₁ := s.setReg 1702 N
  have he₁ : Exec w (.assign 1702 (gm06Alg511PackLengthExpr sources)) s s₁
      ((gm06Alg511PackLengthExpr sources).cost + 1) :=
    .assign (by
      rw [hpay]
      exact pack_length_eval sources rows hsame s harr (by rw [← hpay]; exact hN))
  let s₂ := s₁.setArr 1600 (List.replicate N 0)
  have he₂ : Exec w (.alloc 1600 (.reg 1702)) s₁ s₂ (N + 1) := by
    simpa only [Expr.cost, Nat.add_comm] using
      Exec.alloc (a := 1600) (Crossing.eval_reg (State.setReg_regs_self _ _ _) hN)
  let s₃ := s₂.writeArr 1600 0 sources.length
  have he₃ : Exec w (.write 1600 (.const 0) (.const sources.length)) s₂ s₃ 3 :=
    .write (Crossing.eval_const (Nat.two_pow_pos _)) (Crossing.eval_const hcount) (by simp [s₂]; exact hNpos)
  let s₄ := s₃.setReg 1700 1
  have he₄ : Exec w (.assign 1700 (.const 1)) s₃ s₄ 2 := .assign (Crossing.eval_const hw)
  have hbuf : IsPrefixBuffer 1600 [rows.length] (gm06EncodeRowsPayload rows).length s₄ := by
    change s₄.arrs 1600 = [rows.length] ++ List.replicate (gm06EncodeRowsPayload rows).length 0
    simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr, State.setArr_arrs_self,
      hpay, show 1 + (gm06EncodeRowsPayload rows).length = (gm06EncodeRowsPayload rows).length + 1 by omega, List.replicate_succ, List.set_cons_zero, hsame, List.singleton_append]
  obtain ⟨s₅, t₅, he₅, ht₅, hb₅, _, ha₅, hr₅⟩ := pack_fields_exec sources rows hsame
    (fun a ha => (hsrc a ha).2) hw
    (by
      intro row hm d hd
      exact hwords d (gm06Alg511_mem_encoded_row hm hd))
    [rows.length] 0 s₄ (by simpa only [List.length_singleton, hpay] using hN)
    (by
      intro i hi
      simpa only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr, State.setArr_arrs_ne _ _
        ((hsrc _ (List.getElem_mem hi)).2)] using harr i hi)
    (by simpa only [Nat.add_zero] using hbuf) (by simp [s₄])
  have hcode : s₅.arrs 1600 = gm06EncodeRows rows := by
    simpa only [IsPrefixBuffer, List.replicate_zero, List.append_nil, gm06EncodeRows,
      List.singleton_append] using hb₅
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, hcode₆⟩ := gm06Alg511CopyRowProg_exec 1600 0 (by decide)
    (gm06EncodeRows rows) s₅ hw hfit hwords hcode
  refine ⟨s₆, (gm06Alg511PackLengthExpr sources).cost + 1 + (N + 1 + (3 + (2 + (t₅ + t₆)))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆)))), ?_, hcode₆, ?_, ?_⟩
  · dsimp only [N] at hpay ⊢
    omega
  · intro a ha0 ha1600
    rw [hk₆.2 a (by simpa using ha0), ha₅ a ha1600]
    simp only [s₄, s₃, s₂, s₁, State.setReg_arrs, State.writeArr, State.setArr_arrs_ne _ _ ha1600]
  · intro r hr h20
    rw [hk₆.1 r (by simpa using h20), hr₅ r (by omega) (by omega) (by omega)]
    simp [s₄, s₃, s₂, s₁, show r ≠ 1700 by omega, show r ≠ 1702 by omega]

/-- Packing the six fields of an actual successor input produces
exactly its supplied-input format. The fixed field count gives a
linear bound with a constant independent of the graph and linkage. -/
theorem gm06Alg511PackSuccessorInput_exec {w : ℕ} (x : GM06SuccessorInput)
    (source : Fin 6 → ℕ) (hsource : ∀ i, source i ≠ 0 ∧ source i ≠ 1600)
    (s : State) (hw : 1 < 2 ^ w)
    (hfit : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeSuccessorInput x, d < 2 ^ w)
    (hfields : ∀ i : Fin 6,
      s.arrs (source i) = (gm06SuccessorRows x)[i.val]'(by simp [gm06SuccessorRows])) :
    ∃ s' t, Exec w (gm06Alg511PackSuccessorProg (List.ofFn source)) s s' t ∧
      t ≤ 45 + 44 * (gm06EncodeSuccessorInput x).length ∧
      s'.arrs 0 = gm06EncodeSuccessorInput x ∧
      (∀ a : ℕ, a ≠ 0 → a ≠ 1600 → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 1700 → r ≠ 20 → s'.regs r = s.regs r) := by
  have hsrc : ∀ a ∈ List.ofFn source, a ≠ 0 ∧ a ≠ 1600 := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hsource i
  have hcost : (gm06Alg511PackLengthExpr (List.ofFn source)).cost = 25 := by
    simp [gm06Alg511PackLengthExpr, List.ofFn_succ, Expr.cost]
  obtain ⟨s', t, he, ht, hout, ha, hr⟩ := gm06Alg511PackSuccessorProg_exec
    (List.ofFn source) (gm06SuccessorRows x) (by simp [gm06SuccessorRows]) hsrc s hw hfit hwords
    (by
      intro i hi
      have hi6 : i < 6 := by simpa only [List.length_ofFn] using hi
      simpa only [List.getElem_ofFn] using hfields ⟨i, hi6⟩)
  exact ⟨s', t, he, by rw [hcost] at ht; exact ht, hout, ha, hr⟩

end GraphMinor.Compute
