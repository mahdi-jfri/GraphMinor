module

public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.GM13SocietyInput
public import GraphMinor.Compute.Algorithm86Aux1

/-!
# Scanning serialized division records

A division member record stores its vertex bits, followed by its vertex and
edge counts and its simple edge list. The next record address is therefore
determined by its edge count. Skipping a member takes constant time,
independently of the number of its edges.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Advance register 20 past the member record at its current address.
Register zero holds n. Register 23 is scratch. -/
def gm13SkipRecordProg : Cmd :=
  .seq (.assign 23 (.read 65 (.op .add (.op .add (.reg 20) (.reg 0)) (.const 1))))
    (.assign 20 (.op .add (.op .add (.reg 20) (.reg 0))
      (.op .add (.const 2) (.op .mul (.const 2) (.reg 23)))))

/-- A member record can be skipped without reading any of its edge entries. -/
theorem gm13SkipRecordProg_exec {w n : ℕ} (A : Finset (Fin n) × List (Fin n × Fin n))
    (pre suf : List ℕ) (hw : (pre ++ encAlg86Subgraph A.1 A.2).length < 2 ^ w)
    {s : State} (hin : s.arrs 65 = pre ++ encAlg86Subgraph A.1 A.2 ++ suf)
    (hoff : s.regs 20 = pre.length) (hn : s.regs 0 = n) :
    ∃ s', Exec w gm13SkipRecordProg s s' 17 ∧
      s'.regs 20 = (pre ++ encAlg86Subgraph A.1 A.2).length ∧
      s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ 20 → r ≠ 23 → s'.regs r = s.regs r) := by
  have hlen : (pre ++ encAlg86Subgraph A.1 A.2).length =
      pre.length + (n + 2 + 2 * A.2.length) := by
    rw [List.length_append, length_encAlg86Subgraph]
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  have hpw : pre.length < 2 ^ w := by omega
  have hmw : A.2.length < 2 ^ w := by omega
  have haddr : pre.length + n + 1 < 2 ^ w := by omega
  have hget : (s.arrs 65)[pre.length + n + 1]? = some A.2.length := by
    have hsrc : s.arrs 65 = (pre ++ bitSetList A.1 ++ [n]) ++
        A.2.length :: (flatEdges A.2 ++ suf) := by
      simpa only [encAlg86Subgraph, List.append_assoc, List.cons_append,
        List.nil_append] using hin
    obtain ⟨hi, hv⟩ := getElem_of_eq_append_cons hsrc
    have hp : (pre ++ bitSetList A.1 ++ [n]).length = pre.length + n + 1 := by
      simp only [List.length_append, length_bitSetList, List.length_cons, List.length_nil]
    simpa only [hp] using (List.getElem?_eq_some_iff.mpr ⟨hi, hv⟩)
  have hidx := eval_add (eval_add (eval_reg hoff hpw) (eval_reg hn hnw) (by omega))
    (eval_const hw1) haddr
  let s₁ := s.setReg 23 A.2.length
  have he₁ : Exec w (.assign 23 (.read 65
      (.op .add (.op .add (.reg 20) (.reg 0)) (.const 1)))) s s₁ 7 :=
    .assign (gm13_read_eval hidx hget hmw)
  let s₂ := s₁.setReg 20 (pre ++ encAlg86Subgraph A.1 A.2).length
  have he₂ : Exec w (.assign 20 (.op .add (.op .add (.reg 20) (.reg 0))
      (.op .add (.const 2) (.op .mul (.const 2) (.reg 23))))) s₁ s₂ 10 := by
    apply Exec.assign
    have hp : (Expr.reg 20).eval w s₁ = some pre.length :=
      eval_reg (by simpa [s₁] using hoff) hpw
    have hn' : (Expr.reg 0).eval w s₁ = some n :=
      eval_reg (by simpa [s₁] using hn) hnw
    have hm : (Expr.reg 23).eval w s₁ = some A.2.length := eval_reg (by simp [s₁]) hmw
    have he := eval_add (eval_add hp hn' (by omega))
      (eval_add (eval_const hw2) (eval_mul (eval_const hw2) hm (by omega)) (by omega))
      (show pre.length + n + (2 + 2 * A.2.length) < 2 ^ w by omega)
    simpa only [hlen, Nat.add_assoc] using he
  refine ⟨s₂, .seq he₁ he₂, by simp [s₂], rfl, ?_⟩
  intro r hr20 hr23
  simp [s₂, s₁, hr20, hr23]

/-- Skip the given number of member records. Register 21 is the count and
register 22 the current index. -/
def gm13SkipRecordsLoop : Cmd := forUp 22 (.reg 21) gm13SkipRecordProg

/-- Scanning a list of member records costs constant time per record. -/
theorem gm13SkipRecordsLoop_exec {w n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (pre suf : List ℕ)
    (k N : ℕ) (hN : k + L.length = N) (hNw : N < 2 ^ w)
    (hw : (pre ++ L.flatMap (fun A => encAlg86Subgraph A.1 A.2)).length < 2 ^ w)
    {s : State} (hin : s.arrs 65 = pre ++ L.flatMap (fun A => encAlg86Subgraph A.1 A.2) ++ suf)
    (hoff : s.regs 20 = pre.length) (hn : s.regs 0 = n)
    (hcount : s.regs 21 = N) (hk : s.regs 22 = k) (hw1 : 1 < 2 ^ w) :
    ∃ s' t, Exec w gm13SkipRecordsLoop s s' t ∧ t ≤ 24 * L.length + 3 ∧
      s'.regs 20 = (pre ++ L.flatMap (fun A => encAlg86Subgraph A.1 A.2)).length ∧
      s'.arrs = s.arrs ∧
      (∀ r : ℕ, r ≠ 20 → r ≠ 22 → r ≠ 23 → s'.regs r = s.regs r) := by
  induction L generalizing pre k s with
  | nil =>
    have hkn : k = N := by simpa using hN
    have htest : (Expr.op .lt (.reg 22) (.reg 21)).eval w s = some 0 := by
      simpa [hkn] using eval_lt (eval_reg hk (by omega)) (eval_reg hcount hNw) hw1
    exact ⟨s, 3, .while_false htest, by simp, by simpa using hoff, rfl,
      fun _ _ _ _ => rfl⟩
  | cons A rest ih =>
    have hkN : k < N := by simp only [List.length_cons] at hN; omega
    have htest : (Expr.op .lt (.reg 22) (.reg 21)).eval w s = some 1 := by
      simpa [hkN] using eval_lt (eval_reg hk (by omega)) (eval_reg hcount hNw) hw1
    have hrec : (pre ++ encAlg86Subgraph A.1 A.2).length < 2 ^ w := by
      simp only [List.flatMap_cons, List.length_append] at hw ⊢
      omega
    obtain ⟨s₁, he₁, hoff₁, ha₁, hr₁⟩ := gm13SkipRecordProg_exec (w := w) A pre
      (rest.flatMap (fun A => encAlg86Subgraph A.1 A.2) ++ suf) hrec
      (by simpa only [List.flatMap_cons, List.append_assoc] using hin) hoff hn
    let s₂ := s₁.setReg 22 (k + 1)
    have he₂ : Exec w (.assign 22 (.op .add (.reg 22) (.const 1))) s₁ s₂ 4 :=
      .assign (eval_add (eval_reg ((hr₁ 22 (by decide) (by decide)).trans hk) (by omega))
        (eval_const hw1) (by omega))
    obtain ⟨s₃, t₃, he₃, ht₃, hoff₃, ha₃, hr₃⟩ := ih
      (pre ++ encAlg86Subgraph A.1 A.2) (k + 1) (by simp only [List.length_cons] at hN; omega)
      (by simpa only [List.flatMap_cons, List.append_assoc] using hw)
      (s := s₂) (by simpa [s₂, ha₁, List.flatMap_cons, List.append_assoc] using hin)
      (by simpa [s₂] using hoff₁)
      (by simpa [s₂] using (hr₁ 0 (by decide) (by decide)).trans hn)
      (by simpa [s₂] using (hr₁ 21 (by decide) (by decide)).trans hcount)
      (by simp [s₂])
    refine ⟨s₃, 3 + (17 + 4) + t₃, .while_true htest (by decide) (.seq he₁ he₂) he₃,
      by simp only [List.length_cons]; omega, ?_, ha₃.trans ha₁, ?_⟩
    · simpa only [List.flatMap_cons, List.append_assoc] using hoff₃
    · intro r hr20 hr22 hr23
      rw [hr₃ r hr20 hr22 hr23]
      simpa [s₂, hr22] using hr₁ r hr20 hr23

end GraphMinor.Compute
