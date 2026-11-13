module

public import GraphMinor.Compute.GM06Alg34BlockBody
public import GraphMinor.Compute.GM06Alg34SplitBlock

/-!
# The RAM test for one counted division block

An empty block meets no two components. For a nonempty block, read
its first label and test the rest against that label's component.
This consumes precisely the supplied block and returns the complement
of the split-block test used for rejection in VI (3.3)(iii).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Test whether the counted block at cursor 103 lies in one component. -/
def gm06BlockTestProg : Cmd :=
  .ite (.reg 108) gm06BlockBodyProg (.assign 112 (.const 1))

/-- The block test consumes exactly the supplied labels and returns one
exactly when the block does not meet two graph components. -/
theorem gm06BlockTestProg_exec {w off : ℕ} (x : GM06DrawingData)
    (L : List (Fin x.n)) (tail : List ℕ) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) (hend : off + L.length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n)
    (hs : AtStream 0 off (L.map Fin.val ++ tail) s)
    (hp : s.regs 103 = off) (hcount : s.regs 108 = L.length) :
    ∃ s' t, Exec w gm06BlockTestProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 44 ∧
      s'.regs 112 = (if !x.isSplitBlock L then 1 else 0) ∧
      s'.regs 103 = off + L.length ∧ AtStream 0 (off + L.length) tail s' ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 → q ≠ 187 →
        s'.regs q = s.regs q) := by
  cases L with
  | nil =>
    have hc : (Expr.reg 108).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hcount, Nat.zero_lt_of_lt hw]
    let s' := s.setReg 112 1
    have hex : Exec w gm06BlockTestProg s s' 3 :=
      .ite_false hc (.assign (by simp [Expr.eval, checkWord, hw]))
    refine ⟨s', 3, hex, by omega, by simp [s', GM06DrawingData.isSplitBlock],
      by simpa [s'] using hp, by simpa using hs.of_arr_eq (s' := s') rfl,
      fun _ _ _ => rfl, ?_⟩
    intro q _ _ _ _ h112 _
    exact State.setReg_regs_ne _ _ h112
  | cons a L =>
    obtain ⟨s', t, hex, ht, hans, hp', hs', ha, hg⟩ :=
      gm06BlockBodyProg_exec x a L tail hw hn hsquare
        (by simp only [List.length_cons] at hend; omega)
        hsize hlists hlen hs hp (by simpa only [List.length_cons] using hcount)
    have hc : (Expr.reg 108).eval w s = some (L.length + 1) := by
      have hh : L.length + 1 < 2 ^ w := by simp only [List.length_cons] at hend; omega
      simp [Expr.eval, checkWord, hcount, hh]
    refine ⟨s', 1 + t, .ite_true hc (Nat.succ_ne_zero _) hex,
      by simp only [List.length_cons]; omega, ?_, ?_, ?_, ha, hg⟩
    · simpa only [x.isSplitBlock_cons, Bool.not_not] using hans
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 L.length] using hp'
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 L.length] using hs'

end GraphMinor.Compute
