module

public import GraphMinor.Compute.Algorithm101Stream
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Writing the header of the dual payload

Primal regions become dual vertices, primal edges keep their slots,
and primal vertices become dual regions. Copy the three prepared
counts to the output buffer in that order. The program leaves the
counts and all input arrays unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Append the dual vertex, edge and region counts. -/
def gm06DualHeaderProg : Cmd :=
  .seq (appendWordProg 55 7804 (.reg 102))
    (.seq (appendWordProg 55 7804 (.reg 101)) (appendWordProg 55 7804 (.reg 100)))

/-- The three dual header words are copied exactly in constant time. -/
theorem gm06DualHeaderProg_exec {w n m r cap : ℕ} {pre : List ℕ} {s : State}
    (hw : 1 < 2 ^ w) (hnw : n < 2 ^ w) (hmw : m < 2 ^ w) (hrw : r < 2 ^ w)
    (hn : s.regs 100 = n) (hm : s.regs 101 = m) (hr : s.regs 102 = r)
    (hbuf : IsPrefixBuffer 55 pre (3 + cap) s) (hpos : s.regs 7804 = pre.length)
    (hfit : pre.length + 3 < 2 ^ w) :
    ∃ s' t, Exec w gm06DualHeaderProg s s' t ∧ t ≤ 30 ∧
      IsPrefixBuffer 55 (pre ++ [r, m, n]) cap s' ∧
      s'.regs 7804 = (pre ++ [r, m, n]).length ∧
      (∀ A : ℕ, A ≠ 55 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 7804 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    appendWordProg_exec (cap := 2 + cap) (val := r) 55 7804 (.reg 102) hw (by omega)
      (by have heq : 3 + cap = (2 + cap) + 1 := by omega
          exact heq ▸ hbuf) hpos (GraphMinor.Compute.Crossing.eval_reg hr hrw)
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    appendWordProg_exec (cap := 1 + cap) (val := m) 55 7804 (.reg 101) hw
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by have heq : 2 + cap = (1 + cap) + 1 := by omega
          exact heq ▸ hb₁) hp₁
      (GraphMinor.Compute.Crossing.eval_reg ((hg₁ 101 (by decide)).trans hm) hmw)
  obtain ⟨s₃, t₃, he₃, ht₃, hb₃, hp₃, ha₃, hg₃⟩ :=
    appendWordProg_exec (cap := cap) (val := n) 55 7804 (.reg 100) hw
      (by simp only [List.length_append, List.length_singleton]; omega)
      (by simpa only [Nat.add_comm 1] using hb₂) hp₂
      (GraphMinor.Compute.Crossing.eval_reg ((hg₂ 100 (by decide)).trans
        ((hg₁ 100 (by decide)).trans hn)) hnw)
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht₁ ht₂ ht₃
    omega
  · simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hb₃
  · simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using hp₃
  · intro A hA
    exact (ha₃ A hA).trans ((ha₂ A hA).trans (ha₁ A hA))
  · intro q hq
    exact (hg₃ q hq).trans ((hg₂ q hq).trans (hg₁ q hq))

end GraphMinor.Compute
