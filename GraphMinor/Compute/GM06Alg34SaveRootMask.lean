module

public import GraphMinor.Compute.GM06Alg34VertexRootMaskProg
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Retaining component roots during branch construction

Copy the computed root mask into the parent's reserved array. The
induced payload builder may reuse its scratch root array afterwards,
while the branch scan still has the original canonical root flags.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Save component root flags in array 40 before building branch inputs. -/
def gm06SaveRootMaskProg : Cmd := readSliceProg 36 (.const 0) 40 (.reg 4) 5100

/-- Copying the component-root mask takes linear time and preserves all
other arrays and all registers below the copy scratch area. -/
theorem gm06SaveRootMaskProg_exec {w : ℕ} (x : GM06DrawingData)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (hmask : s.arrs 36 = gm06VertexRootMask x) (hsize : s.regs 4 = x.n) :
    ∃ s' t, Exec w gm06SaveRootMaskProg s s' t ∧ t ≤ 16 * x.n + 9 ∧
      s'.arrs 40 = gm06VertexRootMask x ∧
      (∀ A : ℕ, A ≠ 40 → s'.arrs A = s.arrs A) ∧
      (∀ q < 5100, s'.regs q = s.regs q) := by
  have hlen : (gm06VertexRootMask x).length = x.n := by simp only [gm06VertexRootMask, List.length_ofFn]
  have hb : ∀ v ∈ gm06VertexRootMask x, v < 2 ^ w := by
    intro v hv
    obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hv
    cases x.isComponentRoot a
    · exact Nat.zero_lt_of_lt hw
    · exact hw
  obtain ⟨s', t, hex, ht, hout, ha, hg⟩ :=
    readSliceProg_exec 36 40 (.const 0) 4 5100 (by decide) (by decide)
      [] (gm06VertexRootMask x) [] rfl rfl hb hw
      (by simpa only [List.length_nil, Nat.zero_add, hlen] using hn)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
      (by simpa only [List.nil_append, List.append_nil] using hmask)
      (by simpa only [hlen] using hsize)
  exact ⟨s', t, hex, by simpa only [Expr.cost, hlen] using ht, hout, ha, hg⟩

end GraphMinor.Compute
