module

public import GraphMinor.Compute.GM06Alg34VertexBfs
public import GraphMinor.Compute.GM06Alg34VertexMask
public import GraphMinor.Compute.GM06Alg34ComponentInputs
public import GraphMinor.Compute.Algorithm101Stream

/-!
# Copying component marks into the branch vertex mask

The searched component's visited array is already its characteristic
function on supplied labels. Copy it into the retained-mask array used
by the induced payload builder. This selects the component itself for
a branch of VI (3.3)(iv).
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Copy the component marks into retained-mask array 4. -/
def gm06ComponentMaskProg : Cmd := readSliceProg 33 (.const 0) 4 (.reg 4) 264

/-- The copied marks are exactly the retained-label mask of the searched
component, in linear time with all other arrays preserved. -/
theorem gm06ComponentMaskProg_exec {w : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (hmarks : s.arrs 33 = gm06VertexReachData x a) (hsize : s.regs 4 = x.n) :
    ∃ s' t, Exec w gm06ComponentMaskProg s s' t ∧ t ≤ 16 * x.n + 9 ∧
      s'.arrs 4 = gm06VertexMask (x.componentVertices a) ∧
      (∀ A : ℕ, A ≠ 4 → s'.arrs A = s.arrs A) ∧
      (∀ q < 264, s'.regs q = s.regs q) := by
  have hlen : (gm06VertexReachData x a).length = x.n := by
    simp only [gm06VertexReachData, List.length_ofFn]
  have hb : ∀ v ∈ gm06VertexReachData x a, v < 2 ^ w := by
    intro v hv
    obtain ⟨b, rfl⟩ := List.mem_ofFn.mp hv
    split
    · exact hw
    · exact Nat.zero_lt_of_lt hw
  obtain ⟨s', t, hex, ht, hout, ha, hg⟩ :=
    readSliceProg_exec 33 4 (.const 0) 4 264 (by decide) (by decide)
      [] (gm06VertexReachData x a) [] rfl rfl hb hw
      (by simpa only [List.length_nil, Nat.zero_add, hlen] using hn)
      (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
      (by simpa only [List.nil_append, List.append_nil] using hmarks)
      (by simpa only [hlen] using hsize)
  refine ⟨s', t, hex, by simpa only [Expr.cost, hlen] using ht, ?_, ha, hg⟩
  rw [hout]
  unfold gm06VertexReachData gm06VertexMask
  congr 1
  funext b
  simp only [x.mem_componentVertices_iff]

end GraphMinor.Compute
