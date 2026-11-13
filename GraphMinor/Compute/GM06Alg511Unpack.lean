module

public import GraphMinor.Compute.GM06UnpackRows
public import GraphMinor.Compute.GM06Alg511Input
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Loading the finite instance of VI (5.11)

The nine length-prefixed fields are read from the input array into
arrays 2 through 10. The read cursor begins after the row count and
finishes at the end of the input. Each work array contains exactly
its supplied field. The program takes linear time in the input size.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Load the nine fields of a feasibility instance into arrays 2 through 10. -/
def gm06Alg511UnpackProg : Cmd :=
  .seq (.assign 8 (.const 1)) (gm06UnpackRowsProg 0 2 9)

/-- The nine input fields are loaded exactly, preserving the source array. -/
theorem gm06Alg511UnpackProg_exec {w : ℕ} (x : GM06Alg511Input) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 0 = gm06Alg511Words x)
    (hn : (gm06Alg511Words x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511Words x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511UnpackProg s s' t ∧
      t ≤ 3 + 22 * (gm06Alg511Words x).length ∧
      (∀ j : Fin 9, s'.arrs (2 + j.val) =
        (gm06Alg511Rows x)[j.val]'(by simp [gm06Alg511Rows])) ∧
      s'.regs 8 = (gm06Alg511Words x).length ∧
      s'.arrs 0 = s.arrs 0 := by
  let s₁ := s.setReg 8 1
  have hrows : (gm06Alg511Rows x).length = 9 := rfl
  have hcode : gm06Alg511Words x =
      [9] ++ gm06EncodeRowsPayload (gm06Alg511Rows x) ++ [] := by
    simp only [gm06Alg511Words, gm06EncodeRows, hrows, List.singleton_append,
      List.append_nil]
  have hlength : (gm06Alg511Words x).length =
      1 + (gm06EncodeRowsPayload (gm06Alg511Rows x)).length := by
    rw [hcode]
    simp
    omega
  obtain ⟨s', t, he, ht, hf, hc, _, har⟩ := gm06UnpackRowsProg_exec 0 2 (by decide)
    (gm06Alg511Rows x) [9] [] s₁ hw
    (by simpa only [s₁, State.setReg_arrs, ha] using hcode)
    (by simpa only [s₁, State.setReg_arrs, ha] using hn)
    (by simpa only [s₁, State.setReg_arrs, ha] using hwords)
    (by simp [s₁])
  refine ⟨s', 2 + t, .seq (.assign (GraphMinor.Compute.Crossing.eval_const hw)) he,
    ?_, ?_, ?_, ?_⟩
  · omega
  · intro j
    exact hf j.val (by simpa only [hrows] using j.isLt)
  · simpa only [List.length_singleton, hlength] using hc
  · simpa only [s₁, State.setReg_arrs] using har 0 (Or.inl (by decide))

end GraphMinor.Compute
