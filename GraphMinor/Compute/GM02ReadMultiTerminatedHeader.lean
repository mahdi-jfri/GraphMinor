module

public import GraphMinor.Compute.GM02MultiTerminatedEncoding
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Locating the termination suffix after the original multigraph

Read the active-pair header, skip its triples, and read the supplied
terminal index. Compute the suffix length including that index. The
program never reads an edge-multiplicity word, and its eighteen-step
execution preserves every input array.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read the original termination suffix offset into 40 and its word count into 41. -/
def gm02ReadMultiTerminatedHeaderProg (src : Arr) : Cmd :=
  .seq (.assign 40 (.read src (.const 1)))
    (.seq (.assign 40 (.op .add (.const 2) (.op .mul (.const 3) (.reg 40))))
      (.seq (.assign 41 (.read src (.reg 40)))
        (.assign 41 (.op .add (.const 1) (.op .mul (.const 2) (.reg 41))))))

private theorem read_of_word {w i v : ℕ} {src : Arr} {s : State} {idx : Expr}
    (hi : idx.eval w s = some i) (hv : (s.arrs src)[i]? = some v) (hvw : v < 2 ^ w) :
    (Expr.read src idx).eval w s = some v := by
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.1 hv
  simpa only [hget] using eval_read hi hidx (hget ▸ hvw)

/-- Suffix metadata is computed from the original plain input without inspecting multiplicities. -/
theorem gm02ReadMultiTerminatedHeaderProg_exec {w : ℕ} (x : GM02MultiTerminatedInput)
    (src : Arr) (s : State) (hsrc : s.arrs src = x.enc) (hw : 3 < 2 ^ w)
    (hlen : x.enc.length < 2 ^ w) :
    ∃ s', Exec w (gm02ReadMultiTerminatedHeaderProg src) s s' 18 ∧
      s'.regs 40 = 2 + 3 * x.G.numActivePairs ∧ s'.regs 41 = 1 + 2 * x.A.index ∧
      s'.arrs = s.arrs ∧ (∀ r, r ≠ 40 → r ≠ 41 → s'.regs r = s.regs r) := by
  have hlength := x.enc_length
  have hm : x.G.numActivePairs < 2 ^ w := by omega
  have h3m : 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hoff : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hk : x.A.index < 2 ^ w := by omega
  have h2k : 2 * x.A.index < 2 ^ w := by omega
  have hcount : 1 + 2 * x.A.index < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  let s₁ := s.setReg 40 x.G.numActivePairs
  have he₁ : Exec w (.assign 40 (.read src (.const 1))) s s₁ 3 :=
    Exec.assign (read_of_word (eval_const h1) (by simpa only [hsrc] using x.enc_one) hm)
  let s₂ := s₁.setReg 40 (2 + 3 * x.G.numActivePairs)
  have he₂ : Exec w (.assign 40 (.op .add (.const 2) (.op .mul (.const 3) (.reg 40)))) s₁ s₂ 6 :=
    Exec.assign (eval_add (eval_const h2) (eval_mul (eval_const hw) (eval_reg (by simp [s₁]) hm) h3m) hoff)
  let s₃ := s₂.setReg 41 x.A.index
  have he₃ : Exec w (.assign 41 (.read src (.reg 40))) s₂ s₃ 3 :=
    Exec.assign (read_of_word (eval_reg (by simp [s₂]) hoff)
      (by simpa only [s₂, s₁, State.setReg_arrs, hsrc] using x.enc_index) hk)
  let s₄ := s₃.setReg 41 (1 + 2 * x.A.index)
  have he₄ : Exec w (.assign 41 (.op .add (.const 1) (.op .mul (.const 2) (.reg 41)))) s₃ s₄ 6 :=
    Exec.assign (eval_add (eval_const h1) (eval_mul (eval_const h2) (eval_reg (by simp [s₃]) hk) h2k) hcount)
  refine ⟨s₄, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), ?_, by simp [s₄], rfl, ?_⟩
  · simp [s₄, s₃, s₂]
  · intro r hr40 hr41
    simp only [s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr40, State.setReg_regs_ne _ _ hr41]

end GraphMinor.Compute
