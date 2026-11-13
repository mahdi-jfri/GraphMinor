module

public import GraphMinor.Compute.GM02TerminatedEncoding
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading the graph and termination headers

The internal routines receive only a plain terminated graph encoding.
Read the vertex count and graph-edge count, locate the terminal index,
and calculate the endpoint slice's start and length. These are exactly
the registers needed by the terminal-support marking routine.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read the plain headers into vertex count 40, endpoint start 280, and
endpoint length 281. -/
def gm02ReadTerminatedHeaderProg (src : Arr) : Cmd :=
  .seq (.assign 40 (.read src (.const 0)))
    (.seq (.assign 280 (.read src (.const 1)))
      (.seq (.assign 280 (.op .add (.const 2) (.op .mul (.const 2) (.reg 280))))
        (.seq (.assign 281 (.read src (.reg 280)))
          (.seq (.assign 281 (.op .mul (.const 2) (.reg 281)))
            (.assign 280 (.op .add (.reg 280) (.const 1)))))))

private theorem read_of_word {w i v : ℕ} {src : Arr} {s : State} {idx : Expr}
    (hi : idx.eval w s = some i) (hv : (s.arrs src)[i]? = some v) (hvw : v < 2 ^ w) :
    (Expr.read src idx).eval w s = some v := by
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.1 hv
  simpa only [hget] using eval_read hi hidx (hget ▸ hvw)

/-- The endpoint-slice metadata is computed from the supplied headers in
23 steps, preserving every array and all other registers. -/
theorem gm02ReadTerminatedHeaderProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (src : Arr) (s : State) (hsrc : s.arrs src = x.enc)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s', Exec w (gm02ReadTerminatedHeaderProg src) s s' 23 ∧
      s'.regs 40 = x.n ∧ s'.regs 280 = 3 + 2 * (edgeListOf x.G).length ∧
      s'.regs 281 = 2 * x.A.index ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ 40 → r ≠ 280 → r ≠ 281 → s'.regs r = s.regs r) := by
  have hl := x.enc_length
  let m := (edgeListOf x.G).length
  let k := x.A.index
  have hm : m < 2 ^ w := by omega
  have hk : k < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have h2m : 2 * m < 2 ^ w := by omega
  have hprefix : 2 + 2 * m < 2 ^ w := by omega
  have hpairs : 2 * k < 2 ^ w := by omega
  have hstart : 3 + 2 * m < 2 ^ w := by omega
  let s₁ := s.setReg 40 x.n
  have he₁ : Exec w (.assign 40 (.read src (.const 0))) s s₁ 3 :=
    Exec.assign (read_of_word (eval_const (by omega)) (by simpa only [hsrc] using x.enc_zero) hn)
  let s₂ := s₁.setReg 280 m
  have he₂ : Exec w (.assign 280 (.read src (.const 1))) s₁ s₂ 3 :=
    Exec.assign (read_of_word (eval_const (by omega))
      (by simpa only [s₁, State.setReg_arrs, hsrc] using x.enc_one) hm)
  let s₃ := s₂.setReg 280 (2 + 2 * m)
  have he₃ : Exec w (.assign 280 (.op .add (.const 2) (.op .mul (.const 2) (.reg 280)))) s₂ s₃ 6 := by
    apply Exec.assign
    exact eval_add (eval_const h2) (eval_mul (eval_const h2) (eval_reg (by simp [s₂]) hm) h2m) hprefix
  let s₄ := s₃.setReg 281 k
  have he₄ : Exec w (.assign 281 (.read src (.reg 280))) s₃ s₄ 3 :=
    Exec.assign (read_of_word (eval_reg (by simp [s₃]) hprefix)
      (by simpa only [s₃, s₂, s₁, State.setReg_arrs, hsrc] using x.enc_index) hk)
  let s₅ := s₄.setReg 281 (2 * k)
  have he₅ : Exec w (.assign 281 (.op .mul (.const 2) (.reg 281))) s₄ s₅ 4 :=
    Exec.assign (eval_mul (eval_const h2) (eval_reg (by simp [s₄]) hk) hpairs)
  let s₆ := s₅.setReg 280 (3 + 2 * m)
  have he₆ : Exec w (.assign 280 (.op .add (.reg 280) (.const 1))) s₅ s₆ 4 := by
    apply Exec.assign
    have hev := eval_add (eval_reg (r := 280) (s := s₅) (by simp [s₅, s₄, s₃]) hprefix) (eval_const (by omega : 1 < 2 ^ w))
      (by omega : 2 + 2 * m + 1 < 2 ^ w)
    have heq : 2 + 2 * m + 1 = 3 + 2 * m := by omega
    simpa only [heq] using hev
  refine ⟨s₆, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ (Exec.seq he₅ he₆)))),
    by simp [s₆, s₅, s₄, s₃, s₂, s₁], by simp [s₆, m], by simp [s₆, s₅, k], rfl, ?_⟩
  intro r hr40 hr280 hr281
  simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr40,
    State.setReg_regs_ne _ _ hr280, State.setReg_regs_ne _ _ hr281]

end GraphMinor.Compute
