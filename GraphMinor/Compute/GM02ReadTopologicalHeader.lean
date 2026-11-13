module

public import GraphMinor.Compute.GM02TopologicalEncoding
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading the two graph headers on the Word RAM

Read the host vertex and edge counts. Its edge count locates the pattern
vertex count, which then locates the pattern edge count. The program
also records the start of the pattern endpoint words. It preserves all
arrays and every register outside its seven metadata registers.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read the plain (4.6) input's counts and offsets into registers 10 through 16. -/
def gm02ReadTopologicalHeaderProg (src : Arr) : Cmd :=
  .seq (.assign 10 (.read src (.const 0)))
  (.seq (.assign 11 (.read src (.const 1)))
  (.seq (.assign 12 (.op .add (.const 2) (.op .mul (.const 2) (.reg 11))))
  (.seq (.assign 13 (.read src (.reg 12)))
  (.seq (.assign 14 (.op .add (.op .add (.reg 12) (.const 1)) (.reg 13)))
  (.seq (.assign 15 (.read src (.reg 14)))
    (.assign 16 (.op .add (.reg 14) (.const 1))))))))

private theorem read_word {w i v : ℕ} {src : Arr} {s : State} {idx : Expr}
    (hi : idx.eval w s = some i) (hv : (s.arrs src)[i]? = some v) (hw : v < 2 ^ w) :
    (Expr.read src idx).eval w s = some v := by
  obtain ⟨hidx, hget⟩ := List.getElem?_eq_some_iff.1 hv
  simpa only [hget] using eval_read hi hidx (hget ▸ hw)

/-- The metadata is computed in twenty-eight steps directly from the supplied input words. -/
theorem gm02ReadTopologicalHeaderProg_exec {w : ℕ} (x : GM02TopologicalInput)
    (src : Arr) (s : State) (hsrc : s.arrs src = x.enc)
    (h₂ : 2 < 2 ^ w) (hsize : gm02TopologicalSize x < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s', Exec w (gm02ReadTopologicalHeaderProg src) s s' 28 ∧
      s'.regs 10 = x.G.n ∧ s'.regs 11 = x.G.edges.length ∧
      s'.regs 12 = 2 + 2 * x.G.edges.length ∧ s'.regs 13 = x.vertices.card ∧
      s'.regs 14 = 3 + 2 * x.G.edges.length + x.vertices.card ∧
      s'.regs 15 = x.edges.length ∧ s'.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card ∧
      s'.arrs = s.arrs ∧
      ∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → r ≠ 16 → s'.regs r = s.regs r := by
  have hLen := x.enc_length
  have hn : x.G.n < 2 ^ w := by unfold gm02TopologicalSize GM02EdgeListInput.size at hsize; omega
  have hm : x.G.edges.length < 2 ^ w := by unfold gm02TopologicalSize GM02EdgeListInput.size at hsize; omega
  have hv : x.vertices.card < 2 ^ w := by unfold gm02TopologicalSize at hsize; omega
  have hk : x.edges.length < 2 ^ w := by unfold gm02TopologicalSize at hsize; omega
  have h2m : 2 * x.G.edges.length < 2 ^ w := by omega
  have hoff : 2 + 2 * x.G.edges.length < 2 ^ w := by omega
  have hoff1 : 2 + 2 * x.G.edges.length + 1 < 2 ^ w := by omega
  have hoffH : 3 + 2 * x.G.edges.length + x.vertices.card < 2 ^ w := by omega
  have hoffE : 4 + 2 * x.G.edges.length + x.vertices.card < 2 ^ w := by omega
  have h₁ : 1 < 2 ^ w := by omega
  let s₁ := s.setReg 10 x.G.n
  have he₁ : Exec w (.assign 10 (.read src (.const 0))) s s₁ 3 :=
    .assign (read_word (eval_const (Nat.two_pow_pos w)) (by simpa only [hsrc] using x.enc_zero) hn)
  let s₂ := s₁.setReg 11 x.G.edges.length
  have he₂ : Exec w (.assign 11 (.read src (.const 1))) s₁ s₂ 3 :=
    .assign (read_word (eval_const h₁) (by simpa only [s₁, State.setReg_arrs, hsrc] using x.enc_one) hm)
  let s₃ := s₂.setReg 12 (2 + 2 * x.G.edges.length)
  have he₃ : Exec w (.assign 12 (.op .add (.const 2) (.op .mul (.const 2) (.reg 11)))) s₂ s₃ 6 :=
    .assign (eval_add (eval_const h₂) (eval_mul (eval_const h₂) (eval_reg (by simp [s₂]) hm) h2m) hoff)
  let s₄ := s₃.setReg 13 x.vertices.card
  have he₄ : Exec w (.assign 13 (.read src (.reg 12))) s₃ s₄ 3 :=
    .assign (read_word (eval_reg (by simp [s₃]) hoff)
      (by simpa only [s₃, s₂, s₁, State.setReg_arrs, hsrc] using x.enc_vertexCount) hv)
  let s₅ := s₄.setReg 14 (3 + 2 * x.G.edges.length + x.vertices.card)
  have hExpr₅ : (Expr.op .add (.op .add (.reg 12) (.const 1)) (.reg 13)).eval w s₄ =
      some (3 + 2 * x.G.edges.length + x.vertices.card) := by
    have he : (Expr.op .add (.op .add (.reg 12) (.const 1)) (.reg 13)).eval w s₄ =
        some (2 + 2 * x.G.edges.length + 1 + x.vertices.card) :=
      eval_add (eval_add (eval_reg (by simp [s₄, s₃]) hoff) (eval_const h₁) hoff1)
        (eval_reg (by simp [s₄]) hv) (by omega)
    exact he.trans (congrArg some (by omega))
  have he₅ : Exec w (.assign 14 (.op .add (.op .add (.reg 12) (.const 1)) (.reg 13))) s₄ s₅ 6 := .assign hExpr₅
  let s₆ := s₅.setReg 15 x.edges.length
  have he₆ : Exec w (.assign 15 (.read src (.reg 14))) s₅ s₆ 3 :=
    .assign (read_word (eval_reg (by simp [s₅]) hoffH)
      (by simpa only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs, hsrc] using x.enc_edgeCount) hk)
  let s₇ := s₆.setReg 16 (4 + 2 * x.G.edges.length + x.vertices.card)
  have hExpr₇ : (Expr.op .add (.reg 14) (.const 1)).eval w s₆ =
      some (4 + 2 * x.G.edges.length + x.vertices.card) := by
    have he : (Expr.op .add (.reg 14) (.const 1)).eval w s₆ =
        some (3 + 2 * x.G.edges.length + x.vertices.card + 1) :=
      eval_add (eval_reg (by simp [s₆, s₅]) hoffH) (eval_const h₁) (by omega)
    exact he.trans (congrArg some (by omega))
  have he₇ : Exec w (.assign 16 (.op .add (.reg 14) (.const 1))) s₆ s₇ 4 := .assign hExpr₇
  refine ⟨s₇, .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇))))), ?_⟩
  refine ⟨by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁], by simp [s₇, s₆, s₅, s₄, s₃, s₂],
    by simp [s₇, s₆, s₅, s₄, s₃], by simp [s₇, s₆, s₅, s₄], by simp [s₇, s₆, s₅],
    by simp [s₇, s₆], by simp [s₇], rfl, ?_⟩
  intro r hr10 hr11 hr12 hr13 hr14 hr15 hr16
  simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg_regs_ne _ _ hr10,
    State.setReg_regs_ne _ _ hr11, State.setReg_regs_ne _ _ hr12, State.setReg_regs_ne _ _ hr13,
    State.setReg_regs_ne _ _ hr14, State.setReg_regs_ne _ _ hr15, State.setReg_regs_ne _ _ hr16]

end GraphMinor.Compute
