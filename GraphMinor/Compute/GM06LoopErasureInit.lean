module

public import GraphMinor.Compute.GM06LoopErasureStackOps
public import GraphMinor.Compute.GM13SocietyTabulate
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Initializing the chronological loop-erasure stacks

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) starts with
the source as its only vertex, no darts, and every other position absent.
The absent sentinel is one more than the input dart count. The two
stack capacities are computed from that input length. The position
array is built and the source is marked by an actual RAM write.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Dynamic-capacity stack initialization preserves unrelated memory. -/
theorem gm06StackInit_exec {w a top cap : ℕ} (count : Expr) (s : State)
    (hcount : count.eval w s = some cap) :
    ∃ sf, Exec w (stackInit a top count) s sf (count.cost + cap + 2) ∧
      Keeps [top] [a] s sf ∧ IsStack a top cap [] sf := by
  let s₀ := s.setArr a (List.replicate cap 0)
  let sf := s₀.setReg top 0
  have he₀ : Exec w (.alloc a count) s s₀ (count.cost + cap) := .alloc hcount
  have he₁ : Exec w (.assign top (.const 0)) s₀ sf 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  refine ⟨sf, .seq he₀ he₁, ((Keeps.refl _ _ s).setArr (by simp) _).setReg (by simp) _, ?_⟩
  exact ⟨by simp [sf, s₀], by simp, by simp [sf], by intro i hi; simp at hi⟩

/-- Allocate both stacks, push the source, set all positions absent and
mark source position zero, then initialize the input scan index. -/
def gm06EraseInitProg : Cmd :=
  .seq (.assign 616 (.op .add (.len 603) (.const 1)))
    (.seq (stackInit 604 614 (.op .add (.len 603) (.const 1)))
      (.seq (stackInit 605 615 (.len 603))
        (.seq (stackPush 604 614 (.reg 606))
          (.seq (gm13TabulateProg 619 (.reg 648) (.reg 616) 606)
            (.seq (.write 606 (.reg 606) (.const 0)) (.assign 610 (.const 0)))))))

/-- The initializer computes exactly the one-vertex/zero-dart stack
state and dense position table from the source and input length. -/
theorem gm06EraseInitProg_exec {w n source : ℕ} (input : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hsource : source < n)
    (hfit : input.length + 2 < 2 ^ w)
    (h603 : s.arrs 603 = input) (h606 : s.regs 606 = source) (h648 : s.regs 648 = n) :
    ∃ sf t, Exec w gm06EraseInitProg s sf t ∧ t ≤ 31 + 2 * input.length + 13 * n ∧
      Keeps [616, 614, 615, 619, 610] [604, 605, 606] s sf ∧
      IsStack 604 614 (input.length + 1) [source] sf ∧ IsStack 605 615 input.length [] sf ∧
      sf.arrs 606 = gm06StackPositions n (input.length + 1) [source] ∧
      sf.regs 616 = input.length + 1 ∧ sf.regs 610 = 0 := by
  let s₀ := s.setReg 616 (input.length + 1)
  have he₀ : Exec w (.assign 616 (.op .add (.len 603) (.const 1))) s s₀ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_len h603 (by omega)) (GraphMinor.Compute.Crossing.eval_const hw) (by omega))
  have hk₀ : Keeps [616, 614, 615, 619, 610] [604, 605, 606] s s₀ :=
    (Keeps.refl _ _ s).setReg (by simp) _
  obtain ⟨s₁, he₁, hk₁, hd₁⟩ := gm06StackInit_exec (w := w) (a := 604) (top := 614)
    (.op .add (.len 603) (.const 1)) s₀
    (GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_len (by simpa [s₀] using h603) (by omega))
      (GraphMinor.Compute.Crossing.eval_const hw) (by omega))
  have hk₀₁ : Keeps [616, 614, 615, 619, 610] [604, 605, 606] s s₁ :=
    hk₀.trans hk₁ (by simp) (by simp)
  obtain ⟨s₂, he₂, hk₂, hd₂⟩ := gm06StackInit_exec (w := w) (a := 605) (top := 615) (.len 603) s₁
    (GraphMinor.Compute.Crossing.eval_len ((hk₀₁.2 603 (by decide)).trans h603) (by omega))
  have hk₀₂ : Keeps [616, 614, 615, 619, 610] [604, 605, 606] s s₂ :=
    hk₀₁.trans hk₂ (by simp) (by simp)
  have h604₂ := hd₁.of_preserve (hk₂.2 604 (by decide)) (hk₂.1 614 (by decide))
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06StackPush_exec (.reg 606) [] s₂ hw
    (by omega) (by simp) h604₂
    (GraphMinor.Compute.Crossing.eval_reg ((hk₀₂.1 606 (by decide)).trans h606) (hsource.trans hn))
  have hk₀₃ : Keeps [616, 614, 615, 619, 610] [604, 605, 606] s s₃ :=
    hk₀₂.trans hk₃ (by simp) (by simp)
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm13TabulateProg_exec (w := w) 619 (.reg 648) (.reg 616)
    606 (List.replicate n (input.length + 1)) s₃ hw (by simpa using hn)
    (fun st hk => by
      simpa only [List.length_replicate] using GraphMinor.Compute.Crossing.eval_reg
        ((hk.1 648 (by decide)).trans ((hk₀₃.1 648 (by decide)).trans h648)) hn)
    (fun st i hi hk _ => by
      simpa only [List.getElem_replicate] using GraphMinor.Compute.Crossing.eval_reg
        ((hk.1 616 (by decide)).trans ((hk₃.1 616 (by decide)).trans ((hk₂.1 616 (by decide)).trans
          ((hk₁.1 616 (by decide)).trans (by simp [s₀]))))) (by omega))
  have hk₀₄ : Keeps [616, 614, 615, 619, 610] [604, 605, 606] s s₄ :=
    hk₀₃.trans hk₄ (by simp) (by simp)
  let s₅ := s₄.writeArr 606 source 0
  let sf := s₅.setReg 610 0
  have he₅ : Exec w (.write 606 (.reg 606) (.const 0)) s₄ s₅ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_reg ((hk₀₄.1 606 (by decide)).trans h606) (hsource.trans hn))
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (by simpa only [hd₄, List.length_replicate] using hsource)
  have he₆ : Exec w (.assign 610 (.const 0)) s₅ sf 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  refine ⟨sf, 4 + (((Expr.op .add (.len 603) (.const 1)).cost + (input.length + 1) + 2) +
    ((Expr.len 603).cost + input.length + 2 + (t₃ + (t₄ + (3 + 2))))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆))))), ?_,
    (hk₀₄.writeArr (by simp) _ _).setReg (by simp) _, ?_, ?_, ?_, ?_, by simp [sf]⟩
  · simp only [Expr.cost, List.length_replicate] at ht₃ ht₄ ⊢
    omega
  · exact hd₃.of_preserve (by simpa [sf, s₅, State.writeArr] using hk₄.2 604 (by decide))
      (by simpa [sf, s₅, State.writeArr] using hk₄.1 614 (by decide))
  · exact hd₂.of_preserve (by simpa [sf, s₅, State.writeArr] using
      (hk₄.2 605 (by decide)).trans (hk₃.2 605 (by decide)))
      (by simpa [sf, s₅, State.writeArr] using (hk₄.1 615 (by decide)).trans (hk₃.1 615 (by decide)))
  · change (s₄.arrs 606).set source 0 = _
    rw [hd₄, ← gm06StackPositions_nil]
    simpa only [List.length_nil, List.nil_append] using
      (gm06StackPositions_append (absent := input.length + 1) [] hsource (by simp)).symm
  · exact (by simpa [sf, s₅, State.writeArr] using (hk₄.1 616 (by decide)).trans ((hk₃.1 616 (by decide)).trans
      ((hk₂.1 616 (by decide)).trans ((hk₁.1 616 (by decide)).trans (by simp [s₀])))))

end GraphMinor.Compute
