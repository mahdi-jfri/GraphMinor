module

public import GraphMinor.Compute.GM06LoopErasureStacks
public import GraphMinor.Compute.TwoPathsCyc

import GraphMinor.Compute.CrossingOpsBasic

/-!
# Verified stack operations for the loop-erasure program

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) pushes the
dart and its new head together, then records that head's stack position.
The generic array-stack specifications supply the actual pushes and
pops. Their memory frames allow the vertex stack, dart stack and
position table to be composed while keeping the input walk unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The verified push also preserves all unrelated memory. -/
theorem gm06StackPush_exec {w a top cap value : ℕ} (val : Expr) (stack : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w) (hfit : stack.length < cap)
    (hs : IsStack a top cap stack s) (hv : val.eval w s = some value) :
    ∃ sf t, Exec w (stackPush a top val) s sf t ∧ t ≤ val.cost + 6 ∧
      Keeps [top] [a] s sf ∧ IsStack a top cap (stack ++ [value]) sf := by
  obtain ⟨sf, t, he, ht, hs'⟩ := Triple.stackPush_spec a top val cap stack value hw hcap hfit s ⟨hs, hv⟩
  refine ⟨sf, t, he, ht, ⟨?_, ?_⟩, hs'⟩
  · intro r hr
    exact he.regs_eq_of_not_mem_writtenRegs (by simpa [stackPush, Cmd.writtenRegs] using hr)
  · intro A hA
    exact he.arrs_eq_of_not_mem_writtenArrs (by simpa [stackPush, Cmd.writtenArrs] using hA)

/-- The verified pop also preserves both physical stack arrays. -/
theorem gm06StackPop_exec {w a top dst cap value : ℕ} (stack : List ℕ) (s : State)
    (hne : dst ≠ top) (hw : 1 < 2 ^ w) (hcap : cap < 2 ^ w) (hv : value < 2 ^ w)
    (hs : IsStack a top cap (stack ++ [value]) s) :
    ∃ sf t, Exec w (stackPop a top dst) s sf t ∧ t ≤ 7 ∧
      Keeps [top, dst] [] s sf ∧ IsStack a top cap stack sf ∧ sf.regs dst = value := by
  obtain ⟨sf, t, he, ht, hs', hd⟩ := Triple.stackPop_spec a top dst cap stack value hne hw hcap hv s hs
  refine ⟨sf, t, he, ht, ⟨?_, ?_⟩, hs', hd⟩
  · intro r hr
    exact he.regs_eq_of_not_mem_writtenRegs (by simpa [stackPop, Cmd.writtenRegs] using hr)
  · intro A _
    exact he.arrs_eq_of_not_mem_writtenArrs (by simp [stackPop, Cmd.writtenArrs])

/-- Push the new dart and vertex, then mark the vertex's actual position. -/
def gm06ErasePushProg : Cmd :=
  .seq (stackPush 605 615 (.reg 611))
    (.seq (stackPush 604 614 (.reg 612)) (.write 606 (.reg 612) (.reg 615)))

/-- A nonrepeated head extends both stacks and installs exactly its
position. The three data structures satisfy the same appended lists. -/
theorem gm06ErasePushProg_exec {w n cap absent d v : ℕ} (vertices darts : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hcap : cap + 1 < 2 ^ w)
    (hd : d < 2 ^ w) (hv : v < n) (hnot : v ∉ vertices)
    (hlen : vertices.length = darts.length + 1) (hroom : darts.length < cap)
    (h604 : IsStack 604 614 (cap + 1) vertices s) (h605 : IsStack 605 615 cap darts s)
    (h606 : s.arrs 606 = gm06StackPositions n absent vertices)
    (h611 : s.regs 611 = d) (h612 : s.regs 612 = v) :
    ∃ sf t, Exec w gm06ErasePushProg s sf t ∧ t ≤ 17 ∧
      Keeps [615, 614] [605, 604, 606] s sf ∧
      IsStack 604 614 (cap + 1) (vertices ++ [v]) sf ∧
      IsStack 605 615 cap (darts ++ [d]) sf ∧
      sf.arrs 606 = gm06StackPositions n absent (vertices ++ [v]) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06StackPush_exec (.reg 611) darts s hw (by omega) hroom
    h605 (GraphMinor.Compute.Crossing.eval_reg h611 hd)
  have h604₁ := h604.of_preserve (hk₁.2 604 (by decide)) (hk₁.1 614 (by decide))
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06StackPush_exec (.reg 612) vertices s₁ hw hcap (by omega)
    h604₁ (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 612 (by decide)).trans h612) (hv.trans hn))
  have h605₂ := hd₁.of_preserve (hk₂.2 605 (by decide)) (hk₂.1 615 (by decide))
  have hv₂ : s₂.regs 612 = v := (hk₂.1 612 (by decide)).trans ((hk₁.1 612 (by decide)).trans h612)
  have htop : s₂.regs 615 = vertices.length := by
    simpa only [List.length_append, List.length_singleton, ← hlen] using h605₂.2.2.1
  have hpos₂ : s₂.arrs 606 = gm06StackPositions n absent vertices :=
    (hk₂.2 606 (by decide)).trans ((hk₁.2 606 (by decide)).trans h606)
  let sf := s₂.writeArr 606 v vertices.length
  have he₃ : Exec w (.write 606 (.reg 612) (.reg 615)) s₂ sf 3 :=
    .write (GraphMinor.Compute.Crossing.eval_reg hv₂ (hv.trans hn))
      (GraphMinor.Compute.Crossing.eval_reg htop (by omega))
      (by simpa only [hpos₂, gm06StackPositions_length] using hv)
  have hk₁₂ : Keeps [615, 614] [605, 604, 606] s s₂ :=
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)
  refine ⟨sf, t₁ + (t₂ + 3), .seq he₁ (.seq he₂ he₃), by simp only [Expr.cost] at ht₁ ht₂; omega,
    hk₁₂.writeArr (by simp) _ _, ?_, ?_, ?_⟩
  · exact hd₂.of_preserve (by simp [sf, State.writeArr]) rfl
  · exact h605₂.of_preserve (by simp [sf, State.writeArr]) rfl
  · change (s₂.arrs 606).set v vertices.length = _
    rw [hpos₂, gm06StackPositions_append vertices hv hnot]

end GraphMinor.Compute
