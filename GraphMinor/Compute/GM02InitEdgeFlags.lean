module

public import GraphMinor.Compute.GM02TopologicalInput
public import GraphMinor.Compute.Algorithm33Multigraph
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Initializing the two active-edge arrays

Allocate one entry per supplied host edge and per supplied pattern edge,
and fill both arrays with one. Every actual edge is initially active.
The program preserves the input and all other arrays, and changes only
the fill counter and the register holding the constant one.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Initialize host flags in array 20 and pattern flags in array 21. -/
def gm02InitEdgeFlagsProg : Cmd :=
  .seq (.assign 31 (.const 1))
    (.seq (fillArrProg 20 11 31 30) (fillArrProg 21 15 31 30))

/-- Both actual edge lists are initially retained, in time linear in their lengths. -/
theorem gm02InitEdgeFlagsProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (hM : s.regs 11 = x.G.edges.length) (hH : s.regs 15 = x.edges.length)
    (hw : 1 < 2 ^ w) (hMw : x.G.edges.length < 2 ^ w) (hHw : x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w gm02InitEdgeFlagsProg s s' t ∧
      t ≤ 11 * (x.G.edges.length + x.edges.length) + 14 ∧
      s'.arrs 20 = List.replicate x.G.edges.length 1 ∧
      s'.arrs 21 = List.replicate x.edges.length 1 ∧
      (∀ a, a ≠ 20 → a ≠ 21 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 30 → r ≠ 31 → s'.regs r = s.regs r) := by
  let s₁ := s.setReg 31 1
  have he₁ : Exec w (.assign 31 (.const 1)) s s₁ 2 := .assign (eval_const hw)
  obtain ⟨s₂, t₂, he₂, ht₂, hG₂, ha₂, hr₂⟩ := fillArrProg_exec 20 11 31 30 (by decide) (by decide)
    hw hMw hw (s := s₁) (by simpa [s₁, State.setReg] using hM)
      (by simp [s₁])
  obtain ⟨s₃, t₃, he₃, ht₃, hH₃, ha₃, hr₃⟩ := fillArrProg_exec 21 15 31 30 (by decide) (by decide)
    hw hHw hw (s := s₂)
      (by rw [hr₂ 15 (by decide)]; simpa [s₁, State.setReg] using hH)
      (by rw [hr₂ 31 (by decide)]; simp [s₁])
  refine ⟨s₃, 2 + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), by omega, ?_, hH₃, ?_, ?_⟩
  · rw [ha₃ 20 (by decide)]
    exact hG₂
  · intro a ha20 ha21
    rw [ha₃ a ha21, ha₂ a ha20]
    rfl
  · intro r hr30 hr31
    rw [hr₃ r hr30, hr₂ r hr30]
    exact State.setReg_regs_ne _ _ hr31

end GraphMinor.Compute
