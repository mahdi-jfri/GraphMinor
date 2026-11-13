module

public import GraphMinor.Compute.GM02InjectedEdgeRegisters
public import GraphMinor.Compute.GM02WriteRegisterList
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic.Ring

/-!
# Building the edge part of a labelled pattern input

Allocate a fixed-size array for the pattern edge count and endpoint
words. Write the fixed count, then copy the selected endpoint registers
in original edge order. All registers and the host array are preserved.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Build the edge-count and injected endpoint suffix in array 31. -/
@[expose] def gm02BuildInjectedEdgesProg (H : GM02EdgeListInput) : Cmd :=
  .seq (.alloc 31 (.const (1 + 2 * H.edges.length)))
    (.seq (.write 31 (.const 0) (.const H.edges.length))
      (gm02WriteRegisterListProg 31 1 (gm02InjectedEdgeRegisters H)))

/-- The fixed endpoint writer computes the exact labelled-pattern edge suffix. -/
theorem gm02BuildInjectedEdgesProg_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hn : G.n < 2 ^ W) (hcap : 1 + 2 * H.edges.length < 2 ^ W)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val) :
    ∃ s', Exec W (gm02BuildInjectedEdgesProg H) s s' (6 + 8 * H.edges.length) ∧
      s'.arrs 31 = [H.edges.length] ++ flatEdges (gm02InjectedPattern G H f).edges ∧
      s'.regs = s.regs ∧ (∀ a, a ≠ 31 → s'.arrs a = s.arrs a) := by
  let s₀ := s.setArr 31 (List.replicate (1 + 2 * H.edges.length) 0)
  have he₀ : Exec W (.alloc 31 (.const (1 + 2 * H.edges.length))) s s₀
      (2 + 2 * H.edges.length) := by
    convert Exec.alloc (a := 31) (eval_const (s := s) hcap) using 1
    simp only [Expr.cost]
    omega
  let s₁ := s₀.writeArr 31 0 H.edges.length
  have he₁ : Exec W (.write 31 (.const 0) (.const H.edges.length)) s₀ s₁ 3 :=
    .write (eval_const (by omega)) (eval_const (by omega)) (by simp [s₀])
  have hb₁ : s₁.arrs 31 = [H.edges.length] ++
      List.replicate (gm02InjectedEdgeRegisters H).length 0 := by
    simp [s₁, s₀, gm02InjectedEdgeRegisters_length, Nat.add_comm 1, List.replicate_succ]
  obtain ⟨s₂, he₂, hout, hr, ha⟩ := gm02WriteRegisterListProg_exec 31
    (gm02InjectedEdgeRegisters H) [H.edges.length] s₁ hb₁
    (by simpa only [List.length_singleton, gm02InjectedEdgeRegisters_length] using hcap)
    (fun r hr => (gm02InjectedEdgeRegisters_word_lt G H f s hslots r hr).trans hn)
  refine ⟨s₂, ?_, ?_, hr, ?_⟩
  · have he := Exec.seq he₀ (Exec.seq he₁ he₂)
    dsimp only [gm02BuildInjectedEdgesProg]
    simp only [List.length_singleton, gm02InjectedEdgeRegisters_length] at he
    convert he using 1 <;> ring

  · rw [gm02InjectedEdgeRegisters_words G H f s₁ hslots] at hout
    exact hout
  · intro a ha31
    exact (ha a ha31).trans ((State.writeArr_arrs_ne s₀ 0 H.edges.length ha31).trans
      (State.setArr_arrs_ne s _ ha31))

end GraphMinor.Compute
