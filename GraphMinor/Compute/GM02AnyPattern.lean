module

public import GraphMinor.Compute.Basic
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Sequential testing of a fixed finite pattern list

Run each given test until it returns containment or a width report.
A zero answer advances to the next test. The empty list returns zero.
Induction on the list combines the component executions, their times,
and preservation of the original input array.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Run fixed tests in order, retaining the first positive flag in register 89. -/
@[expose] def gm02AnyPatternProg {ι : Type*} (test : ι → Cmd) : List ι → Cmd
  | [] => .assign 89 (.const 0)
  | i :: is => .seq (test i) (.ite (.reg 89) .skip (gm02AnyPatternProg test is))

/-- Sequential composition of proved three-way tests decides their finite disjunction. -/
theorem gm02AnyPatternProg_exec {ι : Type*} {W : ℕ} (test : ι → Cmd) (B : ι → ℕ)
    (F : ι → Prop) (Q : Prop) (is : List ι) (src : Arr) (words : List ℕ)
    (hw : 3 < 2 ^ W)
    (hTests : ∀ i ∈ is, ∀ st : State, st.arrs src = words →
      ∃ st' t, Exec W (test i) st st' t ∧ t ≤ B i ∧ st'.arrs src = words ∧
        ((st'.regs 89 = 1 ∧ F i) ∨ (st'.regs 89 = 0 ∧ ¬F i) ∨ (st'.regs 89 = 2 ∧ Q)))
    (s : State) (hsrc : s.arrs src = words) :
    ∃ s' t, Exec W (gm02AnyPatternProg test is) s s' t ∧
      t ≤ (is.map (fun i => B i + 2)).sum + 2 ∧ s'.arrs src = words ∧
      ((s'.regs 89 = 1 ∧ ∃ i ∈ is, F i) ∨
        (s'.regs 89 = 0 ∧ ∀ i ∈ is, ¬F i) ∨ (s'.regs 89 = 2 ∧ Q)) := by
  induction is generalizing s with
  | nil =>
    let s' := s.setReg 89 0
    refine ⟨s', 2, .assign (eval_const (by omega)), le_rfl, hsrc,
      Or.inr (Or.inl ⟨State.setReg_regs_self .., ?_⟩)⟩
    intro i hi
    exact (List.not_mem_nil hi).elim
  | cons i is ih =>
    obtain ⟨s₀, t₀, he₀, ht₀, hsrc₀, hc₀⟩ := hTests i (List.mem_cons_self) s hsrc
    have hTail := ih (fun j hj => hTests j (List.mem_cons_of_mem i hj))
    rcases hc₀ with ⟨hf, hp⟩ | ⟨hf, hn⟩ | ⟨hf, hq⟩
    · refine ⟨s₀, t₀ + 2, .seq he₀ (.ite_true (eval_reg hf (by omega : 1 < 2 ^ W))
        (by decide) (.skip s₀)), ?_, hsrc₀, Or.inl ⟨hf, i, List.mem_cons_self, hp⟩⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    · obtain ⟨s₁, t₁, he₁, ht₁, hsrc₁, hc₁⟩ := hTail s₀ hsrc₀
      refine ⟨s₁, t₀ + (1 + t₁), .seq he₀ (.ite_false (eval_reg hf (by omega : 0 < 2 ^ W)) he₁),
        ?_, hsrc₁, ?_⟩
      · simp only [List.map_cons, List.sum_cons]
        omega
      · rcases hc₁ with ⟨hf₁, j, hj, hp⟩ | ⟨hf₁, hn₁⟩ | hc₁
        · exact Or.inl ⟨hf₁, j, List.mem_cons_of_mem i hj, hp⟩
        · refine Or.inr (Or.inl ⟨hf₁, ?_⟩)
          intro j hj
          rcases List.mem_cons.1 hj with rfl | hj
          · exact hn
          · exact hn₁ j hj
        · exact Or.inr (Or.inr hc₁)
    · refine ⟨s₀, t₀ + 2, .seq he₀ (.ite_true (eval_reg hf (by omega : 2 < 2 ^ W))
        (by decide) (.skip s₀)), ?_, hsrc₀, Or.inr (Or.inr ⟨hf, hq⟩)⟩
      simp only [List.map_cons, List.sum_cons]
      omega

end GraphMinor.Compute
