module

public import GraphMinor.Compute.Case3StepsMemberInput72
public import GraphMinor.Compute.Algorithm33Multigraph
import GraphMinor.Compute.Case3StepsRamArrayBounds
import GraphMinor.Compute.Case3StepsRamArrayTime

/-!
# The isolated call to (7.2) on a compact member

The member input is already at array 128. The program clears output array
129 and runs the supplied (7.2) program with arrays and registers shifted
by 128. All previously computed member, compass, and routing data survive.
The checked execution bounds both the output length and every output word.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Clear the isolated output and call the supplied member algorithm. -/
def case3MemberCall72Prog (P72 : Cmd) : Cmd :=
  .seq (.alloc 129 (.const 0)) (P72.shift 128 128)

/-- The shifted member call returns precisely a valid branch code or wall,
retains caller data below 128, and has a uniform bound from the supplied spec. -/
theorem case3MemberCall72Prog_exec (ω h' : ℕ) (P72 : Cmd)
    (h72 : ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h')
      P72 (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (w : ℕ) (x : Alg81Input) (D : MultiDigraph x.n) (Z : Finset (Fin x.n))
        (i : Case3SelectedGroup x Z),
        wordSize c (algorithm72Size (case3MemberAlgorithm72Input x D Z i)) ≤ w →
        ∀ s : State, s.arrs 128 = (case3CompactMember x D Z i).enc →
          ∃ s' t, Exec w (case3MemberCall72Prog P72) s s' t ∧
            t ≤ C * algorithm72Size (case3MemberAlgorithm72Input x D Z i) ∧
            IsAlgorithm72Output ω h' (case3MemberAlgorithm72Input x D Z i) (s'.arrs 129) ∧
            (s'.arrs 129).length < 2 ^ w ∧ (∀ z ∈ s'.arrs 129, z < 2 ^ w) ∧
            (∀ a < 128, s'.arrs a = s.arrs a) ∧ (∀ r < 128, s'.regs r = s.regs r) ∧
            (s'.arrs 129).length ≤ C * algorithm72Size (case3MemberAlgorithm72Input x D Z i) := by
  obtain ⟨C₀, c₀, hC₀, hc₀, hrun⟩ := h72
  refine ⟨C₀ + 1, c₀, by omega, hc₀, ?_⟩
  intro w x D Z i hw s hin
  let y := case3MemberAlgorithm72Input x D Z i
  have h0 : 0 < 2 ^ w := Nat.two_pow_pos _
  have hsize : 1 ≤ algorithm72Size y := by unfold algorithm72Size; omega
  let s₀ := s.setArr 129 []
  have hex₀ : Exec w (.alloc 129 (.const 0)) s s₀ 1 :=
    .alloc (m := 0) (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have hin₀ : (s₀.unshift 128 128).arrs inArr = encAlgorithm72In y := by
    simpa only [State.unshift_arrs, inArr, Nat.zero_add, s₀,
      State.setArr_arrs_ne _ _ (show (128 : ℕ) ≠ 129 by decide),
      encAlgorithm72In, y, case3MemberAlgorithm72Input] using hin
  obtain ⟨s_sub, t, hex, ht, hout⟩ := hrun y (s₀.unshift 128 128) hin₀
  have hexw := hex.mono_wordSize hw
  have hout₀ : (s₀.unshift 128 128).arrs outArr = [] := by
    simp only [State.unshift_arrs, outArr, Nat.reduceAdd, s₀, State.setArr_arrs_self]
  have hlen : (s_sub.arrs outArr).length < 2 ^ w :=
    case3Exec_array_length_lt hexw outArr (by rw [hout₀, List.length_nil]; exact h0)
  have hwords : ∀ z ∈ s_sub.arrs outArr, z < 2 ^ w :=
    case3Exec_array_words_lt hexw outArr (by intro z hz; rw [hout₀] at hz; exact False.elim (List.not_mem_nil hz))
  let s' := s₀.applyShifted 128 128 s_sub
  have houtArr : s'.arrs 129 = s_sub.arrs outArr := by
    simpa only [s', outArr, Nat.reduceAdd] using State.applyShifted_arrs_add' 128 128 s₀ s_sub 1
  refine ⟨s', 1 + t, .seq hex₀ (Exec.shift_from 128 128 hexw), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change t ≤ C₀ * algorithm72Size y at ht
    change 1 + t ≤ (C₀ + 1) * algorithm72Size y
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · rw [houtArr]
    exact hout
  · rw [houtArr]
    exact hlen
  · rw [houtArr]
    exact hwords
  · intro a ha
    rw [State.applyShifted_arrs_lt _ _ _ _ ha, State.setArr_arrs_ne _ _ (by romega)]
  · intro r hr
    rw [State.applyShifted_regs_lt _ _ _ _ hr]
    rfl
  · rw [houtArr]
    have hl := case3Exec_array_length_le_time hexw outArr
    rw [hout₀, List.length_nil, Nat.zero_add] at hl
    change t ≤ C₀ * algorithm72Size y at ht
    change _ ≤ (C₀ + 1) * algorithm72Size y
    rw [Nat.add_mul, Nat.one_mul]
    omega

end GraphMinor.Compute
