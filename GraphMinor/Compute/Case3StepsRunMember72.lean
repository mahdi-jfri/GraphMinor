module

public import GraphMinor.Compute.Case3StepsMemberCall72
public import GraphMinor.Compute.Case3StepsSaveMemberInputProg

/-!
# Running a member call with a saved input

The program of (7.2) may overwrite its input. Save the compact member first,
then run the isolated call. The saved graph and original vertex list remain
available for either writing a branch record or moving the returned wall.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Save the compact graph and run the supplied member program. -/
def case3RunMember72Prog (P72 : Cmd) : Cmd :=
  .seq case3SaveMemberInputProg (case3MemberCall72Prog P72)

/-- The member call retains the exact saved input and all caller arrays
below 128 except the save buffer. Its constants depend only on the supplied
(7.2) specification. -/
theorem case3RunMember72Prog_exec (ω h' : ℕ) (P72 : Cmd)
    (h72 : ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h')
      P72 (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (w : ℕ) (x : Alg81Input) (D : MultiDigraph x.n) (Z : Finset (Fin x.n))
        (i : Case3SelectedGroup x Z),
        wordSize c (algorithm72Size (case3MemberAlgorithm72Input x D Z i)) ≤ w →
        1 < 2 ^ w → (case3SelectedMember x Z i).verts.card < 2 ^ w →
        2 + 3 * (case3CompactMember x D Z i).numActivePairs < 2 ^ w →
        (case3CompactMember x D Z i).numEdges < 2 ^ w →
        ∀ s : State, s.arrs 128 = (case3CompactMember x D Z i).enc →
          ∃ s' t, Exec w (case3RunMember72Prog P72) s s' t ∧
            t ≤ C * algorithm72Size (case3MemberAlgorithm72Input x D Z i) +
              45 * (case3CompactMember x D Z i).numActivePairs + 38 ∧
            s'.arrs 38 = (case3CompactMember x D Z i).enc ∧
            IsAlgorithm72Output ω h' (case3MemberAlgorithm72Input x D Z i) (s'.arrs 129) ∧
            (s'.arrs 129).length < 2 ^ w ∧ (∀ z ∈ s'.arrs 129, z < 2 ^ w) ∧
            (∀ a < 128, a ≠ 38 → s'.arrs a = s.arrs a) ∧
            (∀ r < 118, s'.regs r = s.regs r) ∧
            (s'.arrs 129).length ≤ C * algorithm72Size (case3MemberAlgorithm72Input x D Z i) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := case3MemberCall72Prog_exec ω h' P72 h72
  refine ⟨C, c, hC, hc, ?_⟩
  intro w x D Z i hw hw1 hn hA he s hin
  obtain ⟨s₁, t₁, hex₁, ht₁, hsave, harr₁, hreg₁⟩ :=
    case3SaveMemberInputProg_exec (case3CompactMember x D Z i) hw1 hn hA he hin
  obtain ⟨s₂, t₂, hex₂, ht₂, hout, hlen, hwords, harr₂, hreg₂, htime⟩ :=
    hrun w x D Z i hw s₁ ((harr₁ 128 (by decide)).trans hin)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    (harr₂ 38 (by decide)).trans hsave, hout, hlen, hwords, ?_, ?_, htime⟩
  · intro a ha h38
    exact (harr₂ a ha).trans (harr₁ a h38)
  · intro r hr
    dsimp only [Reg] at hr ⊢
    exact (hreg₂ r (by dsimp only [Reg]; omega)).trans
      (hreg₁ r (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega))

end GraphMinor.Compute
