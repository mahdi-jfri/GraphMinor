module

public import GraphMinor.Compute.Case3StepsRunMember72
public import GraphMinor.Compute.Case3StepsMemberCompactProg
public import GraphMinor.Compute.Case3StepsOriginalMemberVerticesProg

/-!
# Preparing and running one selected member

Compact the routed graph on the selected vertices, compose the member and
compass inverse vertex lists, save the compact graph, and run (7.2). All
routing data survive. The returned code can therefore be interpreted in
both compact and original labels without repeating the graph scan.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Compact a member, prepare its original labels, and invoke (7.2). -/
def case3PrepareMember72Prog (P72 : Cmd) : Cmd :=
  .seq case3MemberCompactProg
    (.seq case3OriginalMemberVerticesProg (case3RunMember72Prog P72))

/-- The prepared call produces the exact saved compact graph, original
vertex list, and valid returned code, while preserving earlier routing data. -/
theorem case3PrepareMember72Prog_exec (ω h' : ℕ) (P72 : Cmd)
    (h72 : ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h')
      P72 (fun s => s)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (w : ℕ) (x : Alg81Input) (D : MultiDigraph x.n) (Z : Finset (Fin x.n))
        (i : Case3SelectedGroup x Z) (N : ℕ) (orig : Fin x.n → Fin N),
        wordSize c (algorithm72Size (case3MemberAlgorithm72Input x D Z i)) ≤ w →
        3 < 2 ^ w → x.n < 2 ^ w →
        2 + 3 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs < 2 ^ w →
        (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges < 2 ^ w →
        2 + 3 * (case3CompactMember x D Z i).numActivePairs < 2 ^ w →
        (case3CompactMember x D Z i).numEdges < 2 ^ w →
        ∀ s : State,
          s.arrs 30 = bitSetList (case3SelectedMember x Z i).verts →
          s.arrs 39 = (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).enc →
          s.regs 14 = x.n →
          s.arrs 31 = (case3BoundaryVertices (case3SelectedMember x Z i).verts).map Fin.val ++
            List.replicate (x.n - (case3SelectedMember x Z i).verts.card) 0 →
          s.regs 62 = (case3SelectedMember x Z i).verts.card →
          x.n ≤ (s.arrs 32).length →
          (∀ u : Fin x.n, (s.arrs 32).getD u.1 0 = (orig u).1) →
          (∀ z ∈ s.arrs 32, z < 2 ^ w) →
          ∃ s' t, Exec w (case3PrepareMember72Prog P72) s s' t ∧
            t ≤ C * algorithm72Size (case3MemberAlgorithm72Input x D Z i) +
              160 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs +
              45 * (case3CompactMember x D Z i).numActivePairs + 47 * x.n + 170 ∧
            s'.arrs 38 = (case3CompactMember x D Z i).enc ∧
            s'.arrs 47 = (List.finRange (case3SelectedMember x Z i).verts.card).map
              (fun u => (orig ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl u)).1) ∧
            IsAlgorithm72Output ω h' (case3MemberAlgorithm72Input x D Z i) (s'.arrs 129) ∧
            (s'.arrs 129).length < 2 ^ w ∧ (∀ z ∈ s'.arrs 129, z < 2 ^ w) ∧
            (∀ a < 128, a ≠ 38 → a ≠ 40 → a ≠ 41 → a ≠ 42 → a ≠ 47 → s'.arrs a = s.arrs a) ∧
            (∀ r < 78, s'.regs r = s.regs r) ∧
            (s'.arrs 129).length ≤ C * algorithm72Size (case3MemberAlgorithm72Input x D Z i) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := case3RunMember72Prog_exec ω h' P72 h72
  refine ⟨C, c, hC, hc, ?_⟩
  intro w x D Z i N orig hw hw3 hn hRA hRe hCA hCe s hv he hrn hlist hcount hlen hlabels hwords
  have hvcard : (case3SelectedMember x Z i).verts.card ≤ x.n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (case3SelectedMember x Z i).verts
  obtain ⟨s₁, t₁, hex₁, ht₁, hcompact, hrank, harr₁, hreg₁⟩ :=
    case3MemberCompactProg_exec x D Z i hw3 hn hRA hRe hv he hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hinverse, harr₂, hreg₂⟩ :=
    case3OriginalMemberVerticesProg_exec (case3SelectedMember x Z i).verts orig (by omega) hn
      ((harr₁ 31 (by decide) (by decide) (by decide) (by decide)).trans hlist)
      ((hreg₁ 62 (by decide)).trans hcount)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlen)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlabels)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hwords)
  obtain ⟨s₃, t₃, hex₃, ht₃, hsave, hout, houtlen, houtwords, harr₃, hreg₃, htime⟩ :=
    hrun w x D Z i hw (by omega) (lt_of_le_of_lt hvcard hn) hCA hCe s₂
      ((harr₂ 128 (by decide)).trans hcompact)
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hsave, (harr₃ 47 (by decide) (by decide)).trans hinverse, hout, houtlen, houtwords, ?_, ?_, htime⟩
  · intro a ha h38 h40 h41 h42 h47
    exact (harr₃ a ha h38).trans ((harr₂ a h47).trans (harr₁ a h40 h41 h42 (by romega)))
  · intro r hr
    exact (hreg₃ r (by romega)).trans ((hreg₂ r (by romega)).trans (hreg₁ r hr))

end GraphMinor.Compute
