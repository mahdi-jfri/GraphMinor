module

public import GraphMinor.Compute.Case3StepsMemberCompactProg
public import GraphMinor.Compute.Case3StepsOriginalMemberVerticesProg
public import GraphMinor.Compute.Case3StepsSaveMemberInputProg

/-!
# Preparing a noninterior member record

The noninterior records use the same increasing member labels and full
multigraph input as the interior calls. Compact the graph, write its
original inverse labels, and save its encoding. This supplies the record
writer without invoking (7.2).
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare the compact graph and original labels used by a member record. -/
def case3PrepareMemberRecordProg : Cmd :=
  .seq case3MemberCompactProg (.seq case3OriginalMemberVerticesProg case3SaveMemberInputProg)

/-- Preparing a record takes linear vertex and positive-pair work and
retains the routing tables and scan counters. -/
theorem case3PrepareMemberRecordProg_exec {w N : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z) (orig : Fin x.n → Fin N)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hRA : 2 + 3 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs < 2 ^ w)
    (hRe : (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges < 2 ^ w)
    (hCA : 2 + 3 * (case3CompactMember x D Z i).numActivePairs < 2 ^ w)
    (hCe : (case3CompactMember x D Z i).numEdges < 2 ^ w)
    {s : State}
    (hverts : s.arrs 30 = bitSetList (case3SelectedMember x Z i).verts)
    (henc : s.arrs 39 = (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).enc)
    (hrn : s.regs 14 = x.n)
    (hmember : s.arrs 31 = (case3BoundaryVertices (case3SelectedMember x Z i).verts).map Fin.val ++
      List.replicate (x.n - (case3SelectedMember x Z i).verts.card) 0)
    (hcount : s.regs 62 = (case3SelectedMember x Z i).verts.card)
    (hlistlen : x.n ≤ (s.arrs 32).length)
    (hlist : ∀ u : Fin x.n, (s.arrs 32).getD u.1 0 = (orig u).1)
    (hwords : ∀ z ∈ s.arrs 32, z < 2 ^ w) :
    ∃ s' t, Exec w case3PrepareMemberRecordProg s s' t ∧
      t ≤ 160 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs +
        45 * (case3CompactMember x D Z i).numActivePairs + 47 * x.n + 170 ∧
      s'.arrs 38 = (case3CompactMember x D Z i).enc ∧
      s'.arrs 47 = (List.finRange (case3SelectedMember x Z i).verts.card).map
        (fun u => (orig ((case3SelectedMember x Z i).verts.orderEmbOfFin rfl u)).1) ∧
      (∀ a, a ≠ 38 → a ≠ 40 → a ≠ 41 → a ≠ 42 → a ≠ 47 → a ≠ 128 → s'.arrs a = s.arrs a) ∧
      (∀ r < 78, s'.regs r = s.regs r) := by
  have hvcard : (case3SelectedMember x Z i).verts.card ≤ x.n := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (case3SelectedMember x Z i).verts
  obtain ⟨s₁, t₁, hex₁, ht₁, hcompact, _, harr₁, hreg₁⟩ :=
    case3MemberCompactProg_exec x D Z i hw hn hRA hRe hverts henc hrn
  obtain ⟨s₂, t₂, hex₂, ht₂, hinverse, harr₂, hreg₂⟩ :=
    case3OriginalMemberVerticesProg_exec (case3SelectedMember x Z i).verts orig (by omega) hn
      ((harr₁ 31 (by decide) (by decide) (by decide) (by decide)).trans hmember)
      ((hreg₁ 62 (by decide)).trans hcount)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlistlen)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hlist)
      (by rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide)]; exact hwords)
  obtain ⟨s₃, t₃, hex₃, ht₃, hsave, harr₃, hreg₃⟩ :=
    case3SaveMemberInputProg_exec (case3CompactMember x D Z i) (by omega)
      (lt_of_le_of_lt hvcard hn) hCA hCe ((harr₂ 128 (by decide)).trans hcompact)
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hsave, (harr₃ 47 (by decide)).trans hinverse, ?_, ?_⟩
  · intro a h38 h40 h41 h42 h47 h128
    exact (harr₃ a h38).trans ((harr₂ a h47).trans (harr₁ a h40 h41 h42 h128))
  · intro r hr
    exact (hreg₃ r (by romega) (by romega)).trans ((hreg₂ r (by romega)).trans (hreg₁ r hr))

end GraphMinor.Compute
