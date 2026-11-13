module

public import GraphMinor.Compute.Case3StepsMemberVerticesProg
public import GraphMinor.Compute.Case3StepsLoopOwnerPrefix

/-!
# Recording loop owners for one selected member

The program prepares the member's vertex bitset and then records its label
at vertices with no earlier owner. The exact table invariant advances by one
candidate, while the graph and group tables survive for later scans.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare a selected member and record its previously unassigned vertices. -/
def case3MemberLoopOwnerProg : Cmd :=
  .seq case3MemberVerticesProg (case3RecordOwnerProg 30 33 14 63 54 52)

/-- One selected member advances the exact loop-owner table in linear time. -/
theorem case3MemberLoopOwnerProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1)
    (hrL : s.regs 52 = x.n + (case3InputEdges x).length)
    (howners : s.arrs 33 = case3LoopOwnerPrefix x d.core.Z (case3RawIndexLabel x i.1)) :
    ∃ s' t, Exec w case3MemberLoopOwnerProg s s' t ∧ t ≤ 77 * x.n + 102 ∧
      s'.arrs 25 = case3BoundaryKey (case3GroupBoundary x d.core.Z i.1) ∧
      s'.arrs 30 = bitSetList (case3SelectedMember x d.core.Z i).verts ∧
      s'.arrs 33 = case3LoopOwnerPrefix x d.core.Z (case3RawIndexLabel x i.1 + 1) ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 33 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 ∨ 64 ≤ r → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hkey₁, hbits₁, harr₁, hreg₁⟩ :=
    case3MemberVerticesProg_exec x d hd i hw hn hkeys hm hsize hin hZ htab hreps hrn hrg
  have hnw : x.n < 2 ^ w := by omega
  have hlabel := (case3RawIndexLabel_lt x i.1).trans hsize
  have hwords : ∀ z ∈ case3LoopOwnerPrefix x d.core.Z (case3RawIndexLabel x i.1),
      z < 2 ^ w := fun z hz =>
    (case3LoopOwnerPrefix_words x d.core.Z _ (case3RawIndexLabel_lt x i.1).le z hz).trans_lt hsize
  obtain ⟨s₂, t₂, hex₂, ht₂, howners₂, harr₂, hreg₂⟩ :=
    case3RecordOwnerProg_exec (case3SelectedMember x d.core.Z i).verts
      (case3LoopOwnerPrefix x d.core.Z (case3RawIndexLabel x i.1))
      (case3RawIndexLabel x i.1) (x.n + (case3InputEdges x).length)
      (case3LoopOwnerPrefix_length x d.core.Z _) 30 33 14 63 54 52
      (by decide) (by decide) (by decide) (by decide) (by omega) hnw hlabel hsize hwords
      (s := s₁) (IsBitSet.of_bitSetList _ _ _ hbits₁)
      ((harr₁ 33 (by decide) (by decide)).trans howners)
      ((hreg₁ 14 (by decide)).trans hrn) ((hreg₁ 54 (by decide)).trans hrg)
      ((hreg₁ 52 (by decide)).trans hrL)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    (harr₂ 25 (by decide)).trans hkey₁, (harr₂ 30 (by decide)).trans hbits₁,
    howners₂.trans (case3LoopOwnerPrefix_selected x d.core.Z i), ?_, ?_⟩
  · intro a h25 h30 h33
    exact (harr₂ a h33).trans (harr₁ a h25 h30)
  · intro r hr
    rw [hreg₂ r (by romega)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
