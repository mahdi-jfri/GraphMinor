module

public import GraphMinor.Compute.Case3StepsMemberVerticesProg
public import GraphMinor.Compute.Case3StepsCollectVerticesProg

/-!
# Ordered vertices of a selected member

After preparing the member bitset, a scan collects its vertices in increasing
order and records their count. The graph and group tables survive for edge
routing and the subsequent calls in Graph Minors XIII, (9.9), steps 5–6,
pp. 105–106.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare a member bitset and collect its ordered vertex list. -/
def case3MemberVertexListProg : Cmd :=
  .seq case3MemberVerticesProg (case3CollectVerticesProg 30 31 14 61 62)

/-- The member vertex list is computed in linear time, with its length in
register 62 and its meaningful entries at the start of array 31. -/
theorem case3MemberVertexListProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1) :
    ∃ s' t, Exec w case3MemberVertexListProg s s' t ∧ t ≤ 78 * x.n + 105 ∧
      s'.arrs 25 = case3BoundaryKey (case3GroupBoundary x d.core.Z i.1) ∧
      s'.arrs 30 = bitSetList (case3SelectedMember x d.core.Z i).verts ∧
      s'.arrs 31 = (case3BoundaryVertices (case3SelectedMember x d.core.Z i).verts).map Fin.val ++
        List.replicate (x.n - (case3SelectedMember x d.core.Z i).verts.card) 0 ∧
      s'.regs 62 = (case3SelectedMember x d.core.Z i).verts.card ∧
      (∀ a, a ≠ 25 → a ≠ 30 → a ≠ 31 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 ∨ 63 ≤ r → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hkey₁, hbits₁, harr₁, hreg₁⟩ :=
    case3MemberVerticesProg_exec x d hd i hw hn hkeys hm hsize hin hZ htab hreps hrn hrg
  obtain ⟨s₂, t₂, hex₂, ht₂, hlist₂, hcount₂, harr₂, hreg₂⟩ :=
    case3CollectVerticesProg_exec (case3SelectedMember x d.core.Z i).verts
      30 31 14 61 62 (by decide) (by decide) (by decide) (by decide) hw hn
      (s := s₁) (IsBitSet.of_bitSetList _ _ _ hbits₁)
      ((hreg₁ 14 (by decide)).trans hrn)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    (harr₂ 25 (by decide)).trans hkey₁, (harr₂ 30 (by decide)).trans hbits₁,
    hlist₂, hcount₂, ?_, ?_⟩
  · intro a h25 h30 h31
    exact (harr₂ a h31).trans (harr₁ a h25 h30)
  · intro r hr
    rw [hreg₂ r (by romega) (by romega)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
