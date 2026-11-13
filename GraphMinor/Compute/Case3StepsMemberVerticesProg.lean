module

public import GraphMinor.Compute.Case3StepsGroupKeyProg
public import GraphMinor.Compute.Case3StepsMemberBitsProg

/-!
# Preparing a member boundary and its vertex set

The constant-time key preparation is followed by one scan of compact
vertices. The result gives the exact boundary key and vertex bitset of the
selected merged member while retaining graph and grouping data.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Prepare the boundary key and vertex bitset of group register 54. -/
def case3MemberVerticesProg : Cmd := .seq case3GroupKeyProg case3MemberBitsProg

/-- One selected member's vertices are prepared in at most `58 n + 97`
steps. Its outer label, traversal counts, graph, and group tables survive. -/
theorem case3MemberVerticesProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (i : Case3SelectedGroup x d.core.Z)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hkeys : x.n * 4 < 2 ^ w)
    (hm : 2 + 2 * (case3InputEdges x).length < 2 ^ w)
    (hsize : x.n + (case3InputEdges x).length < 2 ^ w) {s : State}
    (hin : s.arrs 16 = encGraph x.G) (hZ : IsBitSet d.core.Z 10 s)
    (htab : s.arrs 26 = case3AttachmentKeys x d.core.Z)
    (hreps : s.arrs 27 = case3ComponentRepList x d.core.Z)
    (hrn : s.regs 14 = x.n) (hrg : s.regs 54 = case3RawIndexLabel x i.1) :
    ∃ s' t, Exec w case3MemberVerticesProg s s' t ∧ t ≤ 58 * x.n + 97 ∧
      s'.arrs 25 = case3BoundaryKey (case3GroupBoundary x d.core.Z i.1) ∧
      s'.arrs 30 = bitSetList (case3SelectedMember x d.core.Z i).verts ∧
      (∀ a, a ≠ 25 → a ≠ 30 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 13 ∨ r = 14 ∨ r = 17 ∨ r = 52 ∨ r = 54 ∨ 61 ≤ r → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hkey₁, harr₁, hreg₁⟩ :=
    case3GroupKeyProg_exec x d hd i.1 hw hn hkeys hm hsize hin htab hrn hrg
  obtain ⟨s₂, t₂, hex₂, ht₂, hverts₂, harr₂, hreg₂⟩ :=
    case3MemberBitsProg_exec x d hd i hw hn hsize (hZ.of_arr_eq (harr₁ 10 (by decide))) hkey₁
      ((harr₁ 27 (by decide)).trans hreps)
      ((hreg₁ 14 (by decide)).trans hrn) ((hreg₁ 54 (by decide)).trans hrg)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, (harr₂ 25 (by decide)).trans hkey₁,
    hverts₂, ?_, ?_⟩
  · intro a h25 h30
    exact (harr₂ a h30).trans (harr₁ a h25)
  · intro r hr
    rw [hreg₂ r (by romega)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
