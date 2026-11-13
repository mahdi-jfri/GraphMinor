module

public import GraphMinor.Compute.Case3StepsMemberCompact
public import GraphMinor.Compute.Algorithm94Aux

/-!
# Renumbering one encoded member for the call to (7.2)

The member vertex bitset is complemented, and the existing compact-deletion
program writes the graph on its increasing retained vertex labels. The rank
array records the inverse numbering. All routing tables and the original
member encoding survive for later branch or wall transport.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Compact the member in array 39 using its vertex bitset in array 30. -/
def case3MemberCompactProg : Cmd :=
  .seq (complBitSetProg 30 40 14 78) (deleteVerticesCompactProg 39 40 41 42 128 80)

/-- The member is renumbered in increasing order with the exact compact graph
encoding and rank table, preserving all prior member and routing data. -/
theorem case3MemberCompactProg_exec {w : ℕ} (x : Alg81Input) (D : MultiDigraph x.n)
    (Z : Finset (Fin x.n)) (i : Case3SelectedGroup x Z)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hA : 2 + 3 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs < 2 ^ w)
    (he : (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numEdges < 2 ^ w)
    {s : State} (hverts : s.arrs 30 = bitSetList (case3SelectedMember x Z i).verts)
    (henc : s.arrs 39 = (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).enc)
    (hrn : s.regs 14 = x.n) :
    ∃ s' t, Exec w case3MemberCompactProg s s' t ∧
      t ≤ 160 * (case3RoutedMember x D Z (case3RawIndexLabel x i.1)).numActivePairs + 34 * x.n + 126 ∧
      s'.arrs 128 = (case3CompactMember x D Z i).enc ∧
      s'.arrs 42 = List.ofFn (fun v : Fin x.n => compactRank (case3SelectedMember x Z i).vertsᶜ v.1) ∧
      (∀ a, a ≠ 40 → a ≠ 41 → a ≠ 42 → a ≠ 128 → s'.arrs a = s.arrs a) ∧
      (∀ r < 78, s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hcompl₁, harr₁, hreg₁⟩ :=
    complBitSetProg_exec (case3SelectedMember x Z i).verts 30 40 14 78
      (by decide) (by decide) (by omega) hn (IsBitSet.of_bitSetList _ _ _ hverts) hrn
  have hcompl : s₁.arrs 40 = bitSetList (case3SelectedMember x Z i).vertsᶜ := by
    simpa only [Finset.compl_eq_univ_sdiff] using hcompl₁.arr_eq_bitSetList
  obtain ⟨s₂, t₂, hex₂, ht₂, henc₂, hrank₂, harr₂, hreg₂⟩ :=
    deleteVerticesCompactProg_exec (case3RoutedMember x D Z (case3RawIndexLabel x i.1))
      (case3SelectedMember x Z i).vertsᶜ 39 40 41 42 128 80
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn hA he ((harr₁ 39 (by decide)).trans henc) hcompl
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    henc₂.trans (case3CompactMember_enc_eq x D Z i), hrank₂, ?_, ?_⟩
  · intro a h40 h41 h42 h128
    exact (harr₂ a h41 h42 h128).trans (harr₁ a h40)
  · intro r hr
    rw [hreg₂ r (by romega)]
    exact hreg₁ r (by romega)

end GraphMinor.Compute
