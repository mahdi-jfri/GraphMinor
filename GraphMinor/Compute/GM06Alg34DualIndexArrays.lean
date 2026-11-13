module

public import GraphMinor.Compute.Algorithm99State

/-!
# Finite source arrays for the dual serializer

Construct consecutive index arrays for the supplied vertices, edges,
regions and cuff gaps. Each array contains exactly its source labels.
The serializers can then use the same verified selection loop for all
three incidence lists and for the dual gap classes.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Build source index arrays 50–53, using only register 7900 as scratch. -/
def gm06DualIndexArraysProg : Cmd :=
  .seq (iotaProg 50 100 7900) (.seq (iotaProg 51 101 7900)
    (.seq (iotaProg 52 102 7900) (iotaProg 53 105 7900)))

/-- The four source arrays are exact consecutive labels, constructed in
linear time and preserving every other array and outer register. -/
theorem gm06DualIndexArraysProg_exec {w n m r k : ℕ} {s : State}
    (hw : 1 < 2 ^ w) (hnw : n < 2 ^ w) (hmw : m < 2 ^ w)
    (hrw : r < 2 ^ w) (hkw : k < 2 ^ w)
    (hn : s.regs 100 = n) (hm : s.regs 101 = m)
    (hr : s.regs 102 = r) (hk : s.regs 105 = k) :
    ∃ s' t, Exec w gm06DualIndexArraysProg s s' t ∧
      t ≤ 12 * (n + m + r + k) + 32 ∧
      s'.arrs 50 = List.range n ∧ s'.arrs 51 = List.range m ∧
      s'.arrs 52 = List.range r ∧ s'.arrs 53 = List.range k ∧
      (∀ A : ℕ, A ≠ 50 → A ≠ 51 → A ≠ 52 → A ≠ 53 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 7900 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, h50, ha₁, hg₁⟩ :=
    iotaProg_exec 50 100 7900 (by decide) hw hnw hn
  obtain ⟨s₂, t₂, he₂, ht₂, h51, ha₂, hg₂⟩ :=
    iotaProg_exec 51 101 7900 (by decide) hw hmw ((hg₁ 101 (by decide)).trans hm)
  obtain ⟨s₃, t₃, he₃, ht₃, h52, ha₃, hg₃⟩ :=
    iotaProg_exec 52 102 7900 (by decide) hw hrw
      ((hg₂ 102 (by decide)).trans ((hg₁ 102 (by decide)).trans hr))
  obtain ⟨s₄, t₄, he₄, ht₄, h53, ha₄, hg₄⟩ :=
    iotaProg_exec 53 105 7900 (by decide) hw hkw
      ((hg₃ 105 (by decide)).trans ((hg₂ 105 (by decide)).trans ((hg₁ 105 (by decide)).trans hk)))
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)),
    by omega, ?_, ?_, (ha₄ 52 (by decide)).trans h52, h53, ?_, ?_⟩
  · exact (ha₄ 50 (by decide)).trans ((ha₃ 50 (by decide)).trans ((ha₂ 50 (by decide)).trans h50))
  · exact (ha₄ 51 (by decide)).trans ((ha₃ 51 (by decide)).trans h51)
  · intro A h50 h51 h52 h53
    exact (ha₄ A h53).trans ((ha₃ A h52).trans ((ha₂ A h51).trans (ha₁ A h50)))
  · intro q hq
    exact (hg₄ q hq).trans ((hg₃ q hq).trans ((hg₂ q hq).trans (hg₁ q hq)))

end GraphMinor.Compute
