module

public import GraphMinor.Compute.GM06Alg34PayloadEnds

/-!
# Serializing the header and endpoint prefix

The header registers contain the three new counts. The endpoint
array contains the prepared relabeled edges. These two passes append
exactly the fixed prefix of the new drawing encoding.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Write the header, then the prepared endpoint section. -/
def gm06PayloadFrontProg : Cmd := .seq gm06PayloadHeaderProg gm06PayloadEndsProg

/-- The two prefix passes serialize exactly the new counts and endpoints. -/
theorem gm06PayloadFrontProg_exec (x : GM06DrawingData) {w cap : ℕ} {s : State}
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w) (hm : x.ends.length < 2 ^ w)
    (hr : x.regions.length < 2 ^ w)
    (hout : 3 + x.endpointWords.length < 2 ^ w)
    (hsrc : s.arrs 8 = x.endpointWords)
    (hbuf : IsPrefixBuffer 10 [] (3 + x.endpointWords.length + cap) s)
    (hpos : s.regs 143 = 0) (hvn : s.regs 131 = x.n)
    (hem : s.regs 137 = x.ends.length) (hrr : s.regs 203 = x.regions.length) :
    ∃ s' t, Exec w gm06PayloadFrontProg s s' t ∧
      t ≤ 17 * x.endpointWords.length + 28 ∧
      IsPrefixBuffer 10 ([x.n, x.ends.length, x.regions.length] ++ x.endpointWords) cap s' ∧
      s'.regs 143 = 3 + x.endpointWords.length ∧
      (∀ a : ℕ, a ≠ 10 → s'.arrs a = s.arrs a) ∧
      (∀ q < 240, q ≠ 142 → q ≠ 143 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
    gm06PayloadHeaderProg_exec hw hn hm hr
      (by simpa only [Nat.add_assoc] using hbuf) hpos hvn hem hrr
  obtain ⟨s₂, t₂, hex₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    gm06PayloadEndsProg_exec x (by omega) hn.le (by simpa using hout)
      ((ha₁ 8 (by decide)).trans hsrc) hb₁ (by simpa using hp₁)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hb₂, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at hp₂
    omega
  · intro a ha
    exact (ha₂ a ha).trans (ha₁ a ha)
  · intro q hq hq142 hq143
    exact (hg₂ q hq hq142 hq143).trans (hg₁ q hq143)

end GraphMinor.Compute
