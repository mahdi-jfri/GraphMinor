module

public import GraphMinor.Compute.Case3StepsWritePlaceholderRecord
public import GraphMinor.Compute.Case3StepsStoreMemberRecord

/-!
# Appending a noninterior record to the shared buffer

Write the prescribed placeholder record, split the unused buffer at its
actual length, and copy it into that slice. The existing prefix is retained,
and the used length and member count advance by the exact amounts.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Serialize a noninterior member and append it to the record buffer. -/
def case3StorePlaceholderRecordProg : Cmd :=
  .seq case3WritePlaceholderRecordProg case3StoreMemberRecordProg

/-- A noninterior record consumes its reserved capacity and changes only
the record work arrays and the two buffer counters. -/
theorem case3StorePlaceholderRecordProg_exec {w n N count remaining : ℕ}
    (G : MultiDigraph n) (orig : Fin n → Fin N) (hinj : Function.Injective orig) (pre : List ℕ)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hremaining : n + 6 * G.numEdges + 4 ≤ remaining)
    (hcapacity : pre.length + remaining < 2 ^ w) (hcount : count + 1 < 2 ^ w)
    {s : State} (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1))
    (hbuf : s.arrs 57 = pre ++ List.replicate remaining 0)
    (hused : s.regs 1 = pre.length) (hnum : s.regs 2 = count) :
    ∃ s' t, Exec w case3StorePlaceholderRecordProg s s' t ∧
      t ≤ 1500 * (n + G.numEdges + G.numActivePairs + 1) ∧
      let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj)
        (case3PlaceholderCode G.numEdges)
      s'.arrs 57 = pre ++ r.enc ++ List.replicate (remaining - r.enc.length) 0 ∧
      s'.regs 1 = pre.length + r.enc.length ∧ s'.regs 2 = count + 1 ∧
      (∀ a, a ≠ 48 → a ≠ 49 → a ≠ 50 → a ≠ 51 → a ≠ 52 → a ≠ 53 → a ≠ 57 → s'.arrs a = s.arrs a) ∧
      (∀ q < 101, q ≠ 1 → q ≠ 2 → s'.regs q = s.regs q) := by
  let r := case3BranchRecord G (origVertexEmb orig hinj) (origEdgeEmb orig hinj) (case3PlaceholderCode G.numEdges)
  obtain ⟨s₁, t₁, hex₁, ht₁, hrec, hrlen, hwords, harr₁, hreg₁⟩ :=
    case3WritePlaceholderRecordProg_exec G orig hinj hw hn hN hA (by omega) hG hlabels
  change r.enc.length ≤ n + 6 * G.numEdges + 4 at hrlen
  have hfits : r.enc.length ≤ remaining := hrlen.trans hremaining
  have hsplit : List.replicate remaining (0 : ℕ) =
      List.replicate r.enc.length 0 ++ List.replicate (remaining - r.enc.length) 0 := by
    rw [← List.replicate_add, Nat.add_sub_of_le hfits]
  have hbuf' : s₁.arrs 57 = pre ++ List.replicate r.enc.length 0 ++
      List.replicate (remaining - r.enc.length) 0 := by
    rw [harr₁ 57 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      hbuf, hsplit, List.append_assoc]
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hused₂, hnum₂, harr₂, hreg₂⟩ :=
    case3StoreMemberRecordProg_exec (w := w) (count := count) pre r.enc
      (List.replicate (remaining - r.enc.length) 0) (by omega) (by omega) hcount
      (by rw [← hrec]; exact hwords) hrec hbuf'
      ((hreg₁ 1 (by decide)).trans hused) ((hreg₁ 2 (by decide)).trans hnum)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hbuf₂, hused₂, hnum₂, ?_, ?_⟩
  · intro a h48 h49 h50 h51 h52 h53 h57
    exact (harr₂ a h57).trans (harr₁ a h48 h49 h50 h51 h52 h53)
  · intro q hq h1 h2
    exact (hreg₂ q (by romega) h1 h2).trans (hreg₁ q hq)

end GraphMinor.Compute
