module

public import GraphMinor.Compute.GM06Alg34BranchRebuild
public import GraphMinor.Compute.GM06Alg34AppendBranch
public import GraphMinor.Compute.GM06Alg34BranchWords
import Mathlib.Tactic.Ring

/-!
# Building and emitting one component branch

Restore the original parent, construct the selected component payload,
and append its complete length-prefixed record to the queue. The
original root mask and saved parent survive, so the outer scan can
repeat the same operation for the next canonical root.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Build the selected component and append its serialized input to queue 42. -/
def gm06EmitBranchProg : Cmd := .seq gm06BranchRebuildProg gm06AppendBranchProg

private theorem emit_budget (n : ℕ) :
    1200 * (n + 2) ^ 3 + (17 * (n + 2) ^ 3 + 14) ≤ 1300 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- One exact component record is appended in cubic parent time,
while the saved parent, root mask, and outer source counter survive. -/
theorem gm06EmitBranchProg_exec (x : GM06DrawingData) (a : Fin x.n)
    {c cap : ℕ} (hc : 3 ≤ c) {pfx : List ℕ} {s : State}
    (hsaved : s.arrs 41 = x.words) (hlen : s.regs 5003 = x.words.length)
    (hsource : s.regs 5001 = a.val)
    (hend : pfx.length + (gm06ComponentRecordWords x a).length < 2 ^ wordSize c x.size)
    (hbuf : IsPrefixBuffer 42 pfx ((gm06ComponentRecordWords x a).length + cap) s)
    (hpos : s.regs 5002 = pfx.length) :
    ∃ s' t, Exec (wordSize c x.size) gm06EmitBranchProg s s' t ∧
      t ≤ 1300 * (x.size + 2) ^ 3 ∧
      IsPrefixBuffer 42 (pfx ++ gm06ComponentRecordWords x a) cap s' ∧
      s'.regs 5002 = (pfx ++ gm06ComponentRecordWords x a).length ∧
      (∀ A : ℕ, 40 ≤ A → A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, 5000 ≤ q → q < 5100 → q ≠ 5002 → q ≠ 5004 → s'.regs q = s.regs q) := by
  have hsize := (gm06ComponentData_size_le_capacity x a).trans_lt (gm06PayloadCapacity_lt_wordSize x hc)
  have hw : 1 < 2 ^ wordSize c x.size := by
    have hh := (x.componentData a).five_le_words_length
    have hh' := (x.componentData a).words_length_le_size
    omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hin₁, ha₁, hg₁⟩ :=
    gm06BranchRebuildProg_exec x a hc hsaved hlen hsource
  obtain ⟨s₂, t₂, hex₂, ht₂, hb₂, hp₂, ha₂, hg₂⟩ :=
    gm06AppendBranchProg_exec (x.componentData a) hw hsize
      (by simpa only [gm06ComponentRecordWords, GM06DrawingData.listWords, List.length_cons,
        Nat.add_assoc, Nat.add_comm 1] using hend) hin₁
      (by simpa only [IsPrefixBuffer, ha₁ 42 (by decide), gm06ComponentRecordWords,
        GM06DrawingData.listWords, List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hbuf)
      ((hg₁ 5002 (by decide) (by decide)).trans hpos)
  have hh := (x.componentData a).words_length_le_size.trans (gm06ComponentData_size_le_capacity x a)
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂,
    (show t₁ + t₂ ≤ 1200 * (x.size + 2) ^ 3 + (17 * (x.size + 2) ^ 3 + 14) by
      change (x.componentData a).words.length ≤ (x.size + 2) ^ 3 at hh
      omega).trans (emit_budget x.size), hb₂, hp₂, ?_, ?_⟩
  · intro A hA h42
    exact (ha₂ A h42).trans (ha₁ A hA)
  · intro q hq hq' h5002 h5004
    have hq5200 : q < 5200 := hq'.trans (by decide : 5100 < 5200)
    exact (hg₂ q hq5200 h5002 h5004).trans (hg₁ q hq hq')

end GraphMinor.Compute
