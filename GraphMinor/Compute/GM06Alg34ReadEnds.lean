module

public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Reading one supplied endpoint pair

Read the two consecutive endpoint labels at the input cursor. The
cursor advances by two and the input array is preserved. This is the
stream operation used to construct the surviving-edge table.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read one endpoint pair into registers 132 and 133 using cursor 103. -/
def gm06ReadEndsProg : Cmd :=
  .seq (readStreamWordProg 0 103 132) (readStreamWordProg 0 103 133)

/-- Reading a pair advances exactly two words, preserves all arrays,
and changes only its cursor and two endpoint registers. -/
theorem gm06ReadEndsProg_exec {w off a b : ℕ} {tail : List ℕ}
    (hw : 1 < 2 ^ w) (hoff : off + 2 < 2 ^ w)
    (ha : a < 2 ^ w) (hb : b < 2 ^ w) {s : State}
    (hs : AtStream 0 off (a :: b :: tail) s) (hp : s.regs 103 = off) :
    ∃ s' t, Exec w gm06ReadEndsProg s s' t ∧ t ≤ 16 ∧
      s'.regs 132 = a ∧ s'.regs 133 = b ∧ s'.regs 103 = off + 2 ∧
      AtStream 0 (off + 2) tail s' ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hA, hp₁, hs₁, ha₁, hr₁⟩ :=
    readStreamWordProg_exec 103 132 (by decide) hw (by omega) ha hs hp
  obtain ⟨s₂, t₂, he₂, ht₂, hB, hp₂, hs₂, ha₂, hr₂⟩ :=
    readStreamWordProg_exec 103 133 (by decide) hw (by omega) hb hs₁ hp₁
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, ?_, hB, ?_, ?_, ?_, ?_⟩
  · rw [hr₂ 132 (by decide) (by decide)]
    exact hA
  · simpa only [Nat.add_assoc] using hp₂
  · simpa only [Nat.add_assoc] using hs₂
  · intro A
    exact (ha₂ A).trans (ha₁ A)
  · intro q hq hqA hqB
    exact (hr₂ q hq hqB).trans (hr₁ q hq hqA)

end GraphMinor.Compute
