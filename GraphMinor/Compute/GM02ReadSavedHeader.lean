module

public import GraphMinor.Compute.Algorithm101Stream

/-!
# Reading fixed saved-frame headers into control registers

Read successive saved words into a consecutive block of registers.
The stream cursor is outside that block, so each read preserves earlier
values. The exact word-by-word result and unchanged arrays justify
restoring all lengths and loop state from an eight-word frame header.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a fixed number of saved words into consecutive registers. -/
def gm02ReadSavedHeaderProg (stack : Arr) (r_pos r_base : Reg) : ℕ → Cmd
  | 0 => .skip
  | k + 1 => .seq (readStreamWordProg stack r_pos r_base)
      (gm02ReadSavedHeaderProg stack r_pos (r_base + 1) k)

/-- Every read header word is recovered in its assigned register. -/
theorem gm02ReadSavedHeaderProg_exec {w off : ℕ} (stack : Arr) (r_pos r_base : Reg)
    (words rest : List ℕ) (s : State) (hregs : r_base + words.length ≤ r_pos)
    (hw : 1 < 2 ^ w) (hlen : off + words.length < 2 ^ w)
    (hwords : ∀ v ∈ words, v < 2 ^ w)
    (hstream : AtStream stack off (words ++ rest) s) (hpos : s.regs r_pos = off) :
    ∃ s' t, Exec w (gm02ReadSavedHeaderProg stack r_pos r_base words.length) s s' t ∧
      t ≤ 8 * words.length + 1 ∧
      (∀ i (hi : i < words.length), s'.regs (r_base + i) = words[i]) ∧
      s'.regs r_pos = off + words.length ∧
      AtStream stack (off + words.length) rest s' ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ r_pos → r < r_base ∨ r_base + words.length ≤ r → s'.regs r = s.regs r) := by
  induction words generalizing off r_base s with
  | nil =>
    exact ⟨s, 1, Exec.skip s, by simp, by simp, by simpa using hpos,
      by simpa using hstream, rfl, fun _ _ _ => rfl⟩
  | cons v vs ih =>
    have hne : r_pos ≠ r_base := by dsimp only [Reg] at *; simp only [List.length_cons] at hregs; omega
    obtain ⟨s₁, t₁, he₁, ht₁, hv₁, hpos₁, hstream₁, ha₁, hr₁⟩ :=
      readStreamWordProg_exec r_pos r_base hne hw
        (by simp only [List.length_cons] at hlen; omega) (hwords v (List.mem_cons_self ..)) hstream hpos
    obtain ⟨s₂, t₂, he₂, ht₂, hvals₂, hpos₂, hstream₂, ha₂, hr₂⟩ :=
      ih (r_base + 1) s₁
        (by dsimp only [Reg] at *; simp only [List.length_cons] at hregs; omega)
        (by simp only [List.length_cons] at hlen; omega)
        (fun x hx => hwords x (List.mem_cons_of_mem _ hx)) hstream₁ hpos₁
    refine ⟨s₂, t₁ + t₂, Exec.seq he₁ he₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro i hi
      cases i with
      | zero =>
        simpa only [Nat.add_zero, List.getElem_cons_zero] using
          (hr₂ r_base hne.symm (Or.inl (by dsimp only [Reg]; omega))).trans hv₁
      | succ i =>
        simpa only [List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hvals₂ i (by simp only [List.length_cons] at hi; omega)
    · simp only [List.length_cons] at *
      omega
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstream₂
    · exact ha₂.trans (funext ha₁)
    · intro r hrp hr
      have hrb : r ≠ r_base := by
        dsimp only [Reg] at *
        simp only [List.length_cons] at hr
        omega
      have hrt : r < r_base + 1 ∨ r_base + 1 + vs.length ≤ r := by
        dsimp only [Reg] at *
        simp only [List.length_cons] at hr
        omega
      exact (hr₂ r hrp hrt).trans (hr₁ r hrp hrb)

end GraphMinor.Compute
