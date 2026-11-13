module

public import GraphMinor.Compute.Case3StepsJoinRecordProg

/-!
# Writing the two arrays of output (a)

The decoder reads the raw block, while Algorithm (9.9) returns the tagged
block preceded by the deletion bitset. Retain the raw block before joining
the bitset, then prefix the required tag 2. The two resulting buffers are
ready to be copied to the caller's output arrays.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Keep the raw block in 62 and write its tagged output with bitset 61 in 63. -/
def case3WriteOutputAProg : Cmd :=
  .seq (copyArrLoopProg 51 62 125 126)
    (.seq (case3JoinRecordProg 61)
      (.seq (.assign 124 (.len 51)) (prependWordProg (.const 2) 51 63 124 128)))

/-- Both output-(a) arrays are exact and take linear copying work. -/
theorem case3WriteOutputAProg_exec {w : ℕ} (bits block : List ℕ)
    (hw : 2 < 2 ^ w) (hlen : 1 + bits.length + block.length < 2 ^ w)
    (hbitsw : ∀ x ∈ bits, x < 2 ^ w) (hblockw : ∀ x ∈ block, x < 2 ^ w)
    {s : State} (hbits : s.arrs 61 = bits) (hblock : s.arrs 51 = block) :
    ∃ s' t, Exec w case3WriteOutputAProg s s' t ∧
      t ≤ 300 * (bits.length + block.length + 1) ∧
      s'.arrs 62 = block ∧ s'.arrs 63 = 2 :: (bits ++ block) ∧
      (∀ a, a ∉ [51, 52, 53, 62, 63] → s'.arrs a = s.arrs a) ∧
      (∀ r < 124, s'.regs r = s.regs r) := by
  have h1 : 1 < 2 ^ w := by omega
  have hjoinlen : bits.length + block.length < 2 ^ w := by omega
  have hjoinw : ∀ x ∈ bits ++ block, x < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hbitsw x hx
    · exact hblockw x hx
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, harr₁, hreg₁⟩ := copyArrLoopProg_exec
    51 62 125 126 (by decide) (by decide) h1 s (by rw [hblock]; omega)
      (by rw [hblock]; exact hblockw)
  obtain ⟨s₂, t₂, hex₂, ht₂, hbuf₂, harr₂, hreg₂⟩ := case3JoinRecordProg_exec
    61 (by decide) bits block h1 hjoinlen hbitsw hblockw
    ((harr₁ 61 (by decide)).trans hbits) ((harr₁ 51 (by decide)).trans hblock)
  let s₃ := s₂.setReg 124 (bits ++ block).length
  have hex₃ : Exec w (.assign 124 (.len 51)) s₂ s₃ 2 :=
    .assign (by simp only [Expr.eval, checkWord, hbuf₂, List.length_append, hjoinlen, ↓reduceIte])
  obtain ⟨s₄, t₄, hex₄, ht₄, hbuf₄, harr₄, hreg₄⟩ := prependWordProg_exec
    (.const 2) 51 63 124 128 (by decide) (by decide) (bits ++ block) hjoinw h1
    (by simpa only [List.length_append, Nat.add_assoc] using hlen)
    (s := s₃) (tag := 2) (by intro v; simp only [Expr.eval, checkWord, hw, ↓reduceIte])
    hbuf₂ (State.setReg_regs_self ..)
  refine ⟨s₄, t₁ + (t₂ + (2 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    ?_, ?_, hbuf₄, ?_, ?_⟩
  · rw [hblock] at ht₁
    simp only [List.length_append, Expr.cost] at ht₄
    omega
  · exact (harr₄ 62 (by decide)).trans ((harr₂ 62 (by decide) (by decide) (by decide)).trans (hbuf₁.trans hblock))
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha
    rcases ha with ⟨h51, h52, h53, h62, h63⟩
    rw [harr₄ a h63, State.setReg_arrs, harr₂ a h51 h52 h53, harr₁ a h62]
  · intro r hr
    rw [hreg₄ r (Or.inl (by romega)), State.setReg_regs_ne _ _ (by romega),
      hreg₂ r hr, hreg₁ r (by romega) (by romega)]

end GraphMinor.Compute
