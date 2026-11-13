module

public import GraphMinor.Compute.Case3StepsAttachmentKeyProg
public import GraphMinor.Compute.Case3StepsAttachmentKeys

/-!
# Storing one attachment key

After computing the selected component's key, four words are copied into
its row in the key table. The table prefix and unused suffix are preserved.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Register 13 contains four, register 15 the seed, and array 26 the table. -/
def case3StoreAttachmentKeyProg : Cmd :=
  .seq case3AttachmentKeyProg
    (writeSliceProg 25 (.const 0) 26 (.op .mul (.reg 15) (.const 4)) 13 36)

/-- Store one four-word key without changing other rows or the seed. -/
theorem case3StoreAttachmentKeyProg_exec {w : ℕ} (x : Alg81Input)
    (d : Alg86DivisionOutput x) (hd : IsValidAlg86DivisionOutput x d)
    (u : Fin x.n) (lists : Fin x.n → List ℕ)
    (hw : 4 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    (hkeys : x.n * 4 < 2 ^ w) (pre suf : List ℕ) (hpre : pre.length = u.1 * 4)
    {s : State} (hmat : s.arrs 12 = case3ComponentRows x d.core.Z)
    (hZ : IsBitSet d.core.Z 10 s)
    (hadj : IsAdjList x.G 19 20 21 lists s) (hent : (s.arrs 21).length < 2 ^ w)
    (htab : s.arrs 26 = pre ++ List.replicate 4 0 ++ suf)
    (hrn : s.regs 14 = x.n) (hru : s.regs 15 = u.1) (hr4 : s.regs 13 = 4) :
    ∃ s' t, Exec w case3StoreAttachmentKeyProg s s' t ∧
      t ≤ 76 * x.n + 19 * totalAdjEntries lists + 118 ∧
      s'.arrs 26 = pre ++ case3BoundaryKey (case3AttachmentRowSet x d.core.Z u) ++ suf ∧
      (∀ a, a ≠ 22 → a ≠ 23 → a ≠ 24 → a ≠ 25 → a ≠ 26 → s'.arrs a = s.arrs a) ∧
      (∀ r < 16, s'.regs r = s.regs r) := by
  have h0 : 0 < 2 ^ w := by omega
  have hnw : x.n < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hnw
  have hend : u.1 * 4 + 4 ≤ x.n * 4 := by omega
  have hoff : u.1 * 4 < 2 ^ w := by omega
  let key := case3BoundaryKey (case3AttachmentRowSet x d.core.Z u)
  have hcard := case3AttachmentRowSet_card_le_three x d hd u
  obtain ⟨s₁, t₁, hex₁, ht₁, hkey₁, harr₁, hreg₁⟩ :=
    case3AttachmentKeyProg_exec x d hd u lists hw hn hsq hmat hZ hadj hent hrn hru
  have hr4₁ : s₁.regs 13 = 4 := (hreg₁ 13 (by decide)).trans hr4
  have hru₁ : s₁.regs 15 = u.1 := (hreg₁ 15 (by decide)).trans hru
  have htab₁ : s₁.arrs 26 = pre ++ List.replicate 4 0 ++ suf := by
    rw [harr₁ 26 (by decide) (by decide) (by decide) (by decide)]
    exact htab
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩ :=
    writeSliceProg_exec (len := 4) (src_off := 0) (dst_off := u.1 * 4)
      25 26 (.const 0) (.op .mul (.reg 15) (.const 4)) 13 36 (by decide) (by decide)
      [] key [] pre (List.replicate 4 0) suf rfl
      (case3BoundaryKey_length _ hcard) hpre (List.length_replicate ..)
      (case3BoundaryKey_words _ hcard hw hnw) (by omega) (by simpa only [Nat.zero_add] using hw)
      (hend.trans_lt hkeys) (s := s₁)
      (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, State.setReg,
        hru₁, huw, hw, hoff])
      (by simpa only [List.nil_append, List.append_nil] using hkey₁) htab₁ hr4₁
  dsimp only [Expr.cost] at ht₂
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hdst₂, ?_, ?_⟩
  · intro a h22 h23 h24 h25 h26
    exact (harr₂ a h26).trans (harr₁ a h22 h23 h24 h25)
  · intro r hr
    rw [hreg₂ r (Or.inl (by romega))]
    exact hreg₁ r hr

end GraphMinor.Compute
