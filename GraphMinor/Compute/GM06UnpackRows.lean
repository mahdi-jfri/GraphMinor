module

public import GraphMinor.Compute.GM06ReadRow

/-!
# Unpacking the cylinder input fields

Read successive structural rows into successive work arrays. The
source array and every array outside the work interval are preserved.
The cursor ends immediately after the last row. The time bound is
linear in the number of input words read.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read a fixed number of consecutive rows into consecutive work arrays. -/
def gm06UnpackRowsProg (src base : Arr) : ℕ → Cmd
  | 0 => .skip
  | n + 1 => .seq (gm06ReadRowProg src base) (gm06UnpackRowsProg src (base + 1) n)

/-- Successive RAM row reads recover every field, with a linear total bound. -/
theorem gm06UnpackRowsProg_exec {w : ℕ} (src base : ℕ) (hsb : src < base)
    (rows : List (List ℕ)) (pre tail : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (ha : s.arrs src = pre ++ gm06EncodeRowsPayload rows ++ tail)
    (hn : (s.arrs src).length < 2 ^ w)
    (hwords : ∀ x ∈ s.arrs src, x < 2 ^ w) (hr : s.regs 8 = pre.length) :
    ∃ s' t, Exec w (gm06UnpackRowsProg src base rows.length) s s' t ∧
      t ≤ 1 + 22 * (gm06EncodeRowsPayload rows).length ∧
      (∀ j (hj : j < rows.length), s'.arrs (base + j) = rows[j]) ∧
      s'.regs 8 = pre.length + (gm06EncodeRowsPayload rows).length ∧
      (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a : ℕ, a < base ∨ base + rows.length ≤ a → s'.arrs a = s.arrs a) := by
  induction rows generalizing base pre s with
  | nil =>
    refine ⟨s, 1, .skip s, by simp [gm06EncodeRowsPayload], ?_, ?_, ?_, ?_⟩
    · intro j hj; simp at hj
    · simpa [gm06EncodeRowsPayload] using hr
    · intro r _ _ _ _; rfl
    · intro a _; rfl
  | cons row rows ih =>
    have hsrc : src ≠ base := by omega
    have ha₀ : s.arrs src = pre ++ gm06EncodeNatList row ++
        (gm06EncodeRowsPayload rows ++ tail) := by
      simpa only [gm06EncodeRowsPayload, List.flatMap_cons, List.append_assoc] using ha
    obtain ⟨s₁, t₁, he₁, ht₁, hd₁, hc₁, hr₁, har₁⟩ :=
      gm06ReadRowProg_exec src base hsrc pre row (gm06EncodeRowsPayload rows ++ tail)
        s hw ha₀ hn hwords hr
    have hs : s₁.arrs src = s.arrs src := har₁ src hsrc
    have ha₁ : s₁.arrs src = (pre ++ gm06EncodeNatList row) ++
        gm06EncodeRowsPayload rows ++ tail := by
      rw [hs, ha₀]
      simp only [List.append_assoc]
    have hc₁' : s₁.regs 8 = (pre ++ gm06EncodeNatList row).length := by
      simpa only [List.length_append, gm06EncodeNatList, List.length_cons, Nat.add_assoc,
        Nat.add_comm 1] using hc₁
    obtain ⟨s₂, t₂, he₂, ht₂, hd₂, hc₂, hr₂, har₂⟩ :=
      ih (base + 1) (by omega) (pre ++ gm06EncodeNatList row) s₁ ha₁
        (by simpa only [hs] using hn) (by simpa only [hs] using hwords) hc₁'
    have hplen : (gm06EncodeRowsPayload (row :: rows)).length =
        1 + row.length + (gm06EncodeRowsPayload rows).length := by
      simp [gm06EncodeRowsPayload, gm06EncodeNatList]
      omega
    refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hplen]
      omega
    · intro j hj
      cases j with
      | zero =>
        simpa only [Nat.add_zero, List.getElem_cons_zero] using
          (har₂ base (Or.inl (by omega))).trans hd₁
      | succ j =>
        have hj' : j < rows.length := Nat.lt_of_succ_lt_succ hj
        simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm 1 j,
          List.getElem_cons_succ] using hd₂ j hj'
    · rw [hc₂, hplen]
      simp only [List.length_append, gm06EncodeNatList, List.length_cons]
      omega
    · intro r h7 h8 h9 h11
      exact (hr₂ r h7 h8 h9 h11).trans (hr₁ r h7 h8 h9 h11)
    · intro a ha'
      have hne : a ≠ base := by simp only [List.length_cons] at ha'; omega
      have ho : a < base + 1 ∨ base + 1 + rows.length ≤ a := by
        simp only [List.length_cons] at ha'
        omega
      exact (har₂ a ho).trans (har₁ a hne)

end GraphMinor.Compute
