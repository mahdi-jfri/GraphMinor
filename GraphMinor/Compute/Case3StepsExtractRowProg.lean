module

public import GraphMinor.Compute.Case3StepsAttachmentRows
public import GraphMinor.Compute.Case3StepsComponentRowProg

/-!
# Extracting a component row

A contiguous copy from the component table produces the bitset needed by
the degree-counting program. The copy uses only linear work in the vertex
count and preserves the table and the core.
-/

@[expose] public section

namespace GraphMinor.Compute

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Copy the seed's row into its own bitset array. -/
def case3ExtractRowProg (a_mat a_row r_n r_seed r_work : ℕ) : Cmd :=
  .seq (.alloc a_row (.reg r_n))
    (writeSliceProg a_mat (.op .mul (.reg r_seed) (.reg r_n)) a_row
      (.const 0) r_n r_work)

/-- Extract a component row for neighbor counting, changing only its own
array and the copy registers. -/
theorem case3ExtractRowProg_exec {w : ℕ} (x : Alg81Input) (Z : Finset (Fin x.n))
    (u : Fin x.n) (a_mat a_row r_n r_seed r_work : ℕ)
    (ha : a_mat ≠ a_row) (hr : r_n < r_work)
    (hw : 1 < 2 ^ w) (hn : x.n + 1 < 2 ^ w) (hsq : x.n * x.n < 2 ^ w)
    {s : State} (hmat : s.arrs a_mat = case3ComponentRows x Z)
    (hrn : s.regs r_n = x.n) (hru : s.regs r_seed = u.1) :
    ∃ s' t, Exec w (case3ExtractRowProg a_mat a_row r_n r_seed r_work) s s' t ∧
      t ≤ 18 * x.n + 12 ∧ IsBitSet (case3ComponentRowSet x Z u) a_row s' ∧
      (∀ a, a ≠ a_row → s'.arrs a = s.arrs a) ∧
      (∀ r < r_work, s'.regs r = s.regs r) := by
  have hnw : x.n < 2 ^ w := by omega
  have huw : u.1 < 2 ^ w := u.2.trans hnw
  have h0 : 0 < 2 ^ w := by omega
  have hrowEnd : u.1 * x.n + x.n ≤ x.n * x.n := by
    simpa only [Nat.succ_mul] using Nat.mul_le_mul_right x.n (Nat.succ_le_of_lt u.2)
  have hoff : u.1 * x.n < 2 ^ w := by omega
  let s₁ := s.setArr a_row (List.replicate x.n 0)
  have hex₁ : Exec w (.alloc a_row (.reg r_n)) s s₁ (1 + x.n) :=
    .alloc (by simp only [Expr.eval, checkWord, hrn, hnw, ↓reduceIte])
  have hsrc : s₁.arrs a_mat =
      (((List.finRange x.n).take u.1).flatMap (case3ComponentRow x Z)) ++
        case3ComponentRow x Z u ++
          (((List.finRange x.n).drop (u.1 + 1)).flatMap (case3ComponentRow x Z)) := by
    rw [State.setArr_arrs_ne _ _ ha, hmat]
    exact case3ComponentRows_split x Z u
  obtain ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩ :=
    writeSliceProg_exec (len := x.n) (src_off := u.1 * x.n) (dst_off := 0)
      a_mat a_row (.op .mul (.reg r_seed) (.reg r_n)) (.const 0) r_n r_work ha hr
      _ (case3ComponentRow x Z u) _ [] (List.replicate x.n 0) []
      (case3ComponentRows_prefix_length x Z u.1 u.2.le) (case3ComponentRow_length x Z u)
      rfl (List.length_replicate ..) (case3ComponentRow_words x Z u hw) hw
      (hrowEnd.trans_lt hsq) (by simpa only [Nat.zero_add] using hnw) (s := s₁)
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, State.setArr_regs,
        hru, hrn, huw, hnw, hoff])
      (by simp only [Expr.eval, checkWord, h0, ↓reduceIte]) hsrc
      (by simp only [s₁, State.setArr_arrs_self, List.nil_append, List.append_nil])
      hrn
  dsimp only [Expr.cost] at ht₂
  refine ⟨s₂, 1 + x.n + t₂, .seq hex₁ hex₂, by omega, ?_, ?_, ?_⟩
  · apply IsBitSet.of_bitSetList
    simpa only [List.nil_append, List.append_nil, case3ComponentRow_eq_bitSetList] using hdst₂
  · intro a ha'
    rw [harr₂ a ha', State.setArr_arrs_ne _ _ ha']
  · intro r hr'
    rw [hreg₂ r (Or.inl hr')]
    rfl

end GraphMinor.Compute
