module

public import GraphMinor.Compute.GM06Alg34TagDivision

/-!
# Initializing and reading the division table

Allocate one zero entry per supplied vertex, read the supplied block
count, and run the verified division loop. The result is exactly the
finite table obtained by scanning those blocks. The count and cursor
bounds are local input conditions, discharged by the full parser.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Every length-prefixed block occupies at least one word. -/
theorem gm06BlockSection_count_le_length (D : List (List ℕ)) :
    D.length ≤ (D.flatMap GM06DrawingData.listWords).length := by
  induction D with
  | nil => simp
  | cons B D ih =>
    simp only [List.flatMap_cons, List.length_cons, List.length_append, GM06DrawingData.listWords]
    omega

/-- Allocate the table using the vertex count in register 100, read the
block count from cursor 103, and fill table array 3 from the input. -/
def gm06TagDivisionProg : Cmd :=
  .seq (.alloc 3 (.reg 100))
    (.seq (readStreamWordProg 0 103 107) gm06TagDivisionLoopProg)

/-- The initialized division table is obtained by the proved finite block
updates. The input and every array other than table 3 are preserved. -/
theorem gm06TagDivisionProg_exec {w off n : ℕ} (D : List (List ℕ)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hcountw : D.length < 2 ^ w)
    (hvalid : ∀ B ∈ D, ∀ v ∈ B, v < n)
    (hend : off + 1 + (D.flatMap GM06DrawingData.listWords).length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (D.length :: (D.flatMap GM06DrawingData.listWords ++ tail)) s)
    (hpos : s.regs 103 = off) (hvertices : s.regs 100 = n) :
    ∃ s' t, Exec w gm06TagDivisionProg s s' t ∧
      t ≤ 50 * (n + (D.flatMap GM06DrawingData.listWords).length + 1) ∧
      s'.arrs 3 = gm06DivisionIds D (List.replicate n 0) ∧
      s'.regs 103 = off + 1 + (D.flatMap GM06DrawingData.listWords).length ∧
      s'.regs 107 = 0 ∧ AtStream 0 (off + 1 + (D.flatMap GM06DrawingData.listWords).length) tail s' ∧
      (∀ a : ℕ, a ≠ 3 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 107 → q ≠ 108 → q ≠ 109 → s'.regs q = s.regs q) := by
  let s₀ := s.setArr 3 (List.replicate n 0)
  have hex₀ : Exec w (.alloc 3 (.reg 100)) s s₀ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hvertices, hn])
  have hstream₀ : AtStream 0 off (D.length :: (D.flatMap GM06DrawingData.listWords ++ tail)) s₀ :=
    hstream.of_arr_eq (State.setArr_arrs_ne _ _ (by decide : 0 ≠ 3))
  obtain ⟨s₁, t₁, hex₁, ht₁, hcount₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    readStreamWordProg_exec 103 107 (by decide) hw (by omega) hcountw hstream₀ hpos
  have hids₁ : s₁.arrs 3 = List.replicate n 0 :=
    (harr₁ 3).trans (State.setArr_arrs_self _ _ _)
  have hidsw : (List.replicate n 0).length < 2 ^ w := by simpa only [List.length_replicate] using hn
  have hvalid₁ : ∀ B ∈ D, ∀ v ∈ B, v < (List.replicate n 0).length := by
    simpa only [List.length_replicate] using hvalid
  obtain ⟨s₂, t₂, hex₂, ht₂, hids₂, hpos₂, hzero₂, hstream₂, harr₂, hreg₂⟩ :=
    gm06TagDivisionLoopProg_exec D (List.replicate n 0) tail hw hidsw hcountw hvalid₁ hend
      hstream₁ hids₁ hpos₁ hcount₁
  refine ⟨s₂, (1 + n) + (t₁ + t₂), .seq hex₀ (.seq hex₁ hex₂), by omega,
    hids₂, hpos₂, hzero₂, hstream₂, ?_, ?_⟩
  · intro a ha
    rw [harr₂ a ha, harr₁ a]
    exact State.setArr_arrs_ne _ _ ha
  · intro q hq103 hq107 hq108 hq109
    rw [hreg₂ q hq103 hq107 hq108 hq109, hreg₁ q hq103 hq107]
    rfl

end GraphMinor.Compute
