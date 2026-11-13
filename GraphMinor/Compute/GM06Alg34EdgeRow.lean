module

public import GraphMinor.Compute.GM06Alg34StartClosureRow
public import GraphMinor.Compute.GM06Alg34ReadEnds
import GraphMinor.Compute.GM06Alg34RegionRow

/-!
# Writing one edge closure row from its supplied ends

Mark the edge cell itself, read its two supplied endpoint words, and
mark both vertex columns in the same row. Loops cause a repeated mark
and parallel edges retain separate packed rows.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Mark one edge cell and its two supplied endpoints in the closure matrix. -/
def gm06EdgeRowProg : Cmd :=
  .seq gm06StartClosureRowProg (.seq gm06ReadEndsProg
    (.seq (gm06MarkRegisterProg 132) (gm06MarkRegisterProg 133)))

/-- One supplied edge pair yields exactly its own-cell and endpoint
incidences in at most forty-nine RAM steps. -/
theorem gm06EdgeRowProg_exec {w off N i a b : ℕ} (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hsquare : N * N < 2 ^ w)
    (hi : i < N) (ha : a < N) (hb : b < N) (hoff : off + 2 < 2 ^ w)
    {s : State} (hs : AtStream 0 off (a :: b :: tail) s) (hp : s.regs 103 = off)
    (hNr : s.regs 170 = N) (hir : s.regs 171 = i) (hcap : (s.arrs 12).length = N * N) :
    ∃ s' t, Exec w gm06EdgeRowProg s s' t ∧ t ≤ 49 ∧
      s'.arrs 12 = (((s.arrs 12).set (N * i + i) 1).set (N * i + a) 1).set (N * i + b) 1 ∧
      s'.regs 103 = off + 2 ∧ AtStream 0 (off + 2) tail s' ∧
      (∀ A : ℕ, A ≠ 12 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 132 → q ≠ 133 → q ≠ 173 → q ≠ 174 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, he₁, hbuf₁, hrow₁, hshift₁, _, ha₁, hr₁⟩ :=
    gm06StartClosureRowProg_exec hw hN hi hsquare hNr hir hcap
  have hs₁ : AtStream 0 off (a :: b :: tail) s₁ := hs.of_arr_eq (ha₁ 0 (by decide))
  have hp₁ : s₁.regs 103 = off :=
    (hr₁ 103 (by decide) (by decide) (by decide)).trans hp
  obtain ⟨s₂, t₂, he₂, ht₂, hA₂, hB₂, hp₂, hs₂, ha₂, hr₂⟩ :=
    gm06ReadEndsProg_exec hw hoff (ha.trans hN) (hb.trans hN) hs₁ hp₁
  have hrow₂ : s₂.regs 173 = N * i :=
    (hr₂ 173 (by decide) (by decide) (by decide)).trans hrow₁
  have hshift₂ : s₂.regs 174 = 0 :=
    (hr₂ 174 (by decide) (by decide) (by decide)).trans hshift₁
  have hcap₂ : (s₂.arrs 12).length = N * N := by
    rw [ha₂ 12, hbuf₁, List.length_set, hcap]
  have haddrA : N * i + a < N * N := gm06MatrixAddress_lt hi ha
  have haddrB : N * i + b < N * N := gm06MatrixAddress_lt hi hb
  obtain ⟨s₃, he₃, hbuf₃, _, ha₃, hr₃⟩ :=
    gm06MarkRegisterProg_exec (s := s₂) (row := N * i) (shift := 0) (v := a) 132 hw
      (by simpa using haddrA.trans hsquare) hrow₂ hshift₂ hA₂
      (by rw [hcap₂]; simpa using haddrA)
  have hrow₃ : s₃.regs 173 = N * i := (hr₃ 173 (by decide)).trans hrow₂
  have hshift₃ : s₃.regs 174 = 0 := (hr₃ 174 (by decide)).trans hshift₂
  have hB₃ : s₃.regs 133 = b := (hr₃ 133 (by decide)).trans hB₂
  have hcap₃ : (s₃.arrs 12).length = N * N := by rw [hbuf₃, List.length_set, hcap₂]
  obtain ⟨s₄, he₄, hbuf₄, _, ha₄, hr₄⟩ :=
    gm06MarkRegisterProg_exec (s := s₃) (row := N * i) (shift := 0) (v := b) 133 hw
      (by simpa using haddrB.trans hsquare) hrow₃ hshift₃ hB₃
      (by rw [hcap₃]; simpa using haddrB)
  have hex : Exec w gm06EdgeRowProg s s₄ (15 + (t₂ + (9 + 9))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨s₄, _, hex, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbuf₄, hbuf₃, ha₂ 12, hbuf₁]
    simp only [Nat.add_zero]
  · exact (hr₄ 103 (by decide)).trans ((hr₃ 103 (by decide)).trans hp₂)
  · exact hs₂.of_arr_eq ((ha₄ 0 (by decide)).trans (ha₃ 0 (by decide)))
  · intro A hA
    exact (ha₄ A hA).trans ((ha₃ A hA).trans ((ha₂ A).trans (ha₁ A hA)))
  · intro q hqp hqv hqA hqB hqr hqs
    exact (hr₄ q hqv).trans ((hr₃ q hqv).trans
      ((hr₂ q hqp hqA hqB).trans (hr₁ q hqv hqr hqs)))

end GraphMinor.Compute
