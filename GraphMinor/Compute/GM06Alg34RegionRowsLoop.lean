module

public import GraphMinor.Compute.GM06Alg34RegionRow
public import GraphMinor.Compute.GM06Alg34RegionRowsData

/-!
# Marking the supplied region rows on the RAM

Scan the old regions in their supplied order. For each row, mark its
closure and advance the packed region label. The supplied region count
controls termination. The proof records exactly the consecutive finite
row updates, and work is linear in the encoded region boundary stream.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan the supplied regions counted in register 175 at packed index 171. -/
def gm06RegionRowsLoopProg : Cmd :=
  .while (.reg 175) (.seq gm06RegionRowProg
    (.seq (.assign 171 (.op .add (.reg 171) (.const 1)))
      (.assign 175 (.op .sub (.reg 175) (.const 1)))))

/-- The counted region scan performs exactly the consecutive supplied
closure-row updates, with linear work in the original encoded stream. -/
theorem gm06RegionRowsLoopProg_exec {w off N i n : ℕ}
    (rs : List (List ℕ × List ℕ)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hn : n < 2 ^ w) (hsquare : N * N < 2 ^ w)
    (hfit : i + rs.length ≤ N) (hoff : off + (gm06RegionWords rs).length < 2 ^ w)
    (hvalid : ∀ r ∈ rs, (∀ v ∈ r.1, v < N) ∧ (∀ e ∈ r.2, n + e < N))
    {s : State} (hs : AtStream 0 off (gm06RegionWords rs ++ tail) s)
    (hp : s.regs 103 = off) (hc : s.regs 175 = rs.length)
    (hNr : s.regs 170 = N) (hir : s.regs 171 = i) (hnr : s.regs 100 = n)
    (hcap : (s.arrs 12).length = N * N) :
    ∃ s' t, Exec w gm06RegionRowsLoopProg s s' t ∧
      t ≤ 25 * (gm06RegionWords rs).length + 1 ∧
      s'.arrs 12 = gm06RegionRows N n i rs (s.arrs 12) ∧
      s'.regs 103 = off + (gm06RegionWords rs).length ∧
      s'.regs 171 = i + rs.length ∧ s'.regs 175 = 0 ∧
      AtStream 0 (off + (gm06RegionWords rs).length) tail s' ∧
      (∀ a : ℕ, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 171 → q ≠ 172 → q ≠ 173 →
        q ≠ 174 → q ≠ 175 → s'.regs q = s.regs q) := by
  induction rs generalizing off i s with
  | nil =>
    have he : (Expr.reg 175).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hc, Nat.zero_lt_of_lt hw]
    exact ⟨s, 1, .while_false he, by simp [gm06RegionWords], rfl,
      by simpa [gm06RegionWords] using hp, by simpa using hir, hc,
      by simpa [gm06RegionWords] using hs, fun _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  | cons r rs ih =>
    have hold := gm06RegionWords_cons_length r rs
    have hi : i < N := by simp only [List.length_cons] at hfit; omega
    have hiw := hi.trans hN
    have hi1w : i + 1 < 2 ^ w := by simp only [List.length_cons] at hfit; omega
    have hc1w : rs.length + 1 < 2 ^ w := by simp only [List.length_cons] at hfit; omega
    have hcw : rs.length < 2 ^ w := by omega
    have hsrow : AtStream 0 off
        (GM06DrawingData.listWords r.1 ++ GM06DrawingData.listWords r.2 ++
          (gm06RegionWords rs ++ tail)) s := by
      simpa only [gm06RegionWords, List.append_assoc] using hs
    obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hp₁, hs₁, _, _, ha₁, hr₁⟩ :=
      gm06RegionRowProg_exec r.1 r.2 (gm06RegionWords rs ++ tail) hw hN hn hi hsquare
        (by omega) hsrow hp hNr hir hnr hcap (hvalid r List.mem_cons_self).1
        (hvalid r List.mem_cons_self).2
    have hi₁ : s₁.regs 171 = i :=
      (hr₁ 171 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hir
    have hc₁ : s₁.regs 175 = rs.length + 1 := by
      simpa only [List.length_cons] using
        (hr₁ 175 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
    have hN₁ : s₁.regs 170 = N :=
      (hr₁ 170 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hNr
    have hn₁ : s₁.regs 100 = n :=
      (hr₁ 100 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnr
    let s₂ := s₁.setReg 171 (i + 1)
    have he₂ : Exec w (.assign 171 (.op .add (.reg 171) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hiw, hi1w, hw])
    let s₃ := s₂.setReg 175 rs.length
    have he₃ : Exec w (.assign 175 (.op .sub (.reg 175) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hc1w, hcw, hw])
    have hp₃ : s₃.regs 103 = off + 2 + r.1.length + r.2.length := by simp [s₃, s₂, hp₁]
    have hcap₃ : (s₃.arrs 12).length = N * N := by
      change (s₁.arrs 12).length = _
      rw [hbuf₁, gm06MarkCells_length, gm06MarkCells_length, List.length_set, hcap]
    obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hp₄, hi₄, hc₄, hs₄, ha₄, hr₄⟩ :=
      ih (off := off + 2 + r.1.length + r.2.length) (i := i + 1) (s := s₃)
        (by simp only [List.length_cons] at hfit; omega) (by omega)
        (fun r hr => hvalid r (List.mem_cons_of_mem _ hr))
        (hs₁.of_arr_eq (s' := s₃) rfl) hp₃ (by simp [s₃])
        (by simp [s₃, s₂, hN₁]) (by simp [s₃, s₂]) (by simp [s₃, s₂, hn₁]) hcap₃
    have hecond : (Expr.reg 175).eval w s = some (rs.length + 1) := by
      simp [Expr.eval, checkWord, hc, hc1w]
    have hex : Exec w gm06RegionRowsLoopProg s s₄ (1 + (t₁ + (4 + 4)) + t₄) :=
      .while_true hecond (by omega) (.seq he₁ (.seq he₂ he₃)) he₄
    refine ⟨s₄, _, hex, by omega, ?_, ?_, ?_, hc₄, ?_, ?_, ?_⟩
    · rw [hbuf₄]
      change gm06RegionRows N n (i + 1) rs (s₁.arrs 12) = _
      rw [hbuf₁]
      rfl
    · omega
    · simp only [List.length_cons]
      omega
    · convert hs₄ using 1 <;> omega
    · intro a ha
      exact (ha₄ a ha).trans (ha₁ a ha)
    · intro q hqp hqv hqi hqc hqr hqs hqn
      rw [hr₄ q hqp hqv hqi hqc hqr hqs hqn]
      change (s₂.setReg 175 rs.length).regs q = _
      rw [State.setReg_regs_ne _ _ hqn, State.setReg_regs_ne _ _ hqi]
      exact hr₁ q hqp hqv hqc hqr hqs

end GraphMinor.Compute
