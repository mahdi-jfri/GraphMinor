module

public import GraphMinor.Compute.GM06Alg34EdgeRow
public import GraphMinor.Compute.GM06Alg34EdgeRowsData

/-!
# Scanning supplied edges into the closure matrix

Read consecutive endpoint pairs, mark each edge closure row, and
advance its packed label. The count controls the scan, including the
empty edge list. The proof identifies the complete matrix updates and
bounds the work linearly in the number of supplied edges.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan the endpoint pairs counted in register 175 at packed edge label 171. -/
def gm06EdgeRowsLoopProg : Cmd :=
  .while (.reg 175) (.seq gm06EdgeRowProg
    (.seq (.assign 171 (.op .add (.reg 171) (.const 1)))
      (.assign 175 (.op .sub (.reg 175) (.const 1)))))

/-- The edge scan writes exactly the finite consecutive edge closure
rows in at most fifty-eight steps per edge plus its final count test. -/
theorem gm06EdgeRowsLoopProg_exec {w off N i : ℕ} (es : List (ℕ × ℕ)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hN : N < 2 ^ w) (hsquare : N * N < 2 ^ w)
    (hfit : i + es.length ≤ N) (hoff : off + 2 * es.length < 2 ^ w)
    (hvalid : ∀ p ∈ es, p.1 < N ∧ p.2 < N) {s : State}
    (hs : AtStream 0 off (gm06EdgeWords es ++ tail) s) (hp : s.regs 103 = off)
    (hc : s.regs 175 = es.length) (hNr : s.regs 170 = N) (hir : s.regs 171 = i)
    (hcap : (s.arrs 12).length = N * N) :
    ∃ s' t, Exec w gm06EdgeRowsLoopProg s s' t ∧ t ≤ 58 * es.length + 1 ∧
      s'.arrs 12 = gm06EdgeRows N i es (s.arrs 12) ∧
      s'.regs 103 = off + 2 * es.length ∧ s'.regs 171 = i + es.length ∧ s'.regs 175 = 0 ∧
      AtStream 0 (off + 2 * es.length) tail s' ∧
      (∀ A : ℕ, A ≠ 12 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 109 → q ≠ 132 → q ≠ 133 → q ≠ 171 →
        q ≠ 173 → q ≠ 174 → q ≠ 175 → s'.regs q = s.regs q) := by
  induction es generalizing off i s with
  | nil =>
    have he : (Expr.reg 175).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hc, Nat.zero_lt_of_lt hw]
    exact ⟨s, 1, .while_false he, by simp, rfl, by simpa using hp, by simpa using hir,
      hc, by simpa [gm06EdgeWords] using hs, fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | cons p es ih =>
    have hi : i < N := by simp only [List.length_cons] at hfit; omega
    have hiw := hi.trans hN
    have hi1w : i + 1 < 2 ^ w := by simp only [List.length_cons] at hfit; omega
    have hcw : es.length < 2 ^ w := by simp only [List.length_cons] at hfit; omega
    have hc1w : es.length + 1 < 2 ^ w := by simp only [List.length_cons] at hfit; omega
    have hsrow : AtStream 0 off (p.1 :: p.2 :: (gm06EdgeWords es ++ tail)) s := by
      simpa only [gm06EdgeWords, List.flatMap_cons, List.cons_append, List.nil_append] using hs
    obtain ⟨s₁, t₁, he₁, ht₁, hbuf₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      gm06EdgeRowProg_exec (gm06EdgeWords es ++ tail) hw hN hsquare hi
        (hvalid p List.mem_cons_self).1 (hvalid p List.mem_cons_self).2
        (by simp only [List.length_cons] at hoff; omega) hsrow hp hNr hir hcap
    have hi₁ : s₁.regs 171 = i :=
      (hr₁ 171 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hir
    have hc₁ : s₁.regs 175 = es.length + 1 := by
      simpa only [List.length_cons] using
        (hr₁ 175 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc
    have hN₁ : s₁.regs 170 = N :=
      (hr₁ 170 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hNr
    let s₂ := s₁.setReg 171 (i + 1)
    have he₂ : Exec w (.assign 171 (.op .add (.reg 171) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hiw, hi1w, hw])
    let s₃ := s₂.setReg 175 es.length
    have he₃ : Exec w (.assign 175 (.op .sub (.reg 175) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hc1w, hcw, hw])
    have hp₃ : s₃.regs 103 = off + 2 := by simp [s₃, s₂, hp₁]
    have hcap₃ : (s₃.arrs 12).length = N * N := by
      change (s₁.arrs 12).length = _
      rw [hbuf₁, List.length_set, List.length_set, List.length_set, hcap]
    obtain ⟨s₄, t₄, he₄, ht₄, hbuf₄, hp₄, hi₄, hc₄, hs₄, ha₄, hr₄⟩ :=
      ih (off := off + 2) (i := i + 1) (s := s₃)
        (by simp only [List.length_cons] at hfit; omega)
        (by simp only [List.length_cons] at hoff; omega)
        (fun p hp => hvalid p (List.mem_cons_of_mem _ hp))
        (hs₁.of_arr_eq (s' := s₃) rfl) hp₃ (by simp [s₃])
        (by simp [s₃, s₂, hN₁]) (by simp [s₃, s₂]) hcap₃
    have hecond : (Expr.reg 175).eval w s = some (es.length + 1) := by
      simp [Expr.eval, checkWord, hc, hc1w]
    have hex : Exec w gm06EdgeRowsLoopProg s s₄ (1 + (t₁ + (4 + 4)) + t₄) :=
      .while_true hecond (by omega) (.seq he₁ (.seq he₂ he₃)) he₄
    refine ⟨s₄, _, hex, by simp only [List.length_cons]; omega, ?_, ?_, ?_, hc₄, ?_, ?_, ?_⟩
    · rw [hbuf₄]
      change gm06EdgeRows N (i + 1) es (s₁.arrs 12) = _
      rw [hbuf₁]
      rfl
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega
    · convert hs₄ using 1 <;> simp only [List.length_cons] <;> omega
    · intro A hA
      exact (ha₄ A hA).trans (ha₁ A hA)
    · intro q hqp hqv hqA hqB hqi hqr hqs hqn
      rw [hr₄ q hqp hqv hqA hqB hqi hqr hqs hqn]
      change (s₂.setReg 175 es.length).regs q = _
      rw [State.setReg_regs_ne _ _ hqn, State.setReg_regs_ne _ _ hqi]
      exact hr₁ q hqp hqv hqA hqB hqr hqs

end GraphMinor.Compute
