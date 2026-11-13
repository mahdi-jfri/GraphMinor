module

public import GraphMinor.Compute.GM06Alg34InteriorCandidate

/-!
# Scanning source labels for an interior component

Visit consecutive supplied vertex labels, query each component, and
retain the first successful source. The proof follows the remaining
finite label list, so it also covers an empty graph. Every component
query reads the same prepared adjacency lists and cuff offset.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan the sources counted in 262, starting with source label 187. -/
def gm06InteriorFindLoopProg : Cmd :=
  .while (.reg 262) (.seq gm06InteriorCandidateProg
    (.seq (.assign 187 (.op .add (.reg 187) (.const 1)))
      (.assign 262 (.op .sub (.reg 262) (.const 1)))))

/-- The counted source scan computes exactly the finite first-success
search and costs at most a cubic number of steps for the full label range. -/
theorem gm06InteriorFindLoopProg_exec {w i : ℕ} (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (V : List (Fin x.n)) (found : Option ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hsquare : x.n * x.n < 2 ^ w)
    (hinputSize : x.words.length < 2 ^ w) (hfit : i + V.length ≤ x.n)
    (hlabels : V.map Fin.val = List.range' i V.length) {s : State}
    (hinput : s.arrs 0 = x.words) (hsize : s.regs 4 = x.n)
    (hsource : s.regs 187 = i) (hleft : s.regs 262 = V.length)
    (hcount : s.regs 105 = L.length) (hstart : s.regs 261 = x.cuffOffset + 2)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n) (hfound : gm06SingletonRegs found s) :
    ∃ s' t, Exec w gm06InteriorFindLoopProg s s' t ∧
      t ≤ (26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 50) * V.length + 1 ∧
      gm06SingletonRegs (found.or ((V.find? x.isInteriorComponent).map Fin.val)) s' ∧
      s'.regs 187 = i + V.length ∧ s'.regs 262 = 0 ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 111 →
        q ≠ 112 → q ≠ 113 → q ≠ 114 → q ≠ 187 → q ≠ 262 → s'.regs q = s.regs q) := by
  induction V generalizing i s found with
  | nil =>
    have hzero : s.regs 262 = 0 := hleft
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hzero, Nat.zero_lt_of_lt hw]),
      by simp, ?_, by simpa using hsource, hzero, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
    simpa using hfound
  | cons b V ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have hbval : b.val = i := hcons.1
    have htail : V.map Fin.val = List.range' (i + 1) V.length := hcons.2
    have hiw : i < 2 ^ w := by rw [← hbval]; exact b.isLt.trans hn
    have hi1w : i + 1 < 2 ^ w := (by simp only [List.length_cons] at hfit; omega : i + 1 ≤ x.n).trans_lt hn
    have hremw : V.length + 1 < 2 ^ w := (by simp only [List.length_cons] at hfit; omega : V.length + 1 ≤ x.n).trans_lt hn
    have hcond : (Expr.reg 262).eval w s = some (V.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hremw]
    obtain ⟨s₁, t₁, hex₁, ht₁, hfound₁, ha₁, hg₁⟩ :=
      gm06InteriorCandidateProg_exec x hL b found hw hn hsquare hinputSize hinput hsize
        (hbval.symm ▸ hsource) hcount hstart hlists hlen hfound
    have hsource₁ : s₁.regs 187 = i :=
      (hg₁ 187 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsource
    let s₂ := s₁.setReg 187 (i + 1)
    have hex₂ : Exec w (.assign 187 (.op .add (.reg 187) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hsource₁, hiw, hi1w, hw])
    have hleft₂ : s₂.regs 262 = V.length + 1 :=
      (hg₁ 262 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hleft
    let s₃ := s₂.setReg 262 V.length
    have hex₃ : Exec w (.assign 262 (.op .sub (.reg 262) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hleft₂, hremw, hw,
        show V.length < 2 ^ w by omega])
    have hkeep : ∀ q : ℕ, q = 4 ∨ q = 105 ∨ q = 261 → s₃.regs q = s.regs q := by
      intro q hq
      rcases hq with rfl | rfl | rfl <;>
        exact hg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    have hfound₃ : gm06SingletonRegs
        (found.or (if x.isInteriorComponent b then some b.val else none)) s₃ := hfound₁
    obtain ⟨s₄, t₄, hex₄, ht₄, hfound₄, hsource₄, hzero₄, ha₄, hg₄⟩ :=
      ih (i := i + 1) (s := s₃) _ (by simp only [List.length_cons] at hfit; omega) htail
        ((ha₁ 0 (by decide) (by decide)).trans hinput) ((hkeep _ (by decide)).trans hsize)
        (by simp [s₃, s₂]) (by simp [s₃]) ((hkeep _ (by decide)).trans hcount)
        ((hkeep _ (by decide)).trans hstart)
        (hlists.of_arrs_eq (ha₁ 30 (by decide) (by decide)) (ha₁ 31 (by decide) (by decide)) (ha₁ 32 (by decide) (by decide)))
        (by rw [show s₃.arrs 32 = s₁.arrs 32 from rfl, ha₁ 32 (by decide) (by decide)]; exact hlen) hfound₃
    have heq : (found.or (if x.isInteriorComponent b then some b.val else none)).or
        ((V.find? x.isInteriorComponent).map Fin.val) =
        found.or (((b :: V).find? x.isInteriorComponent).map Fin.val) := by
      cases found <;> cases hb : x.isInteriorComponent b <;> simp [List.find?, hb]
    refine ⟨s₄, 1 + (t₁ + (4 + 4)) + t₄, .while_true hcond (Nat.succ_ne_zero _)
      (.seq hex₁ (.seq hex₂ hex₃)) hex₄, ?_, heq ▸ hfound₄, ?_, hzero₄, ?_, ?_⟩
    · simp only [List.length_cons]
      rw [Nat.mul_succ]
      omega
    · simp only [List.length_cons]
      omega
    · intro A h33 h34
      exact (ha₄ A h33 h34).trans (ha₁ A h33 h34)
    · intro q hq h103 h108 h109 h111 h112 h113 h114 h187 h262
      rw [hg₄ q hq h103 h108 h109 h111 h112 h113 h114 h187 h262]
      change (s₂.setReg 262 V.length).regs q = _
      rw [State.setReg_regs_ne _ _ h262, State.setReg_regs_ne _ _ h187]
      exact hg₁ q hq h103 h108 h109 h111 h112 h113 h114

end GraphMinor.Compute
