module

public import GraphMinor.Compute.GM06Alg34BlockQuery

/-!
# Reading and testing a nonempty division block

Read its first label as the search source, subtract one from the
supplied length, then search and check the remaining labels. The
cursor finishes at the next block and the component tables survive.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Consume a nonempty block whose length has already been read into 108. -/
def gm06BlockBodyProg : Cmd :=
  .seq (readStreamWordProg 0 103 187)
    (.seq (.assign 108 (.op .sub (.reg 108) (.const 1))) gm06BlockQueryProg)

/-- Reading the first label and querying its component computes the
whole nonempty block's reachability conjunction from the supplied stream. -/
theorem gm06BlockBodyProg_exec {w off : ℕ} (x : GM06DrawingData) (a : Fin x.n)
    (L : List (Fin x.n)) (tail : List ℕ) (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hsquare : x.n * x.n < 2 ^ w) (hend : off + 1 + L.length < 2 ^ w)
    {s : State} (hsize : s.regs 4 = x.n)
    (hlists : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s)
    (hlen : (s.arrs 32).length = x.n * x.n)
    (hs : AtStream 0 off ((a :: L).map Fin.val ++ tail) s)
    (hp : s.regs 103 = off) (hcount : s.regs 108 = L.length + 1) :
    ∃ s' t, Exec w gm06BlockBodyProg s s' t ∧
      t ≤ 26 * (x.n * x.n) + 23 * x.n + 22 * L.length + 43 ∧
      s'.regs 112 = (if L.all (fun b => decide (x.vertexGraph.Reachable a b)) then 1 else 0) ∧
      s'.regs 103 = off + 1 + L.length ∧
      AtStream 0 (off + 1 + L.length) tail s' ∧
      (∀ A : ℕ, A ≠ 33 → A ≠ 34 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, (q < 190 ∨ 197 ≤ q) → q ≠ 103 → q ≠ 108 → q ≠ 109 → q ≠ 112 → q ≠ 187 →
        s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hsource₁, hp₁, hs₁, ha₁, hg₁⟩ :=
    readStreamWordProg_exec 103 187 (by decide) hw (by omega) (a.isLt.trans hn)
      (by simpa only [List.map_cons, List.cons_append] using hs) hp
  have hc₁ : s₁.regs 108 = L.length + 1 := (hg₁ 108 (by decide) (by decide)).trans hcount
  let s₂ := s₁.setReg 108 L.length
  have hex₂ : Exec w (.assign 108 (.op .sub (.reg 108) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁,
      show L.length + 1 < 2 ^ w by omega, show L.length < 2 ^ w by omega, hw])
  have hsize₂ : s₂.regs 4 = x.n := by
    simpa [s₂] using (hg₁ 4 (by decide) (by decide)).trans hsize
  have hsource₂ : s₂.regs 187 = a.val := by simpa [s₂] using hsource₁
  have hadj₂ : IsAdjList x.vertexGraph 30 31 32 (adjListOf x.vertexGraph) s₂ := by
    exact hlists.of_arrs_eq (ha₁ 30) (ha₁ 31) (ha₁ 32)
  have hlen₂ : (s₂.arrs 32).length = x.n * x.n := by simpa only [s₂, State.setReg_arrs, ha₁] using hlen
  obtain ⟨s₃, t₃, hex₃, ht₃, hans₃, hp₃, _, hs₃, ha₃, hg₃⟩ :=
    gm06BlockQueryProg_exec x a L tail hw hn hsquare hend hsize₂ hsource₂ hadj₂ hlen₂
      (hs₁.of_arr_eq rfl) (by simpa [s₂] using hp₁) (by simp [s₂])
  refine ⟨s₃, t₁ + (4 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hans₃, hp₃, hs₃, ?_, ?_⟩
  · intro A h33 h34
    exact (ha₃ A h33 h34).trans (ha₁ A)
  · intro q hq h103 h108 h109 h112 h187
    rw [hg₃ q hq h103 h108 h109 h112]
    exact (State.setReg_regs_ne _ _ h108).trans (hg₁ q h103 h187)

end GraphMinor.Compute
