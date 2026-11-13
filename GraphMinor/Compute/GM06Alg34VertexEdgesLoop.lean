module

public import GraphMinor.Compute.GM06Alg34VertexEdgeRead

/-!
# Scanning all supplied edges into the vertex matrix

A remaining-edge counter drives the endpoint stream scan. Induction on
the supplied edge list proves the exact folded row marks and cursor
position. Each edge takes a bounded number of steps, and all other
arrays and all registers outside the endpoint scan remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read and mark the edge pairs counted in register 260. -/
def gm06VertexEdgesLoopProg : Cmd :=
  .while (.reg 260) (.seq gm06VertexEdgeReadProg
    (.assign 260 (.op .sub (.reg 260) (.const 1))))

/-- The endpoint loop produces the exact finite folded adjacency marks
in time linear in the supplied edge count. -/
theorem gm06VertexEdgesLoopProg_exec {w off n : ℕ} (es : List (Fin n × Fin n))
    (tail : List ℕ) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hsquare : n * n < 2 ^ w)
    (hoff : off + 2 * es.length < 2 ^ w) {s : State}
    (hs : AtStream 0 off ((es.flatMap (fun e => [e.1.val, e.2.val])) ++ tail) s)
    (hp : s.regs 103 = off) (hNr : s.regs 100 = n) (hcount : s.regs 260 = es.length)
    (hcap : (s.arrs 28).length = n * n) :
    ∃ s' t, Exec w gm06VertexEdgesLoopProg s s' t ∧ t ≤ 38 * es.length + 1 ∧
      s'.arrs 28 = (es.flatMap gm06VertexEdgeRows).foldl (gm06MatrixMarkRow n) (s.arrs 28) ∧
      s'.regs 103 = off + 2 * es.length ∧ s'.regs 260 = 0 ∧
      AtStream 0 (off + 2 * es.length) tail s' ∧
      (∀ a : ℕ, a ≠ 28 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → q ≠ 260 → s'.regs q = s.regs q) := by
  induction es generalizing off s with
  | nil =>
    have hz : s.regs 260 = 0 := hcount
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw]),
      by simp, by simp, by simpa using hp, hz, ?_, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
    simpa using hs
  | cons e es ih =>
    have hcountw : es.length + 1 < 2 ^ w := by
      simp only [List.length_cons] at hoff
      omega
    have hcond : (Expr.reg 260).eval w s = some (es.length + 1) := by
      simp [Expr.eval, checkWord, hcount, hcountw]
    obtain ⟨s₁, t₁, hex₁, ht₁, hmat₁, hp₁, hs₁, ha₁, hg₁⟩ :=
      gm06VertexEdgeReadProg_exec e (es.flatMap (fun e => [e.1.val, e.2.val]) ++ tail)
        hw hn hsquare (by simp only [List.length_cons, Nat.mul_succ] at hoff; omega)
        (by simpa only [List.flatMap_cons, List.cons_append, List.nil_append] using hs) hp hNr hcap
    have hcount₁ : s₁.regs 260 = es.length + 1 := by
      rw [hg₁ 260 (by decide) (by decide) (by decide), hcount]; rfl
    let s₂ := s₁.setReg 260 es.length
    have hex₂ : Exec w (.assign 260 (.op .sub (.reg 260) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount₁, hw,
        show es.length + 1 < 2 ^ w from hcountw, show es.length < 2 ^ w by omega])
    have hcap₂ : (s₂.arrs 28).length = n * n := by
      change (s₁.arrs 28).length = _
      rw [hmat₁, gm06MatrixMarkRows_length, hcap]
    obtain ⟨s₃, t₃, hex₃, ht₃, hmat₃, hp₃, hz₃, hs₃, ha₃, hg₃⟩ :=
      ih (off := off + 2) (s := s₂) (by simp only [List.length_cons, Nat.mul_succ] at hoff; omega)
        hs₁ (by simpa [s₂] using hp₁)
        (by rw [show s₂.regs 100 = s₁.regs 100 from rfl, hg₁ 100 (by decide) (by decide) (by decide)]; exact hNr)
        (by simp [s₂]) hcap₂
    refine ⟨s₃, 1 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃, ?_, ?_, ?_, hz₃, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      rw [Nat.mul_succ]
      omega
    · rw [hmat₃]
      change _ = _
      rw [show s₂.arrs 28 = s₁.arrs 28 from rfl, hmat₁]
      simp only [List.flatMap_cons, List.foldl_append]
    · simp only [List.length_cons, Nat.mul_succ]
      omega
    · convert hs₃ using 1 <;> simp only [List.length_cons, Nat.mul_succ] <;> omega
    · intro a ha
      exact (ha₃ a ha).trans (ha₁ a ha)
    · intro q h103 h132 h133 h260
      exact (hg₃ q h103 h132 h133 h260).trans
        ((show s₂.regs q = s₁.regs q from State.setReg_regs_ne _ _ h260).trans
          (hg₁ q h103 h132 h133))

end GraphMinor.Compute
