module

public import GraphMinor.Compute.CrossingLiftEdgeFilter

/-!
# The parser header for the recorded search graph

After retaining increasing pairs, the output cursor gives twice the number of retained
edges plus the two header words. The program writes the runtime vertex count and that
edge count. The existing parser accepts the unused zero words after the edge list.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Fill the two parser header words after scanning the recorded pairs. -/
def liftEdgeHeaderProg (dst r_vertices r_pos : ℕ) : Cmd :=
  .seq (.write dst (.const 0) (.reg r_vertices))
    (.write dst (.const 1) (.op .div (.op .sub (.reg r_pos) (.const 2)) (.const 2)))

/-- The header records the runtime vertex count and the edge count read from the cursor.
The assumptions give the padded buffer, count/cursor registers and word bounds. -/
theorem liftEdgeHeaderProg_exec {w : ℕ} (dst r_vertices r_pos M m : ℕ)
    (F spare : List ℕ) (s : State)
    (hd : s.arrs dst = [0, 0] ++ F ++ spare)
    (hv : s.regs r_vertices = M) (hp : s.regs r_pos = 2 + 2 * m)
    (hw : M + 2 * m + 4 < 2 ^ w) :
    ∃ s', Exec w (liftEdgeHeaderProg dst r_vertices r_pos) s s' 10 ∧
      s'.arrs dst = [M, m] ++ F ++ spare ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧ (∀ q, s'.regs q = s.regs q) := by
  let s1 := s.writeArr dst 0 M
  have hd1 : s1.arrs dst = [M, 0] ++ F ++ spare := by
    simp [s1, hd]
  have hecount : (Expr.op .div (.op .sub (.reg r_pos) (.const 2)) (.const 2)).eval w s1 = some m := by
    have hs := eval_sub (w := w) (s := s1) (eval_reg hp (by omega)) (eval_const (show 2 < 2 ^ w by omega))
    rw [Expr.eval, hs, eval_const (by omega : 2 < 2 ^ w)]
    have he : 2 + 2 * m - 2 = 2 * m := by omega
    rw [he]
    simp [BinOp.eval, BinOp.raw, checkWord, show m < 2 ^ w by omega]
  have he1 : Exec w (.write dst (.const 0) (.reg r_vertices)) s s1 3 :=
    .write (eval_const (by omega)) (eval_reg hv (by omega))
      (by rw [hd]; simp)
  refine ⟨s1.writeArr dst 1 m, .seq he1 (.write (eval_const (by omega)) hecount
    (by rw [hd1]; simp)), ?_, ?_, fun _ => rfl⟩
  · simp [hd1]
  · intro a ha
    simp only [State.writeArr_arrs_ne _ _ _ ha, s1]

/-- Filter the pairs and finish the input of the existing parser. -/
def liftEdgeInputProg (src dst r_vertices R : ℕ) : Cmd :=
  .seq (liftEdgeFilterScanProg src dst R) (liftEdgeHeaderProg dst r_vertices (R + 1))

/-- The full edge preparation is linear in the recorded list. It assumes only storage,
word and layout bounds, and writes the parser format with permitted trailing words. -/
theorem liftEdgeInputProg_exec {w N : ℕ} (src dst r_vertices R M : ℕ)
    (hsd : src ≠ dst) (hvR : r_vertices < R) (E : List (Fin N × Fin N)) (s : State)
    (hs : s.arrs src = E.flatMap encPair) (hv : s.regs r_vertices = M)
    (hw : M + N + 8 * E.length + 16 < 2 ^ w) :
    ∃ s' t, Exec w (liftEdgeInputProg src dst r_vertices R) s s' t ∧
      t ≤ 100 * E.length + 40 ∧
      s'.arrs dst = [M, (liftSearchEdges E).length] ++ flatEdges (liftSearchEdges E) ++
        List.replicate (2 * (E.length - (liftSearchEdges E).length)) 0 ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ q < R, s'.regs q = s.regs q) := by
  obtain ⟨s1, t1, he1, ht1, ho1, hp1, ha1, hr1⟩ := liftEdgeFilterScanProg_exec (w := w)
    src dst R hsd E s hs (by omega)
  have hf := liftSearchEdges_length E
  obtain ⟨s2, he2, ho2, ha2, hr2⟩ := liftEdgeHeaderProg_exec (w := w)
    dst r_vertices (R + 1) M (liftSearchEdges E).length _ _ s1 ho1
    ((hr1 _ hvR).trans hv) hp1 (by omega)
  exact ⟨s2, t1 + 10, .seq he1 he2, by omega, ho2,
    fun a ha => (ha2 a ha).trans (ha1 a ha), fun q hq => (hr2 q).trans (hr1 q hq)⟩

end GraphMinor.Compute.Crossing
