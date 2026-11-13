module

public import GraphMinor.Compute.GM06Alg34EdgeMaskData
public import GraphMinor.Compute.GM06Alg34Layout

/-!
# Building the surviving-edge mask from the supplied endpoint array

Allocate one slot per supplied edge using the parsed header count.
Reset the endpoint cursor to the beginning of the endpoint section,
then run the verified edge scan. The result is the exact surviving-edge
mask, including when the graph has no edges.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The finite edge-label stream is the supplied endpoint section. -/
theorem gm06EdgeStream_all (x : GM06DrawingData) :
    gm06EdgeStream x (List.finRange x.ends.length) = x.endpointWords := by
  have hh := congrArg (fun es : List (Fin x.n × Fin x.n) =>
    es.flatMap (fun e => [e.1.val, e.2.val])) (List.map_get_finRange x.ends)
  simp only [List.flatMap_map, Function.comp_def] at hh
  exact hh

/-- Allocate and fill the surviving-edge mask using the parsed edge count. -/
def gm06EdgeMaskProg : Cmd :=
  .seq (.alloc 6 (.reg 101))
    (.seq (.assign 134 (.reg 101))
      (.seq (.assign 135 (.const 0))
        (.seq (.assign 103 (.const 3)) gm06EdgeMaskLoopProg)))

/-- The supplied endpoint section yields the exact induced-edge mask in
array 6 in linear time. The vertex mask and all other arrays are preserved. -/
theorem gm06EdgeMaskProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (tail : List ℕ)
    (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : 3 + 2 * x.ends.length < 2 ^ w) {s : State}
    (hstream : AtStream 0 3 (x.endpointWords ++ tail) s)
    (hcount : s.regs 101 = x.ends.length)
    (hmask : s.arrs 4 = gm06VertexMask vs) :
    ∃ s' t, Exec w gm06EdgeMaskProg s s' t ∧ t ≤ 41 * x.ends.length + 8 ∧
      s'.arrs 6 = gm06EdgeMask x vs ∧ s'.regs 103 = 3 + 2 * x.ends.length ∧
      AtStream 0 (3 + 2 * x.ends.length) tail s' ∧
      (∀ a : ℕ, a ≠ 6 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → q ≠ 134 → q ≠ 135 →
        s'.regs q = s.regs q) := by
  have hm : x.ends.length < 2 ^ w := by omega
  let s₀ := s.setArr 6 (List.replicate x.ends.length 0)
  let s₁ := s₀.setReg 134 x.ends.length
  let s₂ := s₁.setReg 135 0
  let s₃ := s₂.setReg 103 3
  have he₀ : Exec w (.alloc 6 (.reg 101)) s s₀ (1 + x.ends.length) :=
    .alloc (by simp [Expr.eval, checkWord, hcount, hm])
  have he₁ : Exec w (.assign 134 (.reg 101)) s₀ s₁ 2 :=
    .assign (by simp [s₀, Expr.eval, checkWord, hcount, hm])
  have he₂ : Exec w (.assign 135 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have he₃ : Exec w (.assign 103 (.const 3)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hs₃ : AtStream 0 3 (gm06EdgeStream x (List.finRange x.ends.length) ++ tail) s₃ := by
    rw [gm06EdgeStream_all]
    exact hstream.of_arr_eq (by simp [s₃, s₂, s₁, s₀])
  obtain ⟨s₄, t₄, he₄, ht₄, hout₄, hp₄, _, _, hs₄, ha₄, hr₄⟩ :=
    gm06EdgeMaskLoopProg_exec (off := 3) (k := 0) (s := s₃) x vs (List.finRange x.ends.length) tail (by omega) hn
      (by simpa only [List.length_finRange] using hoff)
      (by simpa only [List.length_finRange, Nat.zero_add] using hm)
      hs₃ (by simp [s₃]) (by simp [s₃, s₂]) (by simp [s₃, s₂, s₁])
      (by simpa [s₃, s₂, s₁, s₀] using hmask)
      (by simp [s₃, s₂, s₁, s₀])
  have he : Exec w gm06EdgeMaskProg s s₄ ((1 + x.ends.length) + (2 + (2 + (2 + t₄)))) :=
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄)))
  refine ⟨s₄, _, he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_finRange] at ht₄
    omega
  · rw [hout₄]
    exact gm06EdgeMaskWrites_all x vs _ (by simp [s₃, s₂, s₁, s₀])
  · simpa only [List.length_finRange] using hp₄
  · simpa only [List.length_finRange] using hs₄
  · intro a ha
    exact he.arrs_eq_of_not_mem_writtenArrs (by
      simp [gm06EdgeMaskProg, gm06EdgeMaskLoopProg, gm06EdgeMaskStepProg,
        gm06ReadEndsProg, readStreamWordProg, Cmd.writtenArrs, ha])
  · intro q hq hqA hqB hqc hqi
    exact he.regs_eq_of_not_mem_writtenRegs (by
      simp [gm06EdgeMaskProg, gm06EdgeMaskLoopProg, gm06EdgeMaskStepProg,
        gm06ReadEndsProg, readStreamWordProg, Cmd.writtenRegs, hq, hqA, hqB, hqc, hqi])

end GraphMinor.Compute
