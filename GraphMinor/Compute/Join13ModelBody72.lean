module

public import GraphMinor.Compute.Join13Endpoints72
public import GraphMinor.Compute.Join13VertexBits72

/-!
# Writing one model for the (7.2) subroutine

The routine writes the two dimensions of the model, its mapped edge endpoints,
and its branch-set vertex bits. It then advances the source and destination
positions. All other input data and registers are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Write one model and advance both stream positions. Registers at `r` through
`r + 5` hold source position, destination position, model vertex count, model edge
count, graph vertex count, and graph edge count. The counter is `r + 6`. -/
def writeModelBody72Prog (a_src a_ends a_dst r : ℕ) : Cmd :=
  .seq (bufPush2 a_dst (r + 1) (r + 2) (r + 3))
  (.seq (writeEndpoints72Prog a_src a_ends a_dst r (r + 1) (r + 3) (r + 6))
  (.seq (.assign (r + 1) (.op .add (.reg (r + 1)) (.op .mul (.const 2) (.reg (r + 3)))))
  (.seq (writeVertexBits72Prog a_src a_dst r (r + 1) (r + 3) (r + 2) (r + 4) (r + 5) (r + 6))
  (.seq (.assign (r + 1) (.op .add (.reg (r + 1)) (.op .mul (.reg (r + 2)) (.reg (r + 4)))))
        (.assign r (.op .add (.reg r) (.op .add (.reg (r + 3))
          (.op .mul (.reg (r + 2)) (.op .add (.reg (r + 4)) (.reg (r + 5)))))))))))

/-- One model is converted in time linear in its raw certificate length. -/
theorem writeModelBody72Prog_exec {w : ℕ} {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (a_src a_ends a_dst r : ℕ)
    (hsrc_dst : a_src ≠ a_dst) (hends_dst : a_ends ≠ a_dst)
    (pre_src post_src pre_dst : List ℕ) (rem : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : G.numVerts + G.numEdges < 2 ^ w)
    (hends_len : 2 * G.numEdges < 2 ^ w)
    (hvH : e.H.digraph.numVerts < 2 ^ w) (hmH : e.H.digraph.numEdges < 2 ^ w)
    (hrem : (encRawModel72 e).length ≤ rem)
    (hcap : pre_dst.length + rem < 2 ^ w)
    (hsrc_len : (pre_src ++ encRawCertEntry e ++ post_src).length < 2 ^ w)
    (hsrc : s.arrs a_src = pre_src ++ encRawCertEntry e ++ post_src)
    (hends : s.arrs a_ends = endpointWords72 G)
    (hdst : s.arrs a_dst = pre_dst ++ List.replicate rem 0)
    (hr_src : s.regs r = pre_src.length) (hr_dst : s.regs (r + 1) = pre_dst.length)
    (hr_vH : s.regs (r + 2) = e.H.digraph.numVerts)
    (hr_mH : s.regs (r + 3) = e.H.digraph.numEdges)
    (hr_n : s.regs (r + 4) = G.numVerts) (hr_m : s.regs (r + 5) = G.numEdges) :
    ∃ s' t, Exec w (writeModelBody72Prog a_src a_ends a_dst r) s s' t ∧
      t ≤ 60 * ((encRawCertEntry e).length + 1) ∧
      s'.arrs a_dst = pre_dst ++ encRawModel72 e ++
        List.replicate (rem - (encRawModel72 e).length) 0 ∧
      s'.regs r = (pre_src ++ encRawCertEntry e).length ∧
      s'.regs (r + 1) = (pre_dst ++ encRawModel72 e).length ∧
      Keeps [r, r + 1, r + 6] [a_dst] s s' := by
  let v := e.H.digraph.numVerts
  let m := e.H.digraph.numEdges
  let ends := (List.finRange m).flatMap (fun d =>
    [(G.tail (e.edgeMap d)).1, (G.head (e.edgeMap d)).1])
  let bits := (List.finRange v).flatMap (fun u => bitSetList (e.vertVerts u))
  have hends_words : ends.length = 2 * m := by
    simp [ends, List.length_flatMap, List.map_const', List.sum_replicate, Nat.mul_comm]
  have hbits : bits.length = v * G.numVerts := by
    simp [bits, List.length_flatMap, length_bitSetList, List.map_const', List.sum_replicate]
  have hraw : (encRawCertEntry e).length = m + v * (G.numVerts + G.numEdges) := by
    simp [encRawCertEntry, m, v, List.length_flatMap, length_bitSetList,
      List.map_const', List.sum_replicate]
  have hout : encRawModel72 e = [v, m] ++ ends ++ bits := rfl
  have hlen : (encRawModel72 e).length = 2 + 2 * m + v * G.numVerts := length_encRawModel72 e
  have hsrc_sz : pre_src.length + (encRawCertEntry e).length + post_src.length < 2 ^ w := by
    simpa only [List.length_append] using hsrc_len
  have hsize : 2 + 2 * e.H.digraph.numEdges + e.H.digraph.numVerts * G.numVerts ≤ rem := by
    rwa [length_encRawModel72] at hrem
  have hrawsz : pre_src.length + (e.H.digraph.numEdges +
      e.H.digraph.numVerts * (G.numVerts + G.numEdges)) + post_src.length < 2 ^ w := by
    simpa only [hraw, v, m] using hsrc_sz
  obtain ⟨s₁, t₁, hex₁, ht₁, hd₁, hr₁, ha₁, hreg₁⟩ :=
    bufPush2_exec a_dst (r + 1) (r + 2) (r + 3) pre_dst (rem - 2) v m hw
      (by dsimp only [v, m] at *; omega) hvH hmH
      (by simpa only [Nat.sub_add_cancel (show 2 ≤ rem by dsimp only [v, m] at *; omega)] using hdst)
      hr_dst hr_vH hr_mH
  have hs₁ : s₁.arrs a_src = pre_src ++ encRawCertEntry e ++ post_src := (ha₁ _ hsrc_dst).trans hsrc
  have he₁ : s₁.arrs a_ends = endpointWords72 G := (ha₁ _ hends_dst).trans hends
  have hr_src₁ : s₁.regs r = pre_src.length := (hreg₁ _ (by omega)).trans hr_src
  have hr_mH₁ : s₁.regs (r + 3) = m := (hreg₁ _ (by omega)).trans hr_mH
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hd₂⟩ :=
    writeEndpoints72Prog_exec e a_src a_ends a_dst r (r + 1) (r + 3) (r + 6)
      hsrc_dst hends_dst (by first | omega | (dsimp [Reg, Arr]; omega)) (by first | omega | (dsimp [Reg, Arr]; omega)) (by first | omega | (dsimp [Reg, Arr]; omega))
      pre_src post_src (pre_dst ++ [v, m]) (rem - 2) s₁ hw (by omega) hends_len
      (by dsimp only [v, m] at *; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hsrc_len hs₁ he₁ hd₁ hr_src₁ hr₁ hr_mH₁
  have hregs₂ (j : ℕ) (h1 : j ≠ r + 1) (h6 : j ≠ r + 6) : s₂.regs j = s.regs j :=
    (hk₂.1 j (by simpa using h6)).trans (hreg₁ j h1)
  have hdst₂ : s₂.regs (r + 1) = pre_dst.length + 2 := by
    rw [hk₂.1 (r + 1) (by simp), hr₁]
    simp
  let s₃ := s₂.setReg (r + 1) (pre_dst.length + 2 + 2 * m)
  have hex₃ : Exec w (.assign (r + 1) (.op .add (.reg (r + 1))
      (.op .mul (.const 2) (.reg (r + 3))))) s₂ s₃ 6 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hdst₂,
      hregs₂ (r + 3) (by omega) (by omega), hr_mH, m,
      show pre_dst.length + 2 < 2 ^ w by dsimp only [v, m] at *; omega,
      show 2 * e.H.digraph.numEdges < 2 ^ w by dsimp only [v, m] at *; omega,
      show pre_dst.length + 2 + 2 * e.H.digraph.numEdges < 2 ^ w by omega,
      hw, hmH]
  have hregs₃ (j : ℕ) (h1 : j ≠ r + 1) (h6 : j ≠ r + 6) : s₃.regs j = s.regs j := by
    rw [State.setReg_regs_ne _ _ h1]
    exact hregs₂ j h1 h6
  obtain ⟨s₄, t₄, hex₄, ht₄, hk₄, hd₄⟩ :=
    writeVertexBits72Prog_exec e a_src a_dst r (r + 1) (r + 3) (r + 2) (r + 4) (r + 5) (r + 6)
      hsrc_dst (by first | omega | (dsimp [Reg, Arr]; omega)) (by first | omega | (dsimp [Reg, Arr]; omega)) (by first | omega | (dsimp [Reg, Arr]; omega)) (by first | omega | (dsimp [Reg, Arr]; omega)) (by first | omega | (dsimp [Reg, Arr]; omega)) (by first | omega | (dsimp [Reg, Arr]; omega))
      pre_src post_src ((pre_dst ++ [v, m]) ++ ends) (rem - 2 - ends.length) s₃
      (by omega) hn hvH hmH
      (by rw [hlen] at hrem; rw [hends_words]; omega)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hsrc_len
      (by exact (hk₂.2 _ (by simpa using hsrc_dst)).trans hs₁)
      hd₂ (by rw [hregs₃ r (by omega) (by omega), hr_src])
      (by simp only [s₃, State.setReg_regs_self, List.length_append, List.length_cons, List.length_nil, hends_words])
      (by rw [hregs₃ _ (by omega) (by omega), hr_mH])
      (by rw [hregs₃ _ (by omega) (by omega), hr_vH])
      (by rw [hregs₃ _ (by omega) (by omega), hr_n])
      (by rw [hregs₃ _ (by omega) (by omega), hr_m])
  have hregs₄ (j : ℕ) (h1 : j ≠ r + 1) (h6 : j ≠ r + 6) : s₄.regs j = s.regs j :=
    (hk₄.1 j (by simpa using h6)).trans (hregs₃ j h1 h6)
  have hdst₄ : s₄.regs (r + 1) = pre_dst.length + 2 + 2 * m := by
    rw [hk₄.1 (r + 1) (by simp)]
    simp [s₃]
  let s₅ := s₄.setReg (r + 1) (pre_dst.length + (encRawModel72 e).length)
  have hex₅ : Exec w (.assign (r + 1) (.op .add (.reg (r + 1))
      (.op .mul (.reg (r + 2)) (.reg (r + 4))))) s₄ s₅ 6 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hdst₄,
      hregs₄ (r + 2) (by omega) (by omega), hregs₄ (r + 4) (by omega) (by omega),
      hr_vH, hr_n, v, m, hlen, hvH,
      show G.numVerts < 2 ^ w by omega,
      show e.H.digraph.numVerts * G.numVerts < 2 ^ w by dsimp only [v, m] at *; omega,
      show pre_dst.length + (2 + 2 * e.H.digraph.numEdges) < 2 ^ w by omega,
      show pre_dst.length + (2 + (2 * e.H.digraph.numEdges + e.H.digraph.numVerts * G.numVerts)) < 2 ^ w by omega,
      Nat.add_assoc]
  let s₆ := s₅.setReg r (pre_src.length + (encRawCertEntry e).length)
  have hregs₅ (j : ℕ) (h1 : j ≠ r + 1) (h6 : j ≠ r + 6) : s₅.regs j = s.regs j := by
    rw [State.setReg_regs_ne _ _ h1]
    exact hregs₄ j h1 h6
  have hex₆ : Exec w (.assign r (.op .add (.reg r) (.op .add (.reg (r + 3))
      (.op .mul (.reg (r + 2)) (.op .add (.reg (r + 4)) (.reg (r + 5))))))) s₅ s₆ 10 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hregs₅ r (by omega) (by omega), hregs₅ (r + 2) (by omega) (by omega),
      hregs₅ (r + 3) (by omega) (by omega), hregs₅ (r + 4) (by omega) (by omega),
      hregs₅ (r + 5) (by omega) (by omega), hr_src, hr_vH, hr_mH, hr_n, hr_m,
      hraw, v, m, hn, hvH, hmH,
      show pre_src.length < 2 ^ w by omega,
      show G.numVerts < 2 ^ w by omega, show G.numEdges < 2 ^ w by omega,
      show e.H.digraph.numVerts * (G.numVerts + G.numEdges) < 2 ^ w by omega,
      show e.H.digraph.numEdges + e.H.digraph.numVerts * (G.numVerts + G.numEdges) < 2 ^ w by omega,
      show pre_src.length + (e.H.digraph.numEdges + e.H.digraph.numVerts * (G.numVerts + G.numEdges)) < 2 ^ w by omega]
  refine ⟨s₆, t₁ + (t₂ + (6 + (t₄ + (6 + 10)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_, ?_, ?_, ?_, ?_⟩
  · have hmul := Nat.mul_le_mul_left v (Nat.le_add_right G.numVerts G.numEdges)
    rw [hraw, Nat.mul_add, Nat.mul_add]
    dsimp [v, m] at ht₂ ht₄ hmul ⊢
    omega
  · change s₄.arrs a_dst = _
    change s₄.arrs a_dst = pre_dst ++ [v, m] ++ ends ++ bits ++
      List.replicate (rem - 2 - ends.length - bits.length) 0 at hd₄
    have hlenSum : 2 + ends.length + bits.length = (encRawModel72 e).length := by
      rw [hends_words, hbits, hlen]
    have hsub : rem - 2 - ends.length - bits.length = rem - (encRawModel72 e).length := by omega
    simpa only [hout, List.append_assoc, hsub] using hd₄
  · simp [s₆]
  · simp [s₆, s₅, List.length_append]
  · refine ⟨fun j hj => ?_, fun a ha => ?_⟩
    · have hj' : j ≠ r ∧ j ≠ r + 1 ∧ j ≠ r + 6 := by simpa using hj
      rw [State.setReg_regs_ne _ _ hj'.1]
      exact hregs₅ j hj'.2.1 hj'.2.2
    · change s₄.arrs a = s.arrs a
      have hne' : a ≠ a_dst := by simpa using ha
      exact (hk₄.2 a ha).trans ((hk₂.2 a ha).trans (ha₁ a hne'))

end GraphMinor.Compute
