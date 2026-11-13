module

public import GraphMinor.Compute.GM06Alg34VertexRanks
public import GraphMinor.Compute.GM06Alg34RankLabels
public import GraphMinor.Compute.GM06Alg34EdgeRanks
public import GraphMinor.Compute.GM06Alg34EndsProg

/-!
# Building all finite relabelling tables for induced deletion

Save the original cuff cursor, compute the surviving vertex ranks,
scan old endpoints for the edge mask, compute edge ranks, and emit the
new endpoints. The saved cuff cursor survives the endpoint scans and
allows later output passes to resume the original cuff section.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Compute ranks, edge survival, and new endpoints, saving cursor 103 in 176. -/
def gm06DeletionLabelTablesProg : Cmd :=
  .seq (.assign 176 (.reg 103))
    (.seq gm06VertexRanksProg
      (.seq gm06EdgeMaskProg (.seq gm06EdgeRanksProg gm06EndsProg)))

/-- The complete relabelling-table pass computes exact induced vertex
and edge tables and endpoint words, with a linear RAM time bound. -/
theorem gm06DeletionLabelTablesProg_exec {w p : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (tail : List ℕ) (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hoff : 3 + 2 * x.ends.length < 2 ^ w) (hp : p < 2 ^ w) {s : State}
    (hstream : AtStream 0 3 (x.endpointWords ++ tail) s)
    (hcount : s.regs 101 = x.ends.length) (hcursor : s.regs 103 = p)
    (hmask : s.arrs 4 = gm06VertexMask vs) :
    ∃ s' t, Exec w gm06DeletionLabelTablesProg s s' t ∧
      t ≤ 23 * x.n + 109 * x.ends.length + 2 * (x.activeEdges vs).length + 36 ∧
      s'.arrs 5 = gm06VertexRanks vs ∧ s'.arrs 6 = gm06EdgeMask x vs ∧
      s'.arrs 7 = gm06EdgeRanks x vs ∧ s'.arrs 8 = (x.inducedData vs).endpointWords ∧
      s'.regs 131 = (x.activeVertices vs).length ∧ s'.regs 137 = (x.activeEdges vs).length ∧
      s'.regs 176 = p ∧
      (∀ a : ℕ, a ≠ 5 → a ≠ 6 → a ≠ 7 → a ≠ 8 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 130 → q ≠ 131 → q ≠ 132 → q ≠ 133 → q ≠ 134 →
        q ≠ 135 → q ≠ 136 → q ≠ 137 → q ≠ 176 → s'.regs q = s.regs q) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : x.ends.length < 2 ^ w := by omega
  have hnew : 2 * (x.activeEdges vs).length < 2 ^ w := by
    have hle : (x.activeEdges vs).length ≤ x.ends.length := by
      rw [← gm06EdgeMask_sum]; exact gm06EdgeMask_sum_le x vs
    exact (Nat.mul_le_mul_left 2 hle).trans_lt (by omega)
  let s₀ := s.setReg 176 p
  have hex₀ : Exec w (.assign 176 (.reg 103)) s s₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hcursor, hp])
  obtain ⟨s₁, t₁, hex₁, ht₁, hV, hnewV, harr₁, hreg₁⟩ :=
    gm06VertexRanksProg_exec vs hw1 hn (s := s₀) hmask
  obtain ⟨s₂, t₂, hex₂, ht₂, hE, _, _, harr₂, hreg₂⟩ :=
    gm06EdgeMaskProg_exec x vs tail hw hn hoff
      (hstream.of_arr_eq (harr₁ 0 (by decide)))
      ((hreg₁ _ (by decide) (by decide)).trans (by simpa [s₀] using hcount))
      ((harr₁ _ (by decide)).trans hmask)
  obtain ⟨s₃, t₃, hex₃, ht₃, hR, hnewE, harr₃, hreg₃⟩ :=
    gm06EdgeRanksProg_exec x vs hw1 hmw hE
  obtain ⟨s₄, t₄, hex₄, ht₄, hends, _, _, harr₄, hreg₄⟩ :=
    gm06EndsProg_exec x vs tail hw hn hoff hnew
      (hstream.of_arr_eq ((harr₃ 0 (by decide)).trans
        ((harr₂ 0 (by decide)).trans (harr₁ 0 (by decide)))))
      ((hreg₃ _ (by decide) (by decide)).trans
        ((hreg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          ((hreg₁ _ (by decide) (by decide)).trans (by simpa [s₀] using hcount))))
      hnewE
      ((harr₃ 5 (by decide)).trans ((harr₂ 5 (by decide)).trans hV)) hR
      ((harr₃ 6 (by decide)).trans hE)
  refine ⟨s₄, 2 + (t₁ + (t₂ + (t₃ + t₄))),
    Exec.seq hex₀ (Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ hex₄))), by omega,
    (harr₄ 5 (by decide)).trans ((harr₃ 5 (by decide)).trans ((harr₂ 5 (by decide)).trans hV)),
    (harr₄ 6 (by decide)).trans ((harr₃ 6 (by decide)).trans hE),
    (harr₄ 7 (by decide)).trans hR, hends, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hreg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₃ _ (by decide) (by decide),
      hreg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide), hnewV,
      x.vertexMask_sum_eq_activeVertices_length]
  · exact (hreg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnewE
  · rw [hreg₄ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₃ _ (by decide) (by decide),
      hreg₂ _ (by decide) (by decide) (by decide) (by decide) (by decide),
      hreg₁ _ (by decide) (by decide)]
    simp [s₀]
  · intro a ha₁ ha₂ ha₃ ha₄
    exact (harr₄ a ha₄).trans ((harr₃ a ha₃).trans ((harr₂ a ha₂).trans (harr₁ a ha₁)))
  · intro q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈ hq₉ hq₁₀
    exact (hreg₄ q hq₁ hq₄ hq₅ hq₆ hq₇).trans ((hreg₃ q hq₈ hq₉).trans
      ((hreg₂ q hq₁ hq₄ hq₅ hq₆ hq₇).trans ((hreg₁ q hq₂ hq₃).trans (by simp [s₀, hq₁₀]))))

end GraphMinor.Compute
