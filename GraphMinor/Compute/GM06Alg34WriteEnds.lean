module

public import GraphMinor.Compute.GM06Alg34RankRead
public import GraphMinor.Compute.GM06Alg34RelabelLists

/-!
# Writing one relabelled endpoint pair

For a surviving old edge, its edge rank gives the two output positions
and its endpoint ranks give their values. Write both words to array 8.
The two rank tables and all registers remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Output position of the first endpoint of the old edge in register 135. -/
def gm06EndOffsetExpr : Expr := .op .mul (.const 2) (gm06EdgeRankExpr 135)

/-- Write the new endpoint pair of one surviving edge into array 8. -/
def gm06WriteEndsProg : Cmd :=
  .seq (.write 8 gm06EndOffsetExpr (gm06VertexRankExpr 132))
    (.write 8 (.op .add gm06EndOffsetExpr (.const 1)) (gm06VertexRankExpr 133))

/-- The two endpoint writes agree exactly with the computed induced
endpoint list, and take sixteen RAM steps. -/
theorem gm06WriteEndsProg_exec {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (i : Fin (x.activeEdges vs).length)
    (hn : x.n < 2 ^ w) (hm : x.ends.length < 2 ^ w)
    (hout : 2 * (x.activeEdges vs).length < 2 ^ w) {s : State}
    (hV : s.arrs 5 = gm06VertexRanks vs) (hE : s.arrs 7 = gm06EdgeRanks x vs)
    (hcap : (s.arrs 8).length = 2 * (x.activeEdges vs).length)
    (h₁ : s.regs 132 = x.ends[(x.activeEdges vs).get i].1.val)
    (h₂ : s.regs 133 = x.ends[(x.activeEdges vs).get i].2.val)
    (hi : s.regs 135 = ((x.activeEdges vs).get i).val) :
    ∃ s', Exec w gm06WriteEndsProg s s' 16 ∧
      s'.arrs 8 = ((s.arrs 8).set (2 * i.val)
        ((x.activeEnds vs)[i.val]'(by rw [x.activeEnds_length vs]; exact i.isLt)).1.val).set
          (2 * i.val + 1)
          ((x.activeEnds vs)[i.val]'(by rw [x.activeEnds_length vs]; exact i.isLt)).2.val ∧
      (∀ a : ℕ, a ≠ 8 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, s'.regs q = s.regs q) := by
  let e := (x.activeEdges vs).get i
  have he : e ∈ x.activeEdges vs := List.get_mem _ i
  have he' : x.activeCell vs (.inr (.inl e)) = true := (List.mem_filter.mp he).2
  have hends : x.ends[e].1 ∈ vs ∧ x.ends[e].2 ∈ vs := by
    simpa only [GM06DrawingData.activeCell, decide_eq_true_eq] using he'
  have hidx := gm06ListIndex_get_index (x.activeEdges vs) (x.activeEdges_nodup vs) i
  have hrE : (gm06EdgeRankExpr 135).eval w s = some i.val := by
    have hh := gm06EdgeRankExpr_eval x vs e he' 135 hm hE hi
    rw [hidx] at hh
    exact hh
  have hA := gm06VertexRankExpr_eval x vs x.ends[e].1 hends.1 132 hn hV h₁
  have hB := gm06VertexRankExpr_eval x vs x.ends[e].2 hends.2 133 hn hV h₂
  let a := ((x.activeEnds vs)[i.val]'(by rw [x.activeEnds_length vs]; exact i.isLt)).1.val
  let b := ((x.activeEnds vs)[i.val]'(by rw [x.activeEnds_length vs]; exact i.isLt)).2.val
  have ha : (gm06VertexRankExpr 132).eval w s = some a := by
    simpa only [a, e, GM06DrawingData.activeEnds, List.getElem_ofFn] using hA
  have hb : (gm06VertexRankExpr 133).eval w s = some b := by
    simpa only [b, e, GM06DrawingData.activeEnds, List.getElem_ofFn] using hB
  have hkw : 2 * i.val < 2 ^ w := by have := i.isLt; omega
  have hk1w : 2 * i.val + 1 < 2 ^ w := by have := i.isLt; omega
  have h2w : 2 < 2 ^ w := by have := i.isLt; omega
  have hiw : i.val < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  have hpos : gm06EndOffsetExpr.eval w s = some (2 * i.val) := by
    simp [gm06EndOffsetExpr, Expr.eval, hrE, BinOp.eval, BinOp.raw, checkWord, h2w, hiw, hkw]
  let s₁ := s.writeArr 8 (2 * i.val) a
  have he₁ : Exec w (.write 8 gm06EndOffsetExpr (gm06VertexRankExpr 132)) s s₁ 7 :=
    .write hpos ha (by rw [hcap]; have := i.isLt; omega)
  have hV₁ : s₁.arrs 5 = gm06VertexRanks vs := by simp [s₁, hV]
  have hE₁ : s₁.arrs 7 = gm06EdgeRanks x vs := by simp [s₁, hE]
  have hrE₁ : (gm06EdgeRankExpr 135).eval w s₁ = some i.val := by
    have hh := gm06EdgeRankExpr_eval x vs e he' 135 hm hE₁ hi
    rw [hidx] at hh
    exact hh
  have hb₁ : (gm06VertexRankExpr 133).eval w s₁ = some b := by
    simpa only [b, e, GM06DrawingData.activeEnds, List.getElem_ofFn] using
      gm06VertexRankExpr_eval x vs x.ends[e].2 hends.2 133 hn hV₁ h₂
  have hpos₁ : (.op .add gm06EndOffsetExpr (.const 1) : Expr).eval w s₁ =
      some (2 * i.val + 1) := by
    simp [gm06EndOffsetExpr, Expr.eval, hrE₁, BinOp.eval, BinOp.raw, checkWord,
      h2w, hiw, hkw, h1w, hk1w]
  let s₂ := s₁.writeArr 8 (2 * i.val + 1) b
  have he₂ : Exec w (.write 8 (.op .add gm06EndOffsetExpr (.const 1))
      (gm06VertexRankExpr 133)) s₁ s₂ 9 :=
    .write hpos₁ hb₁ (by
      simp only [s₁, State.writeArr_arrs_self, List.length_set, hcap]
      have := i.isLt
      omega)
  have hex : Exec w gm06WriteEndsProg s s₂ 16 := .seq he₁ he₂
  refine ⟨s₂, hex, rfl, ?_, fun _ => rfl⟩
  intro A hA
  exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [gm06WriteEndsProg, Cmd.writtenArrs, hA])

end GraphMinor.Compute
