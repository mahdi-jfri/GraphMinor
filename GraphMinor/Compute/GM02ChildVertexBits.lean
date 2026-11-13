module

public import GraphMinor.Compute.GM13SocietyTabulate
public import GraphMinor.Compute.BitSet

/-!
# Selecting the vertices of a recursive child

Keep vertices on the chosen side, remove its reserved vertices, and
remove original separator terminals absent from the new termination.
The last deletion is the correction to the printed induced graphs in
II (2.9). Five membership arrays suffice to compute these vertex bits
in linear time.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.Compute.Crossing TwoPaths

/-- Vertex set of a side after the corrected induced-graph deletions. -/
def gm02ChildVertices {n : ℕ} (side other support reserved fresh : Finset (Fin n)) :
    Finset (Fin n) := side \ (reserved ∪ ((support ∩ other) \ fresh))

/-- Compute corrected child vertex bits with counter 341 and count register 40. -/
def gm02ChildVertexBitsProg (side other support reserved fresh dst : Arr) : Cmd :=
  gm13TabulateProg 341 (.reg 40)
    (.op .mul (.read side (.reg 341))
      (.op .mul (.op .sub (.const 1) (.read reserved (.reg 341)))
        (.op .sub (.const 1) (.op .mul
          (.op .mul (.read support (.reg 341)) (.read other (.reg 341)))
          (.op .sub (.const 1) (.read fresh (.reg 341))))))) dst

/-- The computed array has exactly the corrected child vertex set. -/
theorem gm02ChildVertexBitsProg_exec {n w : ℕ}
    (S O Q Z P : Finset (Fin n)) (side other support reserved fresh dst : Arr)
    (hside : side ≠ dst) (hother : other ≠ dst) (hsupport : support ≠ dst)
    (hreserved : reserved ≠ dst) (hfresh : fresh ≠ dst) (s : State)
    (hS : s.arrs side = bitSetList S) (hO : s.arrs other = bitSetList O)
    (hQ : s.arrs support = bitSetList Q) (hZ : s.arrs reserved = bitSetList Z)
    (hP : s.arrs fresh = bitSetList P) (hn : s.regs 40 = n)
    (hnw : n < 2 ^ w) (hw : 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm02ChildVertexBitsProg side other support reserved fresh dst) s s' t ∧
      t ≤ 6 + 32 * n ∧ Keeps [341] [dst] s s' ∧
      s'.arrs dst = bitSetList (gm02ChildVertices S O Q Z P) := by
  obtain ⟨s', t, he, ht, hk, hout⟩ := gm13TabulateProg_exec (w := w) 341 (.reg 40)
    (.op .mul (.read side (.reg 341))
      (.op .mul (.op .sub (.const 1) (.read reserved (.reg 341)))
        (.op .sub (.const 1) (.op .mul
          (.op .mul (.read support (.reg 341)) (.read other (.reg 341)))
          (.op .sub (.const 1) (.read fresh (.reg 341))))))) dst
    (bitSetList (gm02ChildVertices S O Q Z P)) s hw
    (by simpa only [length_bitSetList] using hnw)
    (fun st hk => by
      rw [length_bitSetList]
      exact eval_reg ((hk.1 _ (by decide)).trans hn) hnw)
    (fun st i hi hk hri => by
      have hin : i < n := by simpa only [length_bitSetList] using hi
      let v : Fin n := ⟨i, hin⟩
      have ha (a : Arr) (hne : a ≠ dst) : st.arrs a = s.arrs a :=
        hk.2 _ (by simpa only [List.mem_singleton] using hne)
      have hsa := (ha side hside).trans hS
      have hoa := (ha other hother).trans hO
      have hqa := (ha support hsupport).trans hQ
      have hza := (ha reserved hreserved).trans hZ
      have hpa := (ha fresh hfresh).trans hP
      by_cases hvs : v ∈ S <;> by_cases hvo : v ∈ O <;> by_cases hvq : v ∈ Q <;>
        by_cases hvz : v ∈ Z <;> by_cases hvp : v ∈ P <;>
        simp [Expr.eval, BinOp.eval, BinOp.raw, hsa, hoa, hqa, hza, hpa,
          bitSetList, gm02ChildVertices, hri, hin, v, hvs, hvo, hvq, hvz, hvp,
          checkWord_of_lt (hin.trans hnw), checkWord_of_lt hw,
          checkWord_of_lt (by omega : 0 < 2 ^ w)])
  refine ⟨s', t, he, ?_, hk, hout⟩
  simp only [Expr.cost_op, Expr.cost_const, Expr.cost_reg, Expr.cost_read,
    length_bitSetList] at ht
  omega

end GraphMinor.Compute
