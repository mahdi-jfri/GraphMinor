module

public import GraphMinor.Compute.GM06Alg34VertexMask
public import GraphMinor.Compute.GM06Alg34Cells

/-!
# Testing an edge against the active vertex mask

An edge survives induced deletion exactly when both endpoint labels
remain active. Multiply the two zero-one mask entries to obtain its
survival bit. The test uses the supplied endpoint labels and no
geometric information.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the mask at a vertex label held in the given register. -/
def gm06ActiveVertexExpr (r : ℕ) : Expr := .read 4 (.reg r)

/-- Test whether both endpoint labels held in two registers survive. -/
def gm06ActiveEdgeExpr (r₁ r₂ : ℕ) : Expr :=
  .op .mul (gm06ActiveVertexExpr r₁) (gm06ActiveVertexExpr r₂)

/-- A mask read returns precisely the membership bit of the old label. -/
theorem gm06ActiveVertexExpr_eval {w n : ℕ} (vs : List (Fin n)) (v : Fin n)
    (r : ℕ) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) {s : State}
    (hmask : s.arrs 4 = gm06VertexMask vs) (hr : s.regs r = v.val) :
    (gm06ActiveVertexExpr r).eval w s = some (if v ∈ vs then 1 else 0) := by
  have hvw := v.isLt.trans hn
  have hvlen : v.val < (s.arrs 4).length := by
    rw [hmask, gm06VertexMask_length]
    exact v.isLt
  have hget : (s.arrs 4)[v.val]'hvlen = if v ∈ vs then 1 else 0 := by
    simp [hmask, gm06VertexMask]
  by_cases hv : v ∈ vs <;>
    simp [gm06ActiveVertexExpr, Expr.eval, hr, checkWord, hvw, hvlen, hget,
      hv, hw, Nat.zero_lt_of_lt hw]

/-- The endpoint-mask product is exactly the finite induced-edge test. -/
theorem gm06ActiveEdgeExpr_eval {w : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (e : Fin x.ends.length) (r₁ r₂ : ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) {s : State}
    (hmask : s.arrs 4 = gm06VertexMask vs)
    (h₁ : s.regs r₁ = x.ends[e].1.val) (h₂ : s.regs r₂ = x.ends[e].2.val) :
    (gm06ActiveEdgeExpr r₁ r₂).eval w s =
      some (if x.activeCell vs (.inr (.inl e)) then 1 else 0) := by
  have he₁ := gm06ActiveVertexExpr_eval vs x.ends[e].1 r₁ hw hn hmask h₁
  have he₂ := gm06ActiveVertexExpr_eval vs x.ends[e].2 r₂ hw hn hmask h₂
  simp only [gm06ActiveEdgeExpr, Expr.eval, he₁, he₂, BinOp.eval, BinOp.raw,
    GM06DrawingData.activeCell, decide_eq_true_eq]
  by_cases hA : (x.ends[e.val]'e.isLt).1 ∈ vs <;>
    by_cases hB : (x.ends[e.val]'e.isLt).2 ∈ vs <;>
    simp [hA, hB, checkWord, hw, Nat.zero_lt_of_lt hw]

end GraphMinor.Compute
