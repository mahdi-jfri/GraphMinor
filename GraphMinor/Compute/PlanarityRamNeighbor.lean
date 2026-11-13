module

public import GraphMinor.Compute.PlanarityRamSearchProg

/-!
# Reading one adjacency slice

The frame step obtains a list length by subtracting its stored start from
its end, then reads the next neighbor at start plus the frame index. The
input array may contain padding and may use large offsets. Bounds come
from `IsListAt` and the entries-array word bound, not from compactness.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

/-- Length of the adjacency slice of the vertex in register 41. -/
def adjacencyLengthExpr : Expr :=
  .op .sub (.read 31 (.reg 41)) (.read 30 (.reg 41))

/-- The single neighbor read at the start of `scanNeighborProg`. -/
def readNeighborProg : Cmd :=
  .assign 43 (.read 32 (.op .add (.read 30 (.reg 41)) (.reg 42)))

/-- The slice length is read exactly, including for an empty slice. -/
theorem adjacencyLengthExpr_eval {N w : ℕ} {s : State} {lists : Fin N → List ℕ}
    (h : IsListFamily N 30 31 32 lists s) (v : Fin N) (hr : s.regs 41 = v.val)
    (hN : N < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w) :
    adjacencyLengthExpr.eval w s = some (lists v).length := by
  obtain ⟨start, finish, hs, he, hent, hlen, hstart, hfinish, hle, _⟩ := h.2.2 v
  have hvw : v.val < 2 ^ w := Nat.lt_trans v.isLt hN
  have hsw : start < 2 ^ w := by omega
  have hew : finish < 2 ^ w := by omega
  have hlw : (lists v).length < 2 ^ w := by omega
  have es : (Expr.read 30 (.reg 41)).eval w s = some start := by
    simp [Expr.eval, hr, checkWord_of_lt hvw, hs, hstart, checkWord_of_lt hsw]
  have ee : (Expr.read 31 (.reg 41)).eval w s = some finish := by
    simp [Expr.eval, hr, checkWord_of_lt hvw, he, hfinish, checkWord_of_lt hew]
  unfold adjacencyLengthExpr
  rw [Expr.eval, ee, es]
  simpa only [BinOp.eval, BinOp.raw, hlen] using checkWord_of_lt hlw

/-- Reading an in-range neighbor takes six steps. The input slice relation,
registers, entries-array word bound and neighbor word bound suffice. -/
theorem readNeighborProg_exec {N w : ℕ} {s : State} {lists : Fin N → List ℕ}
    (h : IsListFamily N 30 31 32 lists s) (v : Fin N) (k : ℕ) (hk : k < (lists v).length)
    (hrv : s.regs 41 = v.val) (hrk : s.regs 42 = k)
    (hN : N < 2 ^ w) (hentries : (s.arrs 32).length < 2 ^ w)
    (hval : (lists v)[k] < 2 ^ w) :
    Exec w readNeighborProg s (s.setReg 43 (lists v)[k]) 6 := by
  obtain ⟨start, finish, hs, he, hent, hlen, hstart, hfinish, hle, hvalues⟩ := h.2.2 v
  have hvw : v.val < 2 ^ w := Nat.lt_trans v.isLt hN
  have hsw : start < 2 ^ w := by omega
  have hkw : k < 2 ^ w := by omega
  have hidx : start + k < (s.arrs 32).length := by omega
  have hidxw : start + k < 2 ^ w := by omega
  have es : (Expr.read 30 (.reg 41)).eval w s = some start := by
    simp [Expr.eval, hrv, checkWord_of_lt hvw, hs, hstart, checkWord_of_lt hsw]
  have ek : (Expr.reg 42).eval w s = some k := by
    simpa [Expr.eval, hrk] using checkWord_of_lt hkw
  have eidx : (Expr.op .add (.read 30 (.reg 41)) (.reg 42)).eval w s = some (start + k) := by
    rw [Expr.eval, es, ek]
    exact checkWord_of_lt hidxw
  apply Exec.assign
  rw [Expr.eval, eidx]
  simpa only [hidx, ↓reduceDIte, hvalues k hk] using checkWord_of_lt hval

end GraphMinor.Compute.PlanarityRam
