module

public import GraphMinor.Compute.GM06Alg34Driver
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Direct header reads for the driver

The vertex count is the first supplied word. Reading it requires only
that count to fit a machine word. This read decides the null case and
also contributes to the initial queue reservation.
-/

public section
namespace GraphMinor.Compute

/-- Reading array 0 at index zero gives the supplied vertex count. -/
theorem gm06Driver_vertex_eval (x : GM06DrawingData) {w : ℕ} {s : State}
    (hinput : s.arrs 0 = x.words) (hn : x.n < 2 ^ w) :
    (Expr.read 0 (.const 0)).eval w s = some x.n := by
  have hlen : 0 < (s.arrs 0).length := by
    rw [hinput]
    have hh := x.five_le_words_length
    omega
  have hget : (s.arrs 0)[0] = x.n := by
    simp only [hinput, GM06DrawingData.words, List.cons_append, List.getElem_cons_zero]
  have he := Crossing.eval_read (Crossing.eval_const (Nat.two_pow_pos w)) hlen
    (hget.symm ▸ hn)
  exact he.trans (congrArg some hget)

end GraphMinor.Compute
