module

public import GraphMinor.Compute.CrossingOpsBfsForest
public import GraphMinor.Compute.CrossingOpsFilter

/-!
# Deleting the edges of a computed BFS forest

Two comparisons with the parent array detect whether an edge belongs to the forest.
Keeping all other neighbours gives the adjacency lists of the residual graph for the
next search. The comparisons use only the two endpoint words.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Keep neighbours that are unrelated by a discovery-parent edge. -/
def residualNeighbours {N : ℕ} (nbrs : Fin N → List (Fin N))
    (edges : List (Fin N × Fin N)) (u : Fin N) : List (Fin N) :=
  (nbrs u).filter (fun v => (u, v) ∉ edges ∧ (v, u) ∉ edges)

/-- Filtering discovery-parent edges represents graph difference. -/
theorem mem_residualNeighbours {N : ℕ} {G : SimpleGraph (Fin N)}
    (nbrs : Fin N → List (Fin N)) (edges : List (Fin N × Fin N))
    (hn : ∀ u v, v ∈ nbrs u ↔ G.Adj u v) (u v : Fin N) :
    v ∈ residualNeighbours nbrs edges u ↔ (G \ bfsDiscoveryForest edges).Adj u v := by
  simp only [residualNeighbours, List.mem_filter, decide_eq_true_eq, hn,
    SimpleGraph.sdiff_adj, bfsDiscoveryForest, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hg, huv, hvu⟩
    exact ⟨hg, fun h => h.2.elim huv hvu⟩
  · rintro ⟨hg, hf⟩
    exact ⟨hg, fun h => hf ⟨hg.ne, Or.inl h⟩, fun h => hf ⟨hg.ne, Or.inr h⟩⟩

/-- Residual lists have no repeats when the original lists have no repeats. -/
theorem residualNeighbours_nodup {N : ℕ} (nbrs : Fin N → List (Fin N))
    (edges : List (Fin N × Fin N)) (hnd : ∀ u, (nbrs u).Nodup) (u : Fin N) :
    (residualNeighbours nbrs edges u).Nodup := (hnd u).filter _

/-- Removing parent edges never increases a list length. -/
theorem residualNeighbours_length_le {N : ℕ} (nbrs : Fin N → List (Fin N))
    (edges : List (Fin N × Fin N)) (u : Fin N) :
    (residualNeighbours nbrs edges u).length ≤ (nbrs u).length := List.length_filter_le _ _

/-- Test that neither endpoint is the other's parent. -/
def withoutParentTest (a_par r_x r_y : ℕ) : Expr :=
  .op .mul
    (.op .sub (.const 1) (.op .eq (.read a_par (.reg r_x)) (.reg r_y)))
    (.op .sub (.const 1) (.op .eq (.read a_par (.reg r_y)) (.reg r_x)))

/-- A parent read is a word under the same bound as the dynamic sentinel. -/
theorem eval_bfsParentWord {w N a r : ℕ} {s : State} {edges : List (Fin N × Fin N)}
    (hp : IsBfsParentsAt a edges s) (v : Fin N) (hr : s.regs r = v.val)
    (hN : N < 2 ^ w) :
    (Expr.read a (.reg r)).eval w s = some ((s.arrs a)[v.val]'(by have := hp.1; omega)) :=
  eval_read (eval_reg hr (v.isLt.trans hN)) (by have := hp.1; omega)
    ((hp.2.1 v.val v.isLt).trans_lt hN)

/-- The test evaluates to one exactly for pairs without a discovery-parent relation. -/
theorem eval_withoutParentTest {w N a r_x r_y : ℕ} {s : State}
    {edges : List (Fin N × Fin N)} (hp : IsBfsParentsAt a edges s) (u v : Fin N)
    (hx : s.regs r_x = u.val) (hy : s.regs r_y = v.val)
    (hN : N < 2 ^ w) (hw : 1 < 2 ^ w) :
    (withoutParentTest a r_x r_y).eval w s =
      some (if (u, v) ∉ edges ∧ (v, u) ∉ edges then 1 else 0) := by
  have hpu := eval_bfsParentWord hp u hx hN
  have hpv := eval_bfsParentWord hp v hy hN
  have huv := eval_eq hpu (eval_reg hy (v.isLt.trans hN)) hw
  have hvu := eval_eq hpv (eval_reg hx (u.isLt.trans hN)) hw
  have hsubu := eval_sub (eval_const (w := w) (s := s) hw) huv
  have hsubv := eval_sub (eval_const (w := w) (s := s) hw) hvu
  simp only [hp.2.2 v u] at hsubu
  simp only [hp.2.2 u v] at hsubv
  have hmul := eval_mul hsubu hsubv (show
      (1 - if (v, u) ∈ edges then 1 else 0) * (1 - if (u, v) ∈ edges then 1 else 0) < 2 ^ w by
        split <;> split <;> simp_all)
  by_cases huv' : (u, v) ∈ edges <;> by_cases hvu' : (v, u) ∈ edges <;>
    simpa [withoutParentTest, huv', hvu'] using hmul

end GraphMinor.Compute.Crossing
