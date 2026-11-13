module

public import GraphMinor.Compute.Join13Read72
public import GraphMinor.Compute.TwoPathsRotate

/-!
# Separating the endpoint columns for the core input

The graph-expansion loop writes tail and head words alternately. The core (4.1)
input stores all heads, then all tails. A linear gather loop extracts either
column without changing the endpoint stream.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Extract column zero (tails) or column one (heads) from an endpoint stream. -/
def projectEndpoint72Prog (side : Fin 2) (a_src a_dst r_m r_i : ℕ) : Cmd :=
  mapProg r_i (.reg r_m) a_dst a_src
    (.op .add (.op .mul (.const 2) (.reg r_i)) (.const side.1))

/-- The endpoint-column gather writes the chosen column in linear time and
preserves all other arrays and registers except its counter. -/
theorem projectEndpoint72Prog_exec {w : ℕ} (G : ComputeDigraph) (side : Fin 2)
    (a_src a_dst r_m r_i : ℕ) (hne : a_dst ≠ a_src) (hr : r_m ≠ r_i)
    (s : State) (hw : 2 < 2 ^ w) (hn : G.numVerts < 2 ^ w)
    (hm : 2 * G.numEdges < 2 ^ w)
    (hsrc : s.arrs a_src = endpointWords72 G) (hrm : s.regs r_m = G.numEdges) :
    ∃ s' t, Exec w (projectEndpoint72Prog side a_src a_dst r_m r_i) s s' t ∧
      t ≤ 20 * (G.numEdges + 1) ∧ Keeps [r_i] [a_dst] s s' ∧
      s'.arrs a_dst = List.ofFn (fun e : Fin G.numEdges =>
        [(G.tail e).1, (G.head e).1].getD side.1 0) := by
  obtain ⟨s', t, hex, ht, hk, hout⟩ := mapProg_exec r_i (.reg r_m) a_dst a_src
    (.op .add (.op .mul (.const 2) (.reg r_i)) (.const side.1)) hne G.numEdges
    (fun i => 2 * i + side.1) (endpointWords72 G) s (by omega) (by omega)
    (fun st hk => by
      have hm' : st.regs r_m = G.numEdges := (hk.1 r_m (by simpa using hr)).trans hrm
      simp [Expr.eval, checkWord, hm', show G.numEdges < 2 ^ w by omega])
    (fun st i hk hri hi => by
      have hs := side.2
      have hidx : 2 * i + side.1 < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hw,
        show i < 2 ^ w by omega, show side.1 < 2 ^ w by omega,
        show 2 * i < 2 ^ w by omega, hidx])
    (fun i hi => by rw [length_endpointWords72]; have := side.2; omega)
    (fun x hx => (mem_endpointWords72_lt G hx).trans hn) hsrc
  refine ⟨s', t, hex, ?_, hk, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · rw [hout]
    apply List.ext_getElem (by simp)
    intro i hi hj
    have hilt : i < G.numEdges := by simpa using hj
    rw [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hget := getD_flatMap_fixed72 (List.finRange G.numEdges)
      (fun e => [(G.tail e).1, (G.head e).1]) 2 i side.1 0 (by simp [hilt]) side.2 (by intros; rfl)
    simpa only [endpointWords72, List.getElem_finRange, Fin.cast_mk, Nat.mul_comm] using hget

end GraphMinor.Compute
