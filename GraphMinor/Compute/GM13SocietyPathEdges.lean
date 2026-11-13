module

public import GraphMinor.Compute.GM13SocietyEdgeMatrix
public import GraphMinor.Compute.GM13SocietyTabulate

/-!
# Writing actual edges of a society path

A path vertex list gives consecutive ordered pairs. For each pair the
program reads the direction table and writes the tail or head of edge
number zero in the selected direction. Thus the two endpoint arrays name
actual multigraph edges, including when both directions have parallel edges.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths
open GraphMinor.Compute.Crossing

/-- The tails or heads of the chosen actual edges along a vertex list. Each
edge has parallel-edge index zero. -/
def gm13PathEdgeEnds {n : ℕ} (G : MultiDigraph n) (L : List (Fin n))
    (head : Bool) : List ℕ :=
  List.ofFn (fun i : Fin (L.length - 1) =>
    let u := L[i.1]'(by omega)
    let v := L[i.1 + 1]'(by omega)
    if head then (adjEdgeTriple G u v).2.1 else (adjEdgeTriple G u v).1)

/-- Read a path step and select the tail or head of its actual edge. -/
def gm13PathEndExpr (a_path : Arr) (head : Bool) : Expr :=
  let u := Expr.read a_path (.reg 40)
  let v := Expr.read a_path (.op .add (.reg 40) (.const 1))
  let b := Expr.read 5 (.op .add (.op .mul u (.reg 0)) v)
  if head then gm13SelectExpr b v u else gm13SelectExpr b u v

/-- Write all the actual edge tails or heads of a path. -/
def gm13PathEdgeEndsProg (a_path a_out : Arr) (head : Bool) : Cmd :=
  gm13TabulateProg 40 (.op .sub (.len a_path) (.const 1))
    (gm13PathEndExpr a_path head) a_out

/-- A path's actual edge endpoints are written in linear time. No graph
search or choice is left to the output reader. -/
theorem gm13PathEdgeEndsProg_exec {w n : ℕ} (G : MultiDigraph n)
    (L : List (Fin n)) (a_path a_out : ℕ) (head : Bool)
    (hne : a_path ≠ a_out) (hout : a_out ≠ 5)
    (hw : 8 + n * n + n + L.length < 2 ^ w)
    {s : State} (hpath : s.arrs a_path = L.map Fin.val)
    (hmat : GM13DirectionMatrix G (s.arrs 5)) (hn : s.regs 0 = n) :
    ∃ s' t, Exec w (gm13PathEdgeEndsProg a_path a_out head) s s' t ∧
      t ≤ 100 * L.length + 20 ∧
      Keeps [40] [a_out] s s' ∧ s'.arrs a_out = gm13PathEdgeEnds G L head := by
  obtain ⟨hlen, hcell⟩ := hmat
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have hwords : (gm13PathEdgeEnds G L head).length = L.length - 1 := by
    simp only [gm13PathEdgeEnds, List.length_ofFn]
  have hcount : ∀ st, Keeps [40] [a_out] s st →
      (Expr.op .sub (.len a_path) (.const 1)).eval w st =
        some (gm13PathEdgeEnds G L head).length := by
    intro st hk
    have hp : st.arrs a_path = L.map Fin.val :=
      (hk.2 a_path (by simpa using hne)).trans hpath
    simpa only [hwords, List.length_map] using
      eval_sub (eval_len hp (by simpa only [List.length_map] using
        (show L.length < 2 ^ w by omega))) (eval_const h1)
  have hvalue : ∀ st i (hi : i < (gm13PathEdgeEnds G L head).length),
      Keeps [40] [a_out] s st → st.regs 40 = i →
      (gm13PathEndExpr a_path head).eval w st = some (gm13PathEdgeEnds G L head)[i] := by
    intro st i hi hk hr
    have hi' : i < L.length - 1 := by rwa [hwords] at hi
    have hip : i < L.length := by omega
    have hiv : i + 1 < L.length := by omega
    let u := L[i]'hip
    let v := L[i + 1]'hiv
    have hp : st.arrs a_path = L.map Fin.val :=
      (hk.2 a_path (by simpa using hne)).trans hpath
    have hri := eval_reg hr (show i < 2 ^ w by omega)
    have hu : (Expr.read a_path (.reg 40)).eval w st = some u.1 := by
      apply gm13_read_eval hri
      · rw [hp, List.getElem?_eq_getElem (by simpa only [List.length_map] using hip)]
        simp only [List.getElem_map, u]
      · exact u.2.trans (by omega)
    have hv : (Expr.read a_path (.op .add (.reg 40) (.const 1))).eval w st = some v.1 := by
      apply gm13_read_eval (eval_add hri (eval_const h1) (by omega))
      · rw [hp, List.getElem?_eq_getElem (by simpa only [List.length_map] using hiv)]
        simp only [List.getElem_map, v]
      · exact v.2.trans (by omega)
    have hn' : (Expr.reg 0).eval w st = some n :=
      eval_reg ((hk.1 0 (by simp)).trans hn) (by omega)
    have hind : u.1 * n + v.1 < n * n := mul_add_lt_sq u.2 v.2
    have hidx := eval_add (eval_mul hu hn' (by omega)) hv (by omega)
    have hb : (Expr.read 5 (.op .add (.op .mul (.read a_path (.reg 40)) (.reg 0))
        (.read a_path (.op .add (.reg 40) (.const 1))))).eval w st =
        some (if 0 < G.edgeMult u v then 1 else 0) := by
      apply gm13_read_eval hidx
      · rw [hk.2 5 (by simp [Ne.symm hout])]
        exact List.getElem?_eq_some_iff.mpr ⟨by omega, hcell u v⟩
      · split <;> omega
    cases head
    · simpa only [gm13PathEndExpr, gm13PathEdgeEnds, List.getElem_ofFn,
        Bool.false_eq_true, ↓reduceIte, adjEdgeTriple, apply_ite, u, v] using
        gm13SelectExpr_eval h1 hb hu hv
    · simpa only [gm13PathEndExpr, gm13PathEdgeEnds, List.getElem_ofFn,
        ↓reduceIte, adjEdgeTriple, apply_ite, u, v] using
        gm13SelectExpr_eval h1 hb hv hu
  obtain ⟨s', t, hex, ht, hk, hout'⟩ := gm13TabulateProg_exec 40
    (.op .sub (.len a_path) (.const 1)) (gm13PathEndExpr a_path head) a_out
    (gm13PathEdgeEnds G L head) s h1 (by rw [hwords]; omega) hcount hvalue
  refine ⟨s', t, hex, ?_, hk, hout'⟩
  cases head <;>
    simp only [gm13PathEndExpr, Bool.false_eq_true, ↓reduceIte, gm13SelectExpr, Expr.cost, hwords] at ht <;> omega

end GraphMinor.Compute
