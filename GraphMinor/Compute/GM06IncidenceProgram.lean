module

public import GraphMinor.Compute.GM06FaceIncidence
public import GraphMinor.Compute.GM13SocietyTabulate
import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Building both incidence tables from a face dart row

Section 10 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) requires
vertex and edge incidence at a selected face. The program reads that face's
dart row and the origin table, maps its darts to vertex labels and
edge labels, then marks the two dense tables. Neither mapped labels
nor incidence bits are supplied as input. Repeated boundary visits
are allowed, and each of the four passes takes linear time.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Compute IncV in 606 and IncE in 607 from face darts in 600
and origins in 601. Registers 648 and 649 hold the vertex and edge
label-space sizes. Arrays 604 and 605 hold the mapped label lists. -/
def gm06FaceIncidenceProg : Cmd :=
  .seq (gm13TabulateProg 650 (.len 600) (.read 601 (.read 600 (.reg 650))) 604)
    (.seq (gm06IncidenceBitsProg 604 606 648)
      (.seq (gm13TabulateProg 650 (.len 600)
        (.op .div (.read 600 (.reg 650)) (.const 2)) 605)
        (gm06IncidenceBitsProg 605 607 649)))

/-- Exact RAM construction of both selected-face incidence tables.
The origin function supplies only the finite endpoint data. -/
theorem gm06FaceIncidenceProg_exec {w n m : ℕ}
    (origin : Fin (2 * m) → Fin n) (row : List (Fin (2 * m))) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * m < 2 ^ w)
    (hl : row.length < 2 ^ w)
    (hrow : s.arrs 600 = row.map Fin.val)
    (horg : s.arrs 601 = List.ofFn (fun d => (origin d).val))
    (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) :
    ∃ s' t, Exec w gm06FaceIncidenceProg s s' t ∧
      t ≤ n + m + 32 + 59 * row.length ∧
      Keeps [650, 610, 611, 612] [604, 606, 605, 607] s s' ∧
      s'.arrs 606 = gm06IncV n (List.ofFn (fun d => (origin d).val)) (row.map Fin.val) ∧
      s'.arrs 607 = gm06IncE m (row.map Fin.val) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : m < 2 ^ w := by omega
  let vertices := row.map origin
  let edge : Fin (2 * m) → Fin m := fun d => ⟨d.val / 2, by have := d.isLt; omega⟩
  let edges := row.map edge
  have hvertices : gm06FaceVertices (List.ofFn (fun d => (origin d).val)) (row.map Fin.val) =
      vertices.map Fin.val := by
    simp only [gm06FaceVertices, List.map_map, vertices]
    apply List.map_congr_left
    intro d _
    simp only [Function.comp_def, List.getElem?_ofFn, d.isLt, ↓reduceDIte,
      Option.getD_some]
  have hedges : gm06FaceEdges (row.map Fin.val) = edges.map Fin.val := by
    simp only [gm06FaceEdges, edges, List.map_map, Function.comp_def, edge]
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm13TabulateProg_exec 650 (.len 600)
    (.read 601 (.read 600 (.reg 650))) 604 (vertices.map Fin.val) s hw1
    (by simpa [vertices] using hl)
    (fun st hk => by
      have he := GraphMinor.Compute.Crossing.eval_len ((hk.2 600 (by decide)).trans hrow)
        (by simpa only [List.length_map] using hl)
      simpa only [vertices, List.length_map] using he)
    (fun st i hi hk hidx => by
      have hir : i < row.length := by simpa [vertices] using hi
      have h600 : st.arrs 600 = row.map Fin.val := (hk.2 600 (by decide)).trans hrow
      have h601 : st.arrs 601 = List.ofFn (fun d => (origin d).val) := (hk.2 601 (by decide)).trans horg
      have hread : (Expr.read 600 (.reg 650)).eval w st = some row[i].val := by
        have hh := GraphMinor.Compute.Crossing.eval_read (a := 600)
          (GraphMinor.Compute.Crossing.eval_reg hidx (hir.trans hl))
          (by simpa [h600] using hir) (by simpa [h600] using row[i].isLt.trans hm)
        simpa only [h600, List.getElem_map] using hh
      have hh := GraphMinor.Compute.Crossing.eval_read (a := 601) hread
        (by simp [h601])
        (by simpa [h601] using (origin row[i]).isLt.trans hn)
      simpa [h601, vertices] using hh)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06IncidenceBitsProg_exec 604 606 648 (by decide)
    vertices s₁ hw1 hn (by simpa [vertices] using hl)
    ((hk₁.1 648 (by decide)).trans h648) hd₁
  have hk₁₂ : Keeps [650, 610, 611, 612] [604, 606] s s₂ :=
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm13TabulateProg_exec 650 (.len 600)
    (.op .div (.read 600 (.reg 650)) (.const 2)) 605 (edges.map Fin.val) s₂ hw1
    (by simpa [edges] using hl)
    (fun st hk => by
      have h600 := (hk.2 600 (by decide)).trans ((hk₁₂.2 600 (by decide)).trans hrow)
      have he := GraphMinor.Compute.Crossing.eval_len h600 (by simpa only [List.length_map] using hl)
      simpa only [edges, List.length_map] using he)
    (fun st i hi hk hidx => by
      have hir : i < row.length := by simpa [edges] using hi
      have h600 : st.arrs 600 = row.map Fin.val :=
        (hk.2 600 (by decide)).trans ((hk₁₂.2 600 (by decide)).trans hrow)
      have hread : (Expr.read 600 (.reg 650)).eval w st = some row[i].val := by
        have hh := GraphMinor.Compute.Crossing.eval_read (a := 600)
          (GraphMinor.Compute.Crossing.eval_reg hidx (hir.trans hl))
          (by simpa [h600] using hir) (by simpa [h600] using row[i].isLt.trans hm)
        simpa only [h600, List.getElem_map] using hh
      have he := GraphMinor.Compute.Crossing.eval_div hread
        (GraphMinor.Compute.Crossing.eval_const hw) (by decide : (2 : ℕ) ≠ 0)
        ((Nat.div_le_self _ _).trans_lt (row[i].isLt.trans hm))
      simpa [edges, edge] using he)
  have hk₁₂₃ : Keeps [650, 610, 611, 612] [604, 606, 605] s s₃ :=
    (hk₁₂.mono (fun _ h => h) (by simp)).trans hk₃ (by simp) (by simp)
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm06IncidenceBitsProg_exec 605 607 649 (by decide)
    edges s₃ hw1 hmw (by simpa [edges] using hl)
    ((hk₁₂₃.1 649 (by decide)).trans h649) hd₃
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_,
    (hk₁₂₃.mono (fun _ h => h) (by simp)).trans hk₄ (by simp) (by simp), ?_, ?_⟩
  · simp only [Expr.cost, vertices, edges, List.length_map] at ht₁ ht₂ ht₃ ht₄
    omega
  · rw [hk₄.2 606 (by decide), hk₃.2 606 (by decide), hd₂]
    exact congrArg (gm06IncidenceBits n) hvertices.symm
  · rw [hd₄]
    exact congrArg (gm06IncidenceBits m) hedges.symm

end GraphMinor.Compute
