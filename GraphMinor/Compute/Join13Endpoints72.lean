module

public import GraphMinor.Compute.Join13Write72
public import GraphMinor.Compute.Join13Read72

/-!
# Writing the mapped edge endpoints for (7.2)

The raw model lists edge indices. The caller instead needs their endpoint pairs.
We use one lookup in the raw model and one in the graph's endpoint array per
output word. Thus parallel edges keep their indices throughout the conversion.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Expression selecting the required endpoint of a raw mapped edge. -/
def mappedEndpoint72Expr (a_src a_ends : Arr) (r_src r_i : Reg) : Expr :=
  .read a_ends (.op .add
    (.op .mul (.const 2) (.read a_src (.op .add (.reg r_src)
      (.op .div (.reg r_i) (.const 2)))))
    (.op .mod (.reg r_i) (.const 2)))

/-- Write the endpoint pairs of one model into the caller's buffer. -/
def writeEndpoints72Prog (a_src a_ends a_dst : Arr) (r_src r_dst r_m r_i : Reg) : Cmd :=
  fillModelPart72Prog r_i (.op .mul (.const 2) (.reg r_m)) (.reg r_dst)
    (mappedEndpoint72Expr a_src a_ends r_src r_i) a_dst

private theorem read_getD72 {w : ℕ} {s : State} {a : Arr} {idx : Expr} {i v : ℕ}
    (he : idx.eval w s = some i) (hi : i < (s.arrs a).length)
    (hv : (s.arrs a).getD i 0 = v) (hw : v < 2 ^ w) :
    (.read a idx : Expr).eval w s = some v := by
  rw [List.getD_eq_getElem _ _ hi] at hv
  simpa only [hv] using read_eval he hi (by rwa [hv])

/-- Each output endpoint is read using its raw edge index. The loop preserves
all registers except its counter and all arrays except its output buffer. -/
theorem writeEndpoints72Prog_exec {w : ℕ} {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (a_src a_ends a_dst : Arr) (r_src r_dst r_m r_i : Reg)
    (hsrc_dst : a_src ≠ a_dst) (hends_dst : a_ends ≠ a_dst)
    (hrs : r_src ≠ r_i) (hrd : r_dst ≠ r_i) (hrm : r_m ≠ r_i)
    (pre_src post_src pre_dst : List ℕ) (rem : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : G.numVerts < 2 ^ w)
    (hends_len : 2 * G.numEdges < 2 ^ w)
    (hrem : 2 * e.H.digraph.numEdges ≤ rem)
    (hcap : pre_dst.length + rem < 2 ^ w)
    (hsrc_len : (pre_src ++ encRawCertEntry e ++ post_src).length < 2 ^ w)
    (hsrc : s.arrs a_src = pre_src ++ encRawCertEntry e ++ post_src)
    (hends : s.arrs a_ends = endpointWords72 G)
    (hdst : s.arrs a_dst = pre_dst ++ List.replicate rem 0)
    (hr_src : s.regs r_src = pre_src.length)
    (hr_dst : s.regs r_dst = pre_dst.length)
    (hr_m : s.regs r_m = e.H.digraph.numEdges) :
    let words := (List.finRange e.H.digraph.numEdges).flatMap (fun d =>
      [(G.tail (e.edgeMap d)).1, (G.head (e.edgeMap d)).1])
    ∃ s' t, Exec w (writeEndpoints72Prog a_src a_ends a_dst r_src r_dst r_m r_i) s s' t ∧
      t ≤ 8 + 60 * e.H.digraph.numEdges ∧ Keeps [r_i] [a_dst] s s' ∧
      s'.arrs a_dst = pre_dst ++ words ++ List.replicate (rem - words.length) 0 := by
  let words := (List.finRange e.H.digraph.numEdges).flatMap (fun d =>
    [(G.tail (e.edgeMap d)).1, (G.head (e.edgeMap d)).1])
  have hwords : words.length = 2 * e.H.digraph.numEdges := by
    simp [words, List.length_flatMap, List.map_const', List.sum_replicate, Nat.mul_comm]
  have hraw : e.H.digraph.numEdges ≤ (encRawCertEntry e).length := by
    simp [encRawCertEntry]
  obtain ⟨s', t, hex, ht, hk, hd, _⟩ := fillModelPart72Prog_exec r_i
    (.op .mul (.const 2) (.reg r_m)) (.reg r_dst)
    (mappedEndpoint72Expr a_src a_ends r_src r_i) a_dst words pre_dst rem s
    (by omega) (by rwa [hwords]) hcap
    (fun st hk => by
      have hr : st.regs r_m = e.H.digraph.numEdges :=
        (hk.1 r_m (by simpa using hrm)).trans hr_m
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr, hwords,
        show e.H.digraph.numEdges < 2 ^ w by omega,
        show 2 * e.H.digraph.numEdges < 2 ^ w by omega, hw])
    (fun st hk => by
      have hr : st.regs r_dst = pre_dst.length :=
        (hk.1 r_dst (by simpa using hrd)).trans hr_dst
      simp [Expr.eval, checkWord, hr, show pre_dst.length < 2 ^ w by omega])
    (fun st i hi hk hri => by
      have hi' : i < 2 * e.H.digraph.numEdges := by rwa [hwords] at hi
      have hd : i / 2 < e.H.digraph.numEdges := by omega
      let edge := e.edgeMap ⟨i / 2, hd⟩
      have hs : st.arrs a_src = pre_src ++ encRawCertEntry e ++ post_src :=
        (hk.2 a_src (by simpa using hsrc_dst)).trans hsrc
      have he : st.arrs a_ends = endpointWords72 G :=
        (hk.2 a_ends (by simpa using hends_dst)).trans hends
      have hrs' : st.regs r_src = pre_src.length :=
        (hk.1 r_src (by simpa using hrs)).trans hr_src
      have hidx : pre_src.length + i / 2 < (st.arrs a_src).length := by
        rw [hs]; simp only [List.length_append]; omega
      have hget : (st.arrs a_src).getD (pre_src.length + i / 2) 0 = edge.1 := by
        rw [hs, List.append_assoc,
          List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
          List.getD_append _ _ _ _ (by omega)]
        exact getD_encRawCertEntry_edge72 e ⟨i / 2, hd⟩
      have hsrc_sz : pre_src.length + (encRawCertEntry e).length + post_src.length < 2 ^ w := by
        simpa only [List.length_append] using hsrc_len
      have hsum_w : pre_src.length + i / 2 < 2 ^ w := by omega
      have hdiv : (.op .div (.reg r_i) (.const 2) : Expr).eval w st = some (i / 2) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hw,
          show i < 2 ^ w by omega, show i / 2 < 2 ^ w by omega]
      have heval_idx : (.op .add (.reg r_src) (.op .div (.reg r_i) (.const 2)) : Expr).eval w st =
          some (pre_src.length + i / 2) :=
        op_eval (reg_eval hrs' (by omega)) hdiv (by
          simp [BinOp.eval, BinOp.raw, checkWord, hsum_w])
      have hedge_w : edge.1 < 2 ^ w := by have := edge.2; omega
      have hread := read_getD72 heval_idx hidx hget hedge_w
      have hendidx : 2 * edge.1 + i % 2 < (st.arrs a_ends).length := by
        rw [he, length_endpointWords72]
        have := edge.2
        omega
      have hend_w : 2 * edge.1 + i % 2 < 2 ^ w := by
        rw [he, length_endpointWords72] at hendidx
        omega
      have heval : (.op .add (.op .mul (.const 2)
          (.read a_src (.op .add (.reg r_src) (.op .div (.reg r_i) (.const 2)))))
          (.op .mod (.reg r_i) (.const 2)) : Expr).eval w st = some (2 * edge.1 + i % 2) := by
        have hmul : (.op .mul (.const 2)
            (.read a_src (.op .add (.reg r_src) (.op .div (.reg r_i) (.const 2)))) : Expr).eval w st =
            some (2 * edge.1) :=
          op_eval (A := .const 2) (a := 2) (by simp [Expr.eval, checkWord, hw]) hread (by
            simp [BinOp.eval, BinOp.raw, checkWord, show 2 * edge.1 < 2 ^ w by omega])
        have hmod : (.op .mod (.reg r_i) (.const 2) : Expr).eval w st = some (i % 2) := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hw,
            show i < 2 ^ w by omega, show i % 2 < 2 ^ w by omega]
        exact op_eval hmul hmod (by simp [BinOp.eval, BinOp.raw, checkWord, hend_w])
      have hout : (st.arrs a_ends).getD (2 * edge.1 + i % 2) 0 = words[i] := by
        rw [he]
        have hmapped := getD_mappedEndpointWords72 e i hi'
        rw [getD_encRawCertEntry_edge72 e ⟨i / 2, hd⟩] at hmapped
        exact hmapped.trans (List.getD_eq_getElem _ _ hi)
      have hout_w : words[i] < 2 ^ w := by
        have hmem : (st.arrs a_ends).getD (2 * edge.1 + i % 2) 0 ∈ endpointWords72 G := by
          rw [he, List.getD_eq_getElem _ _ (by rwa [he] at hendidx)]
          exact List.getElem_mem _
        rw [hout] at hmem
        exact (mem_endpointWords72_lt G hmem).trans hn
      exact read_getD72 heval hendidx hout hout_w)
    hdst
  refine ⟨s', t, hex, ?_, hk, hd⟩
  simp only [mappedEndpoint72Expr, Expr.cost] at ht
  rw [hwords] at ht
  omega

end GraphMinor.Compute
