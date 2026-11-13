module

public import GraphMinor.Compute.Join13Write72
public import GraphMinor.Compute.Join13Read72

/-!
# Writing branch-set vertex bits for (7.2)

The raw certificate has vertex bits followed by edge bits for every branch set.
The caller needs only the vertex bits. This loop uses the known block lengths
to skip the edge bits, without changing the input array.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Locate a vertex bit in the raw branch-set blocks. -/
def vertexBits72Expr (a_src : Arr) (r_src r_mH r_n r_m r_i : Reg) : Expr :=
  .read a_src (.op .add (.reg r_src)
    (.op .add (.reg r_mH) (.op .add
      (.op .mul (.op .div (.reg r_i) (.reg r_n)) (.op .add (.reg r_n) (.reg r_m)))
      (.op .mod (.reg r_i) (.reg r_n)))))

/-- Write all vertex bits of a single model. -/
def writeVertexBits72Prog (a_src a_dst : Arr) (r_src r_dst r_mH r_vH r_n r_m r_i : Reg) : Cmd :=
  fillModelPart72Prog r_i (.op .mul (.reg r_vH) (.reg r_n)) (.reg r_dst)
    (vertexBits72Expr a_src r_src r_mH r_n r_m r_i) a_dst

/-- The vertex-bit conversion skips the raw edge-bit blocks and writes exactly
the bit vectors required by the caller's model encoding. -/
theorem writeVertexBits72Prog_exec {w : ℕ} {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (a_src a_dst : Arr) (r_src r_dst r_mH r_vH r_n r_m r_i : Reg)
    (hne : a_src ≠ a_dst)
    (hrs : r_src ≠ r_i) (hrd : r_dst ≠ r_i) (hrmH : r_mH ≠ r_i)
    (hrvH : r_vH ≠ r_i) (hrn : r_n ≠ r_i) (hrm : r_m ≠ r_i)
    (pre_src post_src pre_dst : List ℕ) (rem : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : G.numVerts + G.numEdges < 2 ^ w)
    (hvH : e.H.digraph.numVerts < 2 ^ w) (hmH : e.H.digraph.numEdges < 2 ^ w)
    (hrem : e.H.digraph.numVerts * G.numVerts ≤ rem)
    (hcap : pre_dst.length + rem < 2 ^ w)
    (hsrc_len : (pre_src ++ encRawCertEntry e ++ post_src).length < 2 ^ w)
    (hsrc : s.arrs a_src = pre_src ++ encRawCertEntry e ++ post_src)
    (hdst : s.arrs a_dst = pre_dst ++ List.replicate rem 0)
    (hr_src : s.regs r_src = pre_src.length) (hr_dst : s.regs r_dst = pre_dst.length)
    (hr_mH : s.regs r_mH = e.H.digraph.numEdges)
    (hr_vH : s.regs r_vH = e.H.digraph.numVerts)
    (hr_n : s.regs r_n = G.numVerts) (hr_m : s.regs r_m = G.numEdges) :
    let words := (List.finRange e.H.digraph.numVerts).flatMap (fun u => bitSetList (e.vertVerts u))
    ∃ s' t, Exec w (writeVertexBits72Prog a_src a_dst r_src r_dst r_mH r_vH r_n r_m r_i) s s' t ∧
      t ≤ 8 + 40 * (e.H.digraph.numVerts * G.numVerts) ∧ Keeps [r_i] [a_dst] s s' ∧
      s'.arrs a_dst = pre_dst ++ words ++ List.replicate (rem - words.length) 0 := by
  let words := (List.finRange e.H.digraph.numVerts).flatMap (fun u => bitSetList (e.vertVerts u))
  have hwords : words.length = e.H.digraph.numVerts * G.numVerts := by
    simp [words, List.length_flatMap, length_bitSetList, List.map_const', List.sum_replicate]
  have hraw : (encRawCertEntry e).length =
      e.H.digraph.numEdges + e.H.digraph.numVerts * (G.numVerts + G.numEdges) := by
    simp [encRawCertEntry, List.length_flatMap, length_bitSetList,
      List.map_const', List.sum_replicate]
  have hsrc_sz : pre_src.length + (encRawCertEntry e).length + post_src.length < 2 ^ w := by
    simpa only [List.length_append] using hsrc_len
  obtain ⟨s', t, hex, ht, hk, hd, _⟩ := fillModelPart72Prog_exec r_i
    (.op .mul (.reg r_vH) (.reg r_n)) (.reg r_dst)
    (vertexBits72Expr a_src r_src r_mH r_n r_m r_i) a_dst words pre_dst rem s hw
    (by rwa [hwords]) hcap
    (fun st hk => by
      have hrv : st.regs r_vH = e.H.digraph.numVerts :=
        (hk.1 r_vH (by simpa using hrvH)).trans hr_vH
      have hrn' : st.regs r_n = G.numVerts :=
        (hk.1 r_n (by simpa using hrn)).trans hr_n
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv, hrn', hwords, hvH,
        show G.numVerts < 2 ^ w by omega,
        show e.H.digraph.numVerts * G.numVerts < 2 ^ w by omega])
    (fun st hk => by
      have hr : st.regs r_dst = pre_dst.length :=
        (hk.1 r_dst (by simpa using hrd)).trans hr_dst
      simp [Expr.eval, checkWord, hr, show pre_dst.length < 2 ^ w by omega])
    (fun st i hi hk hri => by
      have hi' : i < e.H.digraph.numVerts * G.numVerts := by rwa [hwords] at hi
      have hnpos : 0 < G.numVerts := by
        by_contra h
        have hz : G.numVerts = 0 := by omega
        simp [hz] at hi'
      have hu : i / G.numVerts < e.H.digraph.numVerts := by
        apply (Nat.div_lt_iff_lt_mul hnpos).2
        simpa only [Nat.mul_comm] using hi'
      have hx : i % G.numVerts < G.numVerts := Nat.mod_lt i hnpos
      have hblock := Nat.mul_le_mul_right (G.numVerts + G.numEdges) (Nat.succ_le_of_lt hu)
      rw [Nat.succ_mul] at hblock
      have hidx_raw : e.H.digraph.numEdges +
          (i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts <
          (encRawCertEntry e).length := by rw [hraw]; omega
      have hs : st.arrs a_src = pre_src ++ encRawCertEntry e ++ post_src :=
        (hk.2 a_src (by simpa using hne)).trans hsrc
      have hregs (r : Reg) (hr : r ≠ r_i) : st.regs r = s.regs r := hk.1 r (by simpa using hr)
      have hindex_w : pre_src.length + (e.H.digraph.numEdges +
          ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts)) < 2 ^ w := by omega
      have hdiv : (.op .div (.reg r_i) (.reg r_n) : Expr).eval w st = some (i / G.numVerts) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hregs r_n hrn, hr_n,
          show i < 2 ^ w by omega, show G.numVerts < 2 ^ w by omega,
          show G.numVerts ≠ 0 by omega, show i / G.numVerts < 2 ^ w by omega]
      have hmod : (.op .mod (.reg r_i) (.reg r_n) : Expr).eval w st = some (i % G.numVerts) := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hregs r_n hrn, hr_n,
          show i < 2 ^ w by omega, show G.numVerts < 2 ^ w by omega,
          show G.numVerts ≠ 0 by omega, show i % G.numVerts < 2 ^ w by omega]
      have hsum : (.op .add (.reg r_n) (.reg r_m) : Expr).eval w st =
          some (G.numVerts + G.numEdges) :=
        op_eval (reg_eval ((hregs r_n hrn).trans hr_n) (by omega))
          (reg_eval ((hregs r_m hrm).trans hr_m) (by omega))
          (by simp [BinOp.eval, BinOp.raw, checkWord, hn])
      have hmul : (.op .mul (.op .div (.reg r_i) (.reg r_n))
          (.op .add (.reg r_n) (.reg r_m)) : Expr).eval w st =
          some ((i / G.numVerts) * (G.numVerts + G.numEdges)) :=
        op_eval hdiv hsum (by simp [BinOp.eval, BinOp.raw, checkWord,
          show (i / G.numVerts) * (G.numVerts + G.numEdges) < 2 ^ w by omega])
      have hinner : (.op .add
          (.op .mul (.op .div (.reg r_i) (.reg r_n)) (.op .add (.reg r_n) (.reg r_m)))
          (.op .mod (.reg r_i) (.reg r_n)) : Expr).eval w st =
          some ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts) :=
        op_eval hmul hmod (by simp [BinOp.eval, BinOp.raw, checkWord,
          show (i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts < 2 ^ w by omega])
      have hinnerH : (.op .add (.reg r_mH) (.op .add
          (.op .mul (.op .div (.reg r_i) (.reg r_n)) (.op .add (.reg r_n) (.reg r_m)))
          (.op .mod (.reg r_i) (.reg r_n))) : Expr).eval w st =
          some (e.H.digraph.numEdges +
            ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts)) :=
        op_eval (reg_eval ((hregs r_mH hrmH).trans hr_mH) hmH) hinner
          (by simp [BinOp.eval, BinOp.raw, checkWord,
            show e.H.digraph.numEdges + ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts) < 2 ^ w by omega])
      have heval : (.op .add (.reg r_src) (.op .add (.reg r_mH) (.op .add
          (.op .mul (.op .div (.reg r_i) (.reg r_n)) (.op .add (.reg r_n) (.reg r_m)))
          (.op .mod (.reg r_i) (.reg r_n)))) : Expr).eval w st =
          some (pre_src.length + (e.H.digraph.numEdges +
            ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts))) :=
        op_eval (reg_eval ((hregs r_src hrs).trans hr_src) (by omega)) hinnerH
          (by simp [BinOp.eval, BinOp.raw, checkWord, hindex_w])
      have hidx : pre_src.length + (e.H.digraph.numEdges +
          ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts)) < (st.arrs a_src).length := by
        rw [hs]; simp only [List.length_append]; omega
      have hget : (st.arrs a_src).getD (pre_src.length + (e.H.digraph.numEdges +
          ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts))) 0 = words[i] := by
        rw [hs, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), Nat.add_sub_cancel_left,
          List.getD_append _ _ _ _ (by omega)]
        have hrawbit := getD_encRawCertEntry_vertex72 e ⟨i / G.numVerts, hu⟩ ⟨i % G.numVerts, hx⟩
        have houtbit := getD_flatMap_fixed72 (List.finRange e.H.digraph.numVerts)
          (fun u => bitSetList (e.vertVerts u)) G.numVerts (i / G.numVerts) (i % G.numVerts) 0
          (by simp [hu]) hx (fun _ _ => length_bitSetList _)
        have hi_eq : i / G.numVerts * G.numVerts + i % G.numVerts = i := by
          simpa only [Nat.mul_comm] using Nat.div_add_mod i G.numVerts
        rw [hi_eq, List.getD_eq_getElem _ _ hi] at houtbit
        simp only [List.getElem_finRange] at houtbit
        have hrawbit' : (encRawCertEntry e).getD (e.H.digraph.numEdges +
            ((i / G.numVerts) * (G.numVerts + G.numEdges) + i % G.numVerts)) 0 =
            (bitSetList (e.vertVerts ⟨i / G.numVerts, hu⟩)).getD (i % G.numVerts) 0 := by
          simpa only [Nat.add_assoc] using hrawbit
        exact hrawbit'.trans houtbit.symm
      have hword : words[i] ≤ 1 := by
        have hmem : words[i] ∈ words := List.getElem_mem hi
        simp only [words, List.mem_flatMap] at hmem
        obtain ⟨u, _, hu⟩ := hmem
        obtain ⟨j, hj, hval⟩ := List.getElem_of_mem hu
        rw [← hval]
        exact getElem_bitSetList_le_one _ _ hj
      rw [List.getD_eq_getElem _ _ hidx] at hget
      simpa only [vertexBits72Expr, hget] using read_eval heval hidx (by rw [hget]; omega))
    hdst
  refine ⟨s', t, hex, ?_, hk, hd⟩
  simp only [vertexBits72Expr, Expr.cost] at ht
  rw [hwords] at ht
  omega

end GraphMinor.Compute
