module

public import GraphMinor.Compute.Algorithm81Aux
public import GraphMinor.Compute.Algorithm94Aux
public import GraphMinor.Compute.Algorithm33Multigraph
import GraphMinor.Compute.Algorithm74Scan

/-!
# Plain multigraph society input for Section 8 of Graph Minors XIII

The input contains only the graph and the cyclic order. The RAM program
removes loops and parallel copies, then copies the supplied boundary order
after the simple graph encoding. The original input remains available for
restoring actual edges.

XIII, Section 2, page 68: "Thus each edge has a head and a tail (the same, for a loop)."
-/

@[expose] public section
namespace GraphMinor.Compute
open SimpleGraph

/-- A society input for XIII (8.1), (8.3), and (8.6), pages 93--96.
The graph may have loops and parallel edges. The list gives the cyclic order. -/
structure GM13SocietyInput where
  n : ℕ
  G : MultiDigraph n
  omega : List (Fin n)
  nodup_omega : omega.Nodup

/-- The size vε of the given multigraph society, rather than its simple graph. -/
def GM13SocietyInput.size (x : GM13SocietyInput) : ℕ :=
  societySize x.n x.G.numEdges

/-- A plain encoding: the multigraph, the boundary length, and its vertex list. -/
def GM13SocietyInput.enc (x : GM13SocietyInput) : List ℕ :=
  x.G.enc ++ (x.omega.length :: x.omega.map Fin.val)

/-- Delete loops and retain one adjacency for each parallel class. -/
noncomputable def GM13SocietyInput.simple (x : GM13SocietyInput) : Alg81Input where
  n := x.n
  G := x.G.toSimpleGraph
  decAdj := MultiDigraph.instDecidableRelToSimpleGraphAdj x.G
  omega := x.omega
  nodup_omega := x.nodup_omega

/-- Simplification does not increase the Section 8 size bound. -/
theorem GM13SocietyInput.simple_size_le (x : GM13SocietyInput) :
    alg81Size x.simple ≤ x.size := by
  unfold alg81Size GM13SocietyInput.size societySize
  change (x.n + 1) * (x.G.toSimpleGraph.edgeFinset.card + x.n + 1) ≤ _
  rw [← length_edgeListOf_eq_card_edgeFinset x.G.toSimpleGraph]
  exact Nat.mul_le_mul_left (x.n + 1)
    (Nat.add_le_add_right (Nat.add_le_add_right
      (card_edgeFinset_toSimpleGraph_le_numEdges x.G) x.n) 1)

/-- Read the graph's endpoint records, then append the unchanged cyclic order.
Array 64 is the simple program's input. Array 0 retains the original society. -/
def gm13SocietySimpleProg : Cmd :=
  .seq (toSimpleGraphEdgeListProg 0 2 64 0)
    (.seq (.assign 20 (.op .add (.const 2) (.op .mul (.const 3) (.read 0 (.const 1)))))
      (.seq (.assign 21 (.op .add (.const 1) (.read 0 (.reg 20))))
        (.seq (readSliceProg 0 (.reg 20) 3 (.reg 21) 22)
          (.seq (.assign 20 (.len 64))
            (appendArrProg 64 3 2 20 21 22)))))

/-- An array read whose index and stored word have already been checked. -/
theorem gm13_read_eval {w j v : ℕ} {s : State} {a : ℕ} {e : Expr}
    (he : e.eval w s = some j) (hg : (s.arrs a)[j]? = some v)
    (hv : v < 2 ^ w) : (Expr.read a e).eval w s = some v := by
  obtain ⟨hj, hval⟩ := List.getElem?_eq_some_iff.mp hg
  simp only [Expr.eval, he, hj, ↓reduceDIte, hval, checkWord, hv, ↓reduceIte]

private theorem gm13_op_eval {w u v z : ℕ} {s : State} {a b : Expr} {op : BinOp}
    (ha : a.eval w s = some u) (hb : b.eval w s = some v)
    (hop : op.eval w u v = some z) : (Expr.op op a b).eval w s = some z := by
  change (match a.eval w s, b.eval w s with
    | some a, some b => op.eval w a b
    | _, _ => none) = _
  rw [ha, hb]
  exact hop

/-- The simple society is written from plain multigraph input in linear time
in the graph's active endpoint records and the boundary list. -/
theorem gm13SocietySimpleProg_exec {w : ℕ} (x : GM13SocietyInput)
    (hw : 8 + 3 * x.G.numActivePairs + x.n < 2 ^ w)
    {s : State} (hin : s.arrs 0 = x.enc) :
    ∃ s' t, Exec w gm13SocietySimpleProg s s' t ∧
      t ≤ 200 * x.G.numActivePairs + 40 * x.n + 250 ∧
      s'.arrs 64 = encAlg81In x.simple ∧ s'.arrs 0 = x.enc := by
  let suffix := x.omega.length :: x.omega.map Fin.val
  let simple := encGraph x.G.toSimpleGraph
  have hk : x.omega.length ≤ x.n := length_omega_le_n x.nodup_omega
  have hm : (edgeListOf x.G.toSimpleGraph).length ≤ x.G.numActivePairs := by
    rw [← MultiDigraph.toSimplePairsAux_activePairsList]
    exact length_toSimplePairsAux_le _ _ _
  have hl : simple.length = 2 + 2 * (edgeListOf x.G.toSimpleGraph).length :=
    length_encGraph _
  have hslen : suffix.length = x.omega.length + 1 := by simp [suffix]
  have hsw : ∀ z ∈ suffix, z < 2 ^ w := by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz
    · omega
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hz
      exact v.2.trans (by omega)
  have hsimplew : ∀ z ∈ simple, z < 2 ^ w := by
    intro z hz
    unfold simple encGraph at hz
    rcases List.mem_append.mp hz with hz | hz
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl <;> omega
    · exact all_lt_flatEdges _ (by omega) z hz
  obtain ⟨s₁, t₁, hex₁, ht₁, hout₁, _, _, harr₁, _⟩ :=
    toSimpleGraphEdgeListProg_exec (w := w) x.G suffix 0 2 64 0 (by decide) (by decide)
      (by omega) (by omega) (by omega) hin
  have hsrc₁ : s₁.arrs 0 = x.enc := (harr₁ 0 (by decide) (by decide)).trans hin
  have hrm : (Expr.read 0 (.const 1)).eval w s₁ = some x.G.numActivePairs := by
    apply gm13_read_eval (j := 1) (by simp [Expr.eval, checkWord, show 1 < 2 ^ w by omega])
      (v := x.G.numActivePairs)
    · obtain ⟨hi, hv⟩ := enc_getElem_one x.G suffix hsrc₁
      exact List.getElem?_eq_some_iff.mpr ⟨hi, hv⟩
    · omega
  let off := 2 + 3 * x.G.numActivePairs
  let s₂ := s₁.setReg 20 off
  have hex₂ : Exec w (.assign 20
      (.op .add (.const 2) (.op .mul (.const 3) (.read 0 (.const 1))))) s₁ s₂ 7 := by
    apply Exec.assign
    apply gm13_op_eval (u := 2) (v := 3 * x.G.numActivePairs)
    · simp [Expr.eval, checkWord, show 2 < 2 ^ w by omega]
    · refine gm13_op_eval (u := 3) (v := x.G.numActivePairs) ?_ hrm ?_
      · simp [Expr.eval, checkWord, show 3 < 2 ^ w by omega]
      · simp [BinOp.eval, BinOp.raw, checkWord, show 3 * x.G.numActivePairs < 2 ^ w by omega]
    · simp [BinOp.eval, BinOp.raw, checkWord, off,
        show 2 + 3 * x.G.numActivePairs < 2 ^ w by omega]
  have hget : (s₂.arrs 0)[off]? = some x.omega.length := by
    change (s₁.arrs 0)[off]? = _
    rw [hsrc₁]
    change (x.G.enc ++ suffix)[off]? = _
    rw [show off = x.G.enc.length from x.G.length_enc.symm]
    simp [suffix]
  have hrk : (Expr.read 0 (.reg 20)).eval w s₂ = some x.omega.length :=
    gm13_read_eval (by simp [s₂, Expr.eval, checkWord, show off < 2 ^ w by omega])
      hget (by omega)
  let s₃ := s₂.setReg 21 suffix.length
  have hex₃ : Exec w (.assign 21 (.op .add (.const 1) (.read 0 (.reg 20)))) s₂ s₃ 5 := by
    apply Exec.assign
    refine gm13_op_eval (u := 1) (v := x.omega.length) ?_ hrk ?_
    · simp [Expr.eval, checkWord, show 1 < 2 ^ w by omega]
    · simp [BinOp.eval, BinOp.raw, checkWord, hslen, Nat.add_comm,
        show x.omega.length + 1 < 2 ^ w by omega]
  obtain ⟨s₄, t₄, hex₄, ht₄, hout₄, harr₄, hreg₄⟩ :=
    readSliceProg_exec (s := s₃) 0 3 (.reg 20) 21 22 (by decide) (by decide)
      x.G.enc suffix [] (by exact x.G.length_enc) rfl hsw (by omega) (by omega)
      (by simp [s₃, s₂, Expr.eval, checkWord, show off < 2 ^ w by omega, off])
      (by simpa [s₃, s₂, GM13SocietyInput.enc, List.append_nil] using hsrc₁) (by simp [s₃])
  have hout₄' : s₄.arrs 64 = simple := by
    rw [harr₄ 64 (by decide)]
    exact hout₁
  let s₅ := s₄.setReg 20 simple.length
  have hex₅ : Exec w (.assign 20 (.len 64)) s₄ s₅ 2 := by
    apply Exec.assign
    simp [Expr.eval, hout₄', checkWord, show simple.length < 2 ^ w by omega]
  obtain ⟨s₆, t₆, hex₆, ht₆, hout₆, _, harr₆, _⟩ :=
    appendArrProg_exec (s := s₅) 64 3 2 20 21 22 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) simple suffix hsimplew hsw
      (by omega) (by omega) (by simpa [s₅] using hout₄')
      (by simpa [s₅] using hout₄) (by simp [s₅])
      (by rw [show s₅.regs 21 = s₄.regs 21 by simp [s₅], hreg₄ 21 (by decide)]; simp [s₃])
  refine ⟨s₆, t₁ + (7 + (5 + (t₄ + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))), ?_, ?_, ?_⟩
  · dsimp only [Expr.cost] at ht₄
    omega
  · have heq : encAlg81In x.simple = simple ++ suffix := by
      unfold encAlg81In
      change encGraph x.G.toSimpleGraph ++ [x.omega.length] ++ x.omega.map Fin.val = _
      simp only [simple, suffix, List.append_assoc, List.cons_append, List.nil_append]
    rw [heq]
    exact hout₆
  · rw [harr₆ 0 (by decide) (by decide)]
    change s₄.arrs 0 = x.enc
    rw [harr₄ 0 (by decide)]
    exact hsrc₁

/-- Run a simple-society program in separate memory, keeping the original
multigraph input below its memory base. -/
def gm13SocietyRunProg (P : Cmd) : Cmd :=
  .seq gm13SocietySimpleProg (P.shift 64 64)

/-- A timed simple-society program can be called on plain multigraph input.
This theorem concerns the call only. The caller must still restore edges
in the output. The original encoding is retained for that step. -/
theorem gm13SocietyRunProg_computes (P : Cmd) (Out : Alg81Input → List ℕ → Prop)
    (hP : ComputesArrRelInTime alg81Size encAlg81In Out P (fun s => s)) :
    ComputesRelInTime GM13SocietyInput.size (fun x s => s.arrs 0 = x.enc)
      (fun x s => Out x.simple (s.arrs 65) ∧ s.arrs 0 = x.enc)
      (gm13SocietyRunProg P) (fun s => s) := by
  obtain ⟨C, c, hC, hc, hrun⟩ := hP
  refine ⟨C + 500, c + 4, by omega, by omega, ?_⟩
  intro x s hin
  have hactive : x.G.numActivePairs ≤ x.G.numEdges := numActivePairs_le_numEdges x.G
  have hsize : x.G.numEdges + x.n + 1 ≤ x.size := by
    exact (Nat.one_mul _).symm.trans_le
      (Nat.mul_le_mul_right _ (show 1 ≤ x.n + 1 by omega))
  have hpow : 8 * (x.size + 2) ≤ (x.size + 2) ^ 4 := by
    have hbase : 3 ≤ x.size + 2 := by omega
    have hcube : 8 ≤ (x.size + 2) ^ 3 :=
      (by decide : 8 ≤ 3 ^ 3).trans (Nat.pow_le_pow_left hbase 3)
    exact (Nat.mul_le_mul_right (x.size + 2) hcube).trans_eq (pow_succ _ 3).symm
  have hwords : 8 + 3 * x.G.numActivePairs + x.n <
      2 ^ wordSize (c + 4) x.size := by
    have hp := pow_lt_two_pow_wordSize (c := 4) (by decide) x.size
    have hw := wordSize_mono_left (show 4 ≤ c + 4 by omega) x.size
    have hp' := hp.trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hw)
    omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hs₁, hin₁⟩ := gm13SocietySimpleProg_exec x hwords hin
  have hinput : (s₁.unshift 64 64).arrs inArr = encAlg81In x.simple := by
    simpa only [State.unshift_arrs, inArr, Nat.zero_add] using hs₁
  obtain ⟨s_sub, t₂, hex₂, ht₂, hout₂⟩ := hrun x.simple (s₁.unshift 64 64) hinput
  have hw : wordSize c (alg81Size x.simple) ≤ wordSize (c + 4) x.size :=
    (wordSize_mono_right c x.simple_size_le).trans
      (wordSize_mono_left (by omega) x.size)
  refine ⟨s₁.applyShifted 64 64 s_sub, t₁ + t₂,
    .seq hex₁ (Exec.shift_from 64 64 (hex₂.mono_wordSize hw)), ?_, ?_, ?_⟩
  · have ht₂' := ht₂.trans (Nat.mul_le_mul_left C x.simple_size_le)
    have ht₁' : t₁ ≤ 500 * x.size := by omega
    simpa only [Nat.add_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Nat.add_le_add ht₁' ht₂'
  · simpa only [show 65 = 64 + 1 from rfl, State.applyShifted_arrs_add', outArr] using hout₂
  · exact (State.applyShifted_arrs_lt 64 64 s₁ s_sub (by decide : 0 < 64)).trans hin₁

end GraphMinor.Compute
