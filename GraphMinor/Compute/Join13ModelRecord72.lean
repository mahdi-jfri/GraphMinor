module

public import GraphMinor.Compute.Join13ModelBody72

/-!
# A length-prefixed model record for (7.2)

The caller's model table stores the length of each model before its words.
This routine writes that length, then uses the model-body writer. The length
is computed from the model dimensions and the ambient vertex count.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Length of the endpoint-and-vertex-bit model encoding, as a RAM expression. -/
def modelLength72Expr (r : ℕ) : Expr :=
  .op .add (.const 2) (.op .add (.op .mul (.const 2) (.reg (r + 3)))
    (.op .mul (.reg (r + 2)) (.reg (r + 4))))

/-- Write a model's length prefix and its body. -/
def writeModelRecord72Prog (a_src a_ends a_dst r : ℕ) : Cmd :=
  .seq (.write a_dst (.reg (r + 1)) (modelLength72Expr r))
    (.seq (.assign (r + 1) (.op .add (.reg (r + 1)) (.const 1)))
      (writeModelBody72Prog a_src a_ends a_dst r))

/-- A model record is written in linear time, with both stream positions
advanced past the record and raw certificate respectively. -/
theorem writeModelRecord72Prog_exec {w : ℕ} {G : ComputeDigraph} {q : ℕ}
    (e : RawCertEntry G q) (a_src a_ends a_dst r : ℕ)
    (hsrc_dst : a_src ≠ a_dst) (hends_dst : a_ends ≠ a_dst)
    (pre_src post_src pre_dst : List ℕ) (rem : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : G.numVerts + G.numEdges < 2 ^ w)
    (hends_len : 2 * G.numEdges < 2 ^ w)
    (hvH : e.H.digraph.numVerts < 2 ^ w) (hmH : e.H.digraph.numEdges < 2 ^ w)
    (hrem : (encRawModel72 e).length + 1 ≤ rem)
    (hcap : pre_dst.length + rem < 2 ^ w)
    (hsrc_len : (pre_src ++ encRawCertEntry e ++ post_src).length < 2 ^ w)
    (hsrc : s.arrs a_src = pre_src ++ encRawCertEntry e ++ post_src)
    (hends : s.arrs a_ends = endpointWords72 G)
    (hdst : s.arrs a_dst = pre_dst ++ List.replicate rem 0)
    (hr_src : s.regs r = pre_src.length) (hr_dst : s.regs (r + 1) = pre_dst.length)
    (hr_vH : s.regs (r + 2) = e.H.digraph.numVerts)
    (hr_mH : s.regs (r + 3) = e.H.digraph.numEdges)
    (hr_n : s.regs (r + 4) = G.numVerts) (hr_m : s.regs (r + 5) = G.numEdges) :
    let words := (encRawModel72 e).length :: encRawModel72 e
    ∃ s' t, Exec w (writeModelRecord72Prog a_src a_ends a_dst r) s s' t ∧
      t ≤ 80 * ((encRawCertEntry e).length + 1) ∧
      s'.arrs a_dst = pre_dst ++ words ++ List.replicate (rem - words.length) 0 ∧
      s'.regs r = (pre_src ++ encRawCertEntry e).length ∧
      s'.regs (r + 1) = (pre_dst ++ words).length ∧
      Keeps [r, r + 1, r + 6] [a_dst] s s' := by
  have hlen := length_encRawModel72 e
  have hlen_w : (encRawModel72 e).length < 2 ^ w := by omega
  have hvalue : (modelLength72Expr r).eval w s = some (encRawModel72 e).length := by
    rw [hlen]
    simp [modelLength72Expr, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr_vH, hr_mH, hr_n, hw, hvH, hmH,
      show G.numVerts < 2 ^ w by omega,
      show 2 * e.H.digraph.numEdges < 2 ^ w by omega,
      show e.H.digraph.numVerts * G.numVerts < 2 ^ w by omega,
      show 2 * e.H.digraph.numEdges + e.H.digraph.numVerts * G.numVerts < 2 ^ w by omega,
      show 2 + (2 * e.H.digraph.numEdges + e.H.digraph.numVerts * G.numVerts) < 2 ^ w by omega,
      Nat.add_assoc]
  let s₁ := s.writeArr a_dst pre_dst.length (encRawModel72 e).length
  have hex₁ : Exec w (.write a_dst (.reg (r + 1)) (modelLength72Expr r)) s s₁ 11 :=
    .write (by simp [Expr.eval, checkWord, hr_dst, show pre_dst.length < 2 ^ w by omega])
      hvalue (by rw [hdst]; simp; omega)
  have hd₁ : s₁.arrs a_dst = (pre_dst ++ [(encRawModel72 e).length]) ++
      List.replicate (rem - 1) 0 := by
    simp only [s₁, State.writeArr_arrs_self, hdst]
    exact list_set_append_replicate_zero_step pre_dst rem _ (by omega)
  let s₂ := s₁.setReg (r + 1) (pre_dst.length + 1)
  have hex₂ : Exec w (.assign (r + 1) (.op .add (.reg (r + 1)) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_dst,
      show pre_dst.length < 2 ^ w by omega, show pre_dst.length + 1 < 2 ^ w by omega,
      show 1 < 2 ^ w by omega])
  obtain ⟨s₃, t₃, hex₃, ht₃, hd₃, hrs₃, hrd₃, hk₃⟩ :=
    writeModelBody72Prog_exec e a_src a_ends a_dst r hsrc_dst hends_dst
      pre_src post_src (pre_dst ++ [(encRawModel72 e).length]) (rem - 1) s₂
      hw hn hends_len hvH hmH (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega) hsrc_len
      (by simp [s₂, s₁, hsrc_dst, hsrc]) (by simp [s₂, s₁, hends_dst, hends])
      (by exact hd₁)
      (by simp [s₂, s₁, hr_src])
      (by simp [s₂])
      (by simp [s₂, s₁, hr_vH])
      (by simp [s₂, s₁, hr_mH])
      (by simp [s₂, s₁, hr_n])
      (by simp [s₂, s₁, hr_m])
  refine ⟨s₃, 11 + (4 + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, hrs₃, ?_, ?_⟩
  · omega
  · have hsub : rem - 1 - (encRawModel72 e).length = rem - ((encRawModel72 e).length + 1) := by omega
    simpa only [List.singleton_append, List.append_assoc, List.length_cons, hsub] using hd₃
  · simp only [List.length_append, List.length_cons, List.length_nil] at hrd₃ ⊢
    omega
  · refine ⟨fun j hj => ?_, fun a ha => ?_⟩
    · rw [hk₃.1 j hj]
      have hj1 : j ≠ r + 1 := by simp only [List.mem_cons, not_or] at hj; exact hj.2.1
      simp [s₂, s₁, hj1]
    · rw [hk₃.2 a ha]
      have hne : a ≠ a_dst := by simpa using ha
      simp [s₂, s₁, hne]

end GraphMinor.Compute
