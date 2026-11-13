module

public import GraphMinor.Compute.GM02PortEdgePrefix
public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.Algorithm94Init
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Finalizing the canonical split graph encoding

The completed pair scan has the right edge words and edge count. Write
that count into the second header word, then copy the used prefix into
a fresh array. The result is exactly the ordinary `encGraph` encoding,
with no unused buffer words included.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Fill the edge-count header and copy just the used graph encoding prefix. -/
@[expose] def gm02FinalizePortGraphProg (dst : Arr) : Cmd :=
  .seq (.write 24 (.const 1) (.reg 68)) (readSliceProg 24 (.const 0) dst (.reg 67) 70)

/-- Finalization produces the plain canonical graph encoding with linear copying time. -/
theorem gm02FinalizePortGraphProg_exec {w n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (s : State) (dst : Arr) (hdst : dst ≠ 24)
    (hbuf : s.arrs 24 = gm02PortEdgeBuffer F (n * n))
    (hpos : s.regs 67 = 2 + 2 * (edgeListOf F).length)
    (hcount : s.regs 68 = (edgeListOf F).length)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hlen : 2 + 2 * (edgeListOf F).length < 2 ^ w) :
    ∃ s' t, Exec w (gm02FinalizePortGraphProg dst) s s' t ∧
      t ≤ 16 * (2 + 2 * (edgeListOf F).length) + 12 ∧ s'.arrs dst = encGraph F ∧
      (∀ a, a ≠ 24 → a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 70 ∨ 72 < r → s'.regs r = s.regs r) := by
  let m := (edgeListOf F).length
  let rest := List.replicate (2 * (n * n - m)) 0
  have hmw : m < 2 ^ w := by dsimp only [m]; omega
  let s₀ := s.writeArr 24 1 m
  have hbound : 1 < (s.arrs 24).length := by
    rw [hbuf]
    simp only [gm02PortEdgeBuffer, gm02PortEdgeWords, List.length_append,
      List.length_cons, List.length_nil, List.length_replicate, length_flatEdges]
    omega
  have he₀ : Exec w (.write 24 (.const 1) (.reg 68)) s s₀ 3 :=
    .write (eval_const hw) (eval_reg hcount hmw) hbound
  have hafter : s₀.arrs 24 = encGraph F ++ rest := by
    rw [show s₀.arrs 24 = (s.arrs 24).set 1 m from State.writeArr_arrs_self .., hbuf]
    simp only [gm02PortEdgeBuffer, gm02PortEdgeWords, gm02EdgePrefix_full, encGraph,
      List.cons_append, List.nil_append, List.set_cons_succ, List.set_cons_zero]
    rfl
  have hwords : ∀ a ∈ encGraph F, a < 2 ^ w := by
    intro a ha
    simp only [encGraph, List.cons_append, List.nil_append, List.mem_cons] at ha
    rcases ha with rfl | rfl | ha
    · exact hn
    · exact hmw
    · exact all_lt_flatEdges (edgeListOf F) hn a ha
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, hr₁⟩ := readSliceProg_exec_full 24 dst (.const 0) 67 70
    (Ne.symm hdst) (by decide) [] (encGraph F) rest rfl rfl hwords hw
    (by simpa only [List.length_nil, Nat.zero_add, length_encGraph] using hlen)
    (s := s₀) (eval_const (by omega)) (by simpa only [List.nil_append] using hafter)
    (by simpa only [s₀, State.writeArr_regs, length_encGraph] using hpos)
  refine ⟨s₁, 3 + t₁, .seq he₀ he₁, ?_, hout, ?_, hr₁⟩
  · simp only [Expr.cost_const, length_encGraph] at ht₁
    omega
  · intro a ha24 hadst
    exact (ha₁ a hadst).trans (State.writeArr_arrs_ne s 1 m ha24)

end GraphMinor.Compute
