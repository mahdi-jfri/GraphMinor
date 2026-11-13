module

public import GraphMinor.Compute.GM02ReadMultiTerminatedHeader
public import GraphMinor.Compute.GM02ConcatArrays
import GraphMinor.Compute.GM02TerminatedWords
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Computing the underlying-simple terminated input

Read the original multigraph prefix without inspecting its multiplicity
words and construct its canonical simple edge list. Locate and copy the
original termination suffix, then concatenate it with the new graph
prefix. The result is exactly the plain input required by A2 in the
last proof step of II (3.2), page 318.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Replace only the original graph prefix by its underlying simple graph. -/
def gm02SimplifyTerminatedProg : Cmd :=
  .seq (toSimpleGraphEdgeListProg inArr 11 10 20)
    (.seq (gm02ReadMultiTerminatedHeaderProg inArr)
      (.seq (readSliceProg inArr (.reg 40) 12 (.reg 41) 50)
        (gm02ConcatArraysProg 10 12 inArr)))

/-- The underlying-simple conversion writes the exact plain A2 input in quadratic-or-better time. -/
theorem gm02SimplifyTerminatedProg_exec {w : ℕ} (x : GM02MultiTerminatedInput) (s : State)
    (hsrc : s.arrs inArr = x.enc) (hw : 3 < 2 ^ w) (hn : x.n < 2 ^ w)
    (hlen : x.enc.length < 2 ^ w) (hsimple : x.simple.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02SimplifyTerminatedProg s s' t ∧
      t ≤ 96 * x.G.numActivePairs + 32 * x.A.index + 16 * x.simple.enc.length + 143 ∧
      s'.arrs inArr = x.simple.enc := by
  have hlength := x.enc_length
  have hoff : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hcount : 1 + 2 * x.A.index < 2 ^ w := by omega
  have hsuffix := x.terminalWords_all_lt hn hsimple
  have hgraph : ∀ v ∈ encGraph x.G.toSimpleGraph, v < 2 ^ w := by
    intro v hv
    apply x.simple.enc_all_lt hn hsimple v
    rw [x.simple_enc]
    exact List.mem_append_left _ hv
  obtain ⟨s₁, t₁, he₁, ht₁, hGraph₁, _, _, ha₁, _⟩ :=
    toSimpleGraphEdgeListProg_exec x.G x.terminalWords inArr 11 10 20
      (by decide) (by decide) hw hn hoff
      (by simpa only [x.enc_eq] using hsrc)
  have hsrc₁ : s₁.arrs inArr = x.enc := (ha₁ _ (by decide) (by decide)).trans hsrc
  obtain ⟨s₂, he₂, hOff₂, hCount₂, ha₂, _⟩ :=
    gm02ReadMultiTerminatedHeaderProg_exec x inArr s₁ hsrc₁ hw hlen
  have hsrc₂ : s₂.arrs inArr = x.G.enc ++ x.terminalWords ++ [] := by
    simpa only [List.append_nil, x.enc_eq] using (congrFun ha₂ inArr).trans hsrc₁
  obtain ⟨s₃, t₃, he₃, ht₃, hSuffix₃, ha₃, _⟩ :=
    readSliceProg_exec inArr 12 (.reg 40) 41 50 (by decide) (by decide)
      x.G.enc x.terminalWords [] x.G.length_enc x.terminalWords_length hsuffix (by omega)
      (by rw [x.enc_length] at hlen; omega)
      (s := s₂) (eval_reg hOff₂ hoff) hsrc₂ hCount₂
  have hGraph₃ : s₃.arrs 10 = encGraph x.G.toSimpleGraph :=
    (ha₃ _ (by decide)).trans ((congrFun ha₂ 10).trans hGraph₁)
  have hconcat : (encGraph x.G.toSimpleGraph).length + x.terminalWords.length < 2 ^ w := by
    simpa only [x.simple_enc, List.length_append] using hsimple
  obtain ⟨s₄, t₄, he₄, ht₄, hOut₄, _, _⟩ := gm02ConcatArraysProg_exec 10 12 inArr
    (by decide) (by decide) (encGraph x.G.toSimpleGraph) x.terminalWords s₃ hGraph₃ hSuffix₃
      (by omega) hconcat hgraph hsuffix
  refine ⟨s₄, t₁ + (18 + (t₃ + t₄)), Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄)), ?_, ?_⟩
  · have hconcatEq : (encGraph x.G.toSimpleGraph).length + x.terminalWords.length = x.simple.enc.length := by
      rw [x.simple_enc, List.length_append]
    rw [hconcatEq] at ht₄
    change t₃ ≤ 16 * (1 + 2 * x.A.index) + 8 + 1 at ht₃
    omega
  · exact hOut₄.trans x.simple_enc.symm

end GraphMinor.Compute
