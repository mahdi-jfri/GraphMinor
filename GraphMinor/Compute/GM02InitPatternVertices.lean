module

public import GraphMinor.Compute.GM02TopologicalEncoding
public import GraphMinor.Compute.Algorithm94Unpack
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Marking the supplied pattern vertices

The two host counts locate the pattern vertex list. Allocate a zero
array on the host vertices, then mark the supplied names. The resulting
bits describe the pattern vertex set, including isolated vertices, and
no other input or working array changes.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Construct the pattern vertex mask in array 22 from the supplied name list. -/
def gm02InitPatternVerticesProg : Cmd :=
  .seq (.assign 17 (.op .add (.reg 12) (.const 1)))
    (.seq (.alloc 22 (.reg 10)) (markSliceGenProg inArr 22 17 13 30))

/-- The marked bits are exactly the supplied pattern vertices, in linear time. -/
theorem gm02InitPatternVerticesProg_exec {w : ℕ} (x : GM02TopologicalInput) (s : State)
    (hsrc : s.arrs inArr = x.enc) (hn : s.regs 10 = x.G.n)
    (hoff : s.regs 12 = 2 + 2 * x.G.edges.length) (hcount : s.regs 13 = x.vertices.card)
    (hw : 1 < 2 ^ w) (hnw : x.G.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w gm02InitPatternVerticesProg s s' t ∧
      t ≤ x.G.n + 14 * x.vertices.card + 10 ∧ s'.arrs 22 = bitSetList x.vertices ∧
      (∀ a, a ≠ 22 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 17 → r ≠ 30 → s'.regs r = s.regs r) := by
  have hLen := x.enc_length
  have hoffw : 2 + 2 * x.G.edges.length < 2 ^ w := by omega
  have hoff1w : 2 + 2 * x.G.edges.length + 1 < 2 ^ w := by omega
  let s₁ := s.setReg 17 (2 + 2 * x.G.edges.length + 1)
  have he₁ : Exec w (.assign 17 (.op .add (.reg 12) (.const 1))) s s₁ 4 :=
    .assign (eval_add (eval_reg hoff hoffw) (eval_const hw) hoff1w)
  let s₂ := s₁.setArr 22 (List.replicate x.G.n 0)
  have he₂ : Exec w (.alloc 22 (.reg 10)) s₁ s₂ (1 + x.G.n) :=
    .alloc (eval_reg (by simpa [s₁, State.setReg] using hn) hnw)
  have hbits : s₂.arrs 22 = bitSetList (∅ : Finset (Fin x.G.n)) := by
    simp [s₂, bitSetList, List.ofFn_const]
  have hsource : s₂.arrs inArr =
      (x.G.enc ++ [x.vertices.card]) ++ ((x.vertices.sort (· ≤ ·)).map Fin.val) ++
        ([x.edges.length] ++ flatEdges x.edges) := by
    simpa only [s₂, s₁, State.setArr_arrs_ne _ _ (by decide : inArr ≠ 22), State.setReg_arrs,
      GM02TopologicalInput.enc, List.append_assoc] using hsrc
  obtain ⟨s₃, t₃, he₃, ht₃, hout, ha, hr⟩ := markSliceGenProg_exec
    (r_start := 17) (r_len := 13) (r_idx := 30) inArr 22 (by decide) (by decide) (by decide)
    (x.G.enc ++ [x.vertices.card]) (x.vertices.sort (· ≤ ·)) ([x.edges.length] ++ flatEdges x.edges) ∅
    hw hnw (by
      simp only [List.length_append, x.G.enc_length, List.length_singleton, List.length_map, Finset.length_sort]
      omega) (s := s₂) hsource
    (by simp [s₂, s₁, x.G.enc_length])
    (by simpa [s₂, s₁, State.setReg, Finset.length_sort] using hcount) hbits
  refine ⟨s₃, 4 + ((1 + x.G.n) + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, ?_⟩
  · rw [Finset.length_sort] at ht₃
    omega
  · simpa only [Finset.empty_union, Finset.sort_toFinset] using hout
  · intro a ha22
    rw [ha a ha22]
    exact State.setArr_arrs_ne _ _ ha22
  · intro r hr17 hr30
    rw [hr r hr30]
    exact State.setReg_regs_ne _ _ hr17

end GraphMinor.Compute
