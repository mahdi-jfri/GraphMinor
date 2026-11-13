module

public import GraphMinor.Compute.GM02TerminalVertices
public import GraphMinor.Compute.Algorithm94Unpack

/-!
# Constructing the terminal-support bits for routine A2

Read the endpoint slice of the plain terminated input and mark its
vertices in an initially zero array. The endpoint-list identity proves
that these bits describe exactly the termination support. The routine
uses linear time in the vertex count and the number of supplied pairs.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Mark terminal endpoints, using vertex count 40, slice start 280,
slice length 281, and loop counter 282. -/
def gm02MarkTerminalSupportProg (src dst : Arr) : Cmd :=
  .seq (.alloc dst (.reg 40)) (markSliceGenProg src dst 280 281 282)

/-- The marked subset is exactly the supplied termination support.
Only the destination array and the endpoint-loop counter change. -/
theorem gm02MarkTerminalSupportProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (src dst : Arr) (hne : src ≠ dst) (s : State)
    (hsrc : s.arrs src = x.enc) (hn : s.regs 40 = x.n)
    (hstart : s.regs 280 = 3 + 2 * (edgeListOf x.G).length)
    (hcount : s.regs 281 = 2 * x.A.index)
    (hnw : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02MarkTerminalSupportProg src dst) s s' t ∧
      t ≤ x.n + 6 + 28 * x.A.index ∧
      s'.arrs dst = bitSetList (gm02TerminalVertices x.A).toFinset ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 282 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by
    have hl := x.enc_length
    omega
  let s₀ := s.setArr dst (List.replicate x.n 0)
  have hex₀ : Exec w (.alloc dst (.reg 40)) s s₀ (1 + x.n) := by
    apply Exec.alloc
    simp [Expr.eval, hn, checkWord_of_lt hnw]
  have hbits : s₀.arrs dst = bitSetList (∅ : Finset (Fin x.n)) := by
    simp [s₀, bitSetList, List.ofFn_const]
  have hsource : s₀.arrs src = (encGraph x.G ++ [x.A.index]) ++
      (gm02TerminalVertices x.A).map Fin.val ++ [] := by
    simp only [s₀, State.setArr_arrs_ne _ _ hne, hsrc, List.append_nil,
      gm02TerminalVertices_map_val, GM02SimpleTerminatedInput.enc]
  obtain ⟨s', t, hex, ht, hout, ha, hr⟩ := markSliceGenProg_exec (r_start := 280) (r_len := 281) (r_idx := 282) src dst hne
    (by decide) (by decide) (encGraph x.G ++ [x.A.index]) (gm02TerminalVertices x.A) [] ∅
    hw hnw (by
      simp only [List.length_append, List.length_map, List.length_singleton,
        length_encGraph, gm02TerminalVertices_length]
      rw [x.enc_length] at hlen
      omega)
    hsource (by simp only [s₀, State.setArr_regs, List.length_append, List.length_singleton, length_encGraph]; omega)
    (by simpa only [s₀, State.setArr_regs, gm02TerminalVertices_length] using hcount) hbits
  refine ⟨s', _, Exec.seq hex₀ hex, ?_, ?_, ?_, ?_⟩
  · rw [gm02TerminalVertices_length] at ht
    omega
  · simpa only [Finset.empty_union] using hout
  · intro a ha'
    rw [ha a ha']
    exact State.setArr_arrs_ne _ _ ha'
  · intro r hr'
    exact hr r hr'

end GraphMinor.Compute
