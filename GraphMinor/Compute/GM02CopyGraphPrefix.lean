module

public import GraphMinor.Compute.Parse
public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.MultiDigraph

/-!
# Copying the plain graph prefix of a recursive input

A terminated input appends endpoint pairs after the graph edge list.
The separator and edge-filtering routines use the graph prefix alone.
Read its edge-count header, compute the prefix length, and copy exactly
that many words into a fresh array. The input suffix is not inspected.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- Copy just the graph prefix, using registers 240 through 244. -/
def gm02CopyGraphPrefixProg (src dst : Arr) : Cmd :=
  .seq (.assign 240 (.read src (.const 1)))
    (.seq (.assign 241 (.op .add (.const 2) (.op .mul (.const 2) (.reg 240))))
      (readSliceProg src (.const 0) dst (.reg 241) 242))

/-- The graph-prefix copy runs in linear edge-list time and preserves all
source arrays. -/
theorem gm02CopyGraphPrefixProg_exec {n w : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (src dst : Arr) (hne : src ≠ dst) (rest : List ℕ)
    (hn : n < 2 ^ w) (hlen : 2 + 2 * (edgeListOf G).length < 2 ^ w)
    (s : State) (hsrc : s.arrs src = encGraph G ++ rest) :
    ∃ s' t, Exec w (gm02CopyGraphPrefixProg src dst) s s' t ∧
      t ≤ 16 * (2 + 2 * (edgeListOf G).length) + 18 ∧
      s'.arrs dst = encGraph G ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 240, s'.regs r = s.regs r) := by
  let m := (edgeListOf G).length
  have hm : m < 2 ^ w := by omega
  have hlen' : 2 + 2 * m < 2 ^ w := hlen
  have htwo : 2 < 2 ^ w := by omega
  let s₁ := s.setReg 240 m
  have he₁ : Exec w (.assign 240 (.read src (.const 1))) s s₁ 3 := by
    apply Exec.assign
    simp [Expr.eval, checkWord_of_lt (by omega : 1 < 2 ^ w), hsrc, encGraph, m, checkWord_of_lt hm]
  let s₂ := s₁.setReg 241 (2 + 2 * m)
  have he₂ : Exec w (.assign 241 (.op .add (.const 2) (.op .mul (.const 2) (.reg 240)))) s₁ s₂ 6 := by
    apply Exec.assign
    simp [Expr.eval, BinOp.eval, BinOp.raw, s₁, checkWord_of_lt htwo,
      checkWord_of_lt hm, checkWord_of_lt (by omega : 2 * m < 2 ^ w), checkWord_of_lt hlen']
  have hwords : ∀ v ∈ encGraph G, v < 2 ^ w := by
    intro v hv
    simp only [encGraph, List.cons_append, List.nil_append, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact hn
    · exact hm
    · exact all_lt_flatEdges (edgeListOf G) hn v hv
  obtain ⟨s', t, he, ht, hout, ha, hr⟩ := readSliceProg_exec src dst (.const 0) 241 242 hne
    (by decide) [] (encGraph G) rest rfl rfl hwords (by omega) (by simpa only [List.length_nil, Nat.zero_add, length_encGraph] using hlen)
    (s := s₂) (by simp [Expr.eval, checkWord_of_lt (by omega : 0 < 2 ^ w)])
    (by simpa [s₂, s₁] using hsrc)
    (by simp [s₂, length_encGraph, m])
  refine ⟨s', 3 + (6 + t), Exec.seq he₁ (Exec.seq he₂ he), ?_, hout, ?_, ?_⟩
  · simp only [Expr.cost_const, length_encGraph] at ht
    omega
  · intro a ha'
    exact ha a ha'
  · intro r hrl
    dsimp only [Reg] at hrl
    rw [hr r (by omega)]
    change ((s.setReg 240 m).setReg 241 (2 + 2 * m)).regs r = s.regs r
    rw [State.setReg_regs_ne (r := 241) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 240) (r' := r) _ _ (by dsimp only [Reg]; omega)]

end GraphMinor.Compute
