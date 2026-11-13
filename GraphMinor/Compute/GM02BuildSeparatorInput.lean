module

public import GraphMinor.Compute.GM02RecursiveSubset
public import GraphMinor.Compute.GM02CopyGraphPrefix
public import GraphMinor.Compute.GM02ConcatArrays

/-!
# Constructing the separator call in each recursive phase

Copy the graph prefix out of the terminated input, construct the subset
specified by A1 or A2, and concatenate those arrays. This gives exactly
the plain input accepted by the proved program for II (3.1). The source
terminated input stays available whenever its array differs from the
three output buffers.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- The actual (3.1) instance specified by the alternating routine. -/
def gm02RecursiveSeparatorInput (allVertices : Bool) (x : GM02SimpleTerminatedInput) :
    GM02Alg31Input where
  n := x.n
  G := x.G
  decAdj := x.decAdj
  Q := gm02RecursiveSubset allVertices x

/-- Construct the graph-and-subset input for II (3.1). -/
def gm02BuildSeparatorInputProg (allVertices : Bool) (src graph bits dst : Arr) : Cmd :=
  .seq (gm02CopyGraphPrefixProg src graph)
    (.seq (gm02RecursiveSubsetProg allVertices src bits) (gm02ConcatArraysProg graph bits dst))

/-- The two recursive phases construct precisely their required separator
inputs from the plain terminated graph, in quadratic-or-better input size. -/
theorem gm02BuildSeparatorInputProg_exec {w : ℕ} (allVertices : Bool) (x : GM02SimpleTerminatedInput)
    (src graph bits dst : Arr) (hsg : src ≠ graph) (hsb : src ≠ bits)
    (hgb : graph ≠ bits) (hgd : graph ≠ dst) (hbd : bits ≠ dst)
    (s : State) (hsrc : s.arrs src = x.enc)
    (hlen : x.enc.length < 2 ^ w)
    (hsep : 2 + 2 * (edgeListOf x.G).length + x.n < 2 ^ w) :
    ∃ s' t, Exec w (gm02BuildSeparatorInputProg allVertices src graph bits dst) s s' t ∧
      t ≤ 150 + 64 * (edgeListOf x.G).length + 30 * x.n + 28 * x.A.index ∧
      s'.arrs dst = (gm02RecursiveSeparatorInput allVertices x).enc ∧
      (∀ a, a ≠ graph → a ≠ bits → a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 40, s'.regs r = s.regs r) := by
  have hn : x.n < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hglen : 2 + 2 * (edgeListOf x.G).length < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hg₁, ha₁, hr₁⟩ := gm02CopyGraphPrefixProg_exec x.G src graph hsg
    ([x.A.index] ++ flatEdges (edgeListOf x.A.pairGraph)) hn hglen s
      (by simpa only [GM02SimpleTerminatedInput.enc, List.append_assoc] using hsrc)
  obtain ⟨s₂, t₂, he₂, ht₂, hb₂, ha₂, hr₂⟩ := gm02RecursiveSubsetProg_exec allVertices x src bits hsb s₁
    ((ha₁ src hsg).trans hsrc) hn hlen
  have hg₂ : s₂.arrs graph = encGraph x.G := (ha₂ graph hgb).trans hg₁
  have hgw : ∀ v ∈ encGraph x.G, v < 2 ^ w := by
    intro v hv
    simp only [encGraph, List.cons_append, List.nil_append, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact hn
    · omega
    · exact all_lt_flatEdges (edgeListOf x.G) hn v hv
  have hbw : ∀ v ∈ gm02VertexBits (gm02RecursiveSubset allVertices x), v < 2 ^ w := by
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    split_ifs <;> omega
  obtain ⟨s₃, t₃, he₃, ht₃, hd₃, ha₃, hr₃⟩ := gm02ConcatArraysProg_exec graph bits dst hgd hbd
    (encGraph x.G) (gm02VertexBits (gm02RecursiveSubset allVertices x)) s₂ hg₂ hb₂ hw
    (by simpa only [length_encGraph, gm02VertexBits, List.length_ofFn] using hsep) hgw hbw
  refine ⟨s₃, _, Exec.seq he₁ (Exec.seq he₂ he₃), ?_, hd₃, ?_, ?_⟩
  · simp only [length_encGraph, gm02VertexBits, List.length_ofFn] at ht₃
    omega
  · intro a hag hab had
    rw [ha₃ a had, ha₂ a hab, ha₁ a hag]
  · intro r hrl
    dsimp only [Reg] at hrl
    rw [hr₃ r (by try dsimp only [Reg]; omega),
      hr₂ r (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)
        (by dsimp only [Reg]; omega) (by dsimp only [Reg]; omega)]
    exact hr₁ r (by try dsimp only [Reg]; omega)

end GraphMinor.Compute
