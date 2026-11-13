module

public import GraphMinor.Compute.Algorithm99OutIII

/-!
# The length of the output (iii) of Algorithm (9.9)

`Alg99Spec` asks that the block of output (iii) has at most `C · N` words, where
`N = |V(G)| + |E(G)| + 1` for the input graph `G`. Output (a) of steps (5) to (7) bounds the
block that steps (5) to (7) write by `C_blk (v + |E(G' \ X)| + 1)`, where `G'` lives on the `v`
labels of the current graph `G_i`. The program then renames this block into the labels of `G`
(`ParsedCase3Block.movedBlock`), which keeps its length.

So the bound follows from three facts: renaming keeps the length (`length_movedBlock_le`),
`v ≤ |V(G)|` since `orig` is injective, and `G' \ X` has at most as many edges as `G`
(`numEdges_deleteVertices_le_orig`). The result is `length_movedBlock_le_of_outputA`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Function

variable {v n : ℕ} {G' : MultiDigraph v} {G : MultiDigraph n} {X : Finset (Fin v)}
  {orig : Fin v → Fin n}

/-- The renamed block is no longer than the block it comes from. -/
theorem length_movedBlock_le (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    {blk : List ℕ} {p : ParsedCase3Block (G'.deleteVertices X) X}
    (hparse : parseCase3Block (G'.deleteVertices X) X blk = some p) :
    (p.movedBlock hinj hmult).length ≤ blk.length := by
  obtain ⟨rest, hblk⟩ := eq_encCase3Block_append_of_parseCase3Block hparse
  rw [← renamedBlock_eq_movedBlock hinj hmult p, length_renamedBlock, hblk]
  simp

/-- **The length bound of output (iii).** For a valid state of (9.9) on `G` and output (a) of
steps (5) to (7), the block that the program writes in the labels of `G` has at most
`C_blk (|V(G)| + |E(G)| + 1)` words. -/
theorem length_movedBlock_le_of_outputA {h' s h ω : ℕ} {st : Alg99Iter h' G}
    (hst : st.IsValid s) {X : Finset (Fin st.v)}
    {W : WallOfHeight h ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X)}
    {h2 : 2 ≤ h} {he : Even h} {hW : W.IsValid} {C_blk w a_out a_wall : ℕ} {s' : State}
    (hA : IsCase3StepsOutputA h ω (WallOfHeight.wallUnionMultiDigraph st.Gi X st.H) X W h2 he
      hW C_blk w a_out a_wall s')
    {p : ParsedCase3Block ((WallOfHeight.wallUnionMultiDigraph st.Gi X st.H).deleteVertices X) X}
    (hparse : parseCase3Block _ X (s'.arrs a_wall) = some p) :
    (p.movedBlock hst.orig_injective (hst.edgeMult_wallUnion X)).length ≤
      C_blk * (n + G.numEdges + 1) := by
  obtain ⟨_, _, _, _, -, hwall, hlen, -⟩ := hA
  have h1 := length_movedBlock_le hst.orig_injective (hst.edgeMult_wallUnion X) hparse
  rw [hwall] at h1
  have hv : st.v ≤ n := le_of_injective_orig hst.orig_injective
  have hE := numEdges_deleteVertices_le_orig hst.orig_injective (hst.edgeMult_wallUnion X)
    (Y := X.image st.orig) (fun _ => mem_image_orig_iff hst.orig_injective)
  have hE' := MultiDigraph.numEdges_deleteVertices_le G (X.image st.orig)
  calc _ ≤ _ := h1
    _ ≤ _ := hlen
    _ ≤ C_blk * (n + G.numEdges + 1) := Nat.mul_le_mul_left _ (by omega)

end GraphMinor.Compute
