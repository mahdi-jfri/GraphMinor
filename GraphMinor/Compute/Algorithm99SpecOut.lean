module

public import GraphMinor.Compute.Algorithm99SpecCore
import GraphMinor.Compute.Algorithm99MoveAProg

/-!
# The outputs (ii) and (iii) of (9.9) in the form that (10.5) reads

When Algorithm (9.9) of Graph Minors XIII (page 104) runs on `D = G_i \ Z_i` with a state map
`orig` that misses `Z_i` (`alg99SpecCoreProg`), the loop ends with `1 :: model` or
`2 :: (bitSetList X ++ block)` in `outArr`. `alg99SpecOut_of_loopOut` says that these words are
what `Alg99Spec` asks for in its cases (ii) and (iii): the model misses `Z_i` and is a model of
`K_p` in `D`; `X` misses `Z_i`, `|X| < C(p, 2)`, the block is at most `C_blk (m + |E(D)| + 1)` words
long, its words are below `2 ^ w`, and it decodes, relative to `X ∪ Z_i` in `G_i`, to a flat wall,
its society, a rural division and the decompositions of the interior members.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Function

/-- The words of the renamed block are below `2 ^ w` when those of the block are, as the
renaming program `alg99MoveAProg` shows. -/
theorem all_lt_movedBlock {v n w : ℕ} {G' : MultiDigraph v} {G : MultiDigraph n}
    {X : Finset (Fin v)} {orig : Fin v → Fin n} (hinj : Injective orig)
    (hmult : ∀ u w, G'.edgeMult u w = 0 ∨ G'.edgeMult u w = G.edgeMult (orig u) (orig w))
    {p : ParsedCase3Block (G'.deleteVertices X) X} {blk : List ℕ}
    (hparse : parseCase3Block (G'.deleteVertices X) X blk = some p)
    (hblk_w : ∀ x ∈ blk, x < 2 ^ w) (hn_w : n < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hlen_w : blk.length < 2 ^ w) : ∀ x ∈ p.movedBlock hinj hmult, x < 2 ^ w := by
  let s : State := ⟨fun _ => 0, fun a => if a = 0 then blk else origList orig⟩
  obtain ⟨-, -, -, -, -, -, hlt, -⟩ := alg99MoveAProg_exec hinj hmult p hparse (a := 0) (o := 1)
    (a_dst := 2) (by decide) (by decide) 0 (s := s) (by simp [s]) (by simp [s]) rfl hblk_w hn_w
    hw4 hlen_w
  exact hlt

/-- Case (ii) of `Alg99Spec`, for the array `a2`: a model of `K_p` in `G_i \ Z_i` that misses
`Z_i`. -/
def Alg99SpecOutII (pp : ℕ) {m : ℕ} (Gi : MultiDigraph m) (Zs : Finset (Fin m)) (a2 : List ℕ) :
    Prop :=
  ∃ X : Fin pp → Finset (Fin m),
    a2 = encBitSetsUpTo X pp ∧
    (∀ j : Fin pp, Disjoint (X j) Zs) ∧
    IsCliqueModel (Gi.deleteVertices Zs).toSimpleGraph pp X

/-- Case (iii) of `Alg99Spec`, for the arrays `a2` and `a3` (with `C_blk` as the constant of the
length of the block). -/
def Alg99SpecOutIII (pp h ω C_blk w : ℕ) {m : ℕ} (Gi : MultiDigraph m) (Zs : Finset (Fin m))
    (a2 a3 : List ℕ) : Prop :=
  ∃ (X : Finset (Fin m)) (block : List ℕ),
    a2 = bitSetList X ∧
    a3 = block ∧
    block.length ≤ C_blk * (m + (Gi.deleteVertices Zs).numEdges + 1) ∧
    (∀ x ∈ block, x < 2 ^ w) ∧
    Disjoint X Zs ∧
    X.card < pp.choose 2 ∧
    let X' := X ∪ Zs
    let H := case3Decoder.wall m Gi X' block
    let S_H := case3Decoder.society m Gi X' block
    let 𝒜 := case3Decoder.division m Gi X' block
    H.height = h ∧
    GM13.IsFlatWallIn
      (GM09.deleteVertices (Gi.toGMDigraph.deleteVertices Zs.toNatSet).toGraph X.toNatSet) H ∧
    GM13.IsWallSociety
      (GM09.deleteVertices (Gi.toGMDigraph.deleteVertices Zs.toNatSet).toGraph X.toNatSet) H S_H ∧
    GM13.IsRuralDivision S_H 𝒜 ∧
    ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      GM13.IsInteriorMember H 𝒜 A →
        let bd := case3Decoder.branchDecomp m Gi X' block A
        E(A).ncard ≤ 1 ∨
          (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
            GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)

/-- **The outputs (ii) and (iii) of (9.9) for (10.5)** (Graph Minors XIII, pages 104 and 108).
What the loop writes, for a run on `D = G_i \ Z_i` whose states map no vertex into `Z_i`, is
`1 :: a2` with case (ii) of `Alg99Spec` for `a2`, or `2 :: (a2 ++ a3)` with `a2` of length `m` and
case (iii) of `Alg99Spec` for `a2` and `a3`. -/
theorem alg99SpecOut_of_loopOut {pp h ω h' C_blk w B m : ℕ} {h2 : 2 ≤ h} {he : Even h}
    {Gi : MultiDigraph m} {Zs : Finset (Fin m)} {out : List ℕ}
    (hout : Alg99LoopOut pp h ω h2 he C_blk w B (h' := h') (G := Gi.deleteVertices Zs)
      (fun st => ∀ u, st.orig u ∉ Zs) out)
    (hm_w : m < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hlen_w : C_blk * (m + (Gi.deleteVertices Zs).numEdges + 1) < 2 ^ w) :
    (∃ a2, out = 1 :: a2 ∧ Alg99SpecOutII pp Gi Zs a2) ∨
    (∃ a2 a3, out = 2 :: (a2 ++ a3) ∧ a2.length = m ∧
      Alg99SpecOutIII pp h ω C_blk w Gi Zs a2 a3) := by
  obtain ⟨st, hst, hR, ⟨K, hK, rfl⟩ | ⟨X, hXc, W, hW, hZ, hKc, s_m, p, hA, hparse, rfl⟩⟩ := hout
  · refine Or.inl ⟨_, rfl, _, rfl, fun j => ?_, IsCliqueModel.map_orig hst hK⟩
    rw [Finset.disjoint_left]
    intro x hx hxZ
    obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hx
    exact hR u hxZ
  · obtain ⟨p', hparse', hdisj, hcard, hH, hflat, hsoc, hrd, hbd⟩ :=
      isAlg99SpecIII_of_case3StepsOutputA (pp := pp) hst hR hXc hZ hKc hA
    rw [hparse] at hparse'
    cases Option.some.inj hparse'
    have hlen := length_movedBlock_le_of_outputA hst hA hparse
    obtain ⟨_, _, _, _, -, hwall, hlenA, hval, -⟩ := hA
    have hv : st.v ≤ m := le_of_injective_orig hst.orig_injective
    have hE := numEdges_deleteVertices_le_orig hst.orig_injective (hst.edgeMult_wallUnion X)
      (Y := X.image st.orig) (fun _ => mem_image_orig_iff hst.orig_injective)
    have hE' := MultiDigraph.numEdges_deleteVertices_le (Gi.deleteVertices Zs) (X.image st.orig)
    have hblk : (s_m.arrs (B - 3)).length < 2 ^ w := by
      rw [hwall]; exact (hlenA.trans (Nat.mul_le_mul_left _ (by omega))).trans_lt hlen_w
    refine Or.inr ⟨_, _, rfl, length_bitSetList _, X.image st.orig, _, rfl, rfl, hlen,
      all_lt_movedBlock _ _ hparse (by rw [hwall]; exact hval) hm_w hw4 hblk,
      hdisj, hcard, hH, hflat, hsoc, hrd, hbd⟩

end GraphMinor.Compute
