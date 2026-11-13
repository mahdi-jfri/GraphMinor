module

public import GraphMinor.Compute.Algorithm86
public import GraphMinor.Compute.Case3Block
public import GraphMinor.Compute.Algorithm99TransportMove
public import GraphMinor.Compute.Algorithm99Relabel

/-!
# Steps (5) to (7) of Algorithm (9.9): the statement used by the loop

Algorithm (9.9) of Graph Minors XIII (page 104) has chosen, in step (4), a flat wall `H^1` of
height `h` and its compass `K^1`. Steps (5) to (7) then read:

"(5) We apply (8.6) to obtain a rural division $\mathcal{A}$ of the society of $H^1$ in
$(G_i \setminus X) \cup H_i$.
(6) For each interior $A \in \mathcal{A}$, we apply (7.2) to $A$ and obtain either a
branch-decomposition of $A$ of width $\le \omega$, or a wall in $A$ of height $h'$.
(7) If for each interior $A \in \mathcal{A}$ we obtain a branch-decomposition of $A$ of width
$\le \omega$, we stop."

These three steps are programmed on the Word RAM by another part of the library. The loop of
(9.9) uses them only through the statement `Case3StepsClaim` of this file, which is a hypothesis of
`algorithm_9_9_of_case3Steps`. It is not a result of the paper: it is the specification of a
program, and it says exactly what that program must do.

All work is in the labels `Fin n` of one multigraph `G'` (in (9.9), `G'` is
`WallOfHeight.wallUnionMultiDigraph G_i X H_i`, the graph $(G_i \setminus X) \cup H_i$), and the
wall `W` lives in `D_del = G'.deleteVertices X`. The program takes as parameters the program of
(8.6) (`alg86Prog shiloachProg`, from `algorithm_8_6`) and a program of (7.2) at height `h'` and
width `ω` (from `Algorithm72Statement`). It ends in one of two ways:

* output (a), tag `0`: the output (iii) of (9.9), written as `2 :: bitSetList X ++ block`, with
  `block` decoded by `case3Decoder` (`IsCase3StepsOutputA`);
* output (b), tag `1`: an interior member `A` of a rural division of the society of `W` in
  `G' \ X`, with its vertex set, its boundary, its edges, and a wall of height `h'` in `A`
  (`IsCase3StepsOutputB`), which step (8) uses.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph

/-- Output (a) of steps (5) to (7) of (9.9) (Graph Minors XIII, page 104): "If for each interior
$A \in \mathcal{A}$ we obtain a branch-decomposition of $A$ of width $\le \omega$, we stop."
The arrays `a_out` and `a_wall` hold `2 :: bitSetList X ++ block` and `block`, and `case3Decoder`
reads from `block` the wall `W`, its society in `G' \ X`, a rural division of it, and a
branch-decomposition of width at most `ω` of each interior member with at least two edges. -/
def IsCase3StepsOutputA (h ω : ℕ) {n : ℕ} (G' : MultiDigraph n) (X : Finset (Fin n))
    (W : WallOfHeight h (G'.deleteVertices X)) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (C_blk w a_out a_wall : ℕ) (s' : State) : Prop :=
  ∃ (K_vList : List ℕ) (K_eList : List (ℕ × ℕ × ℕ)) (corners : List ℕ)
      (members : List Case3MemberRecord),
    s'.arrs a_out = 2 :: (bitSetList X ++ encCase3Block W K_vList K_eList corners members) ∧
    s'.arrs a_wall = encCase3Block W K_vList K_eList corners members ∧
    (encCase3Block W K_vList K_eList corners members).length ≤
      C_blk * (n + (G'.deleteVertices X).numEdges + 1) ∧
    (∀ x ∈ encCase3Block W K_vList K_eList corners members, x < 2 ^ w) ∧
    let block := encCase3Block W K_vList K_eList corners members
    let H := case3Decoder.wall n G' X block
    let S_H := case3Decoder.society n G' X block
    let 𝒜 := case3Decoder.division n G' X block
    H = W.toGMWall h2 he hW ∧
    H.height = h ∧
    GM13.IsFlatWallIn (GM09.deleteVertices G'.toGMDigraph.toGraph X.toNatSet) H ∧
    GM13.IsWallSociety (GM09.deleteVertices G'.toGMDigraph.toGraph X.toNatSet) H S_H ∧
    GM13.IsRuralDivision S_H 𝒜 ∧
    ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      GM13.IsInteriorMember H 𝒜 A →
        let bd := case3Decoder.branchDecomp n G' X block A
        E(A).ncard ≤ 1 ∨
          (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
            GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)

/-- Output (b) of steps (5) to (7) of (9.9) (Graph Minors XIII, page 104): "(8) If for some
interior $A \in \mathcal{A}$ we obtain a wall $H_{i+1}$ in $A$ of height $h'$". There are a
society `S_H` of `H = W.toGMWall` in `G' \ X`, a rural division `𝒜` of it and an interior member
`A`, with

* `V_A`, the vertex set of `A`, inside the compass of `W` and away from `X` and from the perimeter
  of `W`, written in `a_out`;
* `Bd_A`, the boundary of `A` (at most three vertices), written in `a_bd`;
* `A_sub ≤ G' \ X`, a multigraph on `Fin n` with the edges of `A`, written in `a_A_enc`;
* a valid wall `W_A` of height `h'` in `A_sub` renumbered on `Fin |V_A|` (the output of (7.2)),
  moved back to `A_sub` by `compactEmb`, written in `a_wall`. -/
def IsCase3StepsOutputB (h h' : ℕ) {n : ℕ} (G' : MultiDigraph n) (X : Finset (Fin n))
    (W : WallOfHeight h (G'.deleteVertices X)) (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (h2' : 2 ≤ h') (he' : Even h') (a_out a_bd a_wall a_A_enc : ℕ) (s' : State) : Prop :=
  ∃ (S_H : GM09.Society ℕ (ℕ × ℕ × ℕ)) (𝒜 : Set (Graph ℕ (ℕ × ℕ × ℕ)))
      (A : Graph ℕ (ℕ × ℕ × ℕ)) (V_A Bd_A : Finset (Fin n)) (A_sub : MultiDigraph n)
      (W_A : WallOfHeight h' (A_sub.deleteVerticesCompact V_Aᶜ)),
    GM13.IsWallSociety (delGraph G' X) (W.toGMWall h2 he hW) S_H ∧
    GM13.IsRuralDivision S_H 𝒜 ∧
    GM13.IsInteriorMember (W.toGMWall h2 he hW) 𝒜 A ∧
    V_A.toNatSet = V(A) ∧
    V_A ⊆ W.compassFinset ∧
    Disjoint V_A X ∧
    Disjoint V_A W.perimeterFinset ∧
    Bd_A ⊆ V_A ∧
    Bd_A.card ≤ 3 ∧
    Bd_A.toNatSet = GM13.divBoundary S_H A ∧
    A_sub ≤ G'.deleteVertices X ∧
    E(A_sub.toGMDigraph.toGraph) = E(A) ∧
    W_A.IsValid ∧
    (∃ hW_next : (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).IsValid,
      ((W_A.moveOrig A_sub (compactEmb V_Aᶜ)).toGMWall h2' he' hW_next).graph ≤ A ∧
      ((W_A.moveOrig A_sub (compactEmb V_Aᶜ)).toGMWall h2' he' hW_next).height = h') ∧
    s'.arrs a_out = bitSetList V_A ∧
    s'.arrs a_bd = bitSetList Bd_A ∧
    s'.arrs a_wall = (W_A.moveOrig A_sub (compactEmb V_Aᶜ)).encList ∧
    s'.arrs a_A_enc = A_sub.enc

/-- The specification of steps (5) to (7) of Algorithm (9.9) (Graph Minors XIII, page 104).

For even `h, h' ≥ 2`, the program of (8.6) and a program `P72` of (7.2) at height `h'` and width
`ω`, there are constants `C, C_blk, c` such that for all array indices (the inputs `a_G', a_X, a_W,
a_VK` and the four distinct outputs, all below `a_base`) and registers `r_tag < r_base` there is a
program `P` with the following property. Let `W` be a flat wall of height `h` in
`D_del = G'.deleteVertices X`, disjoint from `X`, whose compass avoids `X`. Started with `G'.enc`,
`bitSetList X`, `W.encList` and `bitSetList W.compassFinset` in the input arrays, at word size at
least `wordSize c ((n + 1) * (|E(G')| + n + 1))`, `P` stops within
`C (n + 1) (|E(G')| + n + 1)` steps, changes no array below `a_base` except the outputs and no
register below `r_base` except `r_tag`, and ends with output (a) (tag `0`) or output (b)
(tag `1`). -/
def Case3StepsClaim : Prop :=
  ∀ (h h' ω : ℕ) (h2 : 2 ≤ h) (he : Even h) (h2' : 2 ≤ h') (he' : Even h')
    (shiloachProg : Cmd),
    ComputesArrRelInTime alg81Size encAlg81In
      (fun x out => IsValidAlg86Output x (decAlg86Out x out)) (alg86Prog shiloachProg)
      (fun s => s) →
    ∀ P72 : Cmd,
    ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h') P72
      (fun s => s) →
    ∃ C C_blk c : ℕ,
    ∀ (a_G' a_X a_W a_VK a_out a_bd a_wall a_A_enc a_base r_tag r_base : ℕ),
      (∀ a ∈ [a_G', a_X, a_W, a_VK, a_out, a_bd, a_wall, a_A_enc], a < a_base) →
      [a_out, a_bd, a_wall, a_A_enc].Nodup →
      List.Disjoint [a_out, a_bd, a_wall, a_A_enc] [a_G', a_X, a_W, a_VK] →
      r_tag < r_base →
      ∃ P : Cmd,
      ∀ (w n : ℕ) (G' : MultiDigraph n) (X : Finset (Fin n))
        (W : WallOfHeight h (G'.deleteVertices X)) (hW : W.IsValid),
        Disjoint W.vertexFinset X →
        W.IsFlatWall h2 →
        Disjoint W.compassFinset X →
        W.compassFinset.toNatSet =
          V(GM13.wallCompass (delGraph G' X) (W.toGMWall h2 he hW)) →
        wordSize c ((n + 1) * (G'.numEdges + n + 1)) ≤ w →
        ∀ s : State,
          s.arrs a_G' = G'.enc →
          s.arrs a_X = bitSetList X →
          s.arrs a_W = W.encList →
          s.arrs a_VK = bitSetList W.compassFinset →
          ∃ s' t, Exec w P s s' t ∧
            t ≤ C * (n + 1) * (G'.numEdges + n + 1) ∧
            (∀ a, a < a_base → a ≠ a_out → a ≠ a_bd → a ≠ a_wall → a ≠ a_A_enc →
              s'.arrs a = s.arrs a) ∧
            (∀ r, r < r_base → r ≠ r_tag → s'.regs r = s.regs r) ∧
            ((s'.regs r_tag = 0 ∧
                IsCase3StepsOutputA h ω G' X W h2 he hW C_blk w a_out a_wall s') ∨
              (s'.regs r_tag = 1 ∧
                IsCase3StepsOutputB h h' G' X W h2 he hW h2' he' a_out a_bd a_wall a_A_enc s'))

end GraphMinor.Compute
