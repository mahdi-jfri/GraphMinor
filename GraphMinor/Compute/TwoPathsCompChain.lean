module

public import GraphMinor.Compute.TwoPathsSpec
public import GraphMinor.HP25.Sec5ExtractTwo

/-!
# What the completion leaves for the extraction

The completion program `comp` (Algorithm 5.2 of S. Humeau and D. Pous, *On the Two Paths Theorem
and the Two Disjoint Paths Problem*, arXiv:2505.16431v2 (14 August 2025), page 23, with the
correction
of `GraphMinor/HP25/Sec5Tighten.lean`) and the extraction program `ext` (Section 5.3, pages 22–23,
with the correction in `GraphMinor/HP25/Sec5ExtractTwo.lean`) meet in memory. This file fixes that
meeting point.

The extraction is `extractCrossingTwoPart`. It lifts a crossing of a subinstance to the graph
`H + F` of the subinstances (Figure 11), views it in the graph `H_full` that has every edge the
completion added, and then undoes the added edges, the last one first. The completion adds collapse
edges first and loop edges after them, so the extraction undoes the loop edges first, by
search, and then the collapse edges, with no search (Claim 5.5). To undo a loop edge `y s` it needs
the edge and the path `P₀` that the completion had when it added `y s`. To undo a collapse edge
`y z` it needs only `y`, `z` and the window `N` between them.

So `comp` leaves four record arrays:
* `aStepEdge` (array `202`) holds the loop edges as a flat list `y₀ s₀ y₁ s₁ …`, in the order
  they were added;
* `aStepBase` (array `200`) holds the vertex list of the path at the first loop edge;
* `aStepDrop` (array `201`) holds, for each entry of `aStepBase`, the number of loop edges whose
  path contains that vertex;
* `aT2Rec` (array `203`) holds the collapse edges, in the order they were added, each as
  `y, z, |N|` followed by the vertices of `N` (`encodeT2`).

The paths of the loop edges are sublists of the first one, since each loop step only removes the
pocket `N` from the path. So the path of loop edge `i` (counting from `0`) is the list of the entries
of `aStepBase` whose entry in `aStepDrop` is larger than `i` (`stepPathOf`).

`CompChainOutput` states what a flag-`0` run of `comp` must give `ext`: every hypothesis of
`extractCrossingTwoPart_isSome` for the graphs `H` and `H + F`, a `T2Chain` from `H` to a graph
`G₂` and an `AddedEdgeChain` from `G₂` to a graph `H_full ≥ H + F` whose steps are those of the
record arrays. `CompChainOutput.extract_isSome` checks the fit: from `CompChainOutput` and a
crossing of a subinstance in the form of `CompletionStatement`, `extractCrossingTwoPart` returns a
crossing, for every lawful walk search. It uses one hypothesis that is still open,
`ExtractionExhaustiveStatement`, the exhaustiveness of Rules 1 to 4 (`StepSearchExhaustive`).
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### The record arrays -/

/-- Record array holding the vertex list of the path at the first added edge. -/
abbrev aStepBase : Arr := 200

/-- Record array holding, for each entry of `aStepBase`, the number of added edges whose path
contains it. -/
abbrev aStepDrop : Arr := 201

/-- Record array holding the loop edges, as a flat list `y₀ s₀ y₁ s₁ …`. -/
abbrev aStepEdge : Arr := 202

/-- Record array holding the collapse edges, each as `y, z, |N|` and then the window `N`. -/
abbrev aT2Rec : Arr := 203

/-- The path of loop edge `i`: the entries of `base` whose entry in `drop` is larger than `i`. -/
def stepPathOf (base drop : List ℕ) (i : ℕ) : List ℕ :=
  ((base.zip drop).filter fun p => decide (i < p.2)).map Prod.fst

/-- The loop steps that the arrays describe: for each `i < |E| / 2`, the edge `E[2i] E[2i+1]` and
the path `stepPathOf base drop i`. -/
def recordSteps (E base drop : List ℕ) : List (ℕ × ℕ × List ℕ) :=
  (List.range (E.length / 2)).map fun i =>
    (E.getD (2 * i) 0, E.getD (2 * i + 1) 0, stepPathOf base drop i)

/-- The collapse records: each step `(y, z, N)` as `y, z, |N|` and then `N`. -/
def encodeT2 : List (ℕ × ℕ × List ℕ) → List ℕ
  | [] => []
  | (y, z, N) :: rest => y :: z :: N.length :: (N ++ encodeT2 rest)

/-! ### The steps of a chain of added edges -/

variable {V : Type*} {C A B : List V} {a b : V} {k : ℕ}

/-- The steps of an `AddedEdgeChain`, first added first: the edge `y s` and the vertex list of the
path `P₀` of each step. -/
def chainSteps {G : SimpleGraph V} :
    {H : SimpleGraph V} → AddedEdgeChain V C A B a b k G H → List (V × V × List V)
  | _, .nil => []
  | _, .snoc step _ chain => chainSteps chain ++ [(step.y, step.s, step.P₀.support)]

/-- The steps of a `T2Chain`, first added first: the edge `y z` and the window `N` of each step. -/
def t2Steps {G : SimpleGraph V} :
    {H : SimpleGraph V} → T2Chain V C A B a b k G H → List (V × V × List V)
  | _, .nil => []
  | _, .snoc step _ chain => t2Steps chain ++ [(step.y, step.z, step.N)]

/-- The steps of a list of triples of vertices of `Fin N`, as triples of numbers. -/
def stepsVal {N : ℕ} (l : List (Fin N × Fin N × List (Fin N))) : List (ℕ × ℕ × List ℕ) :=
  l.map fun e => (e.1.1, e.2.1.1, e.2.2.map Fin.val)

theorem length_chainSteps {G : SimpleGraph V} :
    ∀ {H : SimpleGraph V} (chain : AddedEdgeChain V C A B a b k G H),
      (chainSteps chain).length = chain.length
  | _, .nil => rfl
  | _, .snoc _ _ chain => by
    simp [chainSteps, AddedEdgeChain.length, length_chainSteps chain]

/-! ### What the extraction needs from the completion -/

/-- The chains of a completion run, as the arrays record them. `t2rec` is the array `aT2Rec`, and
`E`, `base`, `drop` are the arrays `aStepEdge`, `aStepBase`, `aStepDrop`. There are a `T2Chain`
from `H` to a graph `G₂` and an `AddedEdgeChain` from `G₂` to a graph `H_full` that has every edge
of `H + F`, with fewer loop steps than `P'` has vertices, such that the records describe their
steps. -/
def RecordedChains {N : ℕ} (H : SimpleGraph (Fin N)) (a b : Fin N) (A B : List (Fin N))
    (F : List ℕ) (len : ℕ) (t2rec E base drop : List ℕ) : Prop :=
  ∃ (G₂ H_full : SimpleGraph (Fin N)) (t2 : T2Chain (Fin N) (a :: A ++ b :: B) A B a b 0 H G₂)
    (t3 : AddedEdgeChain (Fin N) (a :: A ++ b :: B) A B a b 0 G₂ H_full),
    H ⊔ pairGraph N F ≤ H_full ∧ t3.length < len ∧
    encodeT2 (stepsVal (t2Steps t2)) = t2rec ∧ stepsVal (chainSteps t3) = recordSteps E base drop

/-- The facts that the extraction needs about the output `F`, `P'` of a completion of the instance
`(H, a A b B)`, with `t2rec`, `E`, `base` and `drop` the record arrays `aT2Rec`, `aStepEdge`,
`aStepBase` and `aStepDrop`. They are the hypotheses of `extractCrossingTwoPart_isSome` for the
graphs `H` and `H + F` and the cycle `C = a A b B`, together with:
* `chains`: the two chains of the run, as the records describe them (`RecordedChains`);
* `baseNodup`, `dropLength`: `base` is a list of distinct vertices, and `drop` has the same length,
  so both have length at most `N`;
* `lenF`: fewer edges are kept than `P'` has vertices. -/
structure ChainFacts {N : ℕ} (H : SimpleGraph (Fin N)) (a b : Fin N) (A B : List (Fin N))
    (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b) (t2rec E base drop : List ℕ) : Prop where
  tpath : IsTPath (H ⊔ pairGraph N F) (a :: A ++ b :: B) P'
  edges : ∀ u v, (H ⊔ pairGraph N F).Adj u v → H.Adj u v ∨ IsListEdge P'.support u v
  induced : ∀ u ∈ P'.support, ∀ v ∈ P'.support, (H ⊔ pairGraph N F).Adj u v →
    IsListEdge P'.support u v
  sep : Separates H {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B}
  sides : OnBothSidesList H (a :: A ++ b :: B) A B P'.support
  tight : IsTight (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P'.support
  chains : RecordedChains H a b A B F P'.support.length t2rec E base drop
  baseNodup : ∃ l : List (Fin N), l.Nodup ∧ base = l.map Fin.val
  dropLength : drop.length = base.length
  lenF : F.length / 2 < P'.support.length

/-- **What a flag-`0` run of `comp` leaves for `ext`.** Arrays `aF` and `aNewPath` hold a list `F`
of edges and the vertex list of a `C`-path `P'` of `H + F` from `a` to `b`, and `ChainFacts` holds
for them and the record arrays `aT2Rec`, `aStepEdge`, `aStepBase`, `aStepDrop`. -/
def CompChainOutput {N : ℕ} (H : SimpleGraph (Fin N)) (a b : Fin N) (A B : List (Fin N))
    (s : State) : Prop :=
  ∃ (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b),
    s.arrs aF = F ∧ s.arrs aNewPath = P'.support.map Fin.val ∧
    ChainFacts H a b A B F P' (s.arrs aT2Rec) (s.arrs aStepEdge) (s.arrs aStepBase)
      (s.arrs aStepDrop)

/-! ### The open hypothesis: exhaustiveness of Rules 1 to 4 -/

/-- **Exhaustiveness of Rules 1 to 4** (open). For every lawful walk search,
every added-edge step and every list `verts` of all vertices, the dichotomy `BridgeSearchExhaustive`
of Case 3 holds for every crossing of the step (`StepSearchExhaustive`,
`GraphMinor/HP25/Sec5ExtractClose.lean`). With it, `extractCrossingTwoPart_isSome` needs no other
open hypothesis. The search is a parameter, since `ext` runs a breadth-first search, not the
default search `findWalkIn`. -/
def ExtractionExhaustiveStatement : Prop :=
  ∀ (V : Type) [DecidableEq V] [WalkSearch V] [LawfulWalkSearch V] (C A B : List V) (a b : V)
    (k : ℕ)
    (step : AddedEdgeStep V C A B a b k) [DecidableRel step.G₀.Adj] (verts : List V),
    (∀ v : V, v ∈ verts) → StepSearchExhaustive step verts

/-- The two vertex lists of a crossing of either subinstance. -/
def subSupports {G₁ G₂ : SimpleGraph V} {T₁ T₂ : List V} :
    CrossingWalks G₁ T₁ ⊕ CrossingWalks G₂ T₂ → List V × List V
  | .inl cr => (cr.Q.support, cr.R.support)
  | .inr cr => (cr.Q.support, cr.R.support)

end GraphMinor.Compute.TwoPaths

end

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

public section

/-- Every chain of added edges is exhaustive under `ExtractionExhaustiveStatement`. -/
theorem exhaustive_of_statement (hexh : ExtractionExhaustiveStatement) {V : Type} [DecidableEq V]
    [WalkSearch V] [LawfulWalkSearch V] {C A B : List V} {a b : V} {k : ℕ} {verts : List V} (hverts : ∀ v : V, v ∈ verts)
    {G : SimpleGraph V} :
    ∀ {H : SimpleGraph V} (chain : AddedEdgeChain V C A B a b k G H), chain.Exhaustive verts
  | _, .nil => trivial
  | _, .snoc step dec chain => by
    let _ := dec
    exact ⟨hexh V C A B a b k step verts hverts, exhaustive_of_statement hexh hverts chain⟩

variable {N : ℕ} {H G : SimpleGraph (Fin N)} {Pv A : List (Fin N)}

/-- The graph of subinstance `1` of `G` along `Pv` is the graph of the first subinstance of
`extractCrossingTwoPart`, when every edge of `G` outside `H` has both ends on `Pv`: the vertices
that `A` reaches off `Pv` are the same in `G` and in `H`. -/
theorem subGraph_one_eq (hle : H ≤ G) (hG : ∀ x y, G.Adj x y → H.Adj x y ∨ (x ∈ Pv ∧ y ∈ Pv)) :
    subGraph G Pv A 1 = restrict G (sideSetOf H Pv A) := by
  have h := restrict_notMem_eq_of_adj_or_mem hle hG
  simp only [subGraph, sideOne, reachOff, sideSetOf, h]

/-- The graph of subinstance `2`, as in `subGraph_one_eq`. -/
theorem subGraph_two_eq (hle : H ≤ G) (hG : ∀ x y, G.Adj x y → H.Adj x y ∨ (x ∈ Pv ∧ y ∈ Pv)) :
    subGraph G Pv A 2 = restrict G (sideComplOf H Pv A) := by
  have h := restrict_notMem_eq_of_adj_or_mem hle hG
  simp only [subGraph, sideTwo, reachOff, sideComplOf, h]

/-- A crossing of subinstance `i` as `CompletionStatement` gives it (`CrossingAt` of
`subGraph (H + F) P' A i` and `subCycle a b A B m i`) is a valid crossing of the matching
subinstance of `extractCrossingTwoPart`, with the same two vertex lists. -/
theorem exists_subCrossing {F : List ℕ} {a b : Fin N} {B m : List (Fin N)}
    {P' : (H ⊔ pairGraph N F).Walk a b} (hm : P'.support = a :: m ++ [b])
    (hedge : ∀ u v, (H ⊔ pairGraph N F).Adj u v → H.Adj u v ∨ IsListEdge P'.support u v)
    {i : ℕ} (hi : i = 1 ∨ i = 2) {aQ' aR' : Arr} {s : State}
    (hcr : CrossingAt (subGraph (H ⊔ pairGraph N F) P'.support A i) (subCycle a b A B m i) aQ' aR'
      s) :
    ∃ subCr : CrossingWalks (restrict (H ⊔ pairGraph N F) (sideSetOf H (a :: m ++ [b]) A))
        (a :: A ++ b :: m.reverse) ⊕
      CrossingWalks (restrict (H ⊔ pairGraph N F) (sideComplOf H (a :: m ++ [b]) A))
        (b :: B ++ a :: m),
      Sum.elim CrossingWalks.Valid CrossingWalks.Valid subCr ∧
      s.arrs aQ' = (subSupports subCr).1.map Fin.val ∧
      s.arrs aR' = (subSupports subCr).2.map Fin.val := by
  have hG : ∀ x y, (H ⊔ pairGraph N F).Adj x y → H.Adj x y ∨
      (x ∈ a :: m ++ [b] ∧ y ∈ a :: m ++ [b]) := fun x y h =>
    (hedge x y h).imp_right fun h => hm ▸ ⟨h.mem_left, h.mem_right⟩
  obtain ⟨x, y, z, t, Q, R, hc, hQ, hR⟩ := hcr
  rcases hi with rfl | rfl
  · have hle : subGraph (H ⊔ pairGraph N F) P'.support A 1 ≤
        restrict (H ⊔ pairGraph N F) (sideSetOf H (a :: m ++ [b]) A) := by
      rw [hm]; exact (subGraph_one_eq le_sup_left hG).le
    refine ⟨.inl ⟨x, y, z, t, Q.mapLe hle, R.mapLe hle⟩, ?_, by simp [subSupports, hQ], by simp [subSupports, hR]⟩
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine ⟨h1, ?_, ?_, by rw [support_mapLe, support_mapLe]; exact h4⟩
    · exact ⟨h2.1.mapLe hle, h2.2.1, h2.2.2.1, by rw [support_mapLe]; exact h2.2.2.2⟩
    · exact ⟨h3.1.mapLe hle, h3.2.1, h3.2.2.1, by rw [support_mapLe]; exact h3.2.2.2⟩
  · have hle : subGraph (H ⊔ pairGraph N F) P'.support A 2 ≤
        restrict (H ⊔ pairGraph N F) (sideComplOf H (a :: m ++ [b]) A) := by
      rw [hm]; exact (subGraph_two_eq le_sup_left hG).le
    refine ⟨.inr ⟨x, y, z, t, Q.mapLe hle, R.mapLe hle⟩, ?_, by simp [subSupports, hQ], by simp [subSupports, hR]⟩
    obtain ⟨h1, h2, h3, h4⟩ := hc
    refine ⟨h1, ?_, ?_, by rw [support_mapLe, support_mapLe]; exact h4⟩
    · exact ⟨h2.1.mapLe hle, h2.2.1, h2.2.2.1, by rw [support_mapLe]; exact h2.2.2.2⟩
    · exact ⟨h3.1.mapLe hle, h3.2.1, h3.2.2.1, by rw [support_mapLe]; exact h3.2.2.2⟩

/-- **The fit of the formats.** After a completion that meets `CompChainOutput`, with `F` in `aF`
and `P' = a m b` in `aNewPath`, there are a `T2Chain` and a loop chain whose steps are those of the
record arrays, and for them `extractCrossingTwoPart` returns a crossing of `C` in `H` from every
valid crossing of a subinstance, for every lawful walk search. The search runs over all vertices
`List.finRange N`. The hypothesis `hexh` is the open exhaustiveness of Rules 1 to 4. -/
theorem CompChainOutput.extract_isSome (hexh : ExtractionExhaustiveStatement)
    [WalkSearch (Fin N)] [LawfulWalkSearch (Fin N)]
    {a b : Fin N} {A B : List (Fin N)} {P : H.Walk a b} (hsplit : IsSplitInput H a b A B P)
    {s : State} (hout : CompChainOutput H a b A B s) {F : List ℕ} {m : List (Fin N)}
    [DecidableRel (H ⊔ pairGraph N F).Adj] (P' : (H ⊔ pairGraph N F).Walk a b)
    (hF : s.arrs aF = F) (hP' : s.arrs aNewPath = P'.support.map Fin.val)
    (hm : P'.support = a :: m ++ [b]) :
    ChainFacts H a b A B F P' (s.arrs aT2Rec) (s.arrs aStepEdge) (s.arrs aStepBase)
      (s.arrs aStepDrop) ∧
    ∃ (G₂ H_full : SimpleGraph (Fin N)) (hle : H ⊔ pairGraph N F ≤ H_full)
      (t2 : T2Chain (Fin N) (a :: A ++ b :: B) A B a b 0 H G₂)
      (t3 : AddedEdgeChain (Fin N) (a :: A ++ b :: B) A B a b 0 G₂ H_full),
      encodeT2 (stepsVal (t2Steps t2)) = s.arrs aT2Rec ∧
      stepsVal (chainSteps t3) = recordSteps (s.arrs aStepEdge) (s.arrs aStepBase)
        (s.arrs aStepDrop) ∧
      ∀ subCr : CrossingWalks (restrict (H ⊔ pairGraph N F) (sideSetOf H (a :: m ++ [b]) A))
          (a :: A ++ b :: m.reverse) ⊕
        CrossingWalks (restrict (H ⊔ pairGraph N F) (sideComplOf H (a :: m ++ [b]) A))
          (b :: B ++ a :: m),
        Sum.elim CrossingWalks.Valid CrossingWalks.Valid subCr →
        (extractCrossingTwoPart (List.finRange N) (a :: A ++ b :: B) P'.support hle t2 t3
          subCr).1.isSome = true := by
  obtain ⟨F₀, P₀, hF₀, hP₀, hfacts⟩ := hout
  have hFF : F₀ = F := hF₀.symm.trans hF
  subst hFF
  have hPP : P₀ = P' := Walk.ext_support
    (List.map_injective_iff.mpr Fin.val_injective (hP₀.symm.trans hP'))
  subst hPP
  obtain ⟨G₂, H_full, t2, t3, hle, -, h2, h3⟩ := hfacts.chains
  have hverts : ∀ v : Fin N, v ∈ List.finRange N := List.mem_finRange
  refine ⟨hfacts, G₂, H_full, hle, t2, t3, h2, h3, fun subCr hvalid => ?_⟩
  exact extractCrossingTwoPart_isSome hverts hsplit.cyc (List.rotate_zero _) hsplit.neA
    hsplit.neB le_sup_left hfacts.edges hfacts.tpath hm hfacts.induced hfacts.sep hfacts.sides
    hfacts.tight hle t2 t3 (exhaustive_of_statement hexh hverts t3) subCr hvalid

end

end GraphMinor.Compute.TwoPaths
