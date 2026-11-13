module

public import GraphMinor.Compute.Graph
public import GraphMinor.HP25.Prop53
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# The two-paths program: memory layout and the interface of the completion step

This file fixes how one instance of Algorithm 5.1 of S. Humeau and D. Pous, *On the Two Paths
Theorem and the Two Disjoint Paths Problem*, arXiv:2505.16431v2 (14 August 2025), Section 5.1,
page 18, sits in the memory of the Word RAM (`GraphMinor/Compute/Basic.lean`), and it states
`CompletionStatement`: what the program for line 9 of Algorithm 5.1 (the call of Algorithm 5.2,
"Computing $P$-completions", page 23) and for the extraction of a crossing in Section 5.3
(pages 22–23) must do.

An instance is a graph `H : SimpleGraph (Fin N)`, a cycle `C = a A b B` of `H`, and a `C`-path `P`
from `a` to `b` that separates `A` from `B`. It is stored as follows (`InstanceAt`):
* register `rN` holds `N` and register `rLenA` holds the length of `A`;
* arrays `aStart`, `aEnd`, `aEnt` hold adjacency lists of `H` (`IsAdjList`);
* array `aCyc` holds the list `a A b B`, and array `aPath` holds the vertex list of `P`.

The completion program reads an instance and either writes a crossing of `C` in `H` (flag `1`) or
writes a list `F` of new edges and a `C`-path `P'` of `H + F` from `a` to `b` (flag `0`) with the
properties that line 10 of Algorithm 5.1 needs: `F` is safe, every vertex of `P'` lies on both
`P'`-sides, and `P'` separates `A` from `B` in `H + F`. Its time is `O(|P'| (N + M + 1))` (flag `0`)
or `O(|P| (N + M + 1))` (flag `1`), where `M` is the number of edges of `H`: one search per edge
added, as in the proof of Proposition 5.9, page 24.

The extraction program is called after a flag-`0` completion when one of the two subinstances of
`H + F` along `P'` (Proposition 5.1, page 16) has a crossing. It writes a crossing of `C` in the
graph `H` itself, not in `H + F`: Section 5.3 builds a crossing of `C` in `H + F` only (see the
correction to Section 5.3 in `corrections/HP25.md`), and how to get one in `H` is still open. Its
time is
`O(|P'| (N + M + 1))`, one search per added edge. It may read the arrays `200` to `299` that the completion run left behind
(`isRecordArr`), so that the completion can pass it any data it needs.

Both programs use registers and arrays from `300` on as scratch space and leave everything below
`300` unchanged, except their outputs.
-/

@[expose] public section

namespace GraphMinor.Compute.TwoPaths

open SimpleGraph GraphMinor.HP25

/-! ### Registers and arrays of an instance -/

/-- Register holding the number `N` of vertices. -/
abbrev rN : Reg := 40
/-- Register holding the length of `A`, so that `b` sits at index `|A| + 1` of `aCyc`. -/
abbrev rLenA : Reg := 41
/-- Register holding the flag written by the completion program. -/
abbrev rFlag : Reg := 42
/-- Register holding the side (`1` or `2`) of the subinstance whose crossing is extracted. -/
abbrev rSide : Reg := 43

/-- Array of start offsets of the adjacency lists. -/
abbrev aStart : Arr := 40
/-- Array of end offsets of the adjacency lists. -/
abbrev aEnd : Arr := 41
/-- Array of the entries of the adjacency lists. -/
abbrev aEnt : Arr := 42
/-- Array holding the cycle `a A b B`. -/
abbrev aCyc : Arr := 43
/-- Array holding the vertex list of the path `P`. -/
abbrev aPath : Arr := 44
/-- Array holding the vertex list of the first path of an output crossing. -/
abbrev aQ : Arr := 45
/-- Array holding the vertex list of the second path of an output crossing. -/
abbrev aR : Arr := 46
/-- Array holding the new edges `F` as a flat list `u₀ v₀ u₁ v₁ …`. -/
abbrev aF : Arr := 47
/-- Array holding the vertex list of the new path `P'`. -/
abbrev aNewPath : Arr := 48
/-- Array holding the vertex list of the first path of an input crossing (of a subinstance). -/
abbrev aQin : Arr := 49
/-- Array holding the vertex list of the second path of an input crossing (of a subinstance). -/
abbrev aRin : Arr := 50

/-- The arrays `200` to `299`, which the completion program may fill for the extraction program. -/
def isRecordArr (a : Arr) : Prop := 200 ≤ a ∧ a < 300

/-! ### Edge lists and the two sides of a path -/

/-- The graph on `Fin N` whose edges are the pairs `l[2i] l[2i+1]` of the flat list `l`. -/
def pairGraph (N : ℕ) (l : List ℕ) : SimpleGraph (Fin N) where
  Adj u v := u ≠ v ∧ ∃ i : ℕ, (l[2 * i]? = some u.1 ∧ l[2 * i + 1]? = some v.1) ∨
    (l[2 * i]? = some v.1 ∧ l[2 * i + 1]? = some u.1)
  symm := ⟨fun _ _ ⟨h, i, hi⟩ => ⟨Ne.symm h, i, hi.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- `l` is a list of new edges for `H` on the vertices of `P`: it has even length, each pair
`l[2i] l[2i+1]` joins two distinct vertices of `P` that are not adjacent in `H`, and no edge is
listed twice. -/
def IsNewEdgeList {N : ℕ} (H : SimpleGraph (Fin N)) (Pv : List (Fin N)) (l : List ℕ) : Prop :=
  Even l.length ∧
  (∀ i, 2 * i + 1 < l.length → ∃ u v : Fin N, l[2 * i]? = some u.1 ∧ l[2 * i + 1]? = some v.1 ∧
    u ≠ v ∧ u ∈ Pv ∧ v ∈ Pv ∧ ¬ H.Adj u v) ∧
  (∀ i j, i < j → 2 * j + 1 < l.length →
    ¬ ((l[2 * i]? = l[2 * j]? ∧ l[2 * i + 1]? = l[2 * j + 1]?) ∨
      (l[2 * i]? = l[2 * j + 1]? ∧ l[2 * i + 1]? = l[2 * j]?)))

variable {V : Type*}

/-- The vertices that a vertex of `A` reaches in `H - P`, where `Pv` is the vertex list of `P`. -/
def reachOff (H : SimpleGraph V) (Pv A : List V) : Set V :=
  {v | ∃ u ∈ A, (restrict H {w | w ∉ Pv}).Reachable u v}

/-- The vertex set of the first subinstance of Proposition 5.1 (page 16): the vertices of `P`
together with the vertices that `A` reaches in `H - P`. -/
def sideOne (H : SimpleGraph V) (Pv A : List V) : Set V :=
  {v | v ∈ Pv} ∪ reachOff H Pv A

/-- The vertex set of the second subinstance of Proposition 5.1 (page 16): the vertices of `P`
together with the vertices that `A` does not reach in `H - P`. -/
def sideTwo (H : SimpleGraph V) (Pv A : List V) : Set V :=
  {v | v ∈ Pv} ∪ (reachOff H Pv A)ᶜ

/-- The two subinstances of line 10 of Algorithm 5.1, after a completion with path `P' = a m b`
(`Pv = a :: m ++ [b]`): side `1` is the graph induced by `sideOne` with the cycle `a A b m⁻¹`, side
`2` is the graph induced by `sideTwo` with the cycle `b B a m`. These are the cycles of
`isCrossed_iff_of_completion` (`GraphMinor/HP25/Method.lean`). -/
def subGraph (H : SimpleGraph V) (Pv A : List V) : ℕ → SimpleGraph V
  | 1 => restrict H (sideOne H Pv A)
  | _ => restrict H (sideTwo H Pv A)

/-- The cycle of subinstance `i` (see `subGraph`). -/
def subCycle (a b : V) (A B m : List V) : ℕ → List V
  | 1 => a :: A ++ b :: m.reverse
  | _ => b :: B ++ a :: m

/-! ### What an instance in memory is -/

/-- The instance `(H, a A b B, P)` is stored in `s` with adjacency lists `lists`. -/
structure InstanceAt {N : ℕ} (H : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) (a b : Fin N)
    (A B : List (Fin N)) (P : H.Walk a b) (s : State) : Prop where
  n : s.regs rN = N
  lenA : s.regs rLenA = A.length
  adj : IsAdjList H aStart aEnd aEnt lists s
  cyc : s.arrs aCyc = (a :: A ++ b :: B).map Fin.val
  path : s.arrs aPath = P.support.map Fin.val

/-- The hypotheses of line 9 of Algorithm 5.1: `a A b B` is a cycle of `H` with `A`, `B` not
empty (so `a` and `b` are not consecutive), and `P` is a `C`-path from `a` to `b` that separates
`A` from `B`. -/
structure IsSplitInput {N : ℕ} (H : SimpleGraph (Fin N)) (a b : Fin N) (A B : List (Fin N))
    (P : H.Walk a b) : Prop where
  cyc : IsCycleList H (a :: A ++ b :: B)
  neA : A ≠ []
  neB : B ≠ []
  path : IsTPath H (a :: A ++ b :: B) P
  sep : Separates H {v | v ∈ P.support} {v | v ∈ A} {v | v ∈ B}

/-- Arrays `aQ` and `aR` of `s` hold a crossing of `T` in `H`. -/
def CrossingAt {N : ℕ} (H : SimpleGraph (Fin N)) (T : List (Fin N)) (aQ' aR' : Arr) (s : State) :
    Prop :=
  ∃ (x y z t : Fin N) (Q : H.Walk x y) (R : H.Walk z t), IsCrossing H T Q R ∧
    s.arrs aQ' = Q.support.map Fin.val ∧ s.arrs aR' = R.support.map Fin.val

/-- The flag-`0` output of the completion program: arrays `aF` and `aNewPath` hold a list `F` of
new edges and the vertex list of a `C`-path `P'` of `H + F` from `a` to `b`. Both ends of every
edge of `F` lie on `P'`, not on `P`: the rerouting of the corrected Algorithm 5.2 (`reroute_all`,
`GraphMinor/HP25/Sec5Tighten.lean`) changes the path before any edge is added, so the final path can
leave `P`, and the added edges are edges of the final path (`completion_loop`). Further, `F` is
safe for `C`, every vertex of `P'` is on both `P'`-sides in `H + F`, `P'` separates `A` from `B` in
`H + F`, fewer edges were added than `P'` has vertices, and the run took at most
`c |P'| (N + M + 1)` steps. -/
def IsCompletionOutput {N : ℕ} (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (a b : Fin N)
    (A B : List (Fin N)) (c t : ℕ) (s : State) : Prop :=
  ∃ (F : List ℕ) (P' : (H ⊔ pairGraph N F).Walk a b),
    s.arrs aF = F ∧ s.arrs aNewPath = P'.support.map Fin.val ∧
    IsNewEdgeList H P'.support F ∧
    IsTPath (H ⊔ pairGraph N F) (a :: A ++ b :: B) P' ∧
    OnBothSides (H ⊔ pairGraph N F) (a :: A ++ b :: B) A B P' ∧
    Separates (H ⊔ pairGraph N F) {v | v ∈ P'.support} {v | v ∈ A} {v | v ∈ B} ∧
    IsSafe H (pairGraph N F) (a :: A ++ b :: B) ∧
    F.length / 2 < P'.support.length ∧
    t ≤ c * P'.support.length * (N + H.edgeFinset.card + 1)

/-- The interface of line 9 of Algorithm 5.1 (Algorithm 5.2, page 23) and of the extraction of
crossings of Section 5.3 (pages 22–23). There are programs `comp` and `ext` and constants `c`,
`c_w` such that, for every instance `(H, a A b B, P)` of `IsSplitInput` stored as in `InstanceAt`,
at every word size `w ≥ c_w (log₂((N + 1)(M + N + 1) + 2) + 1)`:
* `comp` stops, changes no register below `300` other than `rFlag` and no array below `200` other
  than `aQ`, `aR`, `aF`, `aNewPath`, leaves each array `200 … 299` of length at most
  `c (N + M + 1)`, and either sets `rFlag` to `1` and writes a crossing of `C` in `H` within
  `c |P| (N + M + 1)` steps, or sets `rFlag` to `0` and writes an output of `IsCompletionOutput`;
* after a flag-`0` run of `comp` that wrote `F` and `P' = a m b`, from any state that agrees with
  the final state of that run on the instance, on `aF`, `aNewPath` and on the arrays `200 … 299`,
  and that holds in `aQin`, `aRin` a crossing of the cycle of subinstance `i ∈ {1, 2}` in the graph
  of subinstance `i` of `H + F` along `P'` (register `rSide = i`), `ext` writes a crossing of `C` in
  `H` within `c |P'| (N + M + 1)` steps, changing no register below `300` and no array below `300`
  other than `aQ` and `aR`.

The bound of `ext` has the same form as that of `comp`: a crossing of `H + F` may have to be turned
into one of `H` by undoing the added edges one at a time, with one search of `O(N + M)` steps for
each, and fewer edges are added than `P'` has vertices. A run extracts once per level on the way
back up, at most once per split, and the paths `P'` of all splits of a run have at most `5N`
vertices in total (`GraphMinor/Compute/TwoPathsCount.lean`), so all extractions of a run take
`O(N (N + M))` steps. -/
def CompletionStatement : Prop :=
  ∃ (comp ext : Cmd) (c c_w : ℕ), 0 < c ∧ 0 < c_w ∧
    (∀ (N : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (lists : Fin N → List ℕ)
      (a b : Fin N) (A B : List (Fin N)) (P : H.Walk a b),
      IsSplitInput H a b A B P →
      ∀ (w : ℕ), wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w →
      ∀ (s : State), InstanceAt H lists a b A B P s → (s.arrs aEnt).length < 2 ^ w →
        ∃ (s' : State) (t : ℕ), Exec w comp s s' t ∧
          (∀ r < 300, r ≠ rFlag → s'.regs r = s.regs r) ∧
          (∀ x < 200, x ≠ aQ → x ≠ aR → x ≠ aF → x ≠ aNewPath → s'.arrs x = s.arrs x) ∧
          (∀ x, isRecordArr x → (s'.arrs x).length ≤ c * (N + H.edgeFinset.card + 1)) ∧
          ((s'.regs rFlag = 1 ∧ CrossingAt H (a :: A ++ b :: B) aQ aR s' ∧
              t ≤ c * P.support.length * (N + H.edgeFinset.card + 1)) ∨
            (s'.regs rFlag = 0 ∧ IsCompletionOutput H a b A B c t s'))) ∧
    (∀ (N : ℕ) (H : SimpleGraph (Fin N)) [DecidableRel H.Adj] (lists : Fin N → List ℕ)
      (a b : Fin N) (A B : List (Fin N)) (P : H.Walk a b),
      IsSplitInput H a b A B P →
      ∀ (w : ℕ), wordSize c_w ((N + 1) * (H.edgeFinset.card + N + 1)) ≤ w →
      ∀ (s₀ s₁ : State) (t₁ : ℕ), InstanceAt H lists a b A B P s₀ →
        (s₀.arrs aEnt).length < 2 ^ w → Exec w comp s₀ s₁ t₁ → s₁.regs rFlag = 0 →
      ∀ (F : List ℕ) (m : List (Fin N)) (P' : (H ⊔ pairGraph N F).Walk a b),
        s₁.arrs aF = F → s₁.arrs aNewPath = P'.support.map Fin.val →
        P'.support = a :: m ++ [b] →
      ∀ (i : ℕ), (i = 1 ∨ i = 2) →
      ∀ (s : State), InstanceAt H lists a b A B P s → (s.arrs aEnt).length < 2 ^ w →
        s.arrs aF = F → s.arrs aNewPath = P'.support.map Fin.val →
        (∀ x, isRecordArr x → s.arrs x = s₁.arrs x) → s.regs rSide = i →
        CrossingAt (subGraph (H ⊔ pairGraph N F) P'.support A i) (subCycle a b A B m i)
          aQin aRin s →
        ∃ (s' : State) (t : ℕ), Exec w ext s s' t ∧
          t ≤ c * P'.support.length * (N + H.edgeFinset.card + 1) ∧
          (∀ r < 300, s'.regs r = s.regs r) ∧
          (∀ x < 300, x ≠ aQ → x ≠ aR → s'.arrs x = s.arrs x) ∧
          CrossingAt H (a :: A ++ b :: B) aQ aR s')

end GraphMinor.Compute.TwoPaths
