module

public import GraphMinor.Compute.Cited
public import GraphMinor.Compute.CitedPlanarity
public import GraphMinor.Crossing.DefsFlow
public import GraphMinor.Crossing.DefsForest
public import GraphMinor.Crossing.DefsRestore
public import GraphMinor.Crossing.DefsHistory

/-!
# The Word RAM layout and the subprograms of the crossing extractor

This file fixes how the crossing extractor of `docs/crossing/crossing_extractor.tex` keeps its data
in the
memory of the Word RAM, and states what each of its subprograms must do, as propositions in the
form of `Alg92.F92ProgClaim`: the array indices are parameters, the program may change the arrays
it names and the arrays and registers at or above `a_base` and `r_base`, and it runs in the stated
time.

## The layout of an instance

An instance `(G, S, D)` lives on the vertices `Fin N`, where `N` is the number of vertices of the
input graph and never changes. It is kept in five arrays (`InstArrs`, `IsInstanceAt`):
* `alive`: `N` entries, `1` at the vertices of `S` and `0` at the deleted ones;
* `st`, `en`, `ent`: the adjacency lists of `G` (`IsAdjList`), with no unused entries, so that
  `ent` has `2 |E(G)|` entries; a deleted vertex has an empty list;
* `cyc`: the cycle `D`, as its list of vertices.

So `N` is the length of `alive`. A copy of an instance takes `O(N + |E(G)|)` steps (Section 10:
"copy the current instance"). A contraction or a replacement rebuilds the lists in `O(N + |E(G)|)`
steps. This is linear per trial or per bounded-flow query, as Section 12 asks of all the remaining
work (graph copies, contraction and simplification), since a trial makes at most `63` replacements
and initial cleaning at most `N`.

## The records

The accepted operations are kept in one array, the encodings of their records one after the other,
oldest first (`IsRecordsAt`). Each encoding ends with the length of the rest of it, so the lift can
read the records from the newest one back. An encoding keeps what the lift needs:
* a replacement: `0`, the boundary `S`, the recorded component `A₀`, and the edges of the old
  graph inside `A₀ ∪ S` (for the search "for a path from $p$ to $q$ in $K[A\cup\{p,q\}]$" of Lemma
  1, and to see which edges inside `S` are new);
* a contraction: `1`, `u`, `v`, whether `u` and `v` are on the old cycle, and the old neighbours of
  `v` (the lifts of Section 11 test only adjacency to `v` in the recorded graph);
* a deletion: `2`.
Section 12: "Storing complete snapshots is allowed, since the stack of accepted operations contains
only $O(n_0)$ operations."

## The planarity test

`Classify` calls the program of `PlanarityTestStatement`, which reads its graph from arrays `30`,
`31`, `32` and may change every array from `33` and every register from `30`. A caller runs it
shifted (`Cmd.shiftMem R_off A_off`, `Algorithm101Defs.lean`), so that it reads and writes only
arrays and registers above the caller's data. So the claims below that use it take the program as
a parameter (`IsPlanarityProg`).

## The subprograms

* `BoundedFlowProgClaim` (Sections 2.1, 2.2), `CopyInstanceProgClaim` (Section 10),
  `ReplaceProgClaim` (Section 3), `ContractProgClaim` (Section 9);
* `InitialCleaningProgClaim` (Section 4), `BridgeCrossProgClaim` (Section 5),
  `ClassifyProgClaim` (Section 6), `SparsifyProgClaim` (Section 7), `RestoreProgClaim`
  (Section 9.2), `TrialProgClaim` and `LoopProgClaim` (Section 10), `LiftProgClaim`
  (Section 11);
* the top level, `CrossingExtractorStatement`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-! ### Sizes and frames -/

/-- The size `N + |E(G)| + 1` of an instance on `Fin N`. -/
noncomputable def instSize (N : ℕ) (G : SimpleGraph (Fin N)) : ℕ :=
  N + G.edgeSet.ncard + 1

/-- `s'` agrees with `s` on every register below `r_base` outside `R`, and on every array below
`a_base` outside `A`. -/
def KeepsBelow (r_base a_base : ℕ) (R A : List ℕ) (s s' : State) : Prop :=
  (∀ r < r_base, r ∉ R → s'.regs r = s.regs r) ∧ (∀ a < a_base, a ∉ A → s'.arrs a = s.arrs a)

/-- The array indices `l` are distinct and below `a_base`. -/
def ArrsOk (l : List ℕ) (a_base : ℕ) : Prop :=
  l.Nodup ∧ ∀ x ∈ l, x < a_base

/-! ### The layout of an instance -/

/-- The five arrays of an instance. -/
structure InstArrs where
  /-- `1` at the vertices of the instance, `0` at the deleted vertices. -/
  alive : ℕ
  /-- The starts of the adjacency lists. -/
  st : ℕ
  /-- The ends of the adjacency lists. -/
  en : ℕ
  /-- The entries of the adjacency lists. -/
  ent : ℕ
  /-- The cycle. -/
  cyc : ℕ

/-- The list of the five arrays. -/
def InstArrs.list (a : InstArrs) : List ℕ :=
  [a.alive, a.st, a.en, a.ent, a.cyc]

/-- **An instance in memory**: the instance `(G, S, D)` on `Fin N` is stored in the arrays `a`.
-/
def IsInstanceAt {N : ℕ} (a : InstArrs) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
    (D : List (Fin N)) (s : State) : Prop :=
  HP25.IsSupportedOn G (S : Set (Fin N)) ∧
    s.arrs a.alive = List.ofFn (fun v : Fin N => if v ∈ S then 1 else 0) ∧
    (∃ lists, IsAdjList G a.st a.en a.ent lists s) ∧
    (s.arrs a.ent).length = 2 * G.edgeSet.ncard ∧
    s.arrs a.cyc = D.map Fin.val

/-- A vertex list in an array: the array holds the values of a list without repeats whose
members are those of the set `X`. -/
def IsSetListAt {N : ℕ} (x : ℕ) (X : Set (Fin N)) (s : State) : Prop :=
  ∃ l : List (Fin N), l.Nodup ∧ (∀ y, y ∈ l ↔ y ∈ X) ∧ s.arrs x = l.map Fin.val

/-! ### The records -/

/-- The encoding of an ordered pair of vertices. -/
def encPair {N : ℕ} (e : Fin N × Fin N) : List ℕ :=
  [e.1.val, e.2.val]

/-- A body of a record encoding followed by its length. -/
def withLength (body : List ℕ) : List ℕ :=
  body ++ [body.length]

/-- **The encoding of a record.** `l` encodes `rec`:
* a replacement: `0`, the boundary, the recorded component and the ordered pairs of adjacent
  vertices of the old graph inside their union, each list after its length;
* a contraction: `1`, `u`, `v`, whether `u` and `v` are on the old cycle, and the old neighbours
  of `v` after their number;
* a deletion: `2`. -/
def IsRecordEnc {N : ℕ} : CrossRecord (Fin N) → List ℕ → Prop
  | CrossRecord.repl r, l => ∃ (B R : List (Fin N)) (E : List (Fin N × Fin N)),
      B.Nodup ∧ (∀ y, y ∈ B ↔ y ∈ r.boundary) ∧ R.Nodup ∧ (∀ y, y ∈ R ↔ y ∈ r.rep) ∧
      E.Nodup ∧ (∀ a b, (a, b) ∈ E ↔ (r.graph.Adj a b ∧ (a ∈ r.rep ∨ a ∈ r.boundary) ∧
        (b ∈ r.rep ∨ b ∈ r.boundary))) ∧
      l = withLength (0 :: B.length :: B.map Fin.val ++ R.length :: R.map Fin.val ++
        E.length :: E.flatMap encPair)
  | CrossRecord.contr r, l => ∃ Nv : List (Fin N), Nv.Nodup ∧ (∀ y, y ∈ Nv ↔ r.graph.Adj r.v y) ∧
      l = withLength ([1, r.u.val, r.v.val, if r.u ∈ r.cycle then 1 else 0,
        if r.v ∈ r.cycle then 1 else 0, Nv.length] ++ Nv.map Fin.val)
  | CrossRecord.del _ _, l => l = withLength [2]

/-- **The records in memory**: the array `x` holds the encodings of `recs`, oldest first. -/
def IsRecordsAt {N : ℕ} (x : ℕ) (recs : List (CrossRecord (Fin N))) (s : State) : Prop :=
  ∃ ls : List (List ℕ), List.Forall₂ IsRecordEnc recs ls ∧ s.arrs x = ls.flatten

/-- The history of a list of records between two instances on `Fin N`. -/
def IsHistoryFin {N : ℕ} (G : SimpleGraph (Fin N)) (S : Finset (Fin N)) (D : List (Fin N))
    (recs : List (CrossRecord (Fin N))) (G' : SimpleGraph (Fin N)) (S' : Finset (Fin N))
    (D' : List (Fin N)) : Prop :=
  IsHistory (G, (S : Set (Fin N)), D) recs (G', (S' : Set (Fin N)), D')

/-- Every cycle-edge contraction of the records was made on a cycle of at least five vertices
(Section 10, step 3: "contractions of cycle edges are skipped when $|D|=4$"). -/
def ContractionsLong {N : ℕ} (recs : List (CrossRecord (Fin N))) : Prop :=
  ∀ r, CrossRecord.contr r ∈ recs → r.u ∈ r.cycle → 4 < r.cycle.length

/-- A crossing pair in two arrays: the arrays `xQ` and `xR` hold the vertex lists of a crossing
pair of `D` in `G`. -/
def IsCrossingPairAt {N : ℕ} (G : SimpleGraph (Fin N)) (D : List (Fin N)) (xQ xR : ℕ)
    (s : State) : Prop :=
  ∃ L₁ L₂ : List (Fin N), IsCrossingPair G D L₁ L₂ ∧ s.arrs xQ = L₁.map Fin.val ∧
    s.arrs xR = L₂.map Fin.val

/-! ### The planarity test -/

/-- The body of `PlanarityTestStatement`: `prog` decides planarity in `C (|E(G)| + N + 1)`
steps, with the fixed calling convention of that statement. -/
def IsPlanarityProg (prog : Cmd) (C c_w : ℕ) : Prop :=
  ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj] (lists : Fin N → List ℕ),
    ∀ (w : ℕ), wordSize c_w (G.edgeFinset.card + N + 1) ≤ w →
    ∀ (s : State),
      IsAdjList G 30 31 32 lists s →
      (s.arrs 32).length < 2 ^ w →
      s.regs 30 = N →
      ∃ (s' : State) (t : ℕ),
        Exec w prog s s' t ∧
        t ≤ C * (G.edgeFinset.card + N + 1) ∧
        (∀ r < 30, s'.regs r = s.regs r) ∧
        (∀ a < 33, s'.arrs a = s.arrs a) ∧
        ((s'.regs 35 = 1 ∧ Nonempty (HP25.PlaneEmbedding G Set.univ)) ∨
          (s'.regs 35 = 0 ∧ IsEmpty (HP25.PlaneEmbedding G Set.univ)))

theorem planarityTestStatement_iff :
    PlanarityTestStatement ↔ ∃ (prog : Cmd) (C c_w : ℕ), 0 < C ∧ 0 < c_w ∧
      IsPlanarityProg prog C c_w :=
  Iff.rfl

/-! ### The vertex set of a flow query -/

/-- The vertex set of a flow query in `J = G + x` (Section 2.1), or in `B = J - w` (Section 9.2)
when `ow < N` names the excluded vertex `w`. -/
def flowVerts {N : ℕ} (S : Finset (Fin N)) (ow : ℕ) : Set (Option (Fin N)) :=
  if h : ow < N then apexVerts (S : Set (Fin N)) \ {some ⟨ow, h⟩}
  else apexVerts (S : Set (Fin N))

/-! ### The subprograms -/

/-- **The bounded flow with its largest-source-side cut** (Sections 2.1 and 2.2). Input: an
instance `(G, S, D)` at `a`; in registers `r_base`, `r_base + 1`, `r_base + 2`: the source `z`
(a vertex of `S` off `D`), the number `k ≤ 4` of asked paths, and `ow`, the excluded vertex `w`
when `ow < N` ("Form $B=J-w$.") and no vertex otherwise.
Output in register `r_base`: `1` when `k` internally disjoint `z`-`x` paths exist (no `k - 1`
vertices separate `z` from `x`), and `0` otherwise, with the minimum separator with largest
source side in `a_sep` and its source side `U` in `a_src` (as vertices of `G`). Time
`C (N + |E(G)| + 1)`: "each query uses at most $k$ residual searches, each on a graph of size
$O(|V|+|E|)$". -/
def BoundedFlowProgClaim : Prop :=
  ∀ (a : InstArrs) (a_sep a_src a_base r_base : ℕ), ArrsOk (a.list ++ [a_sep, a_src]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      z ∈ S → z ∉ D → 1 ≤ k → k ≤ 4 → ow ≠ z.val →
      s.regs r_base = z.val → s.regs (r_base + 1) = k → s.regs (r_base + 2) = ow →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] [a_sep, a_src] s s' ∧
        ((s'.regs r_base = 1 ∧
            IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1)) ∨
          (s'.regs r_base = 0 ∧ ∃ X : Finset (Option (Fin N)),
            IsMaxSourceSeparator (apex G D) (flowVerts S ow) (some z) none X ∧ X.card < k ∧
            IsSetListAt a_sep {y | some y ∈ X} s' ∧
            IsSetListAt a_src {y | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s'))

/-- **The copy of an instance** (Section 10: "copy the current instance"): from the arrays `a` to
the arrays `b`, in `C (N + |E(G)| + 1)` steps. -/
def CopyInstanceProgClaim : Prop :=
  ∀ (a b : InstArrs) (a_base r_base : ℕ), ArrsOk (a.list ++ b.list) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧ KeepsBelow r_base a_base [] b.list s s' ∧
        IsInstanceAt b G S D s'

/-- **The replacement** (Section 3): "The *replacement* deletes $A$ and adds every missing edge of
the clique on $S$." Input: an instance `(G, S, D)` at `a`, the deleted set in `a_del`, the boundary
in `a_bd`, the recorded component in `a_rep`, and the records `recs` in `a_rec`. Output: the new
instance at `a`, and the record appended to `a_rec`. Time `C (N + |E(G)| + 1)`. -/
def ReplaceProgClaim : Prop :=
  ∀ (a : InstArrs) (a_del a_bd a_rep a_rec a_base r_base : ℕ),
    ArrsOk (a.list ++ [a_del, a_bd, a_rep, a_rec]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (r : ReplRecord (Fin N)) (recs : List (CrossRecord (Fin N)))
      (S' : Finset (Fin N)) (s : State),
      wordSize c (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → r.graph = G → r.verts = S → r.IsValid D →
      (S' : Set (Fin N)) = r.newVerts →
      IsSetListAt a_del r.deleted s → IsSetListAt a_bd (r.boundary : Set (Fin N)) s → IsSetListAt a_rep r.rep s →
      IsRecordsAt a_rec recs s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a r.newGraph S' D s' ∧ IsRecordsAt a_rec (recs ++ [CrossRecord.repl r]) s'

/-- **The contraction** (Section 9): "Contract $uv$ to a new vertex $w$, suppressing loops and
duplicate edges." Input: an instance `(G, S, D)` at `a`, the trial edge `uv` in registers `r_base`
and `r_base + 1`, and the records `recs` in `a_rec`. Output: the contracted instance at `a` (the
merged vertex keeps the name `v`), and the record appended to `a_rec`. Time `C (N + |E(G)| + 1)`. -/
def ContractProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_rec]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (G : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (u v : Fin N) (recs : List (CrossRecord (Fin N)))
      (s : State),
      wordSize c (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → IsTrialEdge G D u v →
      s.regs r_base = u.val → s.regs (r_base + 1) = v.val → IsRecordsAt a_rec recs s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a (contractGraph G u v) (S.erase u) (contractCycle D u) s' ∧
        IsRecordsAt a_rec (recs ++ [CrossRecord.contr
          { graph := G, verts := (S : Set (Fin N)), cycle := D, u := u, v := v }]) s'

/-- **Initial cleaning** (Section 4). Input: an instance `(G, S, D)` at `a` with `D` a cycle, and
the records `recs₀` in `a_rec`. Output: a clean instance `(G', S', D)` at `a`, reached from
`(G, S, D)` by the records appended to `a_rec` ("We record the replacements for the lifting at the
end."), with `|E(G')| ≤ |E(G)| + 3N` ("Every replacement deletes at least one vertex and adds at
most three edges."). Time `C (N + 1) (N + |E(G)| + 1)`: after at most `n` bounded-flow queries the
remaining instance is clean. -/
def InitialCleaningProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_rec]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (recs₀ : List (CrossRecord (Fin N))) (s : State),
      wordSize c ((N + 1) * instSize N G + (s.arrs a_rec).length) ≤ w →
      IsInstanceAt a G S D s → HP25.IsCycleList G D → IsRecordsAt a_rec recs₀ s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (N + 1) * instSize N G ∧
        KeepsBelow r_base a_base [] (a.list ++ [a_rec]) s s' ∧
        ∃ (G' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N))),
          IsInstanceAt a G' S' D s' ∧ IsClean G' (S' : Set (Fin N)) D ∧
          IsHistoryFin G S D recs G' S' D ∧ ContractionsLong recs ∧
          IsRecordsAt a_rec (recs₀ ++ recs) s' ∧ G'.edgeSet.ncard ≤ G.edgeSet.ncard + 3 * N ∧
          (s'.arrs a_rec).length ≤ (s.arrs a_rec).length + C * instSize N G

/-- **`BridgeCross`** (Section 5): "Return a crossing whose two paths use distinct $D$-bridges, or
correctly report that no such crossing exists." Input: an instance `(G, S, D)` at `a` with `D` a
cycle. Output in register `r_base`: `1` with a crossing pair in `a_Q`, `a_R`, or `0` when no
crossing pair uses distinct bridges. Time `C (N + |E(G)| + 1)`: "It takes time $O(n+m)$ and, when it
succeeds, two path searches." -/
def BridgeCrossProgClaim : Prop :=
  ∀ (a : InstArrs) (a_Q a_R a_base r_base : ℕ), ArrsOk (a.list ++ [a_Q, a_R]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] [a_Q, a_R] s s' ∧
        ((s'.regs r_base = 1 ∧ IsCrossingPairAt G D a_Q a_R s') ∨
          (s'.regs r_base = 0 ∧
            ∀ L₁ L₂, IsCrossingPair G D L₁ L₂ → ¬ InDistinctBridges G D L₁ L₂))

/-- **`Classify`** (Section 6), with the planarity program `prog`: if `BridgeCross(K, D)` returns
a crossing, return `WITNESS` and that crossing; if `Planar(K)`, return `NO`; otherwise return `YES`.
Output in
register `r_base`: `2` (WITNESS) with a crossing pair in `a_Q`, `a_R`; `0` (NO) when `G` is planar
and no crossing pair uses distinct bridges; `1` (YES) when `G` is not planar and no crossing pair
uses distinct bridges. Time `C (N + |E(G)| + 1)`: "Thus classification takes linear time." -/
def ClassifyProgClaim : Prop :=
  ∀ (prog : Cmd) (Cp cp_w : ℕ), IsPlanarityProg prog Cp cp_w →
  ∀ (a : InstArrs) (a_Q a_R a_base r_base : ℕ), ArrsOk (a.list ++ [a_Q, a_R]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (s : State),
      wordSize c (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] [a_Q, a_R] s s' ∧
        ((s'.regs r_base = 2 ∧ IsCrossingPairAt G D a_Q a_R s') ∨
          (s'.regs r_base = 0 ∧ Nonempty (HP25.PlaneEmbedding G (S : Set (Fin N))) ∧
            ∀ L₁ L₂, IsCrossingPair G D L₁ L₂ → ¬ InDistinctBridges G D L₁ L₂) ∨
          (s'.regs r_base = 1 ∧ IsEmpty (HP25.PlaneEmbedding G (S : Set (Fin N))) ∧
            ∀ L₁ L₂, IsCrossingPair G D L₁ L₂ → ¬ InDistinctBridges G D L₁ L₂))

/-- **Sparsification** (Section 7.2): "If $M\le16N$, we do nothing." Otherwise the instance becomes
the retained graph of four scan-first forests of `J = G + x` and a set of `3N - 5` edges, and a
deletion record is appended. Here `N` of the note is `|S|`. Time `C (N + |E(G)| + 1)`: "The four
passes take time $O(n+m)$." -/
def SparsifyProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_rec]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (recs : List (CrossRecord (Fin N))) (s : State),
      wordSize c (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → IsRecordsAt a_rec recs s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * instSize N G ∧
        KeepsBelow r_base a_base [] (a.list ++ [a_rec]) s s' ∧
        ((G.edgeSet.ncard ≤ 16 * S.card ∧ IsInstanceAt a G S D s' ∧ IsRecordsAt a_rec recs s') ∨
          (16 * S.card < G.edgeSet.ncard ∧
            ∃ (Fs : List (SimpleGraph (Option (Fin N)))) (E₀ : Set (Sym2 (Fin N))),
              IsSparsifyData G (S : Set (Fin N)) D Fs E₀ ∧
              IsInstanceAt a (sparsifyGraph G D Fs E₀) S D s' ∧
              IsRecordsAt a_rec (recs ++ [CrossRecord.del (sparsifyGraph G D Fs E₀) S]) s'))

/-- **Restoration** (Section 9.2): "We process the fixed list $M$, once for each marker." Input: the
contracted instance `(H, S, D)` at `a`, the merged vertex `w` in register `r_base`, the list `M` of
markers in `a_mk`, and the records `recs` in `a_rec`. Output: the instance at the end of a
restoration run, with the records of its replacements appended. Time `C (|M| + 1) (N + |E(H)| + 1)`:
by Lemma 7, restoration "uses at most $|M|$ flow queries for three paths." -/
def RestoreProgClaim : Prop :=
  ∀ (a : InstArrs) (a_mk a_rec a_base r_base : ℕ), ArrsOk (a.list ++ [a_mk, a_rec]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (H : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (v : Fin N) (M : List (Fin N))
      (recs : List (CrossRecord (Fin N))) (s : State),
      wordSize c ((M.length + 1) * instSize N H + (s.arrs a_rec).length) ≤ w →
      IsInstanceAt a H S D s → HP25.IsCycleList H D → v ∈ S →
      RootedConn (apex H D) (apexVerts (S : Set (Fin N))) none 3 →
      RootedConn (apex H D) (restoreVerts (S : Set (Fin N)) v) none 2 →
      s.regs r_base = v.val → s.arrs a_mk = M.map Fin.val → IsRecordsAt a_rec recs s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (M.length + 1) * instSize N H ∧
        KeepsBelow r_base a_base [] (a.list ++ [a_rec]) s s' ∧
        ∃ (H' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (rs : List (ReplRecord (Fin N))),
          IsRestoreRun D v M H (S : Set (Fin N)) H' (S' : Set (Fin N)) rs ∧
          IsInstanceAt a H' S' D s' ∧ IsRecordsAt a_rec (recs ++ rs.map CrossRecord.repl) s' ∧
          (s'.arrs a_rec).length ≤ (s.arrs a_rec).length + C * (M.length + 1) * instSize N H

/-- **One trial** (Section 10, step 4): "copy the current instance; contract $uv$; restore
cleanliness as in Section 9, using the markers $N_K(u)\setminus\{v\}$; call `Classify` on the
restored instance." Input: a clean instance `(K, S, D)` at `a`, the trial edge `uv` in registers
`r_base` and `r_base + 1`. Output: the restored trial instance at `b`, reached from `(K, S, D)` by
the records in `a_trec` (the contraction and the replacements), and the answer of `Classify` on it
in register `r_base`, as in `ClassifyProgClaim`. The instance at `a` is kept. Time
`C (deg u + 1) (N + |E(K)| + 1)`. -/
def TrialProgClaim : Prop :=
  ∀ (prog : Cmd) (Cp cp_w : ℕ), IsPlanarityProg prog Cp cp_w →
  ∀ (a b : InstArrs) (a_trec a_Q a_R a_base r_base : ℕ),
    ArrsOk (a.list ++ b.list ++ [a_trec, a_Q, a_R]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (K : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (u v : Fin N) (s : State),
      wordSize c ((N + 1) * instSize N K) ≤ w → IsInstanceAt a K S D s →
      HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D → IsTrialEdge K D u v →
      (u ∈ D → 4 < D.length) → s.regs r_base = u.val → s.regs (r_base + 1) = v.val →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * ((K.neighborSet u).ncard + 1) * instSize N K ∧
        KeepsBelow r_base a_base [] (b.list ++ [a_trec, a_Q, a_R]) s s' ∧
        ∃ (H : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N))),
          IsInstanceAt b H S' (contractCycle D u) s' ∧
          IsHistoryFin K S D recs H S' (contractCycle D u) ∧ ContractionsLong recs ∧
          IsRecordsAt a_trec recs s' ∧ IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
          H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard ∧
          ((s'.regs r_base = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s') ∨
            (s'.regs r_base = 0 ∧ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂) ∨
            (s'.regs r_base = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂))

/-- **The loop** (Section 10): "We repeat the following iteration while in the last state." Input:
an instance `(K, S, D)` at `a` that is "clean, nonplanar and crossed", and the records `recs₀` in
`a_rec`. Output: an instance `(K', S', D')` reached by the records appended to `a_rec` (the
accepted iterations: sparsification, contraction, restoration), and a crossing pair of `D'` in
`K'` in `a_Q`, `a_R` (the `WITNESS` of the last trial, not yet lifted). Time
`C (N + 1) (N + |E(K)| + 1)`: "Accepted contraction iterations: At most $n_0$"; "Trials per
iteration: At most $5\cdot64=320$". -/
def LoopProgClaim : Prop :=
  ∀ (prog : Cmd) (Cp cp_w : ℕ), IsPlanarityProg prog Cp cp_w →
  ∀ (a : InstArrs) (a_rec a_Q a_R a_base r_base : ℕ),
    ArrsOk (a.list ++ [a_rec, a_Q, a_R]) a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)] (K : SimpleGraph (Fin N))
      (S : Finset (Fin N)) (D : List (Fin N)) (recs₀ : List (CrossRecord (Fin N)))
      (s : State),
      wordSize c ((N + 1) * instSize N K + (s.arrs a_rec).length) ≤ w →
      IsInstanceAt a K S D s → HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D →
      IsEmpty (HP25.PlaneEmbedding K (S : Set (Fin N))) → HP25.IsCrossed K D →
      IsRecordsAt a_rec recs₀ s →
      ∃ s' t, Exec w P s s' t ∧ t ≤ C * (N + 1) * instSize N K ∧
        KeepsBelow r_base a_base [] (a.list ++ [a_rec, a_Q, a_R]) s s' ∧
        ∃ (K' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (D' : List (Fin N))
          (recs : List (CrossRecord (Fin N))),
          IsHistoryFin K S D recs K' S' D' ∧ ContractionsLong recs ∧
          IsRecordsAt a_rec (recs₀ ++ recs) s' ∧ IsCrossingPairAt K' D' a_Q a_R s' ∧
          (s'.arrs a_rec).length ≤ (s.arrs a_rec).length + C * (N + 1) * instSize N K

/-- **The lifts** (Section 11 and Lemma 1): "Reversing all accepted operations gives two disjoint
$C$-paths in the original graph, with alternating ends." Input: the records `recs` in `a_rec`, and a
crossing pair `(L₁, L₂)` in `a_Q`, `a_R`. Output: a lift of the pair through `recs` in `a_Q`, `a_R`.
Time `C (|a_rec| + (|recs| + 1) (N + 1))`: at most `n₀` searches reverse separator replacements
(Section 12), each in a recorded component, and every contraction lifts without a search. -/
def LiftProgClaim : Prop :=
  ∀ (a_rec a_Q a_R a_base r_base : ℕ), ArrsOk [a_rec, a_Q, a_R] a_base →
    ∃ (P : Cmd) (C c : ℕ), ∀ (w N : ℕ) [DecidableEq (Fin N)]
      (recs : List (CrossRecord (Fin N))) (L₁ L₂ : List (Fin N)) (s : State),
      wordSize c ((s.arrs a_rec).length + (recs.length + 1) * (N + 1)) ≤ w →
      IsRecordsAt a_rec recs s → s.arrs a_Q = L₁.map Fin.val → s.arrs a_R = L₂.map Fin.val →
      L₁.length ≤ N → L₂.length ≤ N → (∃ P, IsLift recs (L₁, L₂) P) →
      ∃ s' t, Exec w P s s' t ∧
        t ≤ C * ((s.arrs a_rec).length + (recs.length + 1) * (N + 1)) ∧
        KeepsBelow r_base a_base [] [a_Q, a_R] s s' ∧
        ∃ P', IsLift recs (L₁, L₂) P' ∧ s'.arrs a_Q = P'.1.map Fin.val ∧
          s'.arrs a_R = P'.2.map Fin.val

/-! ### The top level -/

/-- **The crossing extractor** (Sections 4 to 12 of `docs/crossing/crossing_extractor.tex`): it
returns a crossing in the original graph if there is one, in time `O(nm)` (the theorem of the
introduction). As Section 13 says, "It assumes only that $G$ is finite and simple and that $C$ is a
cycle of $G$."

Input: the adjacency lists `IsAdjList G a_st a_en a_ent lists s` of a simple graph
`G : SimpleGraph (Fin N)`, in the form of `Shiloach80Statement`, with `N` in register `r_N`, and a
cycle `D` of `G` in the array `a_cyc`. Output: register `r_out` is `1` and the arrays `a_Q`, `a_R`
hold the vertex lists of a crossing `Q`, `R` of `D` (`HP25.IsCrossing`), or `r_out` is `0` and `D`
is not crossed. Time `C (N + 1) (|E(G)| + N + 1)`. The program may change `r_out`, `a_Q`, `a_R`,
and the registers and arrays at or above `r_base` and `a_base`. -/
def CrossingExtractorStatement : Prop :=
  ∀ (a_st a_en a_ent a_cyc a_Q a_R a_base r_N r_out r_base : ℕ),
    ArrsOk [a_st, a_en, a_ent, a_cyc, a_Q, a_R] a_base → r_N < r_base → r_out < r_base →
    r_N ≠ r_out →
    ∃ (P : Cmd) (C c_w : ℕ), 0 < C ∧ 0 < c_w ∧
      ∀ (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) (D : List (Fin N)) (w : ℕ)
        (s : State),
        wordSize c_w ((N + 1) * (G.edgeSet.ncard + N + 1)) ≤ w →
        IsAdjList G a_st a_en a_ent lists s → (s.arrs a_ent).length < 2 ^ w →
        s.regs r_N = N → s.arrs a_cyc = D.map Fin.val → HP25.IsCycleList G D →
        ∃ (s' : State) (t : ℕ), Exec w P s s' t ∧
          t ≤ C * (N + 1) * (G.edgeSet.ncard + N + 1) ∧
          KeepsBelow r_base a_base [r_out] [a_Q, a_R] s s' ∧
          ((s'.regs r_out = 1 ∧ ∃ (a b c d : Fin N) (Q : G.Walk a b) (R : G.Walk c d),
              HP25.IsCrossing G D Q R ∧ s'.arrs a_Q = Q.support.map Fin.val ∧
              s'.arrs a_R = R.support.map Fin.val) ∨
            (s'.regs r_out = 0 ∧ ¬ HP25.IsCrossed G D))

end GraphMinor.Compute.Crossing
