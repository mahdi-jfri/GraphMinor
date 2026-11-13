module

public import GraphMinor.Crossing.DefsFlow
public import GraphMinor.Crossing.DefsForest
public import GraphMinor.Crossing.DefsRestore

/-!
# The claims of the crossing extractor, as statements

This file states the claims of Sections 2, 3, 4, 7, 8, 9, 10 and 11 of
`docs/crossing/crossing_extractor.tex` (the crossing extractor) as propositions, each with the
passage of the note it formalizes. They are proved in other files. Sections 5 and 6, Fact T, Euler's
bound and Lemma 4 are stated with their proofs in `Crossing/Bridge*.lean` and
`Crossing/Planar*.lean`.

A graph `K` is a `SimpleGraph V` supported on a finite set `S`, and the cycle is a list `D` with
`HP25.IsCycleList K D`. The apex graph `J = K + x` is `apex K D` on `Option V`, with `x = none`.
"Planar" means `Nonempty (HP25.PlaneEmbedding K S)`.

* Section 2: `CleanIffFourFanStatement`.
* Section 2.1: `Sec21PathsStatement`, `Sec21AugmentStatement`, `Sec21CutStatement`.
* Section 2.2: `Sec22Statement`.
* Section 3: `Lemma1ForwardStatement`, `Lemma1ReverseStatement`, `Lemma2Statement`,
  `Lemma2ApexStatement`.
* Section 4: `Sec4DiscardStatement`, `Sec4ComponentStatement`, `Sec4CleanStatement`,
  `Sec4EdgeCountStatement`.
* Section 7: `Lemma5Statement`, `Sec71CountStatement`, `Sec72Statement`, `Sec72CountStatement`.
* Section 8: `Lemma6Statement`.
* Section 9: `Sec91Statement`, `Sec92ValueStatement`, `Sec93Statement`,
  `Sec94BoundaryGoodStatement`, `Sec94InvariantStatement`, `Lemma7Statement`.
* Section 10: `Sec101FiveStatement`, `Sec101Statement`, `Sec102DegreeStatement`,
  `Sec102Statement`.
* Section 11: `Lift11OffOffStatement`, `Lift11OneOnStatement`, `Lift11BothOnStatement`.
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

universe u

/-! ### Section 2 -/

/-- **Clean instances and four-fans** (Section 2): "Because every vertex of $D$ is adjacent to $x$,
Menger's theorem gives" that $(K,D)$ is clean if and only if every vertex $v\notin V(D)$ has a
four-fan to $D$. -/
def CleanIffFourFanStatement : Prop :=
  ∀ {V : Type u} (K : SimpleGraph V) (S : Set V) (D : List V), S.Finite →
    HP25.IsSupportedOn K S → HP25.IsCycleList K D →
    (IsClean K S D ↔ ∀ v ∈ S, v ∉ D → HasFourFan K D v)

/-! ### Section 2.1: the bounded flow -/

/-- **A flow gives disjoint paths** (Section 2.1): "Every flow query below has a source $z$ and the
sink $x$, where $z$ is not adjacent to $x$, and asks for $k\le4$ internally vertex-disjoint paths
from $z$ to $x$." A flow of value `ℓ` from `z_out` to `x_in` in the split network gives `ℓ`
internally disjoint `z`-`x` paths. -/
def Sec21PathsStatement : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (J : SimpleGraph W) (T : Set W) (z x : W) (k ℓ : ℕ)
    (f : W × Bool → W × Bool → ℕ),
    z ∈ T → x ∈ T → z ≠ x → ¬ J.Adj z x →
    IsFlow (splitCap J T z x k) (z, true) (x, false) f → flowValue (z, true) f = ℓ →
    ∃ P : Fin ℓ → J.Walk z x, IsDisjointPathFamily J T z x P

/-- **Augmentation** (Section 2.1): "Starting with the zero flow, we search the residual graph for a
path from the source to the sink and augment one unit along it. We stop after $k$ augmentations or
after an unsuccessful search." A residual path from the source to the sink gives a flow of value one
more. -/
def Sec21AugmentStatement : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (J : SimpleGraph W) (T : Set W) (z x : W) (k : ℕ)
    (f : W × Bool → W × Bool → ℕ) (ℓ : ℤ),
    IsFlow (splitCap J T z x k) (z, true) (x, false) f → flowValue (z, true) f = ℓ →
    ResReach (splitCap J T z x k) f (z, true) (x, false) →
    ∃ f', IsFlow (splitCap J T z x k) (z, true) (x, false) f' ∧ flowValue (z, true) f' = ℓ + 1

/-- **The cut of a failed computation** (Section 2.1): if the computation stops below $k$, its
minimum cut consists of arcs $v_{\mathrm{in}}\to v_{\mathrm{out}}$ of capacity $1$, and "these arcs
give a vertex separator of that size between $z$ and $x$." After an unsuccessful search, the
extracted set is a minimum `z`-`x` separator of size the value of the flow. -/
def Sec21CutStatement : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (J : SimpleGraph W) (T : Set W) (z x : W) (k ℓ : ℕ)
    (f : W × Bool → W × Bool → ℕ),
    z ∈ T → x ∈ T → z ≠ x → ¬ J.Adj z x → ℓ ≤ k →
    IsFlow (splitCap J T z x k) (z, true) (x, false) f → flowValue (z, true) f = ℓ →
    ¬ ResReach (splitCap J T z x k) f (z, true) (x, false) →
    IsMinSeparator J T z x (extractCut J T z x k f) ∧ (extractCut J T z x k f).card = ℓ

/-! ### Section 2.2 -/

/-- **The cut with largest source side** (Section 2.2): "$W$ is the largest source side of a
minimum network cut: it contains the source side of every minimum cut." "This $U$ contains the open
source side of every minimum vertex separator between $z$ and $x$." -/
def Sec22Statement : Prop :=
  ∀ {W : Type u} [Fintype W] [DecidableEq W] (J : SimpleGraph W) (T : Set W) (z x : W) (k ℓ : ℕ)
    (f : W × Bool → W × Bool → ℕ),
    z ∈ T → x ∈ T → z ≠ x → ¬ J.Adj z x → ℓ ≤ k →
    IsFlow (splitCap J T z x k) (z, true) (x, false) f → flowValue (z, true) f = ℓ →
    ¬ ResReach (splitCap J T z x k) f (z, true) (x, false) →
    IsMaxSourceSeparator J T z x (extractCut J T z x k f)

/-! ### Section 3: the replacement -/

/-- **Lemma 1, forward direction** (Section 3): "If $D$ is crossed before the replacement, then it
is crossed afterward." -/
def Lemma1ForwardStatement : Prop :=
  ∀ {V : Type u} (r : ReplRecord V) (D : List V),
    HP25.IsSupportedOn r.graph r.verts → HP25.IsCycleList r.graph D → r.IsValid D →
    HP25.IsCrossed r.graph D → HP25.IsCrossed r.newGraph D

/-- **Lemma 1, reverse direction** (Section 3): "A crossing afterward can be lifted to a crossing
before the replacement with at most one ordinary path search."
* "exactly one path uses new edges, because two disjoint paths that both use new clique edges would
  need four distinct vertices of $S$."
* "If neither returned path uses a newly added edge, we keep both."
* "We search for a path from $p$ to $q$ in $K[A\cup\{p,q\}]$. Such a path exists because $A$ is
  connected and both $p$ and $q$ have neighbors in $A$. We replace the whole segment between $p$
  and $q$ by this path."
The crossing pair is symmetric in its two paths, so the case where the second path uses new edges
is the case of the first for the swapped pair. -/
def Lemma1ReverseStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (r : ReplRecord V) (D : List V) (L₁ L₂ : List V),
    HP25.IsSupportedOn r.graph r.verts → HP25.IsCycleList r.graph D → r.IsValid D →
    IsCrossingPair r.newGraph D L₁ L₂ →
    ¬ (usesNewEdge r.graph L₁ ∧ usesNewEdge r.graph L₂) ∧
    (¬ usesNewEdge r.graph L₁ → ¬ usesNewEdge r.graph L₂ → IsCrossingPair r.graph D L₁ L₂) ∧
    (usesNewEdge r.graph L₁ → (∃ Y, IsReplSearchPath r L₁ Y) ∧
      ∀ Y, IsReplSearchPath r L₁ Y → IsCrossingPair r.graph D (spliceBetween r.boundary L₁ Y) L₂)

/-- **Lemma 2** (Section 3): "Let $T$ be a set of retained vertices. Every path of the old graph
that avoids $T$ and has retained ends gives a path of the new graph between the same ends that
avoids $T$." -/
def Lemma2Statement : Prop :=
  ∀ {V : Type u} (r : ReplRecord V) (D : List V) (T : Set V) (a b : V),
    HP25.IsSupportedOn r.graph r.verts → r.IsValid D → T ⊆ r.newVerts →
    a ∈ r.newVerts → b ∈ r.newVerts →
    ReachIn r.graph (r.verts \ T) a b → ReachIn r.newGraph (r.newVerts \ T) a b

/-- **Lemma 2, for the apex graph** (Section 3): "Therefore every statement proved earlier that a
retained vertex cannot be separated from $x$ by at most a given number of other vertices stays true
after the replacement." -/
def Lemma2ApexStatement : Prop :=
  ∀ {V : Type u} (r : ReplRecord V) (D : List V) (v : V) (k : ℕ),
    HP25.IsSupportedOn r.graph r.verts → HP25.IsCycleList r.graph D → r.IsValid D →
    v ∈ r.newVerts →
    IsUnseparable (apex r.graph D) (apexVerts r.verts) (some v) none k →
    IsUnseparable (apex r.newGraph D) (apexVerts r.newVerts) (some v) none k

/-! ### Section 4: initial cleaning -/

/-- **Discarding the other components** (Section 4): "First we discard the components of $G$ that
do not contain $C$, since they cannot contain a $C$-path." -/
def Sec4DiscardStatement : Prop :=
  ∀ {V : Type u} (K : SimpleGraph V) (S : Set V) (D : List V),
    HP25.IsSupportedOn K S → HP25.IsCycleList K D →
    (HP25.IsCrossed K D ↔
      HP25.IsCrossed (HP25.restrict K {y | ∃ d ∈ D, ReachIn K Set.univ d y}) D)

/-- **A failed query gives a replacement** (Section 4, steps 3–5): when the query for $v$ fails,
the note obtains a separator $S$ of size at most three, takes the component $A$ of $K-S$ that
contains $v$, and replaces $A$ by the clique on its actual neighborhood $N_K(A)$, using Lemma 1.
"The component $A$ contains no cycle vertex. Indeed, every cycle vertex that is still present is
adjacent to $x$, whereas $S$ separates $v$ from $x$." -/
def Sec4ComponentStatement : Prop :=
  ∀ {V : Type u} (K : SimpleGraph V) (S : Set V) (D : List V) (v : V) (X : Finset (Option V)),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → v ∈ S → v ∉ D →
    IsSeparator (apex K D) (apexVerts S) (some v) none X → X.card ≤ 3 →
    let A : Set V := {y | ReachIn K (S \ {y | some y ∈ X}) v y}
    v ∈ A ∧ ∃ N : Finset V, (N : Set V) = nbhd K A ∧
      ({ graph := K, verts := S, deleted := A, boundary := N, rep := A } : ReplRecord V).IsValid D

/-- **Initial cleaning ends clean** (Section 4): every successful four-path query stays true
afterward, by Lemma 2. "Every unsuccessful query deletes the vertex it asked about. Thus, after at
most $n$ bounded-flow queries, every remaining vertex off the cycle has four paths to $x$ that share
only their ends, and the remaining instance is clean" by the equivalence of Section 2. When no
off-cycle vertex can be separated from `x` by three vertices, the instance is clean. -/
def Sec4CleanStatement : Prop :=
  ∀ {V : Type u} (K : SimpleGraph V) (S : Set V) (D : List V),
    HP25.IsSupportedOn K S → HP25.IsCycleList K D →
    (∀ v ∈ S, v ∉ D → IsUnseparable (apex K D) (apexVerts S) (some v) none 3) →
    IsClean K S D

/-- **The size of a replacement** (Section 4): "Every replacement deletes at least one vertex and
adds at most three edges." -/
def Sec4EdgeCountStatement : Prop :=
  ∀ {V : Type u} (r : ReplRecord V) (D : List V), r.IsValid D →
    r.deleted.Nonempty ∧ (r.newGraph.edgeSet \ r.graph.edgeSet).ncard ≤ 3 ∧
      (r.newGraph.edgeSet \ r.graph.edgeSet).Finite

/-! ### Section 7: sparsification -/

/-- **Lemma 5: strong certificate** (Section 7.1): "Let $F$ be the union of $k$ successive BFS
forests of $J$, taken as above. For every set $S$ of vertices with $|S|<k$, the graphs $F-S$ and
$J-S$ have exactly the same components." -/
def Lemma5Statement : Prop :=
  ∀ {W : Type u} [DecidableEq W] (G : SimpleGraph W) (T : Set W) (Fs : List (SimpleGraph W)),
    HP25.IsSupportedOn G T → IsScanFirstSequence G T Fs →
    ∀ X : Finset W, X.card < Fs.length → ∀ a ∈ T \ X, ∀ b ∈ T \ X,
      (ReachIn G (T \ X) a b ↔ ReachIn (forestUnion Fs) (T \ X) a b)

/-- **The size of the certificate** (Section 7.1): "On $n+1$ vertices their union has at most $4n$
edges." -/
def Sec71CountStatement : Prop :=
  ∀ {W : Type u} [DecidableEq W] (G : SimpleGraph W) (T : Set W) (Fs : List (SimpleGraph W))
    (n : ℕ), T.Finite → T.ncard = n + 1 → HP25.IsSupportedOn G T → IsScanFirstSequence G T Fs →
    (forestUnion Fs).edgeSet.ncard ≤ Fs.length * n

/-- **The sparsification step** (Section 7.2): "Adding all edges from the apex to the cycle gives a
graph that contains the certificate and is contained in $J$." By Lemma 5, "the kept graph is still
clean. Its $3N-5$ kept edges of $K$ make it nonplanar by Euler's bound." As in Section 6, "Fact T
then shows that $D$ is still crossed." -/
def Sec72Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) (S : Set V) (D : List V)
    (Fs : List (SimpleGraph (Option V))) (E₀ : Set (Sym2 V)),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → IsClean K S D →
    IsSparsifyData K S D Fs E₀ →
    IsClean (sparsifyGraph K D Fs E₀) S D ∧
      ¬ Nonempty (HP25.PlaneEmbedding (sparsifyGraph K D Fs E₀) S) ∧
      HP25.IsCrossed (sparsifyGraph K D Fs E₀) D

/-- **The size of the retained graph** (Section 7.2): "The kept graph has at most
$4N+N+(3N-5)=8N-5$ edges." -/
def Sec72CountStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) (S : Set V) (D : List V)
    (Fs : List (SimpleGraph (Option V))) (E₀ : Set (Sym2 V)),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → IsSparsifyData K S D Fs E₀ →
    (sparsifyGraph K D Fs E₀).edgeSet.ncard ≤ 8 * S.ncard - 5

/-! ### Section 8: the maximum two-cut lemma -/

/-- **Lemma 6** (Section 8): let $B$ be a graph with a vertex $x$ such that $\mathcal R_2(B,x)$
holds, let $z\ne x$ be a vertex whose minimum vertex separators from $x$ have size two, and choose
$S=\{p,q\}$ with maximum open source side, as in Section 2.2. "Then neither $p$ nor $q$ can be
separated from $x$ by at most two other vertices." -/
def Lemma6Statement : Prop :=
  ∀ {W : Type u} (B : SimpleGraph W) (T : Set W) (x z : W) (X : Finset W),
    T.Finite → HP25.IsSupportedOn B T → x ∈ T → z ∈ T → z ≠ x → RootedConn B T x 2 →
    IsMaxSourceSeparator B T z x X → X.card = 2 →
    ∀ p ∈ X, IsUnseparable B T p x 2

/-! ### Section 9: repairing one trial contraction -/

/-- **What the contraction guarantees** (Section 9.1). Since the old augmented graph $K+x$
satisfied $\mathcal R_4$, the note derives three properties: (1) $\mathcal R_3(J,x)$ holds;
(2) "every separator of size at most three that excludes $x$ and disconnects $J$ contains $w$";
(3) for $B=J-w$, $\mathcal R_2(B,x)$ holds. "Furthermore, every component $Q$ of $J-\{w,p,q\}$
that does not contain $x$, for vertices $p,q$, contains a marker."
Here `H` is `contractGraph K u v` on `S \ {u}`, the cycle is `contractCycle D u`, and `w = v`. -/
def Sec91Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) (S : Set V) (D : List V) (u v : V),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → IsClean K S D →
    IsTrialEdge K D u v →
    let J := apex (contractGraph K u v) (contractCycle D u)
    let T := apexVerts (S \ {u})
    RootedConn J T none 3 ∧
    (∀ X : Finset (Option V), (X : Set (Option V)) ⊆ T \ {none} → X.card ≤ 3 →
      ¬ IsConnectedOn J (T \ X) → some v ∈ X) ∧
    RootedConn J (T \ {some v}) none 2 ∧
    (∀ (p q : Option V) (Q : Set (Option V)), p ≠ none → q ≠ none →
      IsComponentIn J (T \ {some v, p, q}) Q → none ∉ Q →
      ∃ y ∈ markers K u v, some y ∈ Q)

/-- **The value of a failed restoration flow** (Section 9.2): the failed flow has value exactly two,
by $\mathcal R_2(B,x)$. -/
def Sec92ValueStatement : Prop :=
  ∀ {W : Type u} (B : SimpleGraph W) (T : Set W) (x z : W),
    T.Finite → x ∈ T → z ∈ T → z ≠ x → ¬ B.Adj z x → RootedConn B T x 2 →
    ¬ IsUnseparable B T z x 2 → ∃ X : Finset W, IsMinSeparator B T z x X ∧ X.card = 2

/-- **Each restoration replacement is valid** (Section 9.3): "Each deleted component $A$ of
$B-\{p,q\}$ inside $U$ has exactly the neighborhood" $N_J(A)=\{w,p,q\}$. It has neighbors at $p$
and $q$ by $\mathcal R_2(B,x)$, and at $w$ by $\mathcal R_3(J,x)$. "It contains no vertex of the
current cycle, since every cycle vertex outside $\{w,p,q\}$ is still adjacent to $x$." So Lemma 1
applies, in its version that deletes several components with a common neighborhood. -/
def Sec93Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (H : SimpleGraph V) (S : Set V) (D : List V) (w z p q : V),
    S.Finite → HP25.IsSupportedOn H S → HP25.IsCycleList H D → w ∈ S →
    RootedConn (apex H D) (apexVerts S) none 3 →
    RootedConn (apex H D) (restoreVerts S w) none 2 →
    z ∈ S → z ∉ D → p ≠ q →
    IsMaxSourceSeparator (apex H D) (restoreVerts S w) (some z) none {some p, some q} →
    (restoreRecord H S D w z p q).IsValid D ∧ z ∈ (restoreRecord H S D w z p q).rep

/-- **The boundary of a restoration replacement is good** (Section 9.4): "At every replacement
made during restoration, the three boundary vertices $w,p,q$ are good." The vertex $w$ is good by
property 2 of Section 9.1. By Lemma 6, applied to $B$, the vertices $p$ and $q$ cannot be separated
from $x$ in $B$ by at most two vertices, and "since every separator of $J$ of size at most three
contains $w$, they are good in $J$." -/
def Sec94BoundaryGoodStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (H : SimpleGraph V) (S : Set V) (D : List V) (w z p q : V),
    S.Finite → HP25.IsSupportedOn H S → HP25.IsCycleList H D → w ∈ S →
    RootedConn (apex H D) (apexVerts S) none 3 →
    (∀ X : Finset (Option V), (X : Set (Option V)) ⊆ apexVerts S \ {none} → X.card ≤ 3 →
      ¬ IsConnectedOn (apex H D) (apexVerts S \ X) → some w ∈ X) →
    RootedConn (apex H D) (restoreVerts S w) none 2 →
    z ∈ S → z ∉ D → p ≠ q →
    IsMaxSourceSeparator (apex H D) (restoreVerts S w) (some z) none {some p, some q} →
    IsGood (apex H D) (apexVerts S) (some w) none ∧ IsGood (apex H D) (apexVerts S) (some p) none ∧
      IsGood (apex H D) (apexVerts S) (some q) none

/-- **Every bad component keeps a marker** (Section 9.4): "This proves, by induction, that every
bad component during restoration contains an original marker that is still present." A bad
component is a component, not containing `x`, of `J - X` for a set `X` of at most three vertices
other than `x`. -/
def Sec94InvariantStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) (S : Set V) (D : List V) (u v : V)
    (M₁ M₂ : List V) (H : SimpleGraph V) (S' : Set V) (recs : List (ReplRecord V)),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → IsClean K S D →
    IsTrialEdge K D u v → (u ∈ D → 4 < D.length) → (M₁ ++ M₂).Nodup → (∀ y, y ∈ M₁ ++ M₂ ↔ y ∈ markers K u v) →
    IsRestoreRun (contractCycle D u) v M₁ (contractGraph K u v) (S \ {u}) H S' recs →
    ∀ (X : Finset (Option V)) (Q : Set (Option V)),
      (X : Set (Option V)) ⊆ apexVerts S' \ {none} → X.card ≤ 3 →
      IsComponentIn (apex H (contractCycle D u)) (apexVerts S' \ X) Q → none ∉ Q →
      ∃ y ∈ markers K u v, some y ∈ Q

/-- **Lemma 7** (Section 9.4): "Restoration returns a clean instance that has a crossing if and only
if the contracted instance has one, and it uses at most $|M|$ flow queries for three paths." The run
exists, and every run over the list of markers ends clean and crossing-equivalent, with valid
records. A cycle-edge contraction is tried only when `|D| ≥ 5` (Section 10, step 3: "contractions
of cycle edges are skipped when $|D|=4$"), so that the new cycle is a cycle. -/
def Lemma7Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) (S : Set V) (D : List V) (u v : V)
    (M : List V),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → IsClean K S D →
    IsTrialEdge K D u v → (u ∈ D → 4 < D.length) → M.Nodup → (∀ y, y ∈ M ↔ y ∈ markers K u v) →
    (∃ (H : SimpleGraph V) (S' : Set V) (recs : List (ReplRecord V)),
      IsRestoreRun (contractCycle D u) v M (contractGraph K u v) (S \ {u}) H S' recs) ∧
    ∀ (H : SimpleGraph V) (S' : Set V) (recs : List (ReplRecord V)),
      IsRestoreRun (contractCycle D u) v M (contractGraph K u v) (S \ {u}) H S' recs →
      IsClean H S' (contractCycle D u) ∧
      (HP25.IsCrossed (contractGraph K u v) (contractCycle D u) ↔
        HP25.IsCrossed H (contractCycle D u)) ∧
      (∀ r ∈ recs, r.IsValid (contractCycle D u)) ∧ recs.length ≤ M.length

/-! ### Section 10: the contraction algorithm -/

/-- **Nonplanar graphs are not small** (Section 10.1): "A nonplanar graph has at least five
vertices." -/
def Sec101FiveStatement : Prop :=
  ∀ {V : Type u} (K : SimpleGraph V) (S : Set V), S.Finite → HP25.IsSupportedOn K S →
    ¬ Nonempty (HP25.PlaneEmbedding K S) → 5 ≤ S.ncard

/-- **Five low-degree vertices always exist** (Section 10.1): "For $5\le N\le9$, every vertex has
degree at most eight. For $N\ge10$, the number of vertices of degree at least $65$ is at most
$\frac{2M}{65}\le\frac{32N}{65}<\frac N2.$ Thus more than $N/2\ge5$ vertices have degree at most
$64$." -/
def Sec101Statement : Prop :=
  ∀ {V : Type u} (K : SimpleGraph V) (S : Set V), S.Finite → HP25.IsSupportedOn K S →
    ¬ Nonempty (HP25.PlaneEmbedding K S) → K.edgeSet.ncard ≤ 16 * S.ncard →
    ∃ U : Finset V, U.card = 5 ∧ (U : Set V) ⊆ S ∧ ∀ y ∈ U, (K.neighborSet y).ncard ≤ 64

/-- **Off-cycle vertices of a clean instance have degree at least four** (Section 10.2):
"cleanliness implies that every vertex off the cycle has degree at least four." -/
def Sec102DegreeStatement : Prop :=
  ∀ {V : Type u} (K : SimpleGraph V) (S : Set V) (D : List V),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → IsClean K S D →
    ∀ v ∈ S, v ∉ D → 4 ≤ (K.neighborSet v).ncard

/-- **At least one trial is positive** (Section 10.2): "Fix any crossing of $D$. It has exactly four
ends. So at least one of the five chosen vertices, say $u$, is not one of these ends." In each case
some trial edge at `u` keeps a crossing: "The vertex $u$ is off the cycle and lies on a crossing
path. Contract an edge of that path at $u$. The crossing survives." "The vertex $u$ is off the
cycle and lies on neither path. Contract any edge at $u$. The crossing survives." "The vertex $u$
is on the cycle. Then neither crossing path uses it. Contract either cycle edge at $u$. The cyclic
order of the four ends of the crossing does not change. Here $|D|\ge5$, since $D$ contains the four
ends and $u$, so this trial is not skipped." -/
def Sec102Statement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) (S : Set V) (D : List V) (U : Finset V),
    S.Finite → HP25.IsSupportedOn K S → HP25.IsCycleList K D → IsClean K S D →
    HP25.IsCrossed K D → U.card = 5 → (U : Set V) ⊆ S →
    ∃ u ∈ U, ∃ v, IsTrialEdge K D u v ∧ (u ∈ D → D.length ≠ 4) ∧
      HP25.IsCrossed (contractGraph K u v) (contractCycle D u)

/-! ### Section 11: lifting contractions -/

/-- **The lift when both ends are off the cycle** (Section 11, "Both ends off the cycle"): "The
added vertices do not occur on the other path or elsewhere on this path." -/
def Lift11OffOffStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] (S : Set V)
    (D : List V) (u v : V) (L₁ L₂ : List V),
    HP25.IsSupportedOn K S → HP25.IsCycleList K D → K.Adj u v → u ∉ D → v ∉ D →
    IsCrossingPair (contractGraph K u v) D L₁ L₂ →
    IsCrossingPair K D (liftOffOff K u v L₁) (liftOffOff K u v L₂)

/-- **The lift when one end is on the cycle** (Section 11, "One end on the cycle"): "The algorithm
orients this case so that $u\notin V(D)$ and $v\in V(D)$, and keeps $w=v$." "The only vertex added
inside the path is $u$, which is off the cycle." -/
def Lift11OneOnStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] (S : Set V)
    (D : List V) (u v : V) (L₁ L₂ : List V),
    HP25.IsSupportedOn K S → HP25.IsCycleList K D → K.Adj u v → u ∉ D → v ∈ D →
    IsCrossingPair (contractGraph K u v) D L₁ L₂ →
    IsCrossingPair K D (liftOneOn K u v L₁) (liftOneOn K u v L₂)

/-- **The lift when both ends are on the cycle** (Section 11, "Both ends on the cycle"): "Replacing
one cycle position by one of two consecutive positions keeps the cyclic order of the four distinct
ends, since no other end lies between those two positions." -/
def Lift11BothOnStatement : Prop :=
  ∀ {V : Type u} [DecidableEq V] (K : SimpleGraph V) [DecidableRel K.Adj] (S : Set V)
    (D : List V) (u v : V) (L₁ L₂ : List V),
    HP25.IsSupportedOn K S → HP25.IsCycleList K D → K.Adj u v → IsCycleEdge D u v →
    IsCrossingPair (contractGraph K u v) (D.erase u) L₁ L₂ →
    IsCrossingPair K D (liftBothOn K u v L₁) (liftBothOn K u v L₂)

end GraphMinor.Crossing
