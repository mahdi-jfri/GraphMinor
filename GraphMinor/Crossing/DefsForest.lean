module

public import GraphMinor.Crossing.Defs
public import Mathlib.Data.Set.Card

/-!
# Scan-first forests and the sparsification (Section 7 of the note)

Section 7.1 of `docs/crossing/crossing_extractor.tex` computes four forests in turn: "Take a BFS
spanning forest $F_1$ of $J$. Delete its edges and take a BFS spanning forest $F_2$ of the rest",
and so on. "This is the scan-first construction of sparse certificates of Cheriyan, Kao and
Thurimella." Lemma 5 uses only the way such a forest is
built: when a vertex is scanned, the edges to all its unmarked neighbours are selected.

We describe a scan-first forest by its scan order `σ`. In a scan-first search a vertex is marked
by the first of its neighbours to be scanned, and it is a root when no neighbour is scanned before
it. So the forest is `scanForest G σ`: each vertex is joined to its earliest neighbour in `σ`, when
that neighbour comes before it. A list `σ` is a scan order (`IsScanOrder`) when it lists the
vertices once each and every vertex with an earlier vertex in its component has an earlier
neighbour. A BFS forest is the scan-first forest of its order of scanning.

* `IsScanFirstForest G T F`, `IsScanFirstSequence G T Fs`, `forestUnion Fs`.
* `sparsifyGraph K D Fs E₀`: the graph that Section 7.2 retains.
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- `σ` is a scan order of the graph `G` with vertex set `T`: it lists each vertex of `T` once,
and every vertex that comes after some vertex of its component has a neighbour earlier in `σ`. -/
def IsScanOrder (G : SimpleGraph W) (T : Set W) (σ : List W) : Prop :=
  σ.Nodup ∧ (∀ y, y ∈ σ ↔ y ∈ T) ∧
    ∀ (i j : ℕ) (a b : W), i < j → σ[i]? = some a → σ[j]? = some b → ReachIn G T a b →
      ∃ i' < j, ∃ c, σ[i']? = some c ∧ G.Adj c b

/-- `p` is the scan parent of `c`: the neighbour of `c` earliest in `σ`, when it comes before
`c`. -/
def IsScanParent (G : SimpleGraph W) (σ : List W) (c p : W) : Prop :=
  G.Adj c p ∧ σ.idxOf p < σ.idxOf c ∧ ∀ y, G.Adj c y → σ.idxOf p ≤ σ.idxOf y

/-- The scan-first forest of the order `σ`: every vertex joined to its scan parent. -/
def scanForest (G : SimpleGraph W) (σ : List W) : SimpleGraph W where
  Adj a b := IsScanParent G σ a b ∨ IsScanParent G σ b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => by rcases h with h | h <;> exact lt_irrefl _ h.2.1⟩

/-- **A scan-first spanning forest** of `G` with vertex set `T` (Section 7.1: "Take a BFS
spanning forest $F_1$."). -/
def IsScanFirstForest (G : SimpleGraph W) (T : Set W) (F : SimpleGraph W) : Prop :=
  ∃ σ, IsScanOrder G T σ ∧ F = scanForest G σ

/-- **Successive scan-first forests** (Section 7.1): each forest is a scan-first spanning forest
of the graph left after deleting the edges of the forests before it ("Delete its edges and take a
BFS spanning forest $F_2$."). -/
def IsScanFirstSequence (G : SimpleGraph W) (T : Set W) : List (SimpleGraph W) → Prop
  | [] => True
  | F :: Fs => IsScanFirstForest G T F ∧ IsScanFirstSequence (G \ F) T Fs

/-- The union of a list of graphs: "Let $F=F_1\cup F_2\cup F_3\cup F_4$." -/
def forestUnion : List (SimpleGraph W) → SimpleGraph W
  | [] => ⊥
  | F :: Fs => F ⊔ forestUnion Fs

/-- **The retained graph of the sparsification** (Section 7.2): keep the edges of the certificate
that do not contain the apex, keep all edges of `D`, keep any `3N - 5` edges of `K`, and delete
all other edges of `K`. Here `Fs` are
the forests of the certificate of `J = K + x` and `E₀` is the chosen set of edges of `K`. -/
def sparsifyGraph (K : SimpleGraph V) (D : List V) (Fs : List (SimpleGraph (Option V)))
    (E₀ : Set (Sym2 V)) : SimpleGraph V where
  Adj a b := K.Adj a b ∧ ((forestUnion Fs).Adj (some a) (some b) ∨ IsCycleEdge D a b ∨
    s(a, b) ∈ E₀)
  symm := ⟨fun a b h => ⟨h.1.symm, by
    rcases h.2 with h | ⟨p, hp, h⟩ | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl ⟨p, hp, h.symm⟩)
    · exact Or.inr (Or.inr (by rwa [Sym2.eq_swap]))⟩⟩
  loopless := ⟨fun a h => K.loopless.irrefl _ h.1⟩

/-- The sparsification is an instance of Section 7.2, for `K` with vertex set `S` of `N`
vertices: `Fs` are four successive scan-first forests of `J = K + x`, and `E₀` is a set of
`3N - 5` edges of `K`. -/
def IsSparsifyData (K : SimpleGraph V) (S : Set V) (D : List V)
    (Fs : List (SimpleGraph (Option V))) (E₀ : Set (Sym2 V)) : Prop :=
  IsScanFirstSequence (apex K D) (apexVerts S) Fs ∧ Fs.length = 4 ∧ E₀ ⊆ K.edgeSet ∧
    E₀.Finite ∧ E₀.ncard = 3 * S.ncard - 5

end GraphMinor.Crossing
