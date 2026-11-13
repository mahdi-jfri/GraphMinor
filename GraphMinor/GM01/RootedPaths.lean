module

public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.Basic

/-!
# Paths in the base case of the rooted forest bound

Graph Minors I, proof of (3.7), Part 1, page 54, uses the configuration
`P(0,δ)`, a path rooted at one end. We identify the zero-height comb with
that path and map its vertices in order onto an embedded path. Singleton
branches then give the required rooted minor model.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- At height zero, the comb's vertex set consists precisely of its spine. -/
def pathCombZeroVertexEquiv (δ : ℕ) : (pathComb 0 δ).verts ≃ Fin δ where
  toFun v := by
    obtain ⟨v, hv⟩ := v
    cases v with
    | inl i => exact i
    | inr p => exact False.elim (Nat.not_lt_zero _ hv)
  invFun i := ⟨Sum.inl i, pathComb_spine_mem 0 δ i⟩
  left_inv v := by
    obtain ⟨v, hv⟩ := v
    cases v with
    | inl i => rfl
    | inr p => exact False.elim (Nat.not_lt_zero _ hv)
  right_inv i := rfl

/-- The configuration `P(0,δ)` is the path on `δ` vertices, via the map
sending spine vertex `i` to path vertex `i`. -/
def pathComb_zero_iso (δ : ℕ) : (pathComb 0 δ).coe ≃g pathGraph δ := by
  refine { pathCombZeroVertexEquiv δ with map_rel_iff' := ?_ }
  intro x y
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  cases x with
  | inr p => exact False.elim (Nat.not_lt_zero _ hx)
  | inl i =>
    cases y with
    | inr q => exact False.elim (Nat.not_lt_zero _ hy)
    | inl j => rfl

/-- The ordered vertices of a path give an injective map from its index set. -/
def pathWalkVertexEmbedding {α : Type*} {G : SimpleGraph α} {u v : α}
    (p : G.Walk u v) (hp : p.IsPath) {δ : ℕ} (hlen : p.length + 1 = δ) : Fin δ ↪ α where
  toFun i := p.getVert i.val
  inj' i j hij := Fin.ext (hp.getVert_injOn (by change i.val ≤ p.length; omega)
    (by change j.val ≤ p.length; omega) hij)

/-- Consecutive indices on a path give adjacent vertices of that path. -/
theorem pathWalkVertexEmbedding_adj {α : Type*} {G : SimpleGraph α} {u v : α}
    (p : G.Walk u v) (hp : p.IsPath) {δ : ℕ} (hlen : p.length + 1 = δ)
    {i j : Fin δ} (hij : (pathGraph δ).Adj i j) :
    G.Adj (pathWalkVertexEmbedding p hp hlen i) (pathWalkVertexEmbedding p hp hlen j) := by
  rcases pathGraph_adj.mp hij with hij | hji
  · change G.Adj (p.getVert i.val) (p.getVert j.val)
    rw [← hij]
    exact p.adj_getVert_succ (by have := j.isLt; omega)
  · change G.Adj (p.getVert i.val) (p.getVert j.val)
    rw [← hji]
    exact (p.adj_getVert_succ (by have := i.isLt; omega)).symm

/-- An embedded `δ`-vertex path starting at the distinguished root gives a
rooted model of `P(0,δ)`, as used in Part 1 of the proof of Graph Minors I,
(3.7), page 54. No minor-existence step is assumed. -/
noncomputable def rootedModelOfPath {α : Type*}
    (G : (⊤ : SimpleGraph α).Subgraph) {u v : G.verts}
    (p : G.coe.Walk u v) (hp : p.IsPath) {δ : ℕ} (hlen : p.length + 1 = δ)
    (hδ : 0 < δ) :
    RootedMinorModel (rootedPathComb 0 δ hδ)
      (⟨toGraph G, u⟩ : RootedGraph α (Sym2 α)) := by
  let e := pathComb_zero_iso δ
  let f : (pathComb 0 δ).verts ↪ α :=
    e.toEquiv.toEmbedding.trans ((pathWalkVertexEmbedding p hp hlen).trans
      ⟨Subtype.val, Subtype.val_injective⟩)
  have hverts : ∀ x, f x ∈ G.verts := fun x ↦ (p.getVert (e x).val).property
  have hadj : ∀ {x y : (pathComb 0 δ).verts}, (pathComb 0 δ).Adj x.val y.val →
      G.Adj (f x) (f y) := by
    intro x y hxy
    have he : (pathGraph δ).Adj (e x) (e y) := e.map_rel_iff'.mpr hxy
    exact pathWalkVertexEmbedding_adj p hp hlen he
  let root : (pathComb 0 δ).verts := ⟨Sum.inl ⟨0, hδ⟩, pathComb_spine_mem 0 δ _⟩
  let M := rootedModelOfSubgraphEmbedding (pathComb 0 δ) G f hverts hadj root
  apply M.mono (G' := (⟨toGraph G, u⟩ : RootedGraph α (Sym2 α))) le_rfl
  change f root = u.val
  change (p.getVert 0).val = u.val
  rw [Walk.getVert_zero]

/-- A path with at least `δ` vertices contains a rooted copy of `P(0,δ)`
starting at the same root. Take its first `δ` vertices. -/
noncomputable def rootedModelOfPathPrefix {α : Type*}
    (G : (⊤ : SimpleGraph α).Subgraph) {u v : G.verts}
    (p : G.coe.Walk u v) (hp : p.IsPath) {δ : ℕ} (hδ : 0 < δ)
    (hlen : δ ≤ p.length + 1) :
    RootedMinorModel (rootedPathComb 0 δ hδ)
      (⟨toGraph G, u⟩ : RootedGraph α (Sym2 α)) := by
  apply rootedModelOfPath G (p.take (δ - 1)) (hp.take _) ?_ hδ
  rw [Walk.take_length, Nat.min_eq_left (show δ - 1 ≤ p.length by omega)]
  omega

/-- In the base case of the rooted induction for (1.1), excluding `P(0,δ)`
bounds the length of every path beginning at the root. This is the local
path condition used when deleting the root in the paper's proof. -/
theorem path_length_le_of_not_rootedPathComb {α : Type*}
    (G : (⊤ : SimpleGraph α).Subgraph) (root : G.verts) {δ : ℕ} (hδ : 0 < δ)
    (hno : ¬ HasRootedMinor (rootedPathComb 0 δ hδ)
      (⟨toGraph G, root⟩ : RootedGraph α (Sym2 α)))
    {v : G.verts} (p : G.coe.Walk root v) (hp : p.IsPath) : p.length ≤ δ - 2 := by
  have hlt : p.length + 1 < δ := by
    by_contra h
    exact hno ⟨rootedModelOfPathPrefix G p hp hδ (Nat.le_of_not_gt h)⟩
  omega

end GraphMinor.GM01
