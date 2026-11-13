module

public import GraphMinor.GM01.PathCombs
public import GraphMinor.GM01.RootedEmbeddings
public import GraphMinor.GM01.SubdivisionEmbeddingEdges
import Lean.Elab.Tactic.Omega

/-!
# Consecutive subcombs

The proof of Graph Minors I, (4.1), page 55, retains a long comb in the
last block. Map a shorter comb to a consecutive interval of the original
spine, carrying each attached binary copy with its spine vertex. The
vertex map is injective, preserves adjacency and roots, and gives a
rooted model with singleton branches in the corresponding source comb.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set SimpleGraph

/-- Shift a spine index into a consecutive interval of the longer spine. -/
def combShiftIndex {m N : ℕ} (offset : ℕ) (h : offset + m ≤ N) : Fin m ↪ Fin N where
  toFun i := ⟨offset + i.val, by omega⟩
  inj' := by intro i j heq; apply Fin.ext; have hv := congrArg Fin.val heq; dsimp at hv; omega

/-- Shift a comb vertex together with its attached binary copy. -/
def combShiftVertex {m N : ℕ} (offset : ℕ) (h : offset + m ≤ N) :
    PathCombVertex m → PathCombVertex N
  | .inl i => .inl (combShiftIndex offset h i)
  | .inr (i, word) => .inr (combShiftIndex offset h i, word)

/-- The shifted vertex map is injective, including the binary word labels. -/
theorem combShiftVertex_injective {m N : ℕ} (offset : ℕ) (h : offset + m ≤ N) :
    Function.Injective (combShiftVertex offset h) := by
  intro x y hxy
  cases x with
  | inl i =>
    cases y with
    | inl j => exact congrArg Sum.inl ((combShiftIndex offset h).injective (Sum.inl.inj hxy))
    | inr p => cases hxy
  | inr p =>
    rcases p with ⟨i, word⟩
    cases y with
    | inl j => cases hxy
    | inr q =>
      rcases q with ⟨j, word'⟩
      have hp := Sum.inr.inj hxy
      have hij := (combShiftIndex offset h).injective (congrArg Prod.fst hp)
      have hword := congrArg Prod.snd hp
      dsimp only at hword
      subst j
      subst word'
      rfl

/-- All valid vertices of the shorter comb occur in the shifted copy. -/
theorem combShiftVertex_mem {γ m N : ℕ} (offset : ℕ) (h : offset + m ≤ N)
    {x : PathCombVertex m} (hx : x ∈ (pathComb γ m).verts) :
    combShiftVertex offset h x ∈ (pathComb γ N).verts := by
  cases x with
  | inl i => trivial
  | inr p => exact hx

/-- Shifting a consecutive spine interval preserves all comb edges. -/
theorem combShiftVertex_adj {γ m N : ℕ} (offset : ℕ) (h : offset + m ≤ N)
    {x y : PathCombVertex m} (hxy : (pathComb γ m).Adj x y) :
    (pathComb γ N).Adj (combShiftVertex offset h x) (combShiftVertex offset h y) := by
  cases x with
  | inl i =>
    cases y with
    | inl j =>
      apply pathComb_spine_adj
      apply pathGraph_adj.mpr
      rcases pathGraph_adj.mp hxy with hfor | hback
      · exact Or.inl (by change offset + i.val + 1 = offset + j.val; omega)
      · exact Or.inr (by change offset + j.val + 1 = offset + i.val; omega)
    | inr p =>
      exact ⟨congrArg (combShiftIndex offset h) hxy.1, hxy.2⟩
  | inr p =>
    cases y with
    | inl j => exact ⟨congrArg (combShiftIndex offset h) hxy.1, hxy.2⟩
    | inr q => exact ⟨congrArg (combShiftIndex offset h) hxy.1, hxy.2⟩

/-- The shifted map on the actual vertex types of the two combs. -/
def combShiftEmbedding {γ m N : ℕ} (offset : ℕ) (h : offset + m ≤ N) :
    (pathComb γ m).verts ↪ (pathComb γ N).verts where
  toFun x := ⟨combShiftVertex offset h x.val, combShiftVertex_mem offset h x.property⟩
  inj' := fun _ _ heq ↦ Subtype.ext
    (combShiftVertex_injective offset h (congrArg Subtype.val heq))

/-- The shifted actual-vertex embedding preserves adjacency. -/
theorem combShiftEmbedding_adj {γ m N : ℕ} (offset : ℕ) (h : offset + m ≤ N)
    {x y : (pathComb γ m).verts} (hxy : (pathComb γ m).coe.Adj x y) :
    (pathComb γ N).coe.Adj (combShiftEmbedding offset h x) (combShiftEmbedding offset h y) :=
  combShiftVertex_adj offset h hxy

/-- Select the original source edges used by the consecutive subcomb. -/
def combShiftEdges {γ m N : ℕ} (offset : ℕ) (h : offset + m ≤ N) :
    (pathComb γ m).coe.edgeSet ↪ (pathComb γ N).coe.edgeSet :=
  subdivisionEmbeddingEdges (combShiftEmbedding offset h) (combShiftEmbedding_adj offset h)

/-- A selected source edge has exactly the shifted pair of ends. -/
theorem combShiftEdges_ends {γ m N : ℕ} (offset : ℕ) (h : offset + m ≤ N)
    {e : (pathComb γ m).coe.edgeSet} {a b : (pathComb γ m).verts} (he : e.val = s(a,b)) :
    (combShiftEdges offset h e).val = s(combShiftEmbedding offset h a, combShiftEmbedding offset h b) :=
  subdivisionEmbeddingEdges_ends (combShiftEmbedding offset h) (combShiftEmbedding_adj offset h) he

/-- A consecutive subcomb is a rooted minor of the original comb rooted
at the first vertex of the chosen interval. Its branch sets are the
singletons specified by `combShiftVertex`. -/
noncomputable def rootedCombShiftModel {γ m N : ℕ} (hm : 0 < m) (offset : ℕ)
    (h : offset + m ≤ N) :
    RootedMinorModel (rootedPathComb γ m hm)
      (⟨toGraph (pathComb γ N),
        ⟨combShiftVertex offset h (rootedPathComb γ m hm).root.val,
          combShiftVertex_mem offset h (rootedPathComb γ m hm).root.property⟩⟩ :
        RootedGraph (PathCombVertex N) (Sym2 (PathCombVertex N))) :=
  rootedModelOfSubgraphEmbedding (pathComb γ m) (pathComb γ N)
    ⟨fun x ↦ combShiftVertex offset h x.val,
      fun _ _ heq ↦ Subtype.ext (combShiftVertex_injective offset h heq)⟩
    (fun x ↦ combShiftVertex_mem offset h x.property)
    (fun hxy ↦ combShiftVertex_adj offset h hxy) (rootedPathComb γ m hm).root

/-- Each branch of the consecutive-subcomb model is the singleton given
by its explicit shifted vertex map. -/
theorem rootedCombShiftModel_branch {γ m N : ℕ} (hm : 0 < m) (offset : ℕ)
    (h : offset + m ≤ N) (v : (pathComb γ m).verts) :
    (rootedCombShiftModel (γ := γ) hm offset h).branch v =
      {combShiftVertex offset h v.val} := by
  unfold rootedCombShiftModel
  rfl

end GraphMinor.GM01
