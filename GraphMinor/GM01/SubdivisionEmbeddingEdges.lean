module

public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# Edge maps for consecutive subcombs

The tail comb in Graph Minors I, (4.1), page 55, selects a subset of the
source comb's replacing paths. An injective source vertex map preserving
adjacency induces an injective map on actual edges by mapping their two
ends. This is the edge map used to select those paths.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- An injective adjacency-preserving vertex map induces an injective map
on unordered source edges. -/
def subdivisionEmbeddingEdges {ν μ : Type*} {S : SimpleGraph ν} {T : SimpleGraph μ}
    (f : ν ↪ μ) (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b)) :
    S.edgeSet ↪ T.edgeSet where
  toFun e := ⟨Sym2.map f e.val, by
    obtain ⟨edge, he⟩ := e
    induction edge using Sym2.inductionOn with
    | hf a b => exact hf he⟩
  inj' := by
    intro e e' heq
    exact Subtype.ext (Sym2.map.injective f.injective (congrArg Subtype.val heq))

/-- The induced edge map preserves the specified pair of ends. -/
theorem subdivisionEmbeddingEdges_ends {ν μ : Type*} {S : SimpleGraph ν} {T : SimpleGraph μ}
    (f : ν ↪ μ) (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    {e : S.edgeSet} {a b : ν} (he : e.val = s(a,b)) :
    (subdivisionEmbeddingEdges f hf e).val = s(f a,f b) := by
  change Sym2.map f e.val = _
  rw [he]
  rfl

/-- An involutive source reindexing induces an involution on its
actual edges. This reindexes the replacing paths when reversing `D`
after GM01 (4.9), page 58. -/
theorem subdivisionEmbeddingEdges_involutive {ν : Type*} {S : SimpleGraph ν}
    (f : ν ↪ ν) (hf : ∀ {a b}, S.Adj a b → S.Adj (f a) (f b))
    (hInv : Function.Involutive f) : Function.Involutive (subdivisionEmbeddingEdges f hf) := by
  intro e
  apply Subtype.ext
  change Sym2.map f (Sym2.map f e.val) = e.val
  induction e.val using Sym2.inductionOn with
  | hf a b =>
    change s(f (f a),f (f b)) = s(a,b)
    rw [hInv a, hInv b]

end GraphMinor.GM01
