module

public import GraphMinor.GM01.BinaryTrees
public import GraphMinor.GM01.RootedEmbeddings
import Mathlib.Data.List.Basic

/-!
# The binary tree in two branches of the three-branch tree

In the contraction on page 60 of Graph Minors I, each attached
three-branch tree supplies a binary arm. Select two of its branches.
The binary root goes to the centre, while the last bit of every
nonempty binary word selects one of those branches. Removing that
last bit gives the word within the selected branch. The unused
third branch will carry a path from an arbitrary attachment vertex.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set SimpleGraph Function

/-- Embed the binary word labels in two chosen branches of `Y`. -/
def binaryForestVertex (e : Bool ↪ Fin 3) (word : List Bool) : ForestTreeVertex :=
  if h : word = [] then none else some (e (word.getLast h), word.dropLast)

/-- Only the empty binary word maps to the centre. -/
theorem binaryForestVertex_eq_none (e : Bool ↪ Fin 3) (word : List Bool) :
    binaryForestVertex e word = none ↔ word = [] := by
  by_cases h : word = [] <;> simp only [binaryForestVertex, h, ↓reduceDIte, Option.some_ne_none]

/-- Different binary words have different images. -/
theorem binaryForestVertex_injective (e : Bool ↪ Fin 3) : Injective (binaryForestVertex e) := by
  intro a b hab
  by_cases ha : a = []
  · have hb : b = [] := (binaryForestVertex_eq_none e b).mp (hab.symm.trans
      ((binaryForestVertex_eq_none e a).mpr ha))
    exact ha.trans hb.symm
  · have hb : b ≠ [] := by
      intro hb
      exact ha ((binaryForestVertex_eq_none e a).mp (hab.trans
        ((binaryForestVertex_eq_none e b).mpr hb)))
    simp only [binaryForestVertex, ha, hb, ↓reduceDIte] at hab
    have hp := Option.some.inj hab
    have hlast := e.injective (congrArg Prod.fst hp)
    have hdrop : a.dropLast = b.dropLast := congrArg Prod.snd hp
    calc
      a = a.dropLast ++ [a.getLast ha] := (List.dropLast_append_getLast ha).symm
      _ = b.dropLast ++ [b.getLast hb] := by rw [hdrop, hlast]
      _ = b := List.dropLast_append_getLast hb

/-- The two-branch embedding respects the common height. -/
theorem binaryForestVertex_mem (e : Bool ↪ Fin 3) {γ : ℕ} {word : List Bool}
    (hw : word ∈ (binaryTree γ).verts) : binaryForestVertex e word ∈ (forestTree γ).verts := by
  by_cases h : word = []
  · simp only [binaryForestVertex, h, ↓reduceDIte]
    exact forestTree_centre_mem γ
  · simp only [binaryForestVertex, h, ↓reduceDIte]
    change word.dropLast.length + 1 ≤ γ
    cases word with
    | nil => exact False.elim (h rfl)
    | cons bit word =>
      simp only [List.length_dropLast_cons]
      exact hw

/-- A binary parent edge is retained in its selected branch, or joins
that branch to the centre when the parent is the root. -/
theorem binaryForestVertex_parent_adj (e : Bool ↪ Fin 3) {γ : ℕ} {a b : List Bool}
    (ha : a ∈ (binaryTree γ).verts) (hb : b ∈ (binaryTree γ).verts)
    (bit : Bool) (heq : b = bit :: a) :
    (forestTree γ).Adj (binaryForestVertex e a) (binaryForestVertex e b) := by
  refine ⟨binaryForestVertex_mem e ha, binaryForestVertex_mem e hb, Or.inl ?_⟩
  by_cases h : a = []
  · subst a
    subst b
    simp only [binaryForestVertex, List.cons_ne_nil, ↓reduceDIte, List.getLast_singleton,
      List.dropLast_singleton, forestTreeParent]
    exact ⟨Option.some_ne_none _, True.intro⟩
  · subst b
    simp only [binaryForestVertex, h, List.cons_ne_nil, ↓reduceDIte,
      List.getLast_cons h, List.dropLast_cons_of_ne_nil h, forestTreeParent]
    exact ⟨Option.some_ne_none _, True.intro⟩

/-- Select two branches of the three-branch tree as a rooted binary
subgraph, the source contraction used on page 60 of GM01. -/
noncomputable def binaryTreeModelInForest (γ : ℕ) (e : Bool ↪ Fin 3) :
    RootedMinorModel (binaryRootedTree γ)
      (⟨forestTreeGraph γ, ⟨none, forestTree_centre_mem γ⟩⟩ :
        RootedGraph ForestTreeVertex (Sym2 ForestTreeVertex)) := by
  let f : (binaryTree γ).verts ↪ ForestTreeVertex :=
    ⟨fun v ↦ binaryForestVertex e v.val,
      fun _ _ h ↦ Subtype.ext (binaryForestVertex_injective e h)⟩
  have hAdj : ∀ {a b : (binaryTree γ).verts}, (binaryTree γ).Adj a.val b.val →
      (forestTree γ).Adj (f a) (f b) := by
    intro a b hab
    rcases hab.2.2 with ⟨bit,hb⟩ | ⟨bit,ha⟩
    · exact binaryForestVertex_parent_adj e a.property b.property bit hb
    · exact (binaryForestVertex_parent_adj e b.property a.property bit ha).symm
  exact rootedModelOfSubgraphEmbedding (binaryTree γ) (forestTree γ) f
    (fun v ↦ binaryForestVertex_mem e v.property) hAdj (binaryRootedTree γ).root

/-- The selected binary subgraph has singleton branches at its explicit
word images. This identifies the branches avoided by the root path. -/
theorem binaryTreeModelInForest_branch (γ : ℕ) (e : Bool ↪ Fin 3)
    (v : (binaryTree γ).verts) :
    (binaryTreeModelInForest γ e).branch v = {binaryForestVertex e v.val} := by
  unfold binaryTreeModelInForest
  rfl

end GraphMinor.GM01
