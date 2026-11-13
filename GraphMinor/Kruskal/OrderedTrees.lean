module

public import GraphMinor.Kruskal.MinimalBadSequence

/-!
# Homeomorphic embeddings of finite ordered rooted trees

A tree is a root with a finite list of branches. An embedding either matches
roots and embeds the branch list, or embeds the whole source in one branch
of the target. The latter operation allows edges to become longer paths.
This is the ordered version of the rooted trees and homeomorphisms of
Nash-Williams, Theorem 1, pages 833–835 (1963).

We prove reflexivity and transitivity, then apply the minimal bad sequence
argument with the structural size as rank. Connecting these trees to finite
multigraphs requires a separate proof about paths and edge subdivisions.
-/

@[expose] public section

namespace GraphMinor.Kruskal

/-- A finite ordered rooted tree, given by the list of branches at its root. -/
inductive OrderedTree where
  | node : List OrderedTree → OrderedTree

namespace OrderedTree

/-- The branches immediately below the root. -/
def children : OrderedTree → List OrderedTree
  | .node ts => ts

/-- A homeomorphic embedding of ordered rooted trees. Matching roots preserves
the order of the chosen branches. Descending into a branch allows the image
of the source root to lie below the target root. -/
inductive Embeds : OrderedTree → OrderedTree → Prop where
  | root {ts us} : List.SublistForall₂ Embeds ts us → Embeds (.node ts) (.node us)
  | dive {s t ts} : t ∈ ts → Embeds s t → Embeds s (.node ts)

/-- Every ordered rooted tree embeds in itself. -/
theorem Embeds.refl (t : OrderedTree) : Embeds t t := by
  apply OrderedTree.rec
    (motive_1 := fun t ↦ Embeds t t)
    (motive_2 := fun ts ↦ List.SublistForall₂ Embeds ts ts)
    (fun ts ih ↦ Embeds.root ih)
    List.SublistForall₂.nil
    (fun t ts ht hts ↦ List.SublistForall₂.cons ht hts)

/-- Homeomorphic embeddings compose. The proof also composes embeddings of
branch lists and follows the branch chosen by a descending embedding. -/
theorem Embeds.trans {a b c : OrderedTree} (hab : Embeds a b) (hbc : Embeds b c) :
    Embeds a c := by
  have h := Embeds.rec
    (motive_1 := fun b c _ ↦ ∀ a, Embeds a b → Embeds a c)
    (motive_2 := fun ys zs _ ↦
      (∀ xs, List.SublistForall₂ Embeds xs ys → List.SublistForall₂ Embeds xs zs) ∧
      (∀ a, (∃ b ∈ ys, Embeds a b) → ∃ c ∈ zs, Embeds a c))
    (root := ?_) (dive := ?_) (nil := ?_) (cons := ?_) (cons_right := ?_) hbc
  · exact h a hab
  · intro ys zs hsub ih a ha
    cases ha with
    | root h => exact Embeds.root (ih.1 _ h)
    | dive hm he =>
      obtain ⟨c, hc, hec⟩ := ih.2 _ ⟨_, hm, he⟩
      exact Embeds.dive hc hec
  · intro b c cs hc hbc ih a hab
    exact Embeds.dive hc (ih a hab)
  · intro l
    constructor
    · intro xs hxs
      cases hxs
      exact .nil
    · intro a ha
      obtain ⟨b, hb, _⟩ := ha
      exact False.elim (List.not_mem_nil hb)
  · intro b c ys zs hbc hsub ihbc ihsub
    constructor
    · intro xs hxs
      cases hxs with
      | nil => exact .nil
      | cons hab hs => exact .cons (ihbc _ hab) (ihsub.1 _ hs)
      | cons_right hs => exact .cons_right (ihsub.1 _ hs)
    · rintro a ⟨b', hb', hab'⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact ⟨c, List.mem_cons_self, ihbc a hab'⟩
      · obtain ⟨c', hc', hac'⟩ := ihsub.2 a ⟨b', hb', hab'⟩
        exact ⟨c', List.mem_cons_of_mem _ hc', hac'⟩
  · intro c ys zs hs ih
    constructor
    · intro xs hxs
      exact .cons_right (ih.1 xs hxs)
    · intro a ha
      obtain ⟨c', hc', hac'⟩ := ih.2 a ha
      exact ⟨c', List.mem_cons_of_mem _ hc', hac'⟩

instance : IsPreorder OrderedTree Embeds where
  refl := Embeds.refl
  trans _ _ _ := Embeds.trans

/-- A branch is strictly smaller than the tree containing it. -/
theorem sizeOf_lt_of_mem_children (a b : OrderedTree) (hb : b ∈ a.children) :
    sizeOf b < sizeOf a := by
  cases a with
  | node ts =>
    have h := List.sizeOf_lt_of_mem (show b ∈ ts from hb)
    exact Nat.lt_trans h (by simp +arith)

/-- Finite ordered rooted trees are well-quasi-ordered by homeomorphic
embedding, by the minimal bad sequence argument of Nash-Williams, Theorem 1,
pages 834–835, using Higman for the ordered lists of branches. -/
theorem wellQuasiOrdered_embeds : WellQuasiOrdered Embeds := by
  apply wellQuasiOrdered_of_children children sizeOf sizeOf_lt_of_mem_children
  · intro a b hb
    cases a with
    | node ts => exact .dive hb (.refl b)
  · intro a b h
    cases a
    cases b
    exact .root h

end OrderedTree
end GraphMinor.Kruskal
