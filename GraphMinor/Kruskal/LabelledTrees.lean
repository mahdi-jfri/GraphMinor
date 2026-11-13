module

public import Mathlib.Order.WellFoundedSet
import GraphMinor.Kruskal.MinimalBadSequence

/-!
# Labelled finite rooted trees

Labels belong to a well-quasi-order. The minimal bad sequence proof for
ordered rooted trees extends by first passing to a sequence of comparable
root labels, then using Higman's lemma on the lists of branches. This
extends the proof of Nash-Williams, *On well-quasi-ordering finite trees*
(1963), Theorem 1, pages 834–835.
-/

@[expose] public section

namespace GraphMinor.Kruskal

/-- A finite ordered rooted tree, with a label at each node and a list of branches. -/
inductive LabelledTree (L : Type*) where
  | node : L → List (LabelledTree L) → LabelledTree L

namespace LabelledTree

variable {L : Type*}

/-- The branches immediately below the root. -/
def children : LabelledTree L → List (LabelledTree L)
  | .node _ ts => ts

/-- A homeomorphic embedding of labelled ordered rooted trees. Matching roots compares
the labels by `r` and preserves
the order of the chosen branches. Descending into a branch allows the image
of the source root to lie below the target root. -/
inductive Embeds (r : L → L → Prop) : LabelledTree L → LabelledTree L → Prop where
  | root {a b ts us} : r a b → List.SublistForall₂ (Embeds r) ts us →
      Embeds r (.node a ts) (.node b us)
  | dive {s t a ts} : t ∈ ts → Embeds r s t → Embeds r s (.node a ts)

variable {r : L → L → Prop} [IsPreorder L r]

/-- Every ordered rooted tree embeds in itself. -/
theorem Embeds.refl (t : LabelledTree L) : Embeds r t t := by
  apply LabelledTree.rec
    (motive_1 := fun t ↦ Embeds r t t)
    (motive_2 := fun ts ↦ List.SublistForall₂ (Embeds r) ts ts)
    (fun a ts ih ↦ Embeds.root (_root_.refl a) ih)
    List.SublistForall₂.nil
    (fun t ts ht hts ↦ List.SublistForall₂.cons ht hts)

/-- Homeomorphic embeddings compose. The proof also composes embeddings of
branch lists and follows the branch chosen by a descending embedding. -/
theorem Embeds.trans {a b c : LabelledTree L} (hab : Embeds r a b) (hbc : Embeds r b c) :
    Embeds r a c := by
  have h := Embeds.rec
    (motive_1 := fun b c _ ↦ ∀ a, Embeds r a b → Embeds r a c)
    (motive_2 := fun ys zs _ ↦
      (∀ xs, List.SublistForall₂ (Embeds r) xs ys → List.SublistForall₂ (Embeds r) xs zs) ∧
      (∀ a, (∃ b ∈ ys, Embeds r a b) → ∃ c ∈ zs, Embeds r a c))
    (root := ?_) (dive := ?_) (nil := ?_) (cons := ?_) (cons_right := ?_) hbc
  · exact h a hab
  · intro lb lc ys zs hl hsub ih a ha
    cases ha with
    | root hlabel h => exact Embeds.root (_root_.trans hlabel hl) (ih.1 _ h)
    | dive hm he =>
      obtain ⟨c, hc, hec⟩ := ih.2 _ ⟨_, hm, he⟩
      exact Embeds.dive hc hec
  · intro b c lc cs hc hbc ih a hab
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

instance : IsPreorder (LabelledTree L) (Embeds r) where
  refl := Embeds.refl
  trans _ _ _ := Embeds.trans

/-- A branch is strictly smaller than the tree containing it. -/
theorem sizeOf_lt_of_mem_children (a b : LabelledTree L) (hb : b ∈ a.children) :
    sizeOf b < sizeOf a := by
  cases a with
  | node label ts =>
    have h := List.sizeOf_lt_of_mem (show b ∈ ts from hb)
    exact Nat.lt_trans h (by simp +arith)

/-- The label at the root. -/
def label : LabelledTree L → L
  | .node a _ => a

/-- Labelled ordered rooted trees are well-quasi-ordered by homeomorphic
embedding when their labels are well-quasi-ordered. This is the labelled
form of the Nash-Williams minimal bad sequence proof. -/
theorem wellQuasiOrdered_embeds (hr : WellQuasiOrdered r) :
    WellQuasiOrdered (Embeds r) := by
  open Set Set.PartiallyWellOrderedOn in
    rw [← partiallyWellOrderedOn_univ_iff, iff_not_exists_isMinBadSeq sizeOf]
    rintro ⟨f, hf, hmin⟩
    have hc := children_partiallyWellOrderedOn children sizeOf sizeOf_lt_of_mem_children
      (fun a b hb => by cases a; exact .dive hb (.refl b)) f hf hmin
    have hl := hc.partiallyWellOrderedOn_sublistForall₂ (Embeds r)
    obtain ⟨φ, hφ⟩ := hr.exists_monotone_subseq (fun n => label (f n))
    obtain ⟨i, j, hij, hrel⟩ := partiallyWellOrderedOn_iff_exists_lt.1 hl
      (fun n => children (f (φ n))) (fun n b hb => ⟨φ n, hb⟩)
    have hlabel := hφ i j (Nat.le_of_lt hij)
    apply hf.2 (φ i) (φ j) (φ.strictMono hij)
    cases hi : f (φ i) with
    | node a ts =>
      cases hj : f (φ j) with
      | node b us =>
        rw [hi, hj] at hlabel hrel
        exact .root hlabel hrel

/-- Finite lists of labelled ordered rooted trees are well-quasi-ordered
by matching each source tree to a distinct target tree, in order. This gives
Higman's extension from the trees to ordered forests. -/
theorem wellQuasiOrdered_forestEmbeds (hr : WellQuasiOrdered r) :
    WellQuasiOrdered (List.SublistForall₂ (Embeds r)) := by
  have ht := Set.partiallyWellOrderedOn_univ_iff.mpr (wellQuasiOrdered_embeds hr)
  have hl := ht.partiallyWellOrderedOn_sublistForall₂ (Embeds r)
  intro f
  exact Set.partiallyWellOrderedOn_iff_exists_lt.1 hl f
    (fun _ _ _ => Set.mem_univ _)

end LabelledTree
end GraphMinor.Kruskal
