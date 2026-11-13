module

public import GraphMinor.Kruskal.LabelledTrees
public import GraphMinor.Kruskal.Addresses

/-!
# Shapes and labels of ordered trees

Forgetting labels gives an ordered tree with the same vertex addresses.
Looking up a label follows the branch indices in an address. Separating
these two operations lets the address-path construction for ordinary trees
be used while retaining the attachment counts at the images of vertices.
-/

@[expose] public section

namespace GraphMinor.Kruskal.LabelledTree

variable {L : Type*}

/-- The ordered tree obtained by forgetting all vertex labels. -/
def shape : LabelledTree L → OrderedTree
  | .node _ ts => .node (ts.map shape)

/-- Forgetting labels acts separately on each branch. -/
theorem shape_node (a : L) (ts : List (LabelledTree L)) :
    shape (.node a ts) = .node (ts.map shape) := by simp only [shape]

/-- Follow the branch indices to read a vertex label. Invalid addresses
return the label at the first vertex whose branch index is invalid. Only
valid vertex addresses are used in embedding statements. -/
def labelAt : LabelledTree L → List ℕ → L
  | .node a _, [] => a
  | .node a ts, i :: p =>
    match ts[i]? with
    | none => a
    | some t => labelAt t p
termination_by _ p => p.length

/-- The empty address reads the root label. -/
theorem labelAt_nil (a : L) (ts : List (LabelledTree L)) :
    labelAt (.node a ts) [] = a := by simp only [labelAt]

/-- Reading a valid branch address continues in that branch. -/
theorem labelAt_cons (a : L) (ts : List (LabelledTree L))
    (i : Fin ts.length) (p : List ℕ) :
    labelAt (.node a ts) (i.val :: p) = labelAt ts[i] p := by
  simp [labelAt]

/-- A labelled embedding also embeds the underlying ordered shapes. -/
theorem Embeds.forgetLabels {r : L → L → Prop} {s t : LabelledTree L}
    (h : Embeds r s t) : OrderedTree.Embeds s.shape t.shape := by
  refine Embeds.rec
    (motive_1 := fun s t _ ↦ OrderedTree.Embeds s.shape t.shape)
    (motive_2 := fun ts us _ ↦ List.SublistForall₂ OrderedTree.Embeds
      (ts.map shape) (us.map shape))
    (root := ?_) (dive := ?_) (nil := ?_) (cons := ?_) (cons_right := ?_) h
  · intro a b ts us _ _ ih
    rw [shape_node, shape_node]
    exact .root ih
  · intro s t a ts ht _ ih
    rw [shape_node]
    exact .dive (List.mem_map.mpr ⟨t, ht, rfl⟩) ih
  · intro us
    exact .nil
  · intro s t ts us _ _ ihst ihts
    exact .cons ihst ihts
  · intro t ts us _ ih
    exact .cons_right ih

end GraphMinor.Kruskal.LabelledTree
