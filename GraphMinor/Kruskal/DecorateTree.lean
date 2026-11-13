module

public import GraphMinor.Kruskal.LabelledShape
import Mathlib.Data.List.OfFn

/-!
# Adding prescribed labels to an ordered tree

The address of a vertex determines its label. Label the root at the empty
address, then prefix the branch index when labelling each branch. Forgetting
the labels recovers the original tree, and reading a valid address recovers
the prescribed label.
-/

@[expose] public section

namespace GraphMinor.Kruskal.LabelledTree

variable {L : Type*}

/-- Label each vertex by the value of `f` on its address. -/
def decorate (t : OrderedTree) (f : List ℕ → L) : LabelledTree L :=
  match t with
  | .node ts => .node (f [])
      (List.ofFn fun i : Fin ts.length ↦ decorate ts[i] (fun p ↦ f (i.val :: p)))
termination_by sizeOf t
decreasing_by
  exact OrderedTree.sizeOf_lt_of_mem_children (.node ts) ts[i] (List.getElem_mem _)

/-- Forgetting the added labels gives the original ordered tree. -/
theorem shape_decorate (t : OrderedTree) (f : List ℕ → L) :
    (decorate t f).shape = t := by
  induction hn : sizeOf t using Nat.strong_induction_on generalizing t f with
  | h n ih =>
    cases t with
    | node ts =>
      rw [decorate, shape_node, List.map_ofFn]
      have he : (fun i : Fin ts.length ↦
          (decorate ts[i] (fun p ↦ f (i.val :: p))).shape) = (fun i ↦ ts[i]) := by
        funext i
        apply ih (sizeOf ts[i])
          (hn ▸ OrderedTree.sizeOf_lt_of_mem_children (.node ts) ts[i] (List.getElem_mem _))
          ts[i] _ rfl
      simp only [Function.comp_def]
      rw [he]
      exact congrArg OrderedTree.node (by simpa only [Fin.getElem_fin] using (List.ofFn_getElem (xs := ts)))

/-- The label at each valid address is the one prescribed by `f`. -/
theorem labelAt_decorate (t : OrderedTree) (f : List ℕ → L)
    (p : List ℕ) (hp : p ∈ t.addresses) : (decorate t f).labelAt p = f p := by
  induction p generalizing t f with
  | nil =>
    cases t
    simp only [decorate, labelAt_nil]
  | cons i p ih =>
    cases t with
    | node ts =>
      obtain ⟨j, rfl, hbranch⟩ := (OrderedTree.cons_mem_addresses_iff ts i p).mp hp
      rw [decorate]
      have hj : j.val < (List.ofFn fun k : Fin ts.length ↦
          decorate ts[k] (fun q ↦ f (k.val :: q))).length := by
        simpa only [List.length_ofFn] using j.isLt
      rw [labelAt_cons _ _ ⟨j.val, hj⟩]
      simp only [Fin.getElem_fin, List.getElem_ofFn]
      exact ih ts[j] (fun q ↦ f (j.val :: q)) hbranch

end GraphMinor.Kruskal.LabelledTree
