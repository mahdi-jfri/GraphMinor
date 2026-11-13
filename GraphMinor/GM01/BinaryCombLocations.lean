module

public import GraphMinor.GM01.PathCombs
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# The binary branches in two comb cells

The skipped block in the proof of Graph Minors I, (4.1), page 55, supplies
a binary tree one level taller than each attached copy. Contract the two
spine vertices to its root. A nonempty binary word belongs to the copy
chosen by its last bit, with that last bit removed. The word convention
adds new bits at the front, so this assignment preserves parent edges.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

/-- The two spine positions used for the two children of the binary root. -/
def binaryCombIndex (bit : Bool) : Fin 2 := ⟨if bit then 1 else 0, by cases bit <;> decide⟩

/-- The two bits give distinct spine positions. -/
theorem binaryCombIndex_injective : Function.Injective binaryCombIndex := by
  intro a b h
  cases a <;> cases b <;> simp_all [binaryCombIndex]

/-- The location of a nonroot binary vertex in one of the two comb copies. -/
def binaryCombLocation (word : List Bool) (hne : word ≠ []) : PathCombVertex 2 :=
  Sum.inr (binaryCombIndex (word.getLast hne), word.dropLast)

/-- The children of the root map to the two empty-word attachment vertices. -/
theorem binaryCombLocation_singleton (bit : Bool) :
    binaryCombLocation [bit] (by simp) = Sum.inr (binaryCombIndex bit, []) := rfl

/-- Prepending a bit preserves the chosen copy and prepends that bit to
its internal word, whenever the parent is not the root. -/
theorem binaryCombLocation_cons (bit : Bool) (word : List Bool) (hne : word ≠ []) :
    binaryCombLocation (bit :: word) (by simp) =
      Sum.inr (binaryCombIndex (word.getLast hne), bit :: word.dropLast) := by
  simp only [binaryCombLocation, List.getLast_cons hne, List.dropLast_cons_of_ne_nil hne]

/-- The location map identifies no two nonroot binary vertices. -/
theorem binaryCombLocation_injective {word word' : List Bool} (hne : word ≠ []) (hne' : word' ≠ [])
    (h : binaryCombLocation word hne = binaryCombLocation word' hne') : word = word' := by
  have hp := Sum.inr.inj h
  have hlast := binaryCombIndex_injective (congrArg Prod.fst hp)
  have hdrop := congrArg Prod.snd hp
  dsimp only at hlast hdrop
  calc
    word = word.dropLast ++ [word.getLast hne] := (List.dropLast_append_getLast hne).symm
    _ = word'.dropLast ++ [word'.getLast hne'] := by rw [hdrop, hlast]
    _ = word' := List.dropLast_append_getLast hne'

/-- A valid nonroot binary word maps to a vertex in its attached copy. -/
theorem binaryCombLocation_mem {γ : ℕ} {word : List Bool} (hne : word ≠ [])
    (hw : word.length ≤ γ) : binaryCombLocation word hne ∈ (pathComb γ 2).verts := by
  change word.dropLast.length < γ
  cases word with
  | nil => exact False.elim (hne rfl)
  | cons bit word =>
    simp only [List.length_dropLast_cons]
    simp only [List.length_cons] at hw
    omega

end GraphMinor.GM01
