module

public import GraphMinor.Compute.GM06Alg34Cells
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import GraphMinor.Compute.GM06Alg34Layout

/-!
# The finite graph used to recompute regions

Number vertex, edge, and region cells in consecutive ranges. Join two
inactive cells when the supplied closure lists say they touch. This
ordinary finite simple graph has the same reachability as the cell
relation used in the complement-component proof. Its size is bounded
by the original input size, so generic RAM graph routines can use it.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

open Relation

/-- Total number of supplied vertex, edge, and region cells. -/
def cellCount (x : GM06DrawingData) : ℕ := x.n + (x.ends.length + x.regions.length)

/-- Pack the three supplied kinds of labels into consecutive finite ranges. -/
def cellNumbering (x : GM06DrawingData) : GM06CellIndex x ≃ Fin x.cellCount :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

/-- Touching of supplied cells is symmetric. -/
theorem cellTouch_symm (x : GM06DrawingData) (a b : GM06CellIndex x) :
    x.cellTouch a b = x.cellTouch b a := by
  simp only [cellTouch, or_comm]

/-- The finite incidence graph restricted to the complement cells.
Active drawing cells remain isolated and are omitted when listing regions. -/
def complementGraph (x : GM06DrawingData) (vs : List (Fin x.n)) : SimpleGraph (Fin x.cellCount) where
  Adj a b := a ≠ b ∧ x.activeCell vs (x.cellNumbering.symm a) = false ∧
    x.activeCell vs (x.cellNumbering.symm b) = false ∧
    x.cellTouch (x.cellNumbering.symm a) (x.cellNumbering.symm b) = true
  symm := ⟨by
    intro a b h
    exact ⟨Ne.symm h.1, h.2.2.1, h.2.1, (x.cellTouch_symm _ _).symm.trans h.2.2.2⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance (x : GM06DrawingData) (vs : List (Fin x.n)) : DecidableRel (x.complementGraph vs).Adj :=
  fun _ _ => inferInstanceAs (Decidable (_ ≠ _ ∧ _ = false ∧ _ = false ∧ _ = true))

/-- Packing cell labels and discarding self-loops preserves all cell reachability. -/
theorem complementGraph_reachable_iff (x : GM06DrawingData) (vs : List (Fin x.n))
    (a b : GM06CellIndex x) :
    (x.complementGraph vs).Reachable (x.cellNumbering a) (x.cellNumbering b) ↔
      ReflTransGen (fun c d => x.activeCell vs c = false ∧
        x.activeCell vs d = false ∧ x.cellTouch c d = true) a b := by
  constructor
  · intro hp
    have hf : ∀ p q : Fin x.cellCount, ReflTransGen (x.complementGraph vs).Adj p q →
        ReflTransGen (fun c d => x.activeCell vs c = false ∧
          x.activeCell vs d = false ∧ x.cellTouch c d = true)
          (x.cellNumbering.symm p) (x.cellNumbering.symm q) := by
      intro p q h
      induction h with
      | refl => exact .refl
      | tail _ hstep ih => exact ih.tail hstep.2
    simpa only [Equiv.symm_apply_apply] using hf _ _ ((SimpleGraph.reachable_iff_reflTransGen _ _).mp hp)
  · intro hp
    induction hp with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c hp hstep ih =>
      by_cases hbc : b = c
      · simpa only [hbc] using ih
      · apply ih.trans
        apply SimpleGraph.Adj.reachable
        change x.cellNumbering b ≠ x.cellNumbering c ∧ _
        simpa only [Equiv.symm_apply_apply] using
          (show x.cellNumbering b ≠ x.cellNumbering c ∧ x.activeCell vs b = false ∧
            x.activeCell vs c = false ∧ x.cellTouch b c = true from
            ⟨fun h => hbc (x.cellNumbering.injective h), hstep⟩)

/-- The number of cells used by the region recomputation is at most the
size of the original finite drawing input. -/
theorem cellCount_le_size (x : GM06DrawingData) : x.cellCount ≤ x.size := by
  have hwords := x.words_length
  have hregions := x.regionWords_length
  have hsize : x.size = x.n + x.words.length := rfl
  dsimp only [cellCount]
  omega

end GraphMinor.Compute.GM06DrawingData
