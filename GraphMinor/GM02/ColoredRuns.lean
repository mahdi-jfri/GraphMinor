module

public import Mathlib.Data.List.SplitBy
public import Mathlib.Data.List.Infix

/-!
# Maximal runs of one side of a separation

For the forward implication of corrected II (2.9), color every edge of an
original connecting path by a side that contains it. Group consecutive
edges with the same color. The groups are nonempty contiguous sublists,
each has constant color, and successive groups have different colors.
These groups will supply the side paths of the crossing scheme.
-/

@[expose] public section
namespace GraphMinor.GM02
open List
universe u

/-- Split a list into maximal consecutive runs of one color. -/
def coloredRuns {α : Type u} (color : α → Bool) (l : List α) : List (List α) :=
  l.splitBy (fun a b => color a == color b)

/-- Joining all runs recovers the original list. -/
theorem flatten_coloredRuns {α : Type u} (color : α → Bool) (l : List α) :
    (coloredRuns color l).flatten = l := List.flatten_splitBy _ _

/-- Every color run is nonempty. -/
theorem coloredRun_ne_nil {α : Type u} {color : α → Bool} {l r : List α}
    (hr : r ∈ coloredRuns color l) : r ≠ [] := List.ne_nil_of_mem_splitBy hr

/-- Each color run occurs contiguously in the original list. -/
theorem coloredRun_infix {α : Type u} {color : α → Bool} {l r : List α}
    (hr : r ∈ coloredRuns color l) : r <:+: l := by
  have hi := (List.singleton_infix_iff r (coloredRuns color l)).2 hr |>.flatten
  simpa only [List.flatten_singleton, flatten_coloredRuns] using hi

private theorem color_eq_first_of_chain {α : Type u} (color : α → Bool) (a : α)
    (l : List α) (hc : (a :: l).IsChain (fun x y => color x = color y)) :
    ∀ x ∈ a :: l, color x = color a := by
  induction l generalizing a with
  | nil => intro x hx; exact (List.mem_singleton.1 hx) ▸ rfl
  | cons b xs ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rfl
    · exact (ih b hc.of_cons x hx).trans hc.rel.symm

/-- Every element of a color run has the color of its first element. -/
theorem coloredRun_color_eq_head {α : Type u} {color : α → Bool} {l r : List α}
    (hr : r ∈ coloredRuns color l) {x : α} (hx : x ∈ r) :
    color x = color (r.head (coloredRun_ne_nil hr)) := by
  have hc := List.isChain_of_mem_splitBy hr
  have hc' : r.IsChain (fun a b => color a = color b) := by
    simpa only [beq_iff_eq] using hc
  cases r with
  | nil => exact (coloredRun_ne_nil hr rfl).elim
  | cons a xs => exact color_eq_first_of_chain color a xs hc' x hx

/-- Adjacent runs have different colors at their touching ends. -/
theorem coloredRuns_alternate {α : Type u} (color : α → Bool) (l : List α) :
    (coloredRuns color l).IsChain (fun a b => ∃ ha hb,
      color (a.getLast ha) ≠ color (b.head hb)) := by
  have h := List.isChain_getLast_head_splitBy (fun a b => color a == color b) l
  apply h.imp
  intro a b hab
  obtain ⟨ha, hb, hab⟩ := hab
  exact ⟨ha, hb, beq_eq_false_iff_ne.1 hab⟩

end GraphMinor.GM02
