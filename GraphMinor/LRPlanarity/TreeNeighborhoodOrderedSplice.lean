module

public import Mathlib.Data.List.Pairwise
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

/-!
# Ordered lists under one interval substitution

Part IV, Section 7b of the planarity note substitutes a child's boundary
word for one attachment marker. In boundary parameters, the marker and
all new child points lie in one interval and every unchanged marker lies
outside it. A marker preceding the attachment lies before the entire
interval, and one following it lies after the entire interval. Thus the
ordered child list can replace that marker without changing the order of
any other entries.
-/

public section
namespace GraphMinor.LRPlanarity

open Set

/-- Part IV, Section 7b: replacing an interval marker by a sorted list of
points in that interval preserves strict parameter order. -/
theorem pairwise_parameter_splice {α : Type*} [DecidableEq α]
    (old replacement : List α) (marker : α) (before after : α → ℝ) {lo hi : ℝ}
    (hsorted : old.Pairwise (fun a b => before a < before b))
    (hmarker : before marker ∈ Icc lo hi)
    (houtside : ∀ p ∈ old, p ≠ marker → before p ∉ Icc lo hi ∧ after p = before p)
    (hnewsorted : replacement.Pairwise (fun a b => after a < after b))
    (hnewbounds : ∀ p ∈ replacement, after p ∈ Icc lo hi) :
    (old.flatMap (fun p => if p = marker then replacement else [p])).Pairwise
      (fun a b => after a < after b) := by
  let block := fun p => if p = marker then replacement else [p]
  change (old.flatMap block).Pairwise (fun a b => after a < after b)
  apply List.pairwise_flatMap.mpr
  constructor
  · intro p _
    by_cases hp : p = marker
    · simpa only [block,ite_eq_left hp] using hnewsorted
    · simp only [block,ite_eq_right hp,List.pairwise_singleton]
  · apply List.Pairwise.imp_of_mem ?_ hsorted
    intro p q hp hq hpq
    by_cases hpm : p = marker
    · subst p
      have hqm : q ≠ marker := by
        intro he
        rw [he] at hpq
        exact lt_irrefl _ hpq
      have hright : hi < before q := by
        apply lt_of_not_ge
        intro hle
        exact (houtside q hq hqm).1 ⟨hmarker.1.trans hpq.le,hle⟩
      dsimp only [block]
      rw [ite_eq_left (rfl : marker = marker),ite_eq_right hqm]
      intro a ha b hb
      have hbq : b = q := List.mem_singleton.mp hb
      subst b
      rw [(houtside q hq hqm).2]
      exact lt_of_le_of_lt (hnewbounds a ha).2 hright
    · by_cases hqm : q = marker
      · subst q
        have hleft : before p < lo := by
          apply lt_of_not_ge
          intro hle
          exact (houtside p hp hpm).1 ⟨hle,hpq.le.trans hmarker.2⟩
        dsimp only [block]
        rw [ite_eq_right hpm,ite_eq_left (rfl : marker = marker)]
        intro a ha b hb
        have hap : a = p := List.mem_singleton.mp ha
        subst a
        rw [(houtside p hp hpm).2]
        exact lt_of_lt_of_le hleft (hnewbounds b hb).1
      · dsimp only [block]
        rw [ite_eq_right hpm,ite_eq_right hqm]
        intro a ha b hb
        have hap : a = p := List.mem_singleton.mp ha
        have hbq : b = q := List.mem_singleton.mp hb
        subst a
        subst b
        rw [(houtside p hp hpm).2,(houtside q hq hqm).2]
        exact hpq

/-- Replacing a marker deletes that marker's old occurrence and adds the
replacement labels, leaving all other old labels present. -/
theorem mem_marker_splice_iff {α : Type*} [DecidableEq α] (old replacement : List α)
    (marker : α) (hmarker : marker ∈ old) (p : α) :
    p ∈ old.flatMap (fun e => if e = marker then replacement else [e]) ↔
      (p ∈ old ∧ p ≠ marker) ∨ p ∈ replacement := by
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨e,he,hp⟩
    by_cases hem : e = marker
    · simp only [hem,ite_true] at hp
      exact Or.inr hp
    · simp only [hem,ite_false] at hp
      have hpe : p = e := List.mem_singleton.mp hp
      subst p
      exact Or.inl ⟨he,hem⟩
  · rintro (⟨hp,hpm⟩ | hp)
    · exact ⟨p,hp,by rw [ite_eq_right hpm]; exact List.mem_singleton_self _⟩
    · exact ⟨marker,hmarker,by rw [ite_eq_left (rfl : marker = marker)]; exact hp⟩

end GraphMinor.LRPlanarity
