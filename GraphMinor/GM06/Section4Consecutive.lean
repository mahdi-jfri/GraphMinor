module

public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Max

/-!
# Chaining consecutive points of a finite ordered set

The last argument of VI (4.2) joins vertices along a cuff base. It is
enough to join consecutive vertices: adding the largest point extends
the chain through the previous largest point. This finite-order fact
lets us use only whole-boundary segments for the minimal paths.
-/

public section

namespace GraphMinor.GM06

open Set

/-- An equivalence relation that joins consecutive points of a finite
linearly ordered set joins every pair of its points. -/
theorem relation_of_consecutive_finite
    {α : Type*} [LinearOrder α] {W : Set α} (hW : W.Finite)
    {R : α → α → Prop} (hR : Equivalence R)
    (hnext : ∀ x ∈ W, ∀ y ∈ W, x < y → (∀ z ∈ W, ¬ (x < z ∧ z < y)) → R x y) :
    ∀ x ∈ W, ∀ y ∈ W, R x y := by
  classical
  suffices h : ∀ F : Finset α,
      (∀ x ∈ F, ∀ y ∈ F, x < y → (∀ z ∈ F, ¬ (x < z ∧ z < y)) → R x y) →
      ∀ x ∈ F, ∀ y ∈ F, R x y by
    simpa only [hW.mem_toFinset] using
      h hW.toFinset (by simpa only [hW.mem_toFinset] using hnext)
  intro F
  induction F using Finset.induction_on_max with
  | empty => simp
  | @insert a F hlt ih =>
    intro hn
    have hnF : ∀ x ∈ F, ∀ y ∈ F, x < y →
        (∀ z ∈ F, ¬ (x < z ∧ z < y)) → R x y := by
      intro x hx y hy hxy hz
      apply hn x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy
      intro z hzi hxyz
      rcases Finset.mem_insert.mp hzi with rfl | hzF
      · exact (hlt y hy).not_gt hxyz.2
      · exact hz z hzF hxyz
    have hi := ih hnF
    have hto : ∀ x ∈ insert a F, R x a := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxF
      · subst x
        exact hR.refl a
      · let m := F.max' ⟨x, hxF⟩
        have hm : m ∈ F := F.max'_mem ⟨x, hxF⟩
        have hma : R m a := by
          apply hn m (Finset.mem_insert_of_mem hm) a (Finset.mem_insert_self _ _) (hlt m hm)
          intro z hz hmza
          rcases Finset.mem_insert.mp hz with hza | hzF
          · subst z
            exact lt_irrefl a hmza.2
          · exact (Finset.le_max' F z hzF).not_gt hmza.1
        exact hR.trans (hi x hxF m hm) hma
    intro x hx y hy
    exact hR.trans (hto x hx) (hR.symm (hto y hy))

end GraphMinor.GM06
